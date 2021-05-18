{-# LANGUAGE DeriveTraversable, LambdaCase, FlexibleContexts, TypeFamilies, GADTs, TupleSections, NoMonomorphismRestriction #-}

module Lib where

import Prelude hiding (words, Word)

import           Data.List (intersperse)
import           Data.Set (Set)
import           Data.Maybe (fromMaybe, isJust)
import qualified Data.Map as M
import           Data.Functor.Compose
import qualified Data.Functor.Foldable as Fold

import           Control.Comonad.Cofree (Cofree(..))
import qualified Control.Monad.Free as F
import qualified Control.Monad.Trans.Free as FT

import           Diagrams.Prelude               hiding (E, (:<), (^.), normalize, set) 
import           Diagrams.Backend.SVG.CmdLine    (B)
import           Diagrams.Backend.SVG            (renderSVG)

import           Control.Monad.Bayes.Enumerator
import           Control.Monad.Bayes.Sampler
import           Control.Monad.Bayes.Weighted
import           Control.Monad.Bayes.Traced
import           Control.Monad.Bayes.Class
import           Control.Monad.State 
import           Data.Fix


newtype FixT f m = FixT {runFixT :: (m (f (FixT f m) ))}

type instance Fold.Base (FixT f m) = Compose m f

instance (Functor m, Functor f) => Fold.Recursive (FixT f m) where
  project = Compose . runFixT
instance (Functor m, Functor f) => Fold.Corecursive (FixT f m) where
  embed = FixT . getCompose



type Word = String
data CAT = S | NP | VP | A | N | DET | COP | V deriving (Show, Eq, Ord)

type NodeData = CAT
data NonRecursiveTree leafType branchType =
  Leaf leafType
  | Branch NodeData [branchType]
  deriving (Functor, Foldable, Traversable)

type RecursiveTree m leafType = FixT (NonRecursiveTree leafType) m
type Fragment m leafType pauseType = FT.FreeT (NonRecursiveTree leafType) m pauseType
type FragmentDict = CAT -> [Fragment Deterministic Word CAT]
type Deterministic = Identity -- a type synonym to indicate that the monad is just the identity


cats :: [CAT]
cats = [S, NP, VP, DET, A, N, COP, V]
words :: [Word]
words = ["the", "a", "turn", "blue", "circle", "square", "is"]


deterministicSimpleTree :: RecursiveTree Deterministic Word
deterministicSimpleTree = Fold.unfold (Compose . Identity . \case

  S  -> Branch S [NP, VP]
  NP ->  Branch S [DET, N]
  DET -> Leaf "the"
  N  -> Leaf "cat"
  VP ->  Branch VP [V, NP]
  V  -> Leaf "sees") 

  S -- starting category

deterministicSimpleFragment :: Fragment Deterministic Word CAT
deterministicSimpleFragment = Fold.unfold (Compose . Identity . \case
  
  S  -> branch S [NP, VP]
  NP ->  branch NP [DET, N]
  DET ->  leaf "the"
  N  -> leaf "cat"
  VP ->  pauseAt VP
  V  -> leaf "sees") 

  S 

  where 

  branch a bs = FT.Free $ Branch a bs
  leaf = FT.Free . Leaf
  pauseAt = FT.Pure


deterministicComplexTree :: FragmentDict -> RecursiveTree Deterministic Word
deterministicComplexTree fragmentDict = Fold.futu (Compose . Identity . \case
  
  S  -> Branch S [F.Pure NP, F.Pure VP]
  NP ->  Branch NP [F.Pure DET, F.Pure N]
  DET -> Leaf "the"
  N  -> Leaf "cat"
  VP ->   ((toFree . FT.transFreeT (Compose . return)) <$> fragmentToBranch' (head $ fragmentDict VP)) :: NonRecursiveTree Word (F.Free (Compose Identity (NonRecursiveTree Word)) CAT) -- Fragment Deterministic Word CAT
  --   -- Branch (VP, (True, True)) 
  --   -- [F.Pure V, 
  --   --  F.Free $ Branch (NP, (True,True)) 
  --   --   [F.Pure DET, 
  --   --    F.Free $ Leaf "dog"]]
  V  -> Leaf "sees"
  ) 

  S

deterministicComplexFragment :: FragmentDict -> Fragment Deterministic Word CAT
deterministicComplexFragment fragmentDict = Fold.futu (Compose . Identity . go) S where
  
  branch a bs =  FT.Free $ Branch a (F.Pure <$> bs)
  leaf = FT.Free . Leaf
  pauseAt = FT.Pure

  go S = branch S [NP, VP]
  go DET = leaf "the"
  go N = leaf "cat"
  go NP = pauseAt NP
  go VP = (FT.Free $ (toFree . FT.transFreeT (Compose . return . FT.Free)) <$> fragmentToBranch' (head $ fragmentDict VP)) :: FT.FreeF (NonRecursiveTree Word) CAT (F.Free (Fold.Base (Fragment Deterministic Word CAT)) CAT)
  go V = leaf "sees"


probabilisticSimpleTree :: MonadSample m => RecursiveTree m Word
probabilisticSimpleTree = Fold.unfold (Compose . go) S where

  go S = return $ Branch S [NP, VP]
  go NP = return $ Branch NP [DET, N]
  go DET = return $ Leaf "the"
  go N = uniformD [Branch N [A, N], Leaf "idea"]
  go A = uniformD [Leaf "green", Leaf "furious"]
  go VP = return $ Branch NP [V, NP]
  go V = return $ Leaf "sees"

probabilisticSimpleFragment :: MonadSample m => Fragment m Word CAT
probabilisticSimpleFragment = Fold.unfold (Compose . go) S where

  branch a bs = FT.Free $ Branch a bs
  leaf = FT.Free . Leaf

  go S = return $ branch S [NP, VP]
  go NP = return $ branch NP [DET, N]
  go DET = return $ leaf "the"
  go N = uniformD [branch N [A, N], leaf "idea"]
  go A = uniformD [leaf "green", leaf "furious"]
  go VP = uniformD [FT.Pure VP, branch NP [V, NP]]
  go V = return $ leaf "sees"

probabilisticComplexTree :: MonadSample m => FragmentDict -> RecursiveTree m Word
probabilisticComplexTree fragmentDict = Fold.futu (Compose . go) S where

  branch a bs = Branch a (F.Pure <$> bs)
  leaf = Leaf

  go S = return $ branch S [NP, VP]
  go NP = return $ branch NP [DET, N]
  go DET = return $ leaf "the"
  go N = uniformD [branch N [A, N], leaf "idea"]
  go A = uniformD [leaf "green", leaf "furious"]
  -- go VP = (uniformD $ fmap (toFree . FT.transFreeT (Compose . return)) <$> fragmentToBranch' <$> (fragmentDict VP)) :: MonadSample m => m (NonRecursiveTree Word (F.Free (Fold.Base (RecursiveTree m Word)) CAT)) -- MonadSample m => FT.FreeF (NonRecursiveTree Word) CAT (F.Free (Fold.Base (Fragment m Word CAT)) CAT)
  go VP =  (return $ (toFree . FT.transFreeT (Compose . return)) <$> fragmentToBranch' (head $ fragmentDict VP)) :: MonadSample m => m (NonRecursiveTree Word (F.Free (Fold.Base (RecursiveTree m Word)) CAT)) -- MonadSample m => FT.FreeF (NonRecursiveTree Word) CAT (F.Free (Fold.Base (Fragment m Word CAT)) CAT)
-- ((toFree . FT.transFreeT (Compose . return)) <$> fragmentToBranch' (head $ fragmentDict VP)) :: NonRecursiveTree Word (F.Free (Compose Identity (NonRecursiveTree Word)) CAT) -- Fragment Deterministic Word CAT
  go V = return $ leaf "sees"


probabilisticComplexFragment :: MonadSample m => FragmentDict -> Fragment m Word CAT
probabilisticComplexFragment fragmentDict = Fold.futu (Compose . go) S where

  branch a bs = FT.Free $ Branch a (F.Pure <$> bs)
  leaf = FT.Free . Leaf

  go S = return $ branch S [NP, VP]
  go NP = return $ FT.Pure NP
  go DET = return $ leaf "the"
  go N = uniformD [branch N [A, N], leaf "idea"]
  go A = uniformD [leaf "green", leaf "furious"]
  go V = return $ leaf "sees"
  go VP = uniformD (FT.Free . fmap (toFree . FT.transFreeT (Compose . return . FT.Free)) . fragmentToBranch' <$> (fragmentDict VP)) 




fragmentGrammar :: MonadSample m => FragmentDict -> Fragment m Word CAT
fragmentGrammar fragmentDict = Fold.futu go S where
  
  howMuchToReuse = 1.0
  howMuchToSuspend = 0.5
  howMuchToRecurse = 0.5
  
  go cat = Compose $ do

    reuse <- bernoulli howMuchToReuse
    
    if reuse && not (null (fragmentDict cat)) then uniformD (FT.Free . fmap (toFree . FT.transFreeT (Compose . return . FT.Free)) . fragmentToBranch' <$> (fragmentDict cat))
    else do
      recurse <- bernoulli howMuchToRecurse
      if recurse then makeBranches cat else FT.Free . Leaf <$> uniformD words 

  makeBranchCompositional = do
    suspend <- bernoulli howMuchToSuspend
    cat <- uniformD cats
    return $ if suspend then F.Free $ Compose $ return $ FT.Pure cat else F.Pure cat

  makeBranches cat = do
    bL <- makeBranchCompositional
    bR <- makeBranchCompositional
    return (FT.Free $ Branch cat [bL, bR] )


makeTrees = do
  -- saveDiagram "img/deterministicSimpleTree.svg" $ toDiagram $ fixToFree deterministicSimpleTree
  -- saveDiagram "img/deterministicSimpleFragment.svg" $ toDiagram deterministicSimpleFragment
  -- saveDiagram "img/deterministicComplexTree.svg" $ toDiagram $ fixToFree $ deterministicComplexTree aPossibleGrammar
  -- saveDiagram "img/deterministicComplexFragment.svg" $ toDiagram $ deterministicComplexFragment aPossibleGrammar
  
  -- saveDiagram "img/probabilisticSimpleTree.svg" . toDiagram =<< (sampleIO $ FT.joinFreeT $ fixToFree probabilisticSimpleTree)
  -- saveDiagram "img/probabilisticSimpleFragment.svg" . toDiagram =<< (sampleIO $ FT.joinFreeT probabilisticSimpleFragment)
  -- saveDiagram "img/probabilisticComplexTree.svg" . toDiagram =<< (sampleIO $ FT.joinFreeT $ fixToFree $ probabilisticComplexTree aPossibleGrammar)
  -- saveDiagram "img/probabilisticComplexFragment.svg" . toDiagram =<< (sampleIO $ FT.joinFreeT $ probabilisticComplexFragment aPossibleGrammar)

  saveDiagram "img/fragmentGrammar.svg" . toDiagram =<< (sampleIO $ FT.joinFreeT $ fragmentGrammar aPossibleGrammar)


aPossibleGrammar :: FragmentDict
aPossibleGrammar = \case
  
  S -> [branch S (node NP) (node VP)]
  NP -> [branch S (node DET) (node N)]
  VP -> [branch VP (node V) (branch NP (node DET) (leaf "dog"))]

  N -> [leaf "dog", node N]
  V -> [leaf "sees"]
  DET -> [leaf "the"]

node cat = FT.free $ FT.Pure cat
leaf str = FT.free $ FT.Free $ Leaf str
branch cat lb rb  = FT.free (FT.Free (Branch cat [lb, rb]))


step :: MonadSample m => CAT -> FragmentDict -> m FragmentDict
step cat fragDict = do 
 frag <- FT.joinFreeT $ fragmentGrammar fragDict
 addNew <- bernoulli 0.5
 let newFragDict y = if y == cat then fragDict y <> [frag] else fragDict y
 return (if addNew then newFragDict else fragDict)

iterateMInt :: Monad m => (a -> m a) -> a -> Int -> m a
iterateMInt step init int = if int == 0 then step init else do
  result <- step init
  iterateMInt step result (int -1)



makeDiagram :: IO ()
makeDiagram = do 

  (mcmcSamplesOfFragmentTrees, weight) <- sampleIO (runWeighted $ mh 10 $ do 
    frags <- (=<< cats) <$> iterateMInt (step S) (const []) 10
    let sents = Fold.cata freeTreeAlgebra <$> frags
    condition ("the circle" `elem` sents)
    return frags
    )

  let diagram = hsep 0.5 $ intersperse (vrule 50) $ (toDiagram <$> last mcmcSamplesOfFragmentTrees)
  print (Fold.cata freeTreeAlgebra <$> last mcmcSamplesOfFragmentTrees)
  print weight
  saveDiagram "img/fragment.svg" diagram
  -- renderSVG "img/fragment.svg" size diagram

saveDiagram path diagram = let size = mkSizeSpec $ r2 (Just 500, Just 500) in renderSVG path size diagram

-- foo :: MonadSample m0 => [NonRecursiveTree String (F.Free   (Compose m0 (FT.FreeF (NonRecursiveTree String) CAT))
--                                           CAT)]
-- foo = fragmentToBranch <$> aPossibleGrammar S

-- fragmentToBranch :: MonadSample m => FT.Free (NonRecursiveTree a) b -> NonRecursiveTree a (F.Free (Compose m (FT.FreeF (NonRecursiveTree a) b)) b)
fragmentToBranch (FT.FreeT (Identity (FT.Pure x))) = Branch S [F.Pure x]
fragmentToBranch (FT.FreeT (Identity (FT.Free (Branch c brs)))) = Branch c (toFree <$> brs)
fragmentToBranch (FT.FreeT (Identity (FT.Free (Leaf x)))) = Leaf x


fragmentToBranch' :: Fragment Deterministic Word CAT -> NonRecursiveTree
  Word (Fragment Deterministic Word CAT)
fragmentToBranch' (FT.FreeT (Identity (FT.Pure x))) = Branch S [FT.free $ FT.Pure x]
fragmentToBranch' (FT.FreeT (Identity (FT.Free (Branch c brs)))) = Branch c brs
fragmentToBranch' (FT.FreeT (Identity (FT.Free (Leaf x)))) = Leaf x

-- converts between Free from Control.Monad.Trans.Free and Control.Monad.Free
toFree :: Functor f => FT.Free f a1 -> F.Free f a1
toFree = Fold.cata go where
  go (Compose (Identity (FT.Free x))) = F.Free x
  go (Compose (Identity (FT.Pure x))) = F.Pure x
  -- go (Compose (Identity (FT.Free (Branch c brs)))) = F.Free $ Compose $ return $ FT.Free $ Branch c brs


-- converts from FixT to Free
fixToFree :: (Functor f, Functor m) => FixT f m -> FT.FreeT f m ()
fixToFree = Fold.unfold $ \(FixT x) -> Compose $ FT.Free <$> x


-- loadFragment :: MonadSample m => FT.Free (NonRecursiveTree a) b -> F.Free (Compose m (FT.FreeF (NonRecursiveTree a) b)) b
loadFragment = Fold.cata go where
  go (Compose (Identity (FT.Free (Leaf x)))) = F.Free $ Compose $ return $ FT.Free $ Leaf x
  go (Compose (Identity (FT.Pure x))) = F.Pure x
  go (Compose (Identity (FT.Free (Branch c brs)))) = F.Free $ Compose $ return $ FT.Free $ Branch c brs


freeTreeAlgebra :: Show a => Compose Identity (FT.FreeF (NonRecursiveTree [Char]) a) [Char] -> [Char]
freeTreeAlgebra (Compose (Identity (FT.Free (Branch c brs)))) = join $ intersperse " " brs
freeTreeAlgebra (Compose (Identity (FT.Free (Leaf a)))) = a 
freeTreeAlgebra (Compose (Identity (FT.Pure a))) = show a


toDiagramFix :: RecursiveTree Deterministic String -> Diagram B
toDiagramFix = Fold.cata alg where

  alg (Compose (Identity ((Branch c brs)))) = combineDiagrams c brs
  alg (Compose (Identity ((Leaf x)))) = text x <> rect (maximum [fromIntegral $ length x, 3]) 2 # lc black

toDiagram :: Show a => Fragment Deterministic String a -> Diagram B
toDiagram = Fold.cata alg where
  

  alg (Compose (Identity (FT.Pure x))) =
    text (show x) <> rect (maximum [fromIntegral (length (show x)), 3]) 2 # lc blue

  alg (Compose (Identity (FT.Free (Branch c brs)))) = combineDiagrams c brs
  alg (Compose (Identity (FT.Free (Leaf x)))) = text x <> rect (maximum [fromIntegral $ length x, 3]) 2 # lc black

  -- combine two diagrams together
combineDiagrams :: CAT -> [Diagram B] -> Diagram B
combineDiagrams c ds =

  let arrowStyle = (with & arrowHead .~ dart & headLength .~ verySmall & tailLength .~ small)
  
  in vsep 2 [
    text (show c) <> rect 2 2 # centerX <> translate (r2 (1, -1)) (arrowV' arrowStyle (r2 (1.5, -2))) <> translate (r2 (-1, -1)) (arrowV' arrowStyle (r2 (-1.5, -2))),
    -- <> (case f of 
    --   Just f' -> translateX 5 ( (scale 0.5 (circle 5 <> toDiagram f')))
    --   Nothing -> mempty),
    hsep 0.5 [d # lc black | d <- ds]
       # centerX
    ]
  where
    colorIdiom f color d = if f then d # lc color else d
    --   # connectOutside' arrowStyle (show (str1<>"|"<>str2)) (show str1)
    --   # connectOutside' arrowStyle (show (str1<>"|"<>str2)) (show str2)

{-

todos

- try generalizing stochastic memoization to arbitrary recursive types

-}
