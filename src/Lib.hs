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
import           Data.Void (Void)

type Word = String
data CAT = S | NP | VP | A | N | DET | COP | V deriving (Show, Eq, Ord)

type NodeData = CAT

data NonRecursiveTree leafType branchType =
  Leaf leafType
  | Branch NodeData [branchType]
  deriving (Functor, Foldable, Traversable)

type Deterministic = Identity -- a type synonym to indicate that the monad is just the identity

type Tree m leafType = FT.FreeT (NonRecursiveTree leafType) m Void
type Fragment m leafType = FT.FreeT (NonRecursiveTree leafType) m CAT

type FragmentDict = CAT -> [Fragment Deterministic Word]


cats :: [CAT]
cats = [S, NP, VP, DET, A, N, COP, V]
words :: [Word]
words = ["the", "a", "turn", "blue", "circle", "square", "is"]

-- helper functions
branch a bs = FT.Free $ Branch a bs
leaf = FT.Free . Leaf
pauseAt = FT.Pure


--------------------------------------
-- progressively more complex examples
--------------------------------------

deterministicSimpleTree :: Tree Deterministic Word
deterministicSimpleTree = Fold.unfold (Compose . Identity . \case

  S  -> branch S [NP, VP]
  NP ->  branch NP [DET, N]
  DET ->  leaf "the"
  N  -> leaf "cat"
  VP ->  branch VP [V, NP]
  V  -> leaf "sees") 

  S -- starting category

deterministicSimpleFragment :: Fragment Deterministic Word
deterministicSimpleFragment = Fold.unfold (Compose . Identity . \case
  
  S  -> branch S [NP, VP]
  NP ->  branch NP [DET, N]
  DET ->  leaf "the"
  N  -> leaf "cat"
  VP ->  pauseAt VP
  V  -> leaf "sees") 

  S 

deterministicComplexTree :: FragmentDict -> Tree Deterministic Word
deterministicComplexTree fragmentDict = Fold.futu (Compose . Identity . \case
  
  S  -> branch S [NP, VP]
  NP ->  branch NP [DET, N]
  DET -> leaf "the"
  N  -> leaf "cat"
  VP -> head (loadFragments . fragmentToBranch <$> (fragmentDict VP))
  V  -> leaf "sees"
  ) 

  S

  where 

  branch a bs =  FT.Free $ Branch a (F.Pure <$> bs)


deterministicComplexFragment :: FragmentDict -> Fragment Deterministic Word
deterministicComplexFragment fragmentDict = Fold.futu (Compose . Identity . \case
  
  S  -> branch S [NP, VP]
  DET -> leaf "the"
  N  -> leaf "cat"
  NP ->  pauseAt NP
  VP ->  head (loadFragments . fragmentToBranch <$> (fragmentDict VP))
  V  -> leaf "sees")

  S

  where

  branch a bs =  FT.Free $ Branch a (F.Pure <$> bs)

probabilisticSimpleTree :: MonadSample m => Tree m Word
probabilisticSimpleTree = Fold.unfold (Compose . \case

  S  -> return $ branch S [NP, VP]
  NP ->  return $ branch NP [DET, N]
  DET -> return $ leaf "the"
  N  -> uniformD [branch N [A, N], leaf "idea"]
  A  -> uniformD [leaf "green", leaf "furious"]
  VP ->  return $ branch NP [V, NP]
  V  -> return $ leaf "sees")

  S
 
probabilisticSimpleFragment :: MonadSample m => Fragment m Word
probabilisticSimpleFragment = Fold.unfold (Compose . \case

  S  -> return $ branch S [NP, VP]
  NP ->  return $ branch NP [DET, N]
  DET -> return $ leaf "the"
  N  -> uniformD [branch N [A, N], leaf "idea"]
  A  -> uniformD [leaf "green", leaf "furious"]
  VP ->  uniformD [FT.Pure VP, branch NP [V, NP]]
  V  -> return $ leaf "sees")

  S

probabilisticComplexTree :: MonadSample m => FragmentDict -> Tree m Word
probabilisticComplexTree fragmentDict = Fold.futu (Compose . \case

  S  -> return $ branch S [NP, VP]
  NP ->  return $ branch NP [DET, N]
  DET -> return $ leaf "the"
  N  -> uniformD [branch N [A, N], leaf "idea"]
  A  -> uniformD [leaf "green", leaf "furious"]
  VP ->  uniformD (loadFragments . fragmentToBranch <$> (fragmentDict VP)) 
  V  -> return $ leaf "sees")

  S

  where 

  branch a bs = FT.Free $ Branch a (F.Pure <$> bs)

probabilisticComplexFragment :: MonadSample m => FragmentDict -> Fragment m Word
probabilisticComplexFragment fragmentDict = Fold.futu (Compose . go) S where


  go S = return $ branch S [NP, VP]
  go NP = return $ FT.Pure NP
  go DET = return $ leaf "the"
  go N = uniformD [branch N [A, N], leaf "idea"]
  go A = uniformD [leaf "green", leaf "furious"]
  go V = return $ leaf "sees"
  go VP = uniformD (loadFragments . fragmentToBranch <$> (fragmentDict VP)) 


  branch a bs = FT.Free $ Branch a (F.Pure <$> bs)
  leaf = FT.Free . Leaf





makeTrees = do
  saveDiagram "img/deterministicSimpleTree.svg" $ toDiagram $ deterministicSimpleTree
  saveDiagram "img/deterministicSimpleFragment.svg" $ toDiagram deterministicSimpleFragment
  saveDiagram "img/deterministicComplexTree.svg" $ toDiagram $ deterministicComplexTree aPossibleGrammar
  saveDiagram "img/deterministicComplexFragment.svg" $ toDiagram $ deterministicComplexFragment aPossibleGrammar
  
  -- saveDiagram "img/probabilisticSimpleTree.svg" . toDiagram =<< (sampleIO $ FT.joinFreeT probabilisticSimpleTree)
  -- saveDiagram "img/probabilisticSimpleFragment.svg" . toDiagram =<< (sampleIO $ FT.joinFreeT probabilisticSimpleFragment)
  -- saveDiagram "img/probabilisticComplexTree.svg" . toDiagram =<< (sampleIO $ FT.joinFreeT $ probabilisticComplexTree aPossibleGrammar)
  -- saveDiagram "img/probabilisticComplexFragment.svg" . toDiagram =<< (sampleIO $ FT.joinFreeT $ probabilisticComplexFragment aPossibleGrammar)

  -- saveDiagram "img/fragmentGrammar.svg" . toDiagram =<< (sampleIO $ FT.joinFreeT $ fragmentGrammar aPossibleGrammar)


aPossibleGrammar :: FragmentDict
aPossibleGrammar = \case
  
  S -> [branch S [pauseAt NP, pauseAt VP] ]
  NP -> [branch S [pauseAt DET, pauseAt N] ]
  VP -> [branch VP [pauseAt V, branch NP [pauseAt DET, leaf "dog"] ] ]
  N -> [leaf "dog", pauseAt N]
  V -> [leaf "sees"]
  DET -> [leaf "the"]

  where 

  branch a bs = FT.free $ FT.Free $ Branch a bs
  leaf = FT.free . FT.Free . Leaf
  pauseAt = FT.free . FT.Pure



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



saveDiagram :: String -> Diagram B -> IO ()
saveDiagram path diagram = let size = mkSizeSpec $ r2 (Just 500, Just 500) in renderSVG path size diagram




fragmentToBranch :: Fragment Deterministic Word -> NonRecursiveTree Word (Fragment Deterministic Word)
fragmentToBranch (FT.FreeT (Identity (FT.Pure x))) = Branch S [FT.free $ FT.Pure x]
fragmentToBranch (FT.FreeT (Identity (FT.Free (Branch c brs)))) = Branch c brs
fragmentToBranch (FT.FreeT (Identity (FT.Free (Leaf x)))) = Leaf x

-- converts between Free from Control.Monad.Trans.Free and Control.Monad.Free
toFree :: Functor f => FT.Free f a1 -> F.Free f a1
toFree = Fold.cata go where
  go (Compose (Identity (FT.Free x))) = F.Free x
  go (Compose (Identity (FT.Pure x))) = F.Pure x

loadFragments = FT.Free . fmap (toFree . FT.transFreeT (Compose . return . FT.Free))

freeTreeAlgebra :: Show a => Compose Identity (FT.FreeF (NonRecursiveTree [Char]) a) [Char] -> [Char]
freeTreeAlgebra (Compose (Identity (FT.Free (Branch c brs)))) = join $ intersperse " " brs
freeTreeAlgebra (Compose (Identity (FT.Free (Leaf a)))) = a 
freeTreeAlgebra (Compose (Identity (FT.Pure a))) = show a

toDiagram :: Show a => FT.FreeT (NonRecursiveTree Word) Deterministic a -> Diagram B
toDiagram = Fold.cata alg where
  

  alg (Compose (Identity (FT.Pure x))) = text (show x) <> rect (maximum [fromIntegral (length (show x)), 3]) 2 # lc blue
  alg (Compose (Identity (FT.Free (Branch c brs)))) = combineDiagrams c brs
  alg (Compose (Identity (FT.Free (Leaf x)))) = text x <> rect (maximum [fromIntegral $ length x, 3]) 2 # lc black

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






----------------------------
-- The full fragment grammar 
----------------------------

fragmentGrammar :: MonadSample m => FragmentDict -> Fragment m Word
fragmentGrammar fragmentDict = Fold.futu go S where
  
  howMuchToReuse = 1.0
  howMuchToSuspend = 0.5
  howMuchToRecurse = 0.5
  
  go cat = Compose $ do

    reuse <- bernoulli howMuchToReuse
    
    if reuse && not (null (fragmentDict cat)) then uniformD (FT.Free . fmap (toFree . FT.transFreeT (Compose . return . FT.Free)) . fragmentToBranch <$> (fragmentDict cat))
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

runFragmentGrammar :: IO ()
runFragmentGrammar = do 

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


{-

todos

- try generalizing stochastic memoization to arbitrary recursive types

-}
