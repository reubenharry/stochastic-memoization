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

type IsIdiom = Bool
type NodeData = (CAT, IsIdiom)

data NonRecursiveTree leafType branchType =
  Leaf NodeData leafType
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
leaf a = FT.Free . Leaf a
pauseAt = FT.Pure


--------------------------------------
-- progressively more complex examples
--------------------------------------

deterministicSimpleTree :: Tree Deterministic Word
deterministicSimpleTree = Fold.unfold (Compose . Identity . \case

  S  -> branch (S, False) [NP, VP]
  NP ->  branch (NP, False) [DET, N]
  DET ->  leaf (N, False) "the"
  N  -> leaf (N, False) "cat"
  VP ->  branch (VP, False) [V, NP]
  V  -> leaf (V, False) "sees") 

  S -- starting category

deterministicSimpleFragment :: Fragment Deterministic Word
deterministicSimpleFragment = Fold.unfold (Compose . Identity . \case
  
  S  -> branch (S, False) [NP, VP]
  NP ->  branch (NP, False) [DET, N]
  DET ->  leaf (S, False) "the"
  N  -> leaf (N, False) "cat"
  VP ->  pauseAt VP
  V  -> leaf (V, False) "sees") 

  S 

deterministicComplexTree :: FragmentDict -> Tree Deterministic Word
deterministicComplexTree fragmentDict = Fold.futu (Compose . Identity . \case
  
  S  -> branch (S, False) [NP, VP]
  NP ->  branch (NP, False) [DET, N]
  DET -> leaf (DET, False) "the"
  N  -> leaf (N, False) "cat"
  VP -> head (loadFragments . fragmentToBranch <$> (fragmentDict VP))
  V  -> leaf (V, False) "sees"
  ) 

  S

  where 

  branch a bs =  FT.Free $ Branch a (F.Pure <$> bs)


deterministicComplexFragment :: FragmentDict -> Fragment Deterministic Word
deterministicComplexFragment fragmentDict = Fold.futu (Compose . Identity . \case
  
  S  -> branch (S, False) [NP, VP]
  DET -> leaf (DET, False) "the"
  N  -> leaf (N, False) "cat"
  NP ->  pauseAt NP
  VP ->  head (loadFragments . fragmentToBranch <$> (fragmentDict VP))
  V  -> leaf (V, False) "sees")

  S

  where

  branch a bs =  FT.Free $ Branch a (F.Pure <$> bs)

probabilisticSimpleTree :: MonadSample m => Tree m Word
probabilisticSimpleTree = Fold.unfold (Compose . \case

  S  -> return $ branch (S, False) [NP, VP]
  NP ->  return $ branch (NP, False) [DET, N]
  DET -> return $ leaf (DET, False) "the"
  N  -> uniformD [branch (N, False) [A, N], leaf (N, False) "idea"]
  A  -> uniformD [leaf (A, False) "green", leaf (A, False) "furious"]
  VP ->  return $ branch (NP, False) [V, NP]
  V  -> return $ leaf (V, False) "sees")

  S
 
probabilisticSimpleFragment :: MonadSample m => Fragment m Word
probabilisticSimpleFragment = Fold.unfold (Compose . \case

  S  -> return $ branch (S, False) [NP, VP]
  NP ->  return $ branch (NP, False) [DET, N]
  DET -> return $ leaf (DET, False) "the"
  N  -> uniformD [branch (N, False) [A, N], leaf (N, False) "idea"]
  A  -> uniformD [leaf (A, False) "green", leaf (A, False) "furious"]
  VP ->  uniformD [FT.Pure VP, branch (NP, False) [V, NP]]
  V  -> return $ leaf (V, False) "sees")

  S

probabilisticComplexTree :: MonadSample m => FragmentDict -> Tree m Word
probabilisticComplexTree fragmentDict = Fold.futu (Compose . \case

  S  -> return $ branch (S, False) [NP, VP]
  NP ->  return $ branch (NP, False) [DET, N]
  DET -> return $ leaf (DET, False) "the"
  N  -> uniformD [branch (N, False) [A, N], leaf (N, False) "idea"]
  A  -> uniformD [leaf (A, False) "green", leaf (A, False) "furious"]
  VP ->  uniformD (loadFragments . fragmentToBranch <$> (fragmentDict VP)) 
  V  -> return $ leaf (V, False) "sees")

  S

  where 

  branch a bs = FT.Free $ Branch a (F.Pure <$> bs)

probabilisticComplexFragment :: MonadSample m => FragmentDict -> Fragment m Word
probabilisticComplexFragment fragmentDict = Fold.futu (Compose . go) S where


  go S = return $ branch (S, False) [NP, VP]
  go NP = return $ FT.Pure NP
  go DET = return $ leaf (DET, False) "the"
  go N = uniformD [branch (N, False) [A, N], leaf (N, False) "idea"]
  go A = uniformD [leaf (A, False) "green", leaf (A, False) "furious"]
  go V = return $ leaf (V, False) "sees"
  go VP = uniformD (loadFragments . fragmentToBranch <$> (fragmentDict VP)) 


  branch a bs = FT.Free $ Branch a (F.Pure <$> bs)
  leaf a = FT.Free . Leaf a





aPossibleGrammar :: FragmentDict
aPossibleGrammar = \case
  
  S -> [branch (S, True) [pauseAt NP, pauseAt VP] ]
  NP -> [branch (S, True) [pauseAt DET, pauseAt N] ]
  VP -> [branch (VP, True) [pauseAt V, branch (NP, True) [pauseAt DET, leaf (N, True) "dog"] ] ]
  N -> [leaf (N, True) "dog", pauseAt N]
  V -> [leaf (V, True) "sees"]
  DET -> [leaf (V, True) "the"]

  where 

  branch a bs = FT.free $ FT.Free $ Branch a bs
  leaf a = FT.free . FT.Free . Leaf a
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
fragmentToBranch (FT.FreeT (Identity (FT.Pure x))) = Branch (S, True) [FT.free $ FT.Pure x]
fragmentToBranch (FT.FreeT (Identity (FT.Free (Branch c brs)))) = Branch c brs
fragmentToBranch (FT.FreeT (Identity (FT.Free (Leaf c x)))) = Leaf c x


loadFragments = FT.Free . fmap (toFree . FT.transFreeT (Compose . return . FT.Free)) where
-- converts between Free from Control.Monad.Trans.Free and Control.Monad.Free
  toFree :: Functor f => FT.Free f a1 -> F.Free f a1
  toFree = Fold.cata $ \case
    Compose (Identity (FT.Free x)) -> F.Free x
    Compose (Identity (FT.Pure x)) -> F.Pure x

freeTreeAlgebra :: Show a => Compose Identity (FT.FreeF (NonRecursiveTree [Char]) a) [Char] -> [Char]
freeTreeAlgebra (Compose (Identity (FT.Free (Branch c brs)))) = join $ intersperse " " brs
freeTreeAlgebra (Compose (Identity (FT.Free (Leaf c a)))) = a 
freeTreeAlgebra (Compose (Identity (FT.Pure a))) = show a


numberLeaves :: Show a => FT.Free (NonRecursiveTree Word) a -> FT.Free (NonRecursiveTree Word) a
--   -> FT.Free (NonRecursiveTree Word) a -> State Int (FT.Free (NonRecursiveTree Word) a)
numberLeaves = fst . flip runState 0 . Fold.transverse go where
  -- go = undefined
  go y@(Compose (Identity (FT.Free (Leaf c x)))) = do
    i <- get
    modify (+1)
    return (Compose $ Identity $ FT.Free (Leaf c (x<>show i)))

  go y@(Compose (Identity (FT.Free (Branch c brs)))) = 
    (Compose <$> Identity <$> FT.Free <$> Branch c <$> sequence brs) 

  go (Compose (Identity (FT.Pure x))) = return (Compose $ Identity $ FT.Pure x)
    -- (Compose $ Identity $ FT.Free (Branch c brs))

-- numberLeaves :: Show a => FT.Free (NonRecursiveTree Word) a -> State Int (FT.Free (NonRecursiveTree Word) a)
-- numberLeaves = fmap fst . Fold.cata alg where 

--   alg :: Show a => Fold.Base (FT.Free (NonRecursiveTree Word) a) (State Int Int) -> State Int Int

--   -- alg (Compose (Identity (FT.Pure x))) = 

--   -- do
--   --   i <- get
--   --   modify (+1)
--   --   return (text (show (x,i)) # fc blue <> rect (maximum [fromIntegral (length (show x)), 3]) 2 # lw 0,
--   --     i)
--   alg = undefined
  -- alg (Compose (Identity (FT.Free x@(Leaf _ _)))) = do 

  --   i <- get
  --   modify (+1)
  --   return  undefined
  --   return (vsep 0.5 [
  --     text (show $ (fst c, i)) # fc (col c) <> rect (maximum [fromIntegral $ length x, 3]) 2 # lw 0,
  --     text x # (if (snd c) then fc red else fc black) <> rect (maximum [fromIntegral $ length x, 3]) 2 # lw 0],
  --     i
  --     )

  -- alg (Compose (Identity (FT.Free (Branch c brs)))) = fmap (,1) $ combineDiagrams (col c) c <$> (fmap fst <$> sequence brs)

toDiagram :: Show a => FT.Free (NonRecursiveTree Word) a -> Diagram B
toDiagram = fst . Fold.cata alg where
  

  alg (Compose (Identity (FT.Pure x))) = 
    (text (show x) # fc blue <> rect (maximum [fromIntegral (length (show x)), 3]) 2 # lw 0,
      show x)
  alg (Compose (Identity (FT.Free (Leaf c x)))) = 
    (vsep 0.5 [
      text (show $ fst c) # fc (col c) <> rect (maximum [fromIntegral $ length x, 3]) 2 # lw 0,
      vrule 0.5,
      text (init x) # (if (snd c) then fc red else fc black) <> rect (maximum [fromIntegral $ length x, 3]) 2 # lw 0],
    show $ last x)
  alg (Compose (Identity (FT.Free (Branch c brs)))) = combineDiagrams (col c) c (brs)


  col c = if snd c then red else black

  combineDiagrams textColor c ds = 
    let newName = join $ intersperse "|" $ fmap snd ds
    in (vsep 0.5 [
      text (show $ fst c) # fc textColor <> rect 2 2 # centerX # lw 0 # named newName,

      -- triangle 2 # scaleY 2,
       -- <> translate (r2 (1, -1)) (arrowV' arrowStyle (r2 (1.5, -2))) <> translate (r2 (-1, -1)) (arrowV' arrowStyle (r2 (-1.5, -2))),
      -- <> (case f of 
      --   Just f' -> translateX 5 ( (scale 0.5 (circle 5 <> toDiagram f')))
      --   Nothing -> mempty),
      hsep 0.5 [d # named name | (d, name) <- ds]
         # centerX
      ]
        # connectOutside' arrowStyle newName (snd $ ds !! 0)
        # if length ds > 1 then (connectOutside' arrowStyle newName (snd $ ds !! 1)) else id
        -- # connectOutside' arrowStyle "3" "2"
      , newName )
    where
      arrowStyle = (with & arrowHead .~ noHead & headLength .~ verySmall & tailLength .~ small)
      colorIdiom f color d = if f then d # lc color else d






----------------------------
-- The full fragment grammar 
----------------------------

fragmentGrammar :: MonadSample m => FragmentDict -> Fragment m Word
fragmentGrammar fragmentDict = Fold.futu go S where
  
  howMuchToReuse = 0.5
  howMuchToSuspend = 0.5
  howMuchToRecurse = 0.1
  
  go cat = Compose $ do

    reuse <- bernoulli howMuchToReuse
    
    if reuse && not (null (fragmentDict cat)) then uniformD (loadFragments . fragmentToBranch <$> (fragmentDict cat))
    else do
      recurse <- bernoulli howMuchToRecurse
      if recurse then makeBranches cat else FT.Free . Leaf (cat, False) <$> uniformD words 

  makeBranchCompositional = do
    suspend <- bernoulli howMuchToSuspend
    cat <- uniformD cats
    return $ if suspend then F.Free $ Compose $ return $ FT.Pure cat else F.Pure cat

  makeBranches cat = do
    bL <- makeBranchCompositional
    bR <- makeBranchCompositional
    return (FT.Free $ Branch (cat, False) [bL, bR] )

runFragmentGrammar :: IO ()
runFragmentGrammar = do 

  (mcmcSamplesOfFragmentTrees, weight) <- sampleIO (runWeighted $ mh 10 $ do 
    frags <- (=<< cats) <$> iterateMInt (step S) (const []) 5
    let sents = Fold.cata freeTreeAlgebra <$> frags
    condition ("the circle" `elem` sents)
    return frags
    )

  let diagram = hsep 0.5 $ intersperse (vrule 10 # centerY) $ (toDiagram . numberLeaves <$> last mcmcSamplesOfFragmentTrees)
  print (Fold.cata freeTreeAlgebra <$> last mcmcSamplesOfFragmentTrees)
  print weight
  saveDiagram "img/fragment.svg" diagram


depth :: Integer
depth = 10

makeTrees = do
  saveDiagram "img/deterministicSimpleTree.svg" $ toDiagram $ FT.cutoff depth $ numberLeaves deterministicSimpleTree
  saveDiagram "img/deterministicSimpleFragment.svg" $ toDiagram $ numberLeaves $ deterministicSimpleFragment
  saveDiagram "img/deterministicComplexTree.svg" $ toDiagram $ numberLeaves $ deterministicComplexTree aPossibleGrammar
  saveDiagram "img/deterministicComplexFragment.svg" $ toDiagram $ numberLeaves $ deterministicComplexFragment aPossibleGrammar
  
  saveDiagram "img/probabilisticSimpleTree.svg" . toDiagram =<< (sampleIO $ FT.joinFreeT probabilisticSimpleTree)
  saveDiagram "img/probabilisticSimpleFragment.svg" . toDiagram =<< (sampleIO $ FT.joinFreeT probabilisticSimpleFragment)
  -- saveDiagram "img/probabilisticComplexTree.svg" . toDiagram =<< (sampleIO $ FT.joinFreeT $ probabilisticComplexTree aPossibleGrammar)
  -- saveDiagram "img/probabilisticComplexFragment.svg" . toDiagram =<< (sampleIO $ FT.joinFreeT $ probabilisticComplexFragment aPossibleGrammar)

  saveDiagram "img/fragmentGrammar.svg" . toDiagram . numberLeaves =<< (sampleIO $ FT.joinFreeT $ fragmentGrammar aPossibleGrammar)
