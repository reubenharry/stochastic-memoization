{-# LANGUAGE DeriveTraversable, LambdaCase, FlexibleContexts, TypeFamilies, GADTs, TupleSections, NoMonomorphismRestriction #-}

module Lib where

import Prelude hiding (words, Word)

import           Data.List (intersperse)
import           Data.Set (Set)
import           Data.Maybe (catMaybes, fromMaybe, isJust)
import qualified Data.Map as M
import           Data.Functor.Compose
import qualified Data.Functor.Foldable as Fold

import qualified Control.Monad.Free as F
import qualified Control.Comonad.Cofree as F
import qualified Control.Monad.Trans.Free as FT
import qualified Control.Comonad.Trans.Cofree as FT

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

import Control.Arrow ((***), (&&&))

type Word = String
data CAT = S | NP | VP | A | N | DET | COP | V | PREP deriving (Show, Eq, Ord)
-- mark whether a node was compositionally generated, or generated via a fragment
data NodeData = C CAT | I String

-- the core tree datatype. Importantly, it's not a recursive type
data NonRecursiveTree leafType branchType =
  Leaf leafType
  | Branch [branchType]
  deriving (Functor, Foldable, Traversable)

-- some simple name synonyms to make types built with these types more self-explanatory to read
type Deterministic = Identity -- a type synonym to indicate that the monad is just the identity
type NoPausing = Void
type PauseWithCat = CAT
type AnnotateWith a f = FT.CofreeF f a
type MakeRecursive m pauseType = FT.FreeT (AnnotateWith NodeData (NonRecursiveTree Word)) m pauseType

type Fragment m = MakeRecursive m PauseWithCat
type Tree m = MakeRecursive m NoPausing

type Idiom = [Fragment Deterministic]
type FragmentDict = CAT -> [Idiom]



type Grammar m pauseType = CAT -> Fold.Base (MakeRecursive m pauseType) CAT
type FragmentGrammar m pauseType = 
  CAT -> 
    Fold.Base (MakeRecursive m pauseType) 
    (F.Free (
      Fold.Base (MakeRecursive m pauseType)) 
      CAT)

type Interpreter m resultType = Fold.Base (MakeRecursive m NoPausing) resultType -> resultType
type FragmentInterpreter m pauseType = 
    Fold.Base (MakeRecursive m pauseType) 
    (F.Cofree (
      Fold.Base (MakeRecursive m pauseType)) 
      CAT) -> CAT
                            
-------
-- TODO: trying stuff out
-------

-- monadicFold :: SamplerIO (SamplerIO Int)
-- monadicFold = Fold.histo semantics probabilisticSimpleTree where
  

-- semantics (Compose (x)) = foo =<< x where -- (foo 
--     -- :: Monad m => FT.FreeF (NonRecursiveTree Word) Void (m (Bool, String)) -> (m (Bool, String))) =<< x where 
--   -- foo = undefined 

--   -- foo :: 

--   -- bar
--   -- foo = undefined :: MonadSample m => FT.FreeF (NonRecursiveTree Word) Void a -> m b
--   -- x = c foo1 foo2
--   -- -- foo1 = undefined
--   -- foo1 (FT.Free (Leaf _ lf)) = return $ ((>2) . length) lf
--   -- foo2 (FT.Free (Leaf _ lf)) = return lf
--   -- foo2 = undefined
--   foo (FT.Free (Branch _ ((_ F.:< _):_))) = undefined
--   -- foo (FT.Free (Branch _ brs)) = fmap (foldr1 (\(x,y) (x',y') -> (x && x', y <> " " <> y'  ))) $ sequence brs
--   -- foo (FT.Free (Leaf _ lf)) = return $ ((>2) . length &&& id) lf -- fmap sum $ sequence brs


-- -- x :: MonadSample m => m (Bool, String)
-- -- x = Fold.hylo semantics pcfg S

-- -- s1 = do
-- --   (rec, str) <- x
-- --   condition (rec == True)
-- --   return str

-- -- runS1 = print =<< (sampleIO $ runWeighted s1)

-- experimentalTree :: FT.CofreeT (NonRecursiveTree Word) Deterministic NodeData
-- experimentalTree = Fold.futu (Compose . Identity . \case

--   x -> (x, False) FT.:< case x of 
--     S -> (Branch undefined [F.Free (Compose $ Identity ((NP, False) FT.:< (Branch undefined [F.Pure NP]))), F.Pure VP]))
--   -- S  -> branch (S, False) [NP, VP]
--   -- NP ->  branch (NP, False) [DET, N]
--   -- DET ->  leaf (N, False) "the"
--   -- N  -> leaf (N, False) "cat"
--   -- VP ->  branch (VP, False) [V, NP]
--   -- V  -> leaf (V, False) "sees") 

--   S -- starting category

--------------------------------------
-- progressively more complex examples
--------------------------------------

example1 :: Grammar Deterministic NoPausing
example2 :: Grammar Deterministic PauseWithCat
example3 :: FragmentDict -> FragmentGrammar Deterministic NoPausing
example4 :: FragmentDict -> FragmentGrammar Deterministic PauseWithCat
example5 :: MonadSample m => Grammar m NoPausing
example6 :: MonadSample m => Grammar m PauseWithCat
example7 :: MonadSample m => FragmentDict -> FragmentGrammar m NoPausing
example8 :: MonadSample m => FragmentDict -> FragmentGrammar m PauseWithCat

branch x t = FT.Free (C x FT.:< Branch t)
leaf x t = FT.Free (C x FT.:< Leaf t)
pauseAt = FT.Pure

loadFragments cat brs = FT.Free (C cat FT.:< 
    Branch (F.hoistFree (Compose . Identity . FT.Free) . toFree <$> brs))

example1 = Compose . Identity . \case

  S  -> branch S [NP, VP]
  NP -> branch NP [DET, N]
  DET -> leaf N "the"
  N  -> leaf N "cat"
  VP ->  branch VP [V, NP]
  V  -> leaf V "sees"

example2 = Compose . Identity . \case
  
  S  -> branch S [NP, VP]
  NP ->  branch NP [DET, N]
  DET ->  leaf DET "the"
  N  -> leaf N "cat"
  VP -> pauseAt VP
  V  -> leaf V "sees" 
  
example3 fragmentDict = Compose . Identity . \case
  
  S  -> branch S $ F.Pure <$> [NP, VP]
  NP ->  branch NP $ F.Pure <$> [DET, N]
  DET -> leaf DET "the"
  N  -> leaf N "cat"
  VP -> loadFragments VP $ head $ fragmentDict VP
  V  -> leaf V "sees"

example4 fragmentDict = Compose . Identity . \case
  
  S  -> branch S (F.Pure <$> [NP, VP])
  DET -> leaf DET "the"
  N  -> leaf N  "cat"
  NP ->  pauseAt NP
  VP -> loadFragments VP $ head $ fragmentDict VP
  V  -> leaf V "sees"

example5 = Compose . \case

  S  -> return $ branch S [NP, VP]
  NP ->  return $ branch NP [DET, N]
  DET -> return $ leaf DET "the"
  N  -> uniformD [branch N [A, N], leaf N "idea"]
  A  -> uniformD [leaf A "green", leaf A "furious"]
  VP ->  return $ branch NP [V, NP]
  V  -> return $ leaf V "sees"

example6 = Compose . \case

  S  -> return $ branch S [NP, VP]
  NP ->  return $ branch NP [DET, N]
  DET -> return $ leaf DET "the"
  N  -> uniformD [branch N [A, N], leaf N "idea"]
  A  -> uniformD [leaf A "green", leaf A "furious"]
  VP ->  uniformD [FT.Pure VP, branch NP [V, NP]]
  V  -> return $ leaf V "sees"

example7 fragmentDict = Compose . \case

  S  -> return $ branch S (F.Pure <$> [NP, VP])
--   NP ->  return $ branch (NP, False) [DET, N]
--   DET -> return $ leaf (DET, False) "the"
--   N  -> uniformD [branch (N, False) [A, N], leaf (N, False) "idea"]
--   A  -> uniformD [leaf (A, False) "green", leaf (A, False) "furious"]
--   VP ->  uniformD (loadFragments . fragmentToBranch <$> (fragmentDict VP)) 
--   V  -> return $ leaf (V, False) "sees"

example8 fragmentDict = Compose . \case

  S -> return $ branch S (F.Pure <$> [NP, VP])
  -- NP = return $ FT.Pure NP
  -- DET = return $ leaf (DET, False) "the"
  -- N = uniformD [branch (N, False) [A, N], leaf (N, False) "idea"]
  -- A = uniformD [leaf (A, False) "green", leaf (A, False) "furious"]
  -- V = return $ leaf (V, False) "sees"
  -- VP = uniformD (loadFragments . fragmentToBranch <$> (fragmentDict VP)) 


-- fragmentCFG :: FragmentDict -> Tree [] Word
-- fragmentCFG fragmentDict = Fold.futu (

cfg :: FragmentDict -> FragmentGrammar [] NoPausing
cfg fragmentDict = Compose . \case

  S  -> return $ branch S $ F.Pure <$> [NP, VP]
--   NP ->  return $ branch (NP, False) [DET, N]
--   DET -> return $ leaf (DET, False) "the"
--   N  ->  [branch (N, False) [A, N], leaf (N, False) "idea"]
--   A  ->  [leaf (A, False) "green", leaf (A, False) "furious"]
--   VP ->  (loadFragments . fragmentToBranch <$> (fragmentDict VP)) 
--   V  -> return $ leaf (V, False) "sees")
  
--   S

--   where 

--   branch a bs = FT.Free $ Branch a (F.Pure <$> bs)



grammar :: FragmentDict
grammar = \case
  
  S -> [[branch "red" [pauseAt NP, pauseAt VP] ]]
--   NP -> [[branch [pauseAt DET, pauseAt N] ]]
--   VP -> [[branch [leaf "gives", pauseAt NP], branch [leaf "a", leaf "break" ]]]
--   N -> [[leaf "dog", branch  [pauseAt A, pauseAt N]]]
  V -> [[leaf "blue" "sees"]]
--   DET -> [[leaf "the"]]

--   _ -> [[leaf "no entry: error (grammar)"]]

  where 

  branch c bs = FT.free $ FT.Free $ I c FT.:< Branch bs
  leaf c bs = FT.free $ FT.Free $ I c FT.:< Leaf bs
  pauseAt = FT.free . FT.Pure



-- step :: MonadSample m => CAT -> FragmentDict -> m FragmentDict
-- step cat fragDict = do 
--  frag <- FT.joinFreeT $ fragmentGrammar fragDict
--  addNew <- bernoulli 0.5
--  let newFragDict y = if y == cat then fragDict y <> [frag] else fragDict y
--  return (if addNew then newFragDict else fragDict)

-- iterateMInt :: Monad m => (a -> m a) -> a -> Int -> m a
-- iterateMInt step init int = if int == 0 then step init else do
--   result <- step init
--   iterateMInt step result (int -1)



saveDiagram :: String -> Diagram B -> IO ()
saveDiagram path diagram = let size = mkSizeSpec $ r2 (Just 1000, Just 1000) in renderSVG path size (diagram # bg white)

toFree :: Functor f => FT.Free f a1 -> F.Free f a1
toFree = Fold.cata $ \case
  Compose (Identity (FT.Free x)) -> F.Free x
  Compose (Identity (FT.Pure x)) -> F.Pure x

-- freeTreeAlgebra :: Show a => Compose Identity (FT.FreeF (NonRecursiveTree [Char]) a) [Char] -> [Char]
linearize :: Interpreter Deterministic String
linearize (Compose (Identity (FT.Free (_ FT.:< Branch brs)))) = join $ intersperse " " brs
-- freeTreeAlgebra (Compose (Identity (FT.Free (Leaf c a)))) = a 
-- freeTreeAlgebra (Compose (Identity (FT.Pure a))) = show a


connection :: Monad m => Grammar m NoPausing -> Interpreter m a -> CAT -> a
-- Grammar m a -> Interpreter m String -> m String
connection = flip Fold.hylo

-- -- Surely a one-liner that I'm missing
-- numberLeaves :: Show a => FT.Free (NonRecursiveTree Word) a -> FT.Free (NonRecursiveTree Word) a
-- numberLeaves = undefined
  -- fst . flip runState 0 . Fold.transverse go where

--   go y@(Compose (Identity (FT.Free (Leaf c x)))) = do
--     i <- get
--     modify (+1)
--     return (Compose $ Identity $ FT.Free (Leaf c (x<>show i)))

--   go y@(Compose (Identity (FT.Free (Branch c brs)))) = 
--     (Compose <$> Identity <$> FT.Free <$> Branch c <$> sequence brs) 

--   go (Compose (Identity (FT.Pure x))) = return (Compose $ Identity $ FT.Pure x)

showCat (C x) = show x
showCat (I x) = "Idiom"

toDiagram :: Monad m => Tree m -> m (Diagram B)
toDiagram = fmap fst . Fold.cata alg where


  alg (Compose y) = do
    y' <- y
    case y' of 
      FT.Free (c FT.:< (Leaf x))
        -> return (vsep 0.5 [
          text (showCat c) # fc (col id c) <> rect (maximum [fromIntegral $ length x, 3]) 2 # lw 0,
          vrule 0.5,
          text (init x) # col fc c <> rect (maximum [fromIntegral $ length x, 3]) 2 # lw 0],
          show $ last x)

      FT.Free (c FT.:< Branch brs) -> combineDiagrams (col id c) c <$> sequence brs

  col f c = case c of
   (I _) -> f red
   (C _) -> f black

  combineDiagrams textColor c ds = 
    let newName = join $ intersperse "|" $ fmap snd ds
    in (vsep 0.5 [
      text (showCat c) # fc textColor <> rect 2 2 # centerX # lw 0 # named newName,

      hsep 0.5 [d # named name | (d, name) <- ds]
         # centerX
      ]
        -- # connectOutside' arrowStyle newName (snd $ ds !! 0) 
        -- # if length ds > 1 then (connectOutside' arrowStyle newName (snd $ ds !! 1)) else id
      , newName )
    where
      arrowStyle = with & arrowHead .~ dart & headLength .~ 3 
        & tailLength .~ verySmall
      colorIdiom f color d = if f then d # lc color else d






-- ----------------------------
-- -- The full fragment grammar 
-- ----------------------------

-- fragmentGrammar :: MonadSample m => FragmentDict -> Fragment m Word
-- fragmentGrammar fragmentDict = Fold.futu go S where
  
--   howMuchToReuse = 0.5
--   howMuchToSuspend = 0.5
--   howMuchToRecurse = 0.1
  
--   go cat = Compose $ do

--     reuse <- bernoulli howMuchToReuse
    
--     if reuse && not (null (fragmentDict cat)) then uniformD (loadFragments . fragmentToBranch <$> (fragmentDict cat))
--     else do
--       recurse <- bernoulli howMuchToRecurse
--       if recurse then makeBranches cat else FT.Free . Leaf (cat, False) <$> uniformD words 

--   makeBranchCompositional = do
--     suspend <- bernoulli howMuchToSuspend
--     cat <- uniformD cats
--     return $ if suspend then F.Free $ Compose $ return $ FT.Pure cat else F.Pure cat

--   makeBranches cat = do
--     bL <- makeBranchCompositional
--     bR <- makeBranchCompositional
--     return (FT.Free $ Branch (cat, False) [bL, bR] )

-- runFragmentGrammar :: IO ()
-- runFragmentGrammar = do 

--   (mcmcSamplesOfFragmentTrees, weight) <- sampleIO (runWeighted $ mh 10 $ do 
--     frags <- (=<< cats) <$> iterateMInt (step S) (const []) 5
--     let sents = Fold.cata freeTreeAlgebra <$> frags
--     condition ("the circle" `elem` sents)
--     return frags
--     )

--   let diagram = hsep 0.5 $ intersperse (vrule 10 # centerY) $ (toDiagram . numberLeaves <$> last mcmcSamplesOfFragmentTrees)
--   print (Fold.cata freeTreeAlgebra <$> last mcmcSamplesOfFragmentTrees)
--   print weight
--   saveDiagram "img/fragment.svg" diagram


depth :: Integer
depth = 10

makeTrees = do

  saveDiagram "img/deterministicSimpleTree.svg" $ runIdentity (toDiagram $ Fold.ana example1 S)
  -- saveDiagram "img/probabilisticSimpleTree.svg" =<< 
  saveDiagram "img/probabilisticSimpleTree.svg" =<< sampleIO (toDiagram $ Fold.ana example5 S)

  -- saveDiagram "img/deterministicSimpleFragment.svg" $ toDiagram $ deterministicSimpleFragment
  -- saveDiagram "img/deterministicSimpleTree.svg" $ toDiagram $ deterministicSimpleTree
  -- saveDiagram "img/deterministicSimpleTree.svg" $ toDiagram $ deterministicSimpleTree

  -- saveDiagram "img/deterministicSimpleTree.svg" $ toDiagram $ FT.cutoff depth $ numberLeaves deterministicSimpleTree
--   saveDiagram "img/deterministicSimpleFragment.svg" $ toDiagram $ numberLeaves $ deterministicSimpleFragment
--   saveDiagram "img/deterministicComplexTree.svg" $ toDiagram $ numberLeaves $ deterministicComplexTree grammar
--   saveDiagram "img/deterministicComplexFragment.svg" $ toDiagram $ numberLeaves $ deterministicComplexFragment grammar
  

--   -- saveDiagram "img/probabilisticSimpleTree.svg" . toDiagram =<< (sampleIO $ FT.joinFreeT probabilisticSimpleTree)
--   -- saveDiagram "img/probabilisticSimpleFragment.svg" . toDiagram =<< (sampleIO $ FT.joinFreeT probabilisticSimpleFragment)
--   -- saveDiagram "img/probabilisticComplexTree.svg" . toDiagram =<< (sampleIO $ FT.joinFreeT $ probabilisticComplexTree grammar)
--   -- saveDiagram "img/probabilisticComplexFragment.svg" . toDiagram =<< (sampleIO $ FT.joinFreeT $ probabilisticComplexFragment grammar)

--   saveDiagram "img/fragmentGrammar.svg" . toDiagram . numberLeaves =<< (sampleIO $ FT.joinFreeT $ fragmentGrammar grammar)
  
--   let a = FT.joinFreeT $ FT.cutoff 5 $ fragmentCFG grammar :: [FT.Free (NonRecursiveTree Word) (Maybe Void)]
--   let b = catMaybes $ fmap (Fold.transverse may) a
--   saveDiagram "img/fragmentCFG.svg" $ hsep 2 $ take 2 $ fmap (toDiagram . numberLeaves) $ b

--   let ds x = (circle 9 # translateY (-5) <>) . toDiagram . numberLeaves <$> grammar x
--   saveDiagram "img/grammarFragments.svg" $ vsep 3 [if not (null (grammar cat)) then hsep 0.5 (text (show cat) # scale 5 <> strut 6 : ds cat) else mempty | cat <- cats]

-- -- This is surely a one-liner that I'm not seeing
-- may :: Fold.Base (FT.Free (NonRecursiveTree Word) (Maybe Void)) (Maybe a)
--   -> Maybe (Fold.Base (FT.Free (NonRecursiveTree Word) Void) a) 
-- may (Compose (Identity (FT.Pure x))) = Compose . Identity . FT.Pure <$> x
-- may y@(Compose (Identity (FT.Free (Leaf c x)))) = do
--     return (Compose $ Identity $ FT.Free (Leaf c x))
-- may y@(Compose (Identity (FT.Free (Branch c brs)))) = 
--     (Compose <$> Identity <$> FT.Free <$> Branch c <$> sequence brs)


cats :: [CAT]
cats = [S, NP, VP, DET, A, N, COP, V]
words :: [Word]
words = ["the", "a", "turn", "blue", "circle", "square", "is"]

