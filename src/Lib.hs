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

import           Diagrams.Prelude               hiding (Cat, E, (:<), (^.), normalize, set) 


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

import Numeric.Log

import Control.Comonad



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
type RecursiveTree m pauseType = FT.FreeT (AnnotateWith NodeData (NonRecursiveTree Word)) m pauseType

type Fragment m = RecursiveTree m PauseWithCat
type Tree m = RecursiveTree m NoPausing

type Idiom = [Fragment Deterministic]
type FragmentDict = CAT -> [Idiom]



type Grammar m pauseType startType = startType -> Fold.Base (RecursiveTree m pauseType) startType
type FragmentGrammar m pauseType startType = 
  startType -> 
    Fold.Base (RecursiveTree m pauseType) 
    (F.Free (
      Fold.Base (RecursiveTree m pauseType)) 
      startType)

type Interpreter m pauseType resultType = Fold.Base (RecursiveTree m pauseType) (m resultType) -> m resultType
type FragmentInterpreter m pauseType resultType = 
    Fold.Base (RecursiveTree m pauseType) 
    (F.Cofree (
      Fold.Base (RecursiveTree m pauseType)) 
      (m resultType)) -> m resultType
                            
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




----------
-- helper functions
----------

branch :: CAT -> [b0] -> FT.FreeF (FT.CofreeF (NonRecursiveTree leafType0) NodeData) a0 b0
branch x t = FT.Free (C x FT.:< Branch t)
leaf x t = FT.Free (C x FT.:< Leaf t)
pauseAt = FT.Pure

loadFragments cat brs = FT.Free (C cat FT.:< 
    Branch (F.hoistFree (Compose . return . FT.Free) . toFree <$> brs))


--------------------------------------
-- progressively more complex syntaxs
--------------------------------------

syntax1 :: Grammar Deterministic NoPausing CAT
syntax2 :: Grammar Deterministic PauseWithCat CAT
syntax3 :: FragmentDict -> FragmentGrammar Deterministic NoPausing CAT
syntax4 :: FragmentDict -> FragmentGrammar Deterministic PauseWithCat CAT
syntax5 :: MonadSample m => Grammar m NoPausing CAT
syntax6 :: MonadSample m => Grammar m PauseWithCat CAT
syntax7 :: MonadSample m => FragmentDict -> FragmentGrammar m NoPausing CAT
syntax8 :: MonadSample m => FragmentDict -> FragmentGrammar m PauseWithCat CAT
cfg :: FragmentDict -> FragmentGrammar [] NoPausing CAT

syntax1 = Compose . Identity . \case

  S  -> branch S [NP, VP]
  NP -> branch NP [DET, N]
  DET -> leaf N "the"
  N  -> leaf N "cat"
  VP ->  branch VP [V, NP]
  V  -> leaf V "sees"

syntax2 = Compose . Identity . \case
  
  S  -> branch S [NP, VP]
  NP ->  branch NP [DET, N]
  DET ->  leaf DET "the"
  N  -> leaf N "cat"
  VP -> pauseAt VP
  V  -> leaf V "sees" 
  
syntax3 fragmentDict = Compose . Identity . \case
  
  S  -> branch S $ F.Pure <$> [NP, VP]
  NP ->  branch NP $ F.Pure <$> [DET, N]
  DET -> leaf DET "the"
  N  -> leaf N "cat"
  VP -> loadFragments VP $ head $ fragmentDict VP
  V  -> leaf V "sees"

syntax4 fragmentDict = Compose . Identity . \case
  
  S  -> branch S (F.Pure <$> [NP, VP])
  DET -> leaf DET "the"
  N  -> leaf N  "cat"
  NP ->  pauseAt NP
  VP -> loadFragments VP $ head $ fragmentDict VP
  V  -> leaf V "sees"

syntax5 = Compose . \case

  S  -> return $ branch S [NP, VP]
  NP ->  return $ branch NP [DET, N]
  DET -> return $ leaf DET "the"
  N  -> uniformD [leaf N "idea", leaf N "cat"] -- [branch N [A, N], leaf N "idea"]
  A  -> uniformD [leaf A "green", leaf A "furious"]
  VP ->  return $ branch NP [V, NP]
  V  -> uniformD [leaf V "sees", leaf V "knows"]

syntax6 = Compose . \case

  S  -> return $ branch S [NP, VP]
  NP ->  return $ branch NP [DET, N]
  DET -> return $ leaf DET "the"
  N  -> uniformD [branch N [A, N], leaf N "idea"]
  A  -> uniformD [leaf A "green", leaf A "furious"]
  VP ->  uniformD [FT.Pure VP, branch NP [V, NP]]
  V  -> return $ leaf V "sees"

-- syntax7 fragmentDict = Compose . \case

--   S  -> return $ branch S (F.Pure <$> [NP, VP])
--   NP ->  return $ branch NP $ F.Pure <$> [DET, N]
--   DET -> return $ leaf DET "the"
--   N  -> uniformD [branch N $ F.Pure <$> [A, N], leaf N "idea"]
--   A  -> uniformD [leaf A "green", leaf A "furious"]
--   VP ->  uniformD (loadFragments VP <$> fragmentDict VP) 
--   V  -> return $ leaf V "sees"

syntax7 fragmentDict = Compose . \x

  ->  uniformD (loadFragments x <$> fragmentDict x) 


syntax8 fragmentDict = Compose . \x

  ->  uniformD (loadFragments x <$> fragmentDict x)

  -- Compose . \case

  -- S -> return $ branch S (F.Pure <$> [NP, VP])
  -- NP -> return $ FT.Pure NP
  -- DET -> return $ leaf DET "the"
  -- N -> uniformD [branch N $ F.Pure <$> [A, N], leaf N "idea"]
  -- A -> uniformD [leaf A "green", leaf A "furious"]
  -- V -> return $ leaf V "sees"
  -- VP -> uniformD (loadFragments VP <$> fragmentDict VP) 


cfg fragmentDict = Compose . \case

  S  ->  return $ branch S $ F.Pure <$> [NP, VP]
  NP ->  return $ branch NP $ F.Pure <$> [DET, N]
  DET -> return $ leaf DET "the"
  N  ->  [branch N $ F.Pure <$> [A, N], leaf N "idea"]
  A  ->  [leaf A "green", leaf A "furious"]
  VP ->  loadFragments VP <$> fragmentDict VP
  V  ->  return $ leaf V "sees"


fragmentDict :: FragmentDict
fragmentDict = \case
  
  S -> [[branch "red" [pauseAt NP, pauseAt VP]], [branch "red" [pauseAt S, branch "red" [leaf "purple" "and", pauseAt S]] ]]
  NP -> [[branch "green" [pauseAt DET, pauseAt N] ]]
  VP -> [[branch "purple" [leaf "purple" "gives", pauseAt NP], branch "purple" [leaf "purple" "a", leaf "purple" "break" ]]]
  N -> [[leaf "orange" "dog"], [branch "orange" [pauseAt A, pauseAt N]]]
  V -> [[leaf "cyan" "sees"]]
  DET -> [[leaf "grey" "the"]]
  A -> [[leaf "yellow" "small"]]

  _ -> [[leaf "black" "no entry: error (fragmentDict)"]]

  where 

  branch c bs = FT.free $ FT.Free $ I c FT.:< Branch bs
  leaf c bs = FT.free $ FT.Free $ I c FT.:< Leaf bs
  pauseAt = FT.free . FT.Pure



step :: MonadSample m => CAT -> FragmentDict -> m FragmentDict
step cat fragDict = do 
 frag <- FT.joinFreeT $ Fold.futu (syntax8 fragDict) S
 addNew <- bernoulli 0.5
 let newFragDict y = if y == cat then fragDict y <> [[frag]] else fragDict y
 return (if addNew then newFragDict else fragDict)

iterateMInt :: Monad m => (a -> m a) -> a -> Int -> m a
iterateMInt step init int = if int == 0 then step init else do
  result <- step init
  iterateMInt step result (int -1)



saveDiagram :: String -> Diagram B -> IO ()
saveDiagram path diagram = let size = mkSizeSpec $ r2 (Just 1000, Just 1000) in renderSVG path size (diagram # bg white)

toFree :: Functor f => FT.Free f a1 -> F.Free f a1
toFree = Fold.cata $ \case
  Compose (Identity (FT.Free x)) -> F.Free x
  Compose (Identity (FT.Pure x)) -> F.Pure x

phonology2 :: (Monad m, Show pauseType) => Interpreter m pauseType String
phonology2 (Compose x) = do 
  x' <- x 
  case x' of 
    (FT.Free (_ FT.:< Branch brs)) -> join . intersperse " " <$> sequence brs
    (FT.Free (_ FT.:< Leaf a)) -> return a
    (FT.Pure a) -> return $ show a

semantics1 :: (Monad m, Show pauseType) => Interpreter m pauseType Bool
semantics1 (Compose x) = do 
  x' <- x 
  case x' of 
    (FT.Free (_ FT.:< Branch brs)) -> all (==True) <$> sequence brs
    -- error . show <$> sequence brs -- 
    (FT.Free (_ FT.:< Leaf a)) -> return True
    (FT.Pure a) -> return True


semanticsAndPhonology1 :: (MonadSample m, Show pauseType) => FragmentInterpreter m pauseType (String, World -> Bool)
-- semanticsAndPhonology1 :: (Monad m, Show pauseType) => Interpreter m pauseType (String, World -> Bool)
semanticsAndPhonology1 (Compose x) =  do 
  x' <- x 
  case x' of 
    (FT.Free (_ FT.:< Branch brs)) -> (foldr1 (\(str1, bool1) (str2, bool2) -> (str1<>" "<>str2, liftA2 (&&) bool1 bool2) )) <$> sequence (extract <$> brs)
    -- error . show <$> sequence brs -- 
    (FT.Free (_ FT.:< Leaf "cat")) -> return ("cat", (==Cat))
    -- (FT.Free (_ FT.:< Leaf "idea")) -> return ("idea", (==Idea))
    (FT.Free (_ FT.:< Leaf a)) -> return (a, const True)
    (FT.Pure a) -> return (show a, const True)


type Convention m pauseType resultType startType = (Interpreter m pauseType resultType, Grammar m pauseType startType)

speaker :: Monad m => (Interpreter m pauseType a, Grammar m pauseType b) -> b -> m a
speaker = uncurry Fold.hylo

s w = do
  (phonology, denotation) <- Fold.chrono semanticsAndPhonology1 (syntax8 fragmentDict) S
  condition (denotation w)
  return phonology

data World = Cat | Idea deriving (Eq, Ord, Show)

l u = do
  w <- uniformD [Cat, Idea]
  factor (Exp $ log $ mass (s w) u)
  return w

s1 w = do
  (phonology, denotation) <- Fold.chrono semanticsAndPhonology1 (syntax8 fragmentDict) S
  factor (Exp $ log $ mass (l phonology) w)
  return phonology
  

-- convention = (semanticsAndPhonology1, syntax5)

-- foo :: MonadSample m => Speaker m
-- foo = speaker (semanticsAndPhonology1, syntax5)

runProb = enumerate $ s1 Idea -- l "the idea knows the idea"

-- bar :: Monad m => Interpreter m () (String, String)
-- bar = foo `algebraProduct` foo
-- foo = speaker (phonology1 `algebraProduct` phonology1, undefined)

algebraProduct :: Applicative m => Interpreter m pauseType a -> Interpreter m pauseType b -> Interpreter m pauseType (a, b)
algebraProduct f1 f2 fab = liftA2 (,) (f1 $ fmap fst <$> fab) (f2 $ fmap snd <$> fab) --  (f1 $ fst <$> fab) (f2 $ snd <$> fab)

showCat :: NodeData -> String
showCat (C x) = show x
showCat (I x) = "Idiom"

-- phonology1 :: (Monad m, Show pauseType) => Interpreter m pauseType (Diagram B, String)
phonology1 :: (MonadSample m, Show pauseType) => FragmentInterpreter m pauseType (Diagram B, String)
phonology1 (Compose y) = do
  y' <- y
  case y' of 
    FT.Free (c FT.:< (Leaf x))
      -> do 
        n <- random
        return (vsep 0.5 [
          text (showCat c) # fc (col id c) <> rect (maximum [fromIntegral $ length x, 3]) 2 # lw 0,
          vrule 0.5,
          text x # col fc c <> rect (maximum [fromIntegral $ length x, 3]) 2 # lw 0],
          show ( x) <> show n  )

    FT.Free (c FT.:< Branch brs) -> combineDiagrams (col id c) c =<< sequence (fmap extract brs)

    FT.Pure x -> return (text (show x) # fc blue
      <> rect (maximum [fromIntegral (length (show x)), 3]) 2 # lw 0,
      show x)

  where

  col f c = case c of
   (I "red") -> f red
   (I "blue") -> f blue
   (I "grey") -> f grey
   (I "cyan") -> f cyan
   (I "orange") -> f orange
   (I "green") -> f green
   (I "purple") -> f purple
   (I "black") -> f black
   I "yellow" -> f yellow

   (C _) -> f black

  combineDiagrams textColor c ds = do
    newName <- show <$> random   -- = join $ intersperse "|" $ fmap snd ds
    return (vsep 0.5 [
      text (showCat c) # fc textColor <> rect 2 2 # centerX # lw 0 # named newName,

      hsep 0.5 [d # named name | (d, name) <- ds]
         # centerX
      ]
        -- # error (show ((snd $ ds !! 0)==newName)) -- 
        # connectOutside' arrowStyle newName (snd $ ds !! 0) 
        # if length ds > 1 then (connectOutside' arrowStyle newName (snd $ ds !! 1)) else id
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

runFragmentGrammar :: IO ()
runFragmentGrammar = do 

  (mcmcSamplesOfFragmentTrees, weight) <- sampleIO (runWeighted $ mh 10 $ do 
    frags <- iterateMInt (step S) (fragmentDict) 10
    Fold.chrono phonology1 (syntax8 frags) S
    -- let sents = Fold.cata phonology2 <$> frags
    -- condition ("the circle" `elem` sents)
    -- return frags
    )
  -- let a = (last $ last mcmcSamplesOfFragmentTrees)
  -- let diagram = hsep 0.5 $ intersperse (vrule 10 # centerY) $ (Fold.histo phonology1 <$> last mcmcSamplesOfFragmentTrees)
  let d = fst $ last $ mcmcSamplesOfFragmentTrees
  -- print (Fold.cata phonology2 <$> last mcmcSamplesOfFragmentTrees)
  -- print weight
  saveDiagram "img/fragment4.svg" d


-- f (m a) -> m a
-- f (m b) -> m b



depth :: Integer
depth = 10

makeTrees = do

  -- saveDiagram "img/deterministicSimpleTree.svg" $ runIdentity $ fmap fst 
  --   (speaker (phonology1, syntax1) S)
  -- saveDiagram "img/deterministicSimpleFragment.svg" $ runIdentity (toDiagram $ Fold.ana syntax2 S)
  -- saveDiagram "img/probabilisticSimpleTree.svg" =<< 
  -- saveDiagram "img/probabilisticSimpleTree.svg" =<< sampleIO (toDiagram $ Fold.ana syntax5 S)

  saveDiagram "img/probabilisticComplexFragment.svg" =<< (sampleIO . fmap fst)
    (Fold.chrono phonology1 (syntax7 fragmentDict) S)
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

