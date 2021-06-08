{-# LANGUAGE DeriveTraversable, LambdaCase, FlexibleContexts, TypeFamilies, GADTs, TupleSections, NoMonomorphismRestriction #-}

module Lib where

import Prelude hiding (words, Word)

import           Data.List (intersperse)
import           Data.Set (Set)
import           Data.Maybe (catMaybes, fromMaybe, isJust)
import qualified Data.Map as M
import           Data.Functor.Compose
import qualified Data.Functor.Foldable as Fold

-- import           Control.Comonad.Cofree (Cofree())
import qualified Control.Comonad.Trans.Cofree as FT


import qualified Control.Monad.Free as F
import qualified Control.Comonad.Cofree as F
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

import Control.Arrow ((***), (&&&))

type Word = String
data CAT = S | NP | VP | A | N | DET | COP | V | PREP deriving (Show, Eq, Ord)

type IsIdiom = String
data NodeData = C CAT | I String

data NonRecursiveTree leafType branchType =
  Leaf leafType
  | Branch [branchType]
  deriving (Functor, Foldable, Traversable)

type Deterministic = Identity -- a type synonym to indicate that the monad is just the identity

-- type Tree m leafType = FT.CofreeT (NonRecursiveTree leafType) m NodeData
-- type Fragment m leafType = FT.FreeT (NonRecursiveTree leafType) m CAT

type FragmentDict = CAT -> [[Fragment Deterministic Word]]


type Tree m leafType = FT.FreeT (FT.CofreeF (NonRecursiveTree Word) NodeData) m Void
type Fragment m leafType = FT.FreeT (FT.CofreeF (NonRecursiveTree Word) NodeData) m CAT

cats :: [CAT]
cats = [S, NP, VP, DET, A, N, COP, V]
words :: [Word]
words = ["the", "a", "turn", "blue", "circle", "square", "is"]



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

deterministicSimpleTree :: Tree Deterministic Word
deterministicSimpleTree = Fold.unfold (Compose . Identity . \case

  -- _ -> undefined
  S  -> branch S [NP, VP]
  NP -> branch NP [DET, N]
  -- DET ->  leaf (N, "") "the"
  -- N  -> leaf (N, "") "cat"
  -- VP ->  branch (VP, "") [V, NP]
  -- V  -> leaf (V, "") "sees"
  )

  S -- starting category

  where

  branch x t = FT.Free ((C x) FT.:< Branch t)
  -- leaf tup t = tup FT.:< Leaf t

-- deterministicSimpleFragment :: Fragment Deterministic Word
-- deterministicSimpleFragment = Fold.unfold (Compose . Identity . \case
  
--   S  -> branch [NP, VP]
-- --   NP ->  branch [DET, N]
-- --   DET ->  leaf "the"
-- --   N  -> leaf "cat"
-- --   VP -> pauseAt VP
-- --   V  -> leaf "sees" 
--   )

--   S

--   where 

--   branch = FT.Free . Branch
-- --   leaf = FT.Free . Leaf
-- --   pauseAt = FT.Pure

-- deterministicComplexTree :: FragmentDict -> Tree Deterministic Word
-- deterministicComplexTree fragmentDict = Fold.futu (Compose . Identity . \case
  
--   S  -> branch S [NP, VP]
-- --   NP ->  branch (NP, "False") [DET, N]
-- --   DET -> leaf (DET, "False") "the"
-- --   N  -> leaf (N, "False") "cat"
-- --   VP -> (loadFragments VP $ head $ fragmentDict VP)
-- --   V  -> leaf (V, "False") "sees"
--   ) 

--   S

--   where 

--   branch x bs = FT.Free ((C x) FT.:< Branch (F.Pure <$> bs))
-- --   leaf tup t = tup FT.:< Leaf t

-- -- -- loadFragments :: [Fragment Deterministic Word] -> FT.CofreeF (NonRecursiveTree Word) NodeData
-- -- --   (F.Free
-- -- --   (Compose Identity (FT.CofreeF (NonRecursiveTree Word) NodeData))
-- -- --                                          CAT)
-- --   loadFragments cat brs = (cat, "idiom") FT.:< Branch (F.hoistFree t . toFree <$> brs) where
-- --     t x = Compose $ Identity $ (S,"idiom") FT.:< x
-- --     -- t (Branch [x]) = undefined
-- --     -- t (Branch []) = undefined


-- deterministicComplexFragment :: FragmentDict -> Fragment Deterministic Word
-- deterministicComplexFragment fragmentDict = Fold.futu (Compose . Identity . \case
  
--   S  -> branch [NP, VP]
-- --   DET -> leaf "the"
-- --   N  -> leaf  "cat"
-- --   NP ->  pauseAt NP
-- --   VP -> loadFragments $ head $ fragmentDict VP
-- -- --   VP ->  head (loadFragments . fragmentToBranch <$> (fragmentDict VP))
-- -- --   V  -> leaf (V, False) "sees"
--     )

--   S

--   where

--   branch bs =  FT.Free $ Branch (F.Pure <$> bs)
--   leaf = FT.Free . Leaf
--   pauseAt = FT.Pure

--   loadFragments brs = FT.Free $ Branch $ (F.hoistFree ((Compose . Identity . FT.Free))) . toFree <$> brs 
  -- brs :: [Fragment Deterministic Word]
  --                                   -> FT.FreeF
  --                                        (NonRecursiveTree [Char])
  --                                        CAT
  --                                        (F.Free
  --                                           (Compose
  --                                              Identity (FT.FreeF (NonRecursiveTree Word) CAT))
  --                                           CAT) -- FT.Free . fmap (toFree . FT.transFreeT (Compose . return . FT.Free))

-- probabilisticSimpleTree :: MonadSample m => Tree m Word
-- probabilisticSimpleTree = Fold.unfold pcfg S

-- pcfg = (Compose . \case

--   S  -> return $ branch (S, False) [NP, VP]
--   NP ->  return $ branch (NP, False) [DET, N]
--   DET -> return $ leaf (DET, False) "the"
--   N  -> uniformD [branch (N, False) [A, N], leaf (N, False) "idea"]
--   A  -> uniformD [leaf (A, False) "green", leaf (A, False) "furious"]
--   VP ->  return $ branch (NP, False) [V, NP]
--   V  -> return $ leaf (V, False) "sees")

 
-- probabilisticSimpleFragment :: MonadSample m => Fragment m Word
-- probabilisticSimpleFragment = Fold.unfold (Compose . \case

--   S  -> return $ branch (S, False) [NP, VP]
--   NP ->  return $ branch (NP, False) [DET, N]
--   DET -> return $ leaf (DET, False) "the"
--   N  -> uniformD [branch (N, False) [A, N], leaf (N, False) "idea"]
--   A  -> uniformD [leaf (A, False) "green", leaf (A, False) "furious"]
--   VP ->  uniformD [FT.Pure VP, branch (NP, False) [V, NP]]
--   V  -> return $ leaf (V, False) "sees")

--   S

-- probabilisticComplexTree :: MonadSample m => FragmentDict -> Tree m Word
-- probabilisticComplexTree fragmentDict = Fold.futu (Compose . \case

--   S  -> return $ branch (S, False) [NP, VP]
--   NP ->  return $ branch (NP, False) [DET, N]
--   DET -> return $ leaf (DET, False) "the"
--   N  -> uniformD [branch (N, False) [A, N], leaf (N, False) "idea"]
--   A  -> uniformD [leaf (A, False) "green", leaf (A, False) "furious"]
--   VP ->  uniformD (loadFragments . fragmentToBranch <$> (fragmentDict VP)) 
--   V  -> return $ leaf (V, False) "sees")

--   S

--   where 

--   branch a bs = FT.Free $ Branch a (F.Pure <$> bs)

-- probabilisticComplexFragment :: MonadSample m => FragmentDict -> Fragment m Word
-- probabilisticComplexFragment fragmentDict = Fold.futu (Compose . go) S where


--   go S = return $ branch (S, False) [NP, VP]
--   go NP = return $ FT.Pure NP
--   go DET = return $ leaf (DET, False) "the"
--   go N = uniformD [branch (N, False) [A, N], leaf (N, False) "idea"]
--   go A = uniformD [leaf (A, False) "green", leaf (A, False) "furious"]
--   go V = return $ leaf (V, False) "sees"
--   go VP = uniformD (loadFragments . fragmentToBranch <$> (fragmentDict VP)) 


--   branch a bs = FT.Free $ Branch a (F.Pure <$> bs)
--   leaf a = FT.Free . Leaf a



-- fragmentCFG :: FragmentDict -> Tree [] Word
-- fragmentCFG fragmentDict = Fold.futu (Compose . \case

--   S  -> return $ branch (S, False) [NP, VP]
--   NP ->  return $ branch (NP, False) [DET, N]
--   DET -> return $ leaf (DET, False) "the"
--   N  ->  [branch (N, False) [A, N], leaf (N, False) "idea"]
--   A  ->  [leaf (A, False) "green", leaf (A, False) "furious"]
--   VP ->  (loadFragments . fragmentToBranch <$> (fragmentDict VP)) 
--   V  -> return $ leaf (V, False) "sees")
  
--   S

--   where 

--   branch a bs = FT.Free $ Branch a (F.Pure <$> bs)



-- grammar :: FragmentDict
-- grammar = \case
  
--   S -> [[branch [pauseAt NP, pauseAt VP] ]]
--   NP -> [[branch [pauseAt DET, pauseAt N] ]]
--   VP -> [[branch [leaf "gives", pauseAt NP], branch [leaf "a", leaf "break" ]]]
--   N -> [[leaf "dog", branch  [pauseAt A, pauseAt N]]]
--   V -> [[leaf "sees"]]
--   DET -> [[leaf "the"]]

--   _ -> [[leaf "no entry: error (grammar)"]]

--   where 

--   branch bs = FT.free $ FT.Free $ Branch bs
--   leaf = FT.free . FT.Free . Leaf
--   pauseAt = FT.free . FT.Pure



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




-- fragmentToBranch :: Fragment Deterministic Word -> NonRecursiveTree Word (Fragment Deterministic Word)
-- fragmentToBranch (FT.FreeT (Identity (FT.Pure x))) = Branch (S, True) [FT.free $ FT.Pure x]
-- fragmentToBranch (FT.FreeT (Identity (FT.Free (Branch c brs)))) = Branch c brs
-- fragmentToBranch (FT.FreeT (Identity (FT.Free (Leaf c x)))) = Leaf c x


-- loadFragments = FT.Free . fmap (toFree . FT.transFreeT (Compose . return . FT.Free)) where
-- -- converts between Free from Control.Monad.Trans.Free and Control.Monad.Free
toFree :: Functor f => FT.Free f a1 -> F.Free f a1
toFree = Fold.cata $ \case
  Compose (Identity (FT.Free x)) -> F.Free x
  Compose (Identity (FT.Pure x)) -> F.Pure x

-- freeTreeAlgebra :: Show a => Compose Identity (FT.FreeF (NonRecursiveTree [Char]) a) [Char] -> [Char]
-- freeTreeAlgebra (Compose (Identity (FT.Free (Branch c brs)))) = join $ intersperse " " brs
-- freeTreeAlgebra (Compose (Identity (FT.Free (Leaf c a)))) = a 
-- freeTreeAlgebra (Compose (Identity (FT.Pure a))) = show a


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

toDiagram :: Tree Identity Word -> Diagram B
toDiagram = fst . Fold.cata alg where

  -- alg = undefined
  
  alg (Compose (Identity (FT.Pure x))) = (text (show x) # fc blue <> rect (maximum [fromIntegral (length (show x)), 3]) 2 # lw 0,
      show x)

  alg (Compose (Identity (FT.Free (c FT.:< (Leaf x))))) =
    (vsep 0.5 [
      text (show $ showCat c) # fc (col id c) <> rect (maximum [fromIntegral $ length x, 3]) 2 # lw 0,
      vrule 0.5,
      text (init x) # (col fc c) <> rect (maximum [fromIntegral $ length x, 3]) 2 # lw 0],
    show $ last x)
  alg (Compose (Identity (FT.Free (c FT.:< Branch brs)))) = combineDiagrams (col id c) c (brs)


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
      arrowStyle = (with & arrowHead .~ dart & headLength .~ 3 
        & tailLength .~ verySmall)
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

  saveDiagram "img/deterministicSimpleTree.svg" $ toDiagram $ deterministicSimpleTree
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

