{-# LANGUAGE DeriveTraversable, FlexibleContexts, TypeFamilies, GADTs, TupleSections, NoMonomorphismRestriction #-}

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

type Word = String
data CAT = S | NP | VP | A | N | DET | COP | V deriving (Show, Eq, Ord)

type NodeData = (CAT, (Bool, Bool))
data NonRecursiveTree leafType branchType =
  Leaf leafType
  | Branch NodeData [branchType]
  deriving (Functor, Foldable, Traversable)

type RecursiveTree m leafType = FixT (NonRecursiveTree leafType) m
type Fragment m leafType pauseType = FT.FreeT (NonRecursiveTree leafType) m pauseType
type FragmentDict = CAT -> [Fragment Deterministic Word CAT]
type Deterministic = Identity -- a type synonym to indicate that the monad is just the identity

newtype FixT f m = FixT {runFixT :: (m (f (FixT f m) ))}

type instance Fold.Base (FixT f m) = Compose m f

instance (Functor m, Functor f) => Fold.Recursive (FixT f m) where
  project = Compose . runFixT
instance (Functor m, Functor f) => Fold.Corecursive (FixT f m) where
  embed = FixT . getCompose

cats :: [CAT]
cats = [S, NP, VP, DET, A, N, COP, V]
words :: [Word]
words = ["the", "a", "turn", "blue", "circle", "square", "is"]

node cat = FT.free $ FT.Pure cat
leaf str = FT.free $ FT.Free $ Leaf str
branch cat lb rb  = FT.free (FT.Free (Branch (cat, (False, False)) [lb, rb]))

deterministicSimpleTree :: RecursiveTree Deterministic Word
deterministicSimpleTree = Fold.ana (Compose . Identity . go) S where

  go S = Branch (S, (False, False)) [NP, VP]
  go NP = Branch (NP, (False, False)) [DET, N]
  go DET = Leaf "the"
  go N = Leaf "cat"
  go VP = Branch (VP, (False, False)) [V, NP]
  go V = Leaf "sees"

deterministicSimpleFragment :: Fragment Deterministic Word CAT
deterministicSimpleFragment = Fold.ana (Compose . Identity . go) S where

  branch a bs = FT.Free $ Branch a bs
  leaf = FT.Free . Leaf
  pauseAt = FT.Pure

  go S = branch (S, (False, False)) [NP, VP]
  go NP = branch (NP, (False, False)) [DET, N]
  go DET = leaf "the"
  go N = leaf "cat"
  go VP = pauseAt VP
  go V = leaf "sees"

deterministicComplexTree :: FragmentDict -> RecursiveTree Deterministic Word
deterministicComplexTree fragmentDict = Fold.futu (Compose . Identity . go) S where
  go S = Branch (S, (False, False)) [F.Pure NP, F.Pure VP]
  go NP = Branch (NP, (False, False)) [F.Pure DET, F.Pure N]
  go DET = Leaf "the"
  go N = Leaf "cat"
  -- go VP = fragmentToBranch $ head $ fragmentDict VP  -- Branch (S, (False, False)) [F.Pure V]

  --   -- Branch (VP, (True, True)) 
  --   -- [F.Pure V, 
  --   --  F.Free $ Branch (NP, (True,True)) 
  --   --   [F.Pure DET, 
  --   --    F.Free $ Leaf "dog"]]
  go V = Leaf "sees"

deterministicComplexFragment :: FragmentDict -> Fragment Deterministic Word CAT
deterministicComplexFragment fragmentDict = Fold.futu go S where
  
  branch a bs = Compose $ Identity $ FT.Free $ Branch a (F.Pure <$> bs)
  leaf = Compose . Identity . FT.Free . Leaf
  pauseAt = Compose . Identity . FT.Pure

  -- go DET = Compose $ Identity $ fragmentToBranch $ undefined
  -- branch (DET, (False, False)) [(F.Pure NP), (F.Pure VP)]
  go N = leaf "cat"
  go S = branch (S, (False, False)) [NP, VP]
  -- go VP = Compose $ Identity $ FT.Free $ undefined -- fragmentToBranch $ head $ fragmentDict VP  -- Branch (S, (False, False)) [F.Pure V]

    -- Branch (VP, (True, True)) 
    -- [F.Pure V, 
    --  F.Free $ Branch (NP, (True,True)) 
    --   [F.Pure DET, 
    --    F.Free $ Leaf "dog"]]
  -- go V = Leaf "sees"

probabilisticSimpleTree :: MonadSample m => RecursiveTree m Word
probabilisticSimpleTree = Fold.ana (Compose . go) S where

  go S = return $ Branch (S, (False, False)) [NP, VP]
  go NP = return $ Branch (NP, (False, False)) [NP, VP]
  go DET = return $ Leaf "the"
  go N = uniformD [Branch (N, (False, False)) [A, N], Leaf "idea"]
  go A = uniformD [Leaf "green", Leaf "furious"]
  go VP = return $ Branch (VP, (False, False)) [V, NP]
  go V = return $ Leaf "sees"

probabilisticSimpleFragment :: MonadSample m => Fragment m Word CAT
probabilisticSimpleFragment = Fold.ana (Compose . go) S where

  branch a bs = FT.Free $ Branch a bs
  leaf = FT.Free . Leaf

  go = undefined

probabilisticComplexTree :: MonadSample m => FragmentDict -> RecursiveTree m Word
probabilisticComplexTree fragmentDict = Fold.futu (Compose . go) S where

  branch a bs = FT.Free $ Branch a bs
  leaf = FT.Free . Leaf

  go = undefined


probabilisticComplexFragment :: MonadSample m => FragmentDict -> Fragment m Word CAT
probabilisticComplexFragment fragmentDict = Fold.futu go S where
  
  howMuchToReuse = 1.0
  howMuchToSuspend = 0.5
  howMuchToRecurse = 0.5
  
  go cat = Compose $ do 
    leaf <- bernoulli howMuchToRecurse
    if False then FT.Free . Leaf <$> uniformD words else makeBranches cat

  makeBranchNonCompositional existingFrags = loadFragment <$> uniformD existingFrags

  makeBranchCompositional = do
    suspend <- bernoulli howMuchToSuspend
    cat <- uniformD cats
    return $ if suspend then F.Free $ Compose $ return $ FT.Pure cat else F.Pure cat

  makeBranch cat = do
    let existingFrags = lookupCat cat fragmentDict
    useFragment <- if null existingFrags then return False else bernoulli howMuchToReuse --(1 - (1 / (1 + fromIntegral (length existingFrags ))))
    if useFragment 
      then (, True) <$> makeBranchNonCompositional existingFrags 
      else (, False) <$> makeBranchCompositional

  makeBranches cat = do
    (bL, noncomposL) <- makeBranch cat
    (bR, noncomposR) <- makeBranch cat
    return (FT.Free $ Branch (cat, (noncomposL, noncomposR)) [bL, bR] )

-- probabilisticComplexFragment = FT.joinFreeT . Fold.ana (\x -> Compose $ uniformD (ugo x <> [FT.Pure x])) where
--   ugo S = [FT.Free $ Branch (S, Nothing) NP VP]
--   ugo NP = [FT.Free $ Branch (NP, Nothing) DET N]
--   ugo N = [FT.Free $ Leaf "circle", FT.Free $ Leaf "square", FT.Free $ Branch (N, Nothing) A N]
--   ugo DET = [FT.Free $ Leaf "the"]
--   ugo VP = [FT.Free $ Branch (VP, Nothing) COP NP, FT.Free $ UnaryBranch V]
--   ugo COP = [FT.Free $ Leaf "is"]
--   ugo V = [FT.Free $ Leaf "moves", FT.Free $ Leaf "turns"]
--   ugo A = [FT.Free $ Leaf "green", FT.Free $ Leaf "blue"]


aPossibleGrammar :: FragmentDict
aPossibleGrammar S = 
  let rules = [
        
        -- branch VP (node V) (node NP),
        -- branch NP (node DET) (node N),
        -- branch N (node A) (node N)


        ] 
      terminals = [leaf "there is a cat"]
      idioms = []
        -- do 
        --   x <- branch S (leaf "the") (node S)
        --   y <- branch S (leaf "is") (leaf "foo")
        --   branch S (node x) (node y)
        -- ]
  in rules <> terminals <> idioms
aPossibleGrammar VP = [branch VP (node V) (branch NP (node DET) (leaf "dog"))]


step :: MonadSample m => CAT -> FragmentDict -> m FragmentDict
step cat fragDict = do 
 frag <- FT.joinFreeT $ probabilisticComplexFragment fragDict
 addNew <- bernoulli 0.5
 let newFragDict y = if y == cat then fragDict y <> [frag] else fragDict y
 return (if addNew then newFragDict else fragDict)

lookupCat :: CAT -> FragmentDict -> [Fragment Deterministic String CAT]
lookupCat = flip ($)

iterateMInt step init int = if int == 0 then step init else do
  result <- step init
  iterateMInt step result (int -1)



makeDiagram :: IO ()
makeDiagram = do 

  (mcmcSamplesOfFragmentTrees, weight) <- sampleIO (runWeighted $ mh 10 $ do 
    frags <- (=<< cats) <$> iterateMInt (step S) aPossibleGrammar 1
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
fragmentToBranch (FT.FreeT (Identity (FT.Pure x))) = Branch (S, (False, False)) [F.Pure x]
fragmentToBranch (FT.FreeT (Identity (FT.Free (Branch c brs)))) = Branch c (toFree <$> brs)
fragmentToBranch (FT.FreeT (Identity (FT.Free (Leaf x)))) = Leaf x

-- converts between Free from Control.Monad.Trans.Free and Control.Monad.Free
toFree :: Functor f => FT.Free f a1 -> F.Free f a1
toFree = Fold.cata go where
  go (Compose (Identity (FT.Free x))) = F.Free x
  go (Compose (Identity (FT.Pure x))) = F.Pure x
  -- go (Compose (Identity (FT.Free (Branch c brs)))) = F.Free $ Compose $ return $ FT.Free $ Branch c brs


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
combineDiagrams :: (CAT, (Bool, Bool)) -> [Diagram B] -> Diagram B
combineDiagrams (c, (f1,f2)) [d1, d2] =

  let arrowStyle = (with & arrowHead .~ dart & headLength .~ verySmall & tailLength .~ small)
  
  in vsep 2 [
    text (show c) <> rect 2 2 # centerX <> translate (r2 (1, -1)) (arrowV' arrowStyle (r2 (1.5, -2))) <> translate (r2 (-1, -1)) (arrowV' arrowStyle (r2 (-1.5, -2))),
    -- <> (case f of 
    --   Just f' -> translateX 5 ( (scale 0.5 (circle 5 <> toDiagram f')))
    --   Nothing -> mempty),
    hsep 0.5 [colorIdiom f1 red d1, colorIdiom f2 red d2]
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
