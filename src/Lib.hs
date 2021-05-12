{-# LANGUAGE DeriveTraversable, FlexibleContexts, GADTs, TupleSections #-}

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


type Word = String
data CAT = S | NP | VP | A | N | DET | COP | V deriving (Show, Eq, Ord)

data NonRecursiveTree a x =
  Leaf a
  | Branch (CAT, (Bool, Bool)) x x
  deriving (Functor, Foldable, Traversable)

type TreeWithPauseValofType a = FT.Free (NonRecursiveTree String) a
type Fragment = TreeWithPauseValofType CAT
type FragmentDict = CAT -> [Fragment]


cats :: [CAT]
cats = [S, NP, VP, DET, A, N, COP, V]
words :: [Word]
words = ["the", "a", "turn", "blue", "circle", "square", "is"]

node cat = FT.free $ FT.Pure cat
leaf str = FT.free $ FT.Free $ Leaf str
branch cat lb rb  = FT.free (FT.Free (Branch (cat, (False, False)) lb rb))

aPossibleGrammar :: FragmentDict
aPossibleGrammar S = 
  let rules = [
        
        -- branch S (node NP) (node VP)
        -- branch NP (node DET) (node N),
        -- branch N (node A) (node N)


        ] 
      terminals = [leaf "there is a cat"]
      idioms = [
        do 
          x <- branch S (leaf "the") (node S)
          y <- branch S (leaf "is") (leaf "foo")
          branch S (node x) (node y)
        ]
  in rules <> terminals <> idioms
aPossibleGrammar _ = []

makeFragment :: MonadSample m => FragmentDict -> CAT -> m Fragment
makeFragment fragmentDict = FT.joinFreeT . Fold.futu go where
  
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
    return (FT.Free $ Branch (cat, (noncomposL, noncomposR)) bL bR )

-- makeFragment = FT.joinFreeT . Fold.ana (\x -> Compose $ uniformD (ugo x <> [FT.Pure x])) where
--   ugo S = [FT.Free $ Branch (S, Nothing) NP VP]
--   ugo NP = [FT.Free $ Branch (NP, Nothing) DET N]
--   ugo N = [FT.Free $ Leaf "circle", FT.Free $ Leaf "square", FT.Free $ Branch (N, Nothing) A N]
--   ugo DET = [FT.Free $ Leaf "the"]
--   ugo VP = [FT.Free $ Branch (VP, Nothing) COP NP, FT.Free $ UnaryBranch V]
--   ugo COP = [FT.Free $ Leaf "is"]
--   ugo V = [FT.Free $ Leaf "moves", FT.Free $ Leaf "turns"]
--   ugo A = [FT.Free $ Leaf "green", FT.Free $ Leaf "blue"]

step :: MonadSample m => CAT -> FragmentDict -> m FragmentDict
step cat fragDict = do 
 frag <- makeFragment fragDict cat
 addNew <- bernoulli 0.5
 let newFragDict y = if y == cat then fragDict y <> [frag] else fragDict y
 return (if addNew then newFragDict else fragDict)

lookupCat :: CAT -> FragmentDict -> [Fragment]
lookupCat = flip ($)

iterateMInt step init int = if int == 0 then (step init) else do
  result <- step init
  iterateMInt step result (int -1)



makeDiagram :: IO ()
makeDiagram = do 

  (mcmcSamplesOfFragmentTrees, weight) <- sampleIO (runWeighted $ mh 10 $ do 
    frags <- (=<< cats) <$> iterateMInt (step S) (aPossibleGrammar) 1
    let sents = Fold.cata freeTreeAlgebra <$> frags
    condition ("the circle" `elem` sents)
    return frags
    )

  let diagram = hsep 0.5 $ intersperse (vrule 50) $ (toDiagram <$> last mcmcSamplesOfFragmentTrees)
  let size = mkSizeSpec $ r2 (Just 500, Just 500)
  print (Fold.cata freeTreeAlgebra <$> last mcmcSamplesOfFragmentTrees)
  print weight
  renderSVG "img/fragment.svg" size diagram

-- converts between free and freet representations. I should rewrite this with a catamorphism
loadFragment :: MonadSample m => FT.Free (NonRecursiveTree a) b -> F.Free (Compose m (FT.FreeF (NonRecursiveTree a) b)) b
loadFragment = Fold.cata go where
  go (Compose (Identity (FT.Free (Leaf x)))) = F.Free $ Compose $ return $ FT.Free $ Leaf x
  go (Compose (Identity (FT.Pure x))) = F.Pure x
  go (Compose (Identity (FT.Free (Branch c lb rb)))) = F.Free $ Compose $ return $ FT.Free $ Branch c lb rb


freeTreeAlgebra :: Show a => Compose Identity (FT.FreeF (NonRecursiveTree [Char]) a) [Char] -> [Char]
freeTreeAlgebra (Compose (Identity (FT.Free (Branch c a b)))) = a <> " " <> b
freeTreeAlgebra (Compose (Identity (FT.Free (Leaf a)))) = a 
freeTreeAlgebra (Compose (Identity (FT.Pure a))) = show a



toDiagram :: Show a => TreeWithPauseValofType a -> Diagram B
toDiagram = Fold.cata alg where
  

  alg (Compose (Identity (FT.Pure x))) =
    text (show x) <> rect (maximum [fromIntegral (length (show x)), 3]) 2 # lc blue

  alg (Compose (Identity (FT.Free (Branch c x y)))) = combineDiagrams c x y
  alg (Compose (Identity (FT.Free (Leaf x)))) = text x <> rect (maximum [fromIntegral $ length x, 3]) 2 # lc black

  -- combine two diagrams together
  combineDiagrams :: (CAT, (Bool, Bool)) -> (Diagram B) -> (Diagram B) -> (Diagram B)
  combineDiagrams (c, (f1,f2)) d1 d2 =

    let arrowStyle = (with & arrowHead .~ dart & headLength .~ verySmall & tailLength .~ small)
    
    in vsep 2 [
      text (show (c)) <> rect 2 2 # centerX <> translate (r2 (1, -1)) (arrowV' arrowStyle (r2 (1.5, -2))) <> translate (r2 (-1, -1)) (arrowV' arrowStyle (r2 (-1.5, -2))),
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
