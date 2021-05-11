{-# LANGUAGE DeriveTraversable, FlexibleContexts, GADTs #-}

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
  | Branch (CAT, (Maybe Fragment, Maybe Fragment)) x x
  deriving (Functor, Foldable, Traversable)

type TreeWithPauseValofType a = FT.Free (NonRecursiveTree String) a
type Fragment = TreeWithPauseValofType CAT
type FragmentDict = CAT -> [Fragment]


cats :: [CAT]
cats = [S, NP, VP, DET, A, N, COP, V]
words :: [Word]
words = ["the", "a", "turn", "blue", "circle", "square", "is"]

-- todo: use free monad instance to build these
initialFragments :: CAT -> [Fragment]
initialFragments S = [FT.free (FT.Free (Branch (S, (Nothing, Nothing)) 
                        (FT.free $ FT.Pure NP) 
                        (FT.free $ FT.Pure VP)))]
initialFragments _ = []


makeFragment :: MonadSample m => FragmentDict -> CAT -> m Fragment
makeFragment fragmentDict = FT.joinFreeT . Fold.futu go where
  
  go x = Compose $ do 
    let existingFrags = lookupCat x fragmentDict
    useFragment <- bernoulli (1 - (1 / (1 + fromIntegral (length existingFrags ))))
    if useFragment then noncompositional existingFrags x else compositional x

  noncompositional existingFrags x = do
    let chooseFragmentFromDictionary = uniformD existingFrags
    f1 <- chooseFragmentFromDictionary
    f2 <- chooseFragmentFromDictionary
    return (FT.Free $ Branch (x, (Just f1, Just f2)) (loadFragment f1) (loadFragment f2) )

  compositional x = do
    leaf <- bernoulli 0.8
    if leaf then FT.Free . Leaf <$> uniformD words else makeBranches x

  makeBranch = do
    pause <- bernoulli 0.9
    cat <- uniformD cats
    return $ if pause then F.Free $ Compose $ return $ FT.Pure cat else F.Pure cat

  makeBranches x = do
    b1 <- makeBranch
    b2 <- makeBranch
    return (FT.Free $ Branch (x, (Nothing, Nothing)) (b1) (b2) )

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
 let newFragDict y = if y == cat then fragDict y <> [frag] else fragDict y
 return newFragDict

lookupCat :: CAT -> FragmentDict -> [Fragment]
lookupCat = flip ($)




iterateMInt step init int = if int == 0 then (step init) else do
  result <- step init
  iterateMInt step result (int -1)



makeDiagram :: IO ()
makeDiagram = do 

  fragmentTrees <- fst <$> sampleIO (runWeighted $ (=<< cats) <$> iterateMInt (step S) (const []) 6)
      -- return (x  =<< [S, NP, VP, DET, A, N, COP]))
  let d = hsep 0.5 $ intersperse (vrule 50) $ take 5 (toDiagram <$> fragmentTrees)
  let size = mkSizeSpec $ r2 (Just 500, Just 500)
  print (Fold.cata freeTreeAlgebra <$> fragmentTrees)
  renderSVG "img/fragment.svg" size d




viewMakeFrag :: IO ()
viewMakeFrag = print =<< sampleIO (runWeighted $ do 
  x <- makeFragment initialFragments S
  return (Fold.cata freeTreeAlgebra x))

-- viewFrag :: IO () 
-- viewFrag = do 

--   (ls, ws) <- sampleIO $ runWeighted $ mh 100 $ do 
--     (xs, ys) <- runStateT (replicateM 10 $ fragment S) ( const [])
--     let sents = Fold.cata freeTreeAlgebra <$> xs
--     -- factor $ if (("the") `elem` sents) then 2.0 else 1.0
--     -- condition (["the blue blue blue green circle is red", "the blue green circle is red"] == sents)
--     return (sents, Fold.cata freeTreeAlgebra <$> (ys =<< [S, NP, VP, DET, A, N]))
--   let (a,b) = unzip ls
--   mapM_ print $ drop 90 a
--   mapM_ print $ drop 90 b
--   print ws

-- converts between free and freet representations. I should rewrite this with a catamorphism
loadFragment :: MonadSample m => FT.Free (NonRecursiveTree a) b -> F.Free (Compose m (FT.FreeF (NonRecursiveTree a) b)) b
loadFragment (FT.FreeT (Identity (FT.Pure x))) = F.Pure x
loadFragment (FT.FreeT (Identity (FT.Free (Branch c x y)))) = F.Free $ Compose $ return $ FT.Free $ Branch c (loadFragment x) (loadFragment y)
loadFragment (FT.FreeT (Identity (FT.Free (Leaf x)))) = F.Free $ Compose $ return $ FT.Free $ Leaf x


freeTreeAlgebra :: Show a => Compose Identity (FT.FreeF (NonRecursiveTree [Char]) a) [Char] -> [Char]
freeTreeAlgebra (Compose (Identity (FT.Free (Branch c a b)))) = a <> " " <> b
freeTreeAlgebra (Compose (Identity (FT.Free (Leaf a)))) = a 
freeTreeAlgebra (Compose (Identity (FT.Pure a))) = show a



toDiagram :: Show a => TreeWithPauseValofType a -> Diagram B
toDiagram = Fold.cata alg where
  

  alg (Compose (Identity (FT.Pure x))) =
    vsep 0.75 [
      text (show x) <> rect (maximum [fromIntegral (length (show x)), 3]) 2 # lc blue,
      text $ show x ]



  alg (Compose (Identity (FT.Free (Branch c x y)))) = combineDiagrams c x y
  alg (Compose (Identity (FT.Free (Leaf x)))) = text x <> rect (maximum [fromIntegral $ length x, 3]) 2

  -- combine two diagrams together
  combineDiagrams :: (CAT, (Maybe Fragment, Maybe Fragment)) -> (Diagram B) -> (Diagram B) -> (Diagram B)
  combineDiagrams (c, (f1,f2)) d1 d2 =

    -- let arrowStyle = (with & arrowHead .~ dart & headLength .~ verySmall & tailLength .~ small)
    
    vsep 2 [
      text (show (c)) <> rect 2 2 # centerX <> translate (r2 (1, -1)) (arrowV (r2 (1.5, -2))) <> translate (r2 (-1, -1)) (arrowV (r2 (-1.5, -2))),
      -- <> (case f of 
      --   Just f' -> translateX 5 ( (scale 0.5 (circle 5 <> toDiagram f')))
      --   Nothing -> mempty),
      hsep 0.5 [colorIdiom f1 red d1, colorIdiom f2 red d2]
         # centerX
      ]
    where
      colorIdiom f color d = case f of 
        Just _ -> d # lc color
        Nothing -> d # lc white
    --   # connectOutside' arrowStyle (show (str1<>"|"<>str2)) (show str1)
    --   # connectOutside' arrowStyle (show (str1<>"|"<>str2)) (show str2)

{-

todos

- try generalizing stochastic memoization to arbitrary recursive types

-}
