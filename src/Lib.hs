{-# LANGUAGE DeriveTraversable, FlexibleContexts #-}

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
  | Branch (CAT, Maybe Fragment) x x
  | UnaryBranch x
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
initialFragments S = [FT.free (FT.Free (Branch (S, Nothing) 
                        (FT.free $ FT.Pure NP) 
                        (FT.free $ FT.Pure VP)))]
initialFragments _ = []


makeFragment2 :: MonadSample m => FragmentDict -> CAT -> m Fragment
makeFragment2 fragmentDict = FT.joinFreeT . Fold.futu go where
  
  go x = Compose $ do 
    let existingFrags = lookupCat x fragmentDict
    useFragment <- bernoulli (1 - (1 / (1 + fromIntegral (length existingFrags ))))
    if useFragment then noncompositional existingFrags x else compositional x

  noncompositional existingFrags x = do
    let chooseFragmentFromDictionary = uniformD existingFrags
    f1 <- chooseFragmentFromDictionary
    f2 <- chooseFragmentFromDictionary
    return (FT.Free $ Branch (x, Just f1) (loadFragmentHelper f1) (loadFragmentHelper f2) )

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
    return (FT.Free $ Branch (x, Nothing) (b1) (b2) )

step :: MonadSample m => CAT -> FragmentDict -> m FragmentDict
step cat fragDict = do 
 frag <- makeFragment2 fragDict cat
 let newFragDict y = if y == cat then fragDict y <> [frag] else fragDict y
 return newFragDict


makeFragment :: MonadSample m => FragmentDict -> CAT -> m Fragment
makeFragment fragmentDict = FT.joinFreeT . Fold.ana go where
  
  go x = Compose $ do 
    useFragment <- bernoulli 0.5
    if useFragment then noncompositional x else compositional x

  noncompositional x = undefined 
  -- do
  --   c <- uniformD $ lookupCat x fragmentDict
  --   return (loadFragment c)

  compositional x = do
    leaf <- bernoulli 0.8
    if leaf then FT.Free . Leaf <$> uniformD words else makeBranches x

  makeBranches x = do
    c1 <- uniformD cats
    c2 <- uniformD cats
    return (FT.Free $ Branch (x, Nothing) c1 c2)
-- makeFragment = FT.joinFreeT . Fold.ana (\x -> Compose $ uniformD (ugo x <> [FT.Pure x])) where
--   ugo S = [FT.Free $ Branch (S, Nothing) NP VP]
--   ugo NP = [FT.Free $ Branch (NP, Nothing) DET N]
--   ugo N = [FT.Free $ Leaf "circle", FT.Free $ Leaf "square", FT.Free $ Branch (N, Nothing) A N]
--   ugo DET = [FT.Free $ Leaf "the"]
--   ugo VP = [FT.Free $ Branch (VP, Nothing) COP NP, FT.Free $ UnaryBranch V]
--   ugo COP = [FT.Free $ Leaf "is"]
--   ugo V = [FT.Free $ Leaf "moves", FT.Free $ Leaf "turns"]
--   ugo A = [FT.Free $ Leaf "green", FT.Free $ Leaf "blue"]

lookupCat :: CAT -> FragmentDict -> [Fragment]
lookupCat = flip ($)



fragment :: (MonadState FragmentDict m, MonadSample m) => CAT -> m (FT.Free (NonRecursiveTree String) String)
fragment = FT.joinFreeT . Fold.futu go where

  go x = Compose $ do
    fragmentDict <- get
    let existingFrags = lookupCat x fragmentDict
    cache <- bernoulli (1.5 - (1 / (1 + fromIntegral (length existingFrags ))))
    if cache 
    then do 
      existing <- uniformD . lookupCat x =<< get
      return $ loadFragment existing
    else do
      frag <- makeFragment fragmentDict x
      modify (\f y -> if y == x then f y <> [frag] else f y)
      return $ loadFragment frag

iterateM step init int = if int == 0 then (step init) else do
  result <- step init
  iterateM step result (int -1)



makeDiagram2 :: IO ()
makeDiagram2 = do 

  fragmentTrees <- fst <$> sampleIO (runWeighted $ ($ S) <$> iterateM (step S) (const []) 4)
      -- return (x  =<< [S, NP, VP, DET, A, N, COP]))
  let d = hsep 0.5 $ intersperse (vrule 50) $ take 5 (toDiagram <$> fragmentTrees)
  let size = mkSizeSpec $ r2 (Just 500, Just 500)
  -- print (Fold.cata freeTreeAlgebra <$> fragmentTrees)
  renderSVG "img/fragment.svg" size d


makeDiagram :: IO ()
makeDiagram = do 

  fragmentTrees <- fst <$> sampleIO (runWeighted $ do 
      (_, frags) <- runStateT (replicateM 10 $ fragment S) (const [])
      return (frags =<< [S, NP, VP, DET, A, N, COP]))
  let d = hsep 0.5 $ intersperse (vrule 50) $ take 5 (toDiagram <$> fragmentTrees)
  let size = mkSizeSpec $ r2 (Just 500, Just 500)
  print (Fold.cata freeTreeAlgebra <$> fragmentTrees)
  renderSVG "img/tree.svg" size d


viewMakeFrag :: IO ()
viewMakeFrag = print =<< sampleIO (runWeighted $ do 
  x <- makeFragment2 initialFragments S
  return (Fold.cata freeTreeAlgebra x))

viewFrag :: IO () 
viewFrag = do 

  (ls, ws) <- sampleIO $ runWeighted $ mh 100 $ do 
    (xs, ys) <- runStateT (replicateM 10 $ fragment S) ( const [])
    let sents = Fold.cata freeTreeAlgebra <$> xs
    -- factor $ if (("the") `elem` sents) then 2.0 else 1.0
    -- condition (["the blue blue blue green circle is red", "the blue green circle is red"] == sents)
    return (sents, Fold.cata freeTreeAlgebra <$> (ys =<< [S, NP, VP, DET, A, N]))
  let (a,b) = unzip ls
  mapM_ print $ drop 90 a
  mapM_ print $ drop 90 b
  print ws

-- there must be a simple way to write this, but I don't know what it is
loadFragment :: MonadSample m => FT.Free (NonRecursiveTree a) b -> FT.FreeF (NonRecursiveTree a) a (F.Free (Compose m (FT.FreeF (NonRecursiveTree a) a)) b)
loadFragment (FT.FreeT (Identity (FT.Pure x))) = FT.Free $ UnaryBranch (F.Pure x)
loadFragment (FT.FreeT (Identity (FT.Free (Branch c x y)))) = FT.Free $ Branch c (loadFragmentHelper x) (loadFragmentHelper y)
loadFragment (FT.FreeT (Identity (FT.Free (UnaryBranch x )))) = FT.Free $ UnaryBranch (loadFragmentHelper x)
loadFragment (FT.FreeT (Identity (FT.Free (Leaf x)))) = FT.Free $ Leaf x

-- loadFragmentHelper :: MonadSample m => FT.Free (NonRecursiveTree a) b -> F.Free (Compose m (FT.FreeF (NonRecursiveTree a) a)) b
loadFragmentHelper (FT.FreeT (Identity (FT.Pure x))) = F.Pure x
loadFragmentHelper (FT.FreeT (Identity (FT.Free (Branch c x y)))) = F.Free $ Compose $ return $ FT.Free $ Branch c (loadFragmentHelper x) (loadFragmentHelper y)
loadFragmentHelper (FT.FreeT (Identity (FT.Free (UnaryBranch x)))) = F.Free $ Compose $ return $ FT.Free $ UnaryBranch (loadFragmentHelper x)
loadFragmentHelper (FT.FreeT (Identity (FT.Free (Leaf x)))) = F.Free $ Compose $ return $ FT.Free $ Leaf x


freeTreeAlgebra :: Show a => Compose Identity (FT.FreeF (NonRecursiveTree [Char]) a) [Char] -> [Char]
freeTreeAlgebra (Compose (Identity (FT.Free (Branch c a b)))) = a <> " " <> b
freeTreeAlgebra (Compose (Identity (FT.Free (UnaryBranch a)))) = a
freeTreeAlgebra (Compose (Identity (FT.Free (Leaf a)))) = a 
freeTreeAlgebra (Compose (Identity (FT.Pure a))) = show a



toDiagram :: Show a => TreeWithPauseValofType a -> Diagram B
toDiagram = Fold.cata alg where
  

  alg (Compose (Identity (FT.Pure x))) =
    vsep 0.75 [
      text (show x) <> rect (fromIntegral (length (show x))) 2,
      text $ show x ]



  alg (Compose (Identity (FT.Free (Branch c x y)))) = combineDiagrams c x y
  alg (Compose (Identity (FT.Free (UnaryBranch x)))) = x
  alg (Compose (Identity (FT.Free (Leaf x)))) = text x <> rect (fromIntegral $ length x) 2

  -- combine two diagrams together
  combineDiagrams :: (CAT, Maybe Fragment) -> (Diagram B) -> (Diagram B) -> (Diagram B)
  combineDiagrams (c, f) d1 d2 =

    -- let arrowStyle = (with & arrowHead .~ dart & headLength .~ verySmall & tailLength .~ small)
    
    vsep 2 [
      text (show (c)) <> rect 2 2 # centerX <> (case f of 
        Just f' -> translateX 5 (scale 0.5 (toDiagram f'))
        Nothing -> mempty),
      hsep 0.5 [d1, d2] # centerX
      ]
    --   # connectOutside' arrowStyle (show (str1<>"|"<>str2)) (show str1)
    --   # connectOutside' arrowStyle (show (str1<>"|"<>str2)) (show str2)

{-

todos

- try generalizing stochastic memoization to arbitrary recursive types

-}
