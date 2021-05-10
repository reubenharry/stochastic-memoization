{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}


module Lib where

import Prelude hiding (words)
import           Control.Comonad.Cofree          (Cofree(..))
import qualified           Control.Monad.Free as F
import qualified           Control.Monad.Trans.Free as FT           -- (unfoldM, iter)
import           Diagrams.Prelude               hiding (E, (:<), (^.), normalize, set) 
-- (Diagram, vsep, text, circle, (#), centerX, connectOutside,
                                                  -- named, red, hsep, white, bgFrame, r2, rect)
import           Diagrams.Backend.SVG.CmdLine    (B)
import           Diagrams.Backend.SVG            (renderSVG)
-- import           Diagrams.Size                   (mkSizeSpec)
import           Data.Maybe                      (isJust)
import Data.Functor.Compose


import Control.Monad.Bayes.Enumerator
import Control.Monad.Bayes.Sampler
import Control.Monad.Bayes.Weighted
import Control.Monad.Bayes.Traced
import Control.Monad.Bayes.Class

import Control.Monad.State 

import qualified Data.Functor.Foldable as Fold

import Data.List (intersperse)

import Data.Set (Set)

import Data.Maybe (fromMaybe)

import qualified Data.Map as M


{-

todos

OH INTERESTING: 

	this is better than a fragment grammar because even the base rules, you learn:
		so the underlying cfg should just:
			randomly choose categories

try generalizing the stochastic memoization to other base functors:

basically the generalization is:

	give me an anamorphism on the Freed base functor, and I will extend that to a distribution over trees

-}

data NonRecursiveTree a x =
  Leaf a
  | Branch (CAT, Maybe (FT.FreeT (NonRecursiveTree String) Identity CAT)) x x
  | UnaryBranch x
  deriving (Functor, Foldable, Traversable)

data CAT = S' | NP' | VP' | A' | N' | DET' | COP' | V' deriving (Show, Eq, Ord)




loadFragment :: MonadSample m => FT.Free (NonRecursiveTree a) b -> FT.FreeF (NonRecursiveTree a) a (F.Free (Compose m (FT.FreeF (NonRecursiveTree a) a)) b)
loadFragment (FT.FreeT (Identity (FT.Pure x))) = FT.Free $ UnaryBranch (F.Pure x)
loadFragment (FT.FreeT (Identity (FT.Free (Branch c x y)))) = FT.Free $ Branch c (conv x) (conv y) --  F.Free $ Compose $ return $ FT.Free $ Branch (conv x) (conv y)
loadFragment (FT.FreeT (Identity (FT.Free (UnaryBranch x )))) = FT.Free $ UnaryBranch (conv x) --  F.Free $ Compose $ return $ FT.Free $ Branch (conv x) (conv y)
loadFragment (FT.FreeT (Identity (FT.Free (Leaf x)))) = FT.Free $ Leaf x

conv :: MonadSample m => FT.Free (NonRecursiveTree a) b -> F.Free (Compose m (FT.FreeF (NonRecursiveTree a) a)) b
conv (FT.FreeT (Identity (FT.Pure x))) = F.Pure x
conv (FT.FreeT (Identity (FT.Free (Branch c x y)))) = F.Free $ Compose $ return $ FT.Free $ Branch c (conv x) (conv y)
conv (FT.FreeT (Identity (FT.Free (UnaryBranch x)))) = F.Free $ Compose $ return $ FT.Free $ UnaryBranch (conv x)
conv (FT.FreeT (Identity (FT.Free (Leaf x)))) = F.Free $ Compose $ return $ FT.Free $ Leaf x

makeFragment :: (MonadSample m) => CAT -> m (FT.Free (NonRecursiveTree String) CAT)
makeFragment = FT.joinFreeT . Fold.ana go where
  go x = Compose $ do
    leaf <- bernoulli 0.8
    if leaf then (FT.Free . Leaf) <$> uniformD words else do
        c1 <- uniformD cats
        c2 <- uniformD cats
        return (FT.Free $ Branch (x, Nothing) c1 c2)
-- makeFragment = FT.joinFreeT . Fold.ana (\x -> Compose $ uniformD (ugo x <> [FT.Pure x])) where
--   ugo S' = [FT.Free $ Branch (S', Nothing) NP' VP']
--   ugo NP' = [FT.Free $ Branch (NP', Nothing) DET' N']
--   ugo N' = [FT.Free $ Leaf "circle", FT.Free $ Leaf "square", FT.Free $ Branch (N', Nothing) A' N']
--   ugo DET' = [FT.Free $ Leaf "the"]
--   ugo VP' = [FT.Free $ Branch (VP', Nothing) COP' NP', FT.Free $ UnaryBranch V']
--   ugo COP' = [FT.Free $ Leaf "is"]
--   ugo V' = [FT.Free $ Leaf "moves", FT.Free $ Leaf "turns"]
--   ugo A' = [FT.Free $ Leaf "green", FT.Free $ Leaf "blue"]

cats = [S', NP', VP', DET', A', N', COP']
words = ["the", "a", "turn", "blue", "circle", "square", "is"]

freeTreeAlgebra (Compose (Identity (FT.Free (Branch c a b)))) = a <> " " <> b
freeTreeAlgebra (Compose (Identity (FT.Free (UnaryBranch a)))) = a
freeTreeAlgebra (Compose (Identity (FT.Free (Leaf a)))) = a 
freeTreeAlgebra (Compose (Identity (FT.Pure a))) = show a

type FragmentDict = CAT -> [FT.FreeT (NonRecursiveTree String) Identity CAT]

fragment :: (MonadState FragmentDict m, MonadSample m) => CAT -> m (FT.Free (NonRecursiveTree String) String)
fragment = FT.joinFreeT . Fold.futu go where

  go x = Compose $ do
    existingFrags <- gets ($ x)
    cache <- bernoulli (1.5 - (1 / (1 + (fromIntegral $ length existingFrags ))))
    frag <- makeFragment x
    if cache then do 
        modify (\f y -> if y == x then f y <> [frag] else f y)
        existing <- uniformD . ($ x) =<< get
        return $ loadFragment existing

      else return $ loadFragment frag



viewMakeFrag :: IO ()
viewMakeFrag = print =<< (sampleIO $ runWeighted $ do 
  x <- makeFragment S'
  return (Fold.cata freeTreeAlgebra x))

makeDiagram = do 

  fragmentTrees <- fst <$> (sampleIO $ runWeighted $ do 
      (_, frags) <- runStateT (sequence $ take 10 $ repeat $ fragment S') (const [])
      return (frags =<< [S', NP', VP', DET', A', N', COP']))
  -- let d = hsep 0.5 (toDiagram <$> fragmentTrees)
  let d = hsep 0.5 $ intersperse (vrule 50) $ take 5 (toDiagram <$> fragmentTrees)
  let size = mkSizeSpec $ r2 (Just 500, Just 500)
  print (Fold.cata freeTreeAlgebra <$> fragmentTrees)
  renderSVG "img/tree.svg" size d


initialFragments S' = [(FT.FreeT (Identity (FT.Free (Branch (S', Nothing) (FT.FreeT $ Identity $ FT.Pure NP') (FT.FreeT $ Identity $ FT.Pure VP')))))]
initialFragments _ = []
  -- condition (["the blue blue blue green circle is red", "the blue green circle is red"] == sents)
  -- return (sents, Fold.cata freeTreeAlgebra <$> (ys =<< [S', NP', VP', DET', A', N']))))
-- viewFrag :: IO ([String], [String])
viewFrag :: IO () -- [([String], [String])]
viewFrag = do 

	(ls, ws) <- ((sampleIO $ runWeighted $ mh 100 $ do 
	  (xs, ys) <- runStateT (sequence $ take 10 $ repeat $ fragment S') (initialFragments)
	  let sents = Fold.cata freeTreeAlgebra <$> xs
	  -- factor $ if (("the") `elem` sents) then 2.0 else 1.0
	  return (sents, Fold.cata freeTreeAlgebra <$> (ys =<< [S', NP', VP', DET', A', N']))))
	let (a,b) = unzip ls
	mapM_ print $ (drop 90 a)
	mapM_ print (drop 90 b)
	print(ws)

toDiagram :: Show a => FT.Free (NonRecursiveTree String) a -> Diagram B
toDiagram = (Fold.cata alg :: Show a => FT.Free (NonRecursiveTree String) a -> Diagram B) where
  

  alg (Compose (Identity (FT.Pure x))) =
    vsep 0.75 [
      text (show x) <> rect (fromIntegral (length (show x))) 2,
      text $ show x ]



  alg (Compose (Identity (FT.Free (Branch (c,_) x y)))) = combineDiagrams c x y
  alg (Compose (Identity (FT.Free (UnaryBranch x)))) = x
  alg (Compose (Identity (FT.Free (Leaf x)))) = text x <> rect (fromIntegral $ length x) 2
  -- alg (Branch brL@((dgrmL,semL,labelL) :< _) brR@((dgrmR,semR,labelR) :< _) ) =


  --     let idiomColor = if isJust $ idiom (brL,brR) then red else white
  --     in combineDiagrams
  --       (idiom (brL,brR))
  --       (dgrmL # bgFrame 2.0 idiomColor, semL,labelL)
  --       (dgrmR # bgFrame 2.0 idiomColor, semR,labelR)



  -- combine two diagrams together
  combineDiagrams :: CAT -> (Diagram B) -> (Diagram B) -> (Diagram B)
  combineDiagrams c d1 d2 =

    -- let arrowStyle = (with & arrowHead .~ dart & headLength .~ verySmall & tailLength .~ small)
    (
    vsep 2 [
      text (show c) <> rect 2 2
        # centerX,
        -- # named (show (str1<>"|"<>str2)),
      hsep 0.5 [d1, d2]
                                            -- # named (show str2)]
                                            # centerX
      ])
    --   # connectOutside' arrowStyle (show (str1<>"|"<>str2)) (show str1)
    --   # connectOutside' arrowStyle (show (str1<>"|"<>str2)) (show str2)