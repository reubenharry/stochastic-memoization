{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}


module Lib where

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
-- import Control.Monad.Bayes.Traced
import Control.Monad.Bayes.Class

import Control.Monad.State 

import qualified Data.Functor.Foldable as Fold

import Data.List (intersperse)


data NonRecursiveTree a x =
  Leaf a
  | Branch x x
  | UnaryBranch x
  deriving (Functor, Foldable, Traversable)

data CAT = S' | NP' | VP' | A' | N' | DET' | COP' | V' deriving (Show, Eq)



loadFragment :: MonadSample m => FT.Free (NonRecursiveTree a) b -> FT.FreeF (NonRecursiveTree a) a (F.Free (Compose m (FT.FreeF (NonRecursiveTree a) a)) b)
loadFragment (FT.FreeT (Identity (FT.Pure x))) = FT.Free $ UnaryBranch (F.Pure x)
loadFragment (FT.FreeT (Identity (FT.Free (Branch x y)))) = FT.Free $ Branch (conv x) (conv y) --  F.Free $ Compose $ return $ FT.Free $ Branch (conv x) (conv y)
loadFragment (FT.FreeT (Identity (FT.Free (UnaryBranch x )))) = FT.Free $ UnaryBranch (conv x) --  F.Free $ Compose $ return $ FT.Free $ Branch (conv x) (conv y)
loadFragment (FT.FreeT (Identity (FT.Free (Leaf x)))) = FT.Free $ Leaf x

conv :: MonadSample m => FT.Free (NonRecursiveTree a) b -> F.Free (Compose m (FT.FreeF (NonRecursiveTree a) a)) b
conv (FT.FreeT (Identity (FT.Pure x))) = F.Pure x
conv (FT.FreeT (Identity (FT.Free (Branch x y)))) = F.Free $ Compose $ return $ FT.Free $ Branch (conv x) (conv y)
conv (FT.FreeT (Identity (FT.Free (UnaryBranch x)))) = F.Free $ Compose $ return $ FT.Free $ UnaryBranch (conv x)
conv (FT.FreeT (Identity (FT.Free (Leaf x)))) = F.Free $ Compose $ return $ FT.Free $ Leaf x

makeFragment :: (MonadSample m) => CAT -> m (FT.Free (NonRecursiveTree String) CAT)
makeFragment = FT.joinFreeT . Fold.ana ugo where
  ugo S' = Compose $ uniformD [FT.Free $ Branch NP' VP']
  ugo NP' = Compose $ uniformD [FT.Free $ Branch DET' N', FT.Pure NP']
  ugo N' = Compose $ uniformD [FT.Free $ Leaf "circle", FT.Free $ Leaf "square", FT.Free $ Branch A' N', FT.Pure N']
  ugo DET' = Compose $ uniformD [FT.Free $ Leaf "the", FT.Pure DET']
  ugo VP' = Compose $ uniformD [FT.Free $ Branch COP' NP', FT.Free $ UnaryBranch V', FT.Pure VP']
  ugo COP' = Compose $ uniformD [FT.Free $ Leaf "is", FT.Pure COP']
  ugo V' = Compose $ uniformD [FT.Free $ Leaf "moves", FT.Free $ Leaf "turns", FT.Pure V']
  ugo A' = Compose $ uniformD [FT.Free $ Leaf "green", FT.Free $ Leaf "blue", FT.Pure A']

freeTreeAlgebra (Compose (Identity (FT.Free (Branch a b)))) = a <> " " <> b
freeTreeAlgebra (Compose (Identity (FT.Free (UnaryBranch a)))) = a
freeTreeAlgebra (Compose (Identity (FT.Free (Leaf a)))) = a 
freeTreeAlgebra (Compose (Identity (FT.Pure a))) = show a

type FragmentDict = CAT -> [FT.FreeT (NonRecursiveTree String) Identity CAT]

fragment :: (MonadState FragmentDict m, MonadSample m) => CAT -> m (FT.Free (NonRecursiveTree String) String)
fragment = FT.joinFreeT . Fold.futu go where

  go x = Compose $ do
    existingFrags <- gets ($ x)
    cache <- bernoulli (1.1 - (1 / (1 + (fromIntegral $ length existingFrags ))))
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
  let d = hsep 0.5 $ intersperse (vrule 50) (toDiagram <$> fragmentTrees)
  let size = mkSizeSpec $ r2 (Just 500, Just 500)
  print (Fold.cata freeTreeAlgebra <$> fragmentTrees)
  renderSVG "img/tree.svg" size d

  -- condition (["the blue blue blue green circle is red", "the blue green circle is red"] == sents)
  -- return (sents, Fold.cata freeTreeAlgebra <$> (ys =<< [S', NP', VP', DET', A', N']))))
viewFrag :: IO ([String], [String])
viewFrag = (fst <$> (sampleIO $ runWeighted $ do 
  (xs, ys) <- runStateT (sequence $ take 5 $ repeat $ fragment S') (const [])
  let sents = Fold.cata freeTreeAlgebra <$> xs
  -- condition (["the blue blue blue green circle is red", "the blue green circle is red"] == sents)
  return (sents, Fold.cata freeTreeAlgebra <$> (ys =<< [S', NP', VP', DET', A', N']))))

toDiagram :: Show a => FT.Free (NonRecursiveTree String) a -> Diagram B
toDiagram = (Fold.cata alg :: Show a => FT.Free (NonRecursiveTree String) a -> Diagram B) where
  

  alg (Compose (Identity (FT.Pure x))) =
    vsep 0.75 [
      text (show x) <> rect (fromIntegral (length (show x))) 2,
      text $ show x ]



  alg (Compose (Identity (FT.Free (Branch x y)))) = x `combineDiagrams` y
  alg (Compose (Identity (FT.Free (UnaryBranch x)))) = x
  alg (Compose (Identity (FT.Free (Leaf x)))) = text x <> rect (fromIntegral $ length x) 2
  -- alg (Branch brL@((dgrmL,semL,labelL) :< _) brR@((dgrmR,semR,labelR) :< _) ) =


  --     let idiomColor = if isJust $ idiom (brL,brR) then red else white
  --     in combineDiagrams
  --       (idiom (brL,brR))
  --       (dgrmL # bgFrame 2.0 idiomColor, semL,labelL)
  --       (dgrmR # bgFrame 2.0 idiomColor, semR,labelR)



  -- combine two diagrams together
  combineDiagrams :: (Diagram B) -> (Diagram B) -> (Diagram B)
  combineDiagrams d1 d2 =

    -- let arrowStyle = (with & arrowHead .~ dart & headLength .~ verySmall & tailLength .~ small)
    (
    vsep 2 [
      rect 2 2
        # centerX,
        -- # named (show (str1<>"|"<>str2)),
      hsep 0.5 [d1, d2]
                                            -- # named (show str2)]
                                            # centerX
      ])
    --   # connectOutside' arrowStyle (show (str1<>"|"<>str2)) (show str1)
    --   # connectOutside' arrowStyle (show (str1<>"|"<>str2)) (show str2)