{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}

{-# OPTIONS_GHC -Wno-everything -Wincomplete-patterns #-}

module Main where

import Control.Monad
import Data.Foldable
import Data.Maybe
import Data.Monoid
import GHC.TypeLits
import Test.QuickCheck
import qualified Data.List as L
import qualified Data.Vector.Persistent as PV
import qualified Data.Vector as V
import qualified OldVector as PV0
import Text.Show.Pretty
import Debug.Trace
import System.Exit

type T = Int

data Expr a where
  Const :: T -> Expr T

  Drop :: Int -> Expr [T] -> Expr [T]
  -- dropWhile ::
  --   (a -> Bool) -> Vector a -> Vector a
  Empty :: Expr [T]
  -- filter ::
  --   (a -> Bool) -> Vector a -> Vector a
  -- foldl' :: (b -> a -> b) -> b -> Vector a -> b
  -- foldr :: (a -> b -> b) -> b -> Vector a -> b
  FromList :: [T] -> Expr [T]
  FromRange :: Int -> Expr [T]
  Index :: Expr [T] -> Int -> Expr T
  -- length :: Vector a -> Int
  -- map :: (a -> b) -> Vector a -> Vector b
  -- null :: Vector a -> Bool
  -- partition :: (a -> Bool) -> Vector a -> (Vector a, Vector a)
  Reverse :: Expr [T] -> Expr [T]
  Shrink :: Expr [T] -> Expr [T]
  Singleton :: Expr T -> Expr [T]
  Slice :: Int -> Int -> Expr [T] -> Expr [T]
  Snoc :: Expr [T] -> Expr T -> Expr [T]
  -- splitAt ::
  --   Int -> Vector a -> (Vector a, Vector a)
  Take :: Int -> Expr [T] -> Expr [T]
  -- takeWhile ::
  --   (a -> Bool) -> Vector a -> Vector a
  -- unsafeIndex :: Vector a -> Int -> a
  Update :: Int -> Expr T -> Expr [T] -> Expr [T]

  Append :: Expr [T] -> Expr [T] -> Expr [T]

  Let :: Expr [T] -> Expr [T] -> Expr [T]
  Var :: Int -> Expr [T] -- de Brujin index wrt `let`s

deriving instance Eq a => Eq (Expr a)
deriving instance Show a => Show (Expr a)

exprLen :: [[T]] -> Expr [T] -> Int
exprLen env = length . interpList env

{-

Type-safe version wrt environments

data Fin n where
  FZ :: Fin 0
  FS :: Fin n -> Fin (n + 1)

-- Variables are only of one type.
-- So environment is the number of variables.
type Env = Nat

data Expr e a where
  Simple :: SimpleExpr a -> Expr e a
  Let :: Expr e [T] -> Expr (e + 1) [T] -> Expr e [T]
  Var :: Int -> Expr e [T]

  -}

range n = choose (0, n-1)

listGen
  :: [[T]] -- ^ environment
  -> Int   -- ^ size
  -> Gen (Expr [T])
listGen env 0 =
  oneof $
    [ pure Empty
--    , FromList <$> arbitrary
    , FromRange <$> sized (\size -> choose (1, size))
    ] ++
    [ Var <$> range (length env) | not (null env) ]
listGen env parentSize =
  let size = parentSize `div` 2 in
  frequency
    -- Drop
    [ (1, do xs <- listGen env size
             ix <- choose (0, exprLen env xs)
             pure (Drop ix xs))

    , (0, Reverse <$> listGen env size)
    , (0, Shrink <$> listGen env size)
    , (0, Singleton <$> valGen env size)

    -- Slice
    , (0, do xs <- listGen env size
             let len = exprLen env xs
             if len == 0 then listGen env size else do
               end <- choose (1, len)
               start <- range end
               pure (Slice start (end-start) xs))
    
    , (0, Snoc <$> listGen env size <*> valGen env size)

    -- Take
    , (1, do xs <- listGen env size
             ix <- choose (0, exprLen env xs)
             pure (Take ix xs))

    -- Update
    , (0, do xs <- listGen env size
             let len = exprLen env xs
             if len == 0 then listGen env size else do
               ix <- range (exprLen env xs)
               x <- valGen env size
               pure (Update ix x xs))

    -- Append
    , (0, Append <$> listGen env size <*> listGen env size)

    -- Let
    , (0, do val <- listGen env size
             body <- listGen (interpList env val : env) size
             pure (Let val body))

    -- leaf
    , (1, listGen env 0)
    ]

valGen :: [[T]] -> Int -> Gen (Expr T)
valGen env size =
  oneof
    [ Const <$> arbitrary

    -- Index
    , do xs <- listGen env (size `div` 2)
         let len = exprLen env xs
         if len == 0 then valGen env size else do
           ix <- range len
           pure (Index xs ix)
    ]

interpList :: [[T]] -> Expr a -> a
interpList env0 = go env0
  where
    go :: [[T]] -> Expr a -> a
    go env = \case
      Const n -> n
      Drop n xs -> L.drop n (go env xs)
      Empty -> []
      FromList xs -> xs
      FromRange n -> [0..n-1]
      Snoc xs x ->
        -- BUG go env x : go env xs
        go env xs ++ [go env x]
      Append xs ys -> go env xs ++ go env ys
      Index xs i -> go env xs !! i
      Reverse xs -> L.reverse (go env xs)
      Shrink xs -> go env xs
      Singleton x -> [go env x]
      Slice start len xs -> L.take len $ L.drop start $ go env xs
      Take n xs -> L.take n $ go env xs
      Update i x xs -> listUpdate i (go env x) (go env xs)

      Let x y -> go (go env x : env) y
      Var n -> env !! n

listUpdate :: Int -> a -> [a] -> [a]
listUpdate n x [] = []
listUpdate 0 x (_:xs) = x:xs
listUpdate n x (y:xs) = y : listUpdate (n-1) x xs

type family InterpPV a where
  InterpPV [a] = PV.Vector (InterpPV a)
  InterpPV a = a

type Show' a = (Show a, Show (InterpPV a))

interpPV :: Show' a => [PV.Vector T] -> Expr a -> InterpPV a
interpPV env0 = go env0
  where
    go :: Show' a => [PV.Vector T] -> Expr a -> InterpPV a
    go env expr =
      let !y = go' env expr
      in
        trace ("--\n" <> show expr <> "\n -> " <> show y <> "\n--")
        y

    go' :: Show' a => [PV.Vector T] -> Expr a -> InterpPV a
    go' env = \case
      Const n -> n
      Drop n xs -> PV.drop n (go env xs)
      Empty -> PV.empty
      FromList xs -> PV.fromList xs
      FromRange n -> PV.fromList [0..n-1]
      Snoc xs x -> go env xs `PV.snoc` go env x
      Append xs ys -> go env xs <> go env ys
      Index xs i ->
        let vec = go env xs
        in fromMaybe (error ("Invalid index: " <> show i <> "\nvector: " <> show vec)) $ vec `PV.index` i
      Reverse xs -> PV.reverse (go env xs)
      Shrink xs -> go env xs
      Singleton x -> PV.singleton (go env x)
      Slice start len xs -> PV.slice start len $ go env xs
      Take n xs -> PV.take n $ go env xs
      Update i x xs -> PV.update i (go env x) (go env xs)

      Let x y -> go (go env x : env) y
      Var n -> env !! n

type family InterpPV0 a where
  InterpPV0 [a] = PV0.Vector (InterpPV0 a)
  InterpPV0 a = a

interpPV0 :: [PV0.Vector T] -> Expr a -> InterpPV0 a
interpPV0 env0 = go env0
  where
    go :: [PV0.Vector T] -> Expr a -> InterpPV0 a
    go env expr = go' env expr

    go' :: [PV0.Vector T] -> Expr a -> InterpPV0 a
    go' env = \case
      Const n -> n
      Drop n xs -> PV0.drop n (go env xs)
      Empty -> PV0.empty
      FromList xs -> PV0.fromList xs
      FromRange n -> PV0.fromList [0..n-1]
      Snoc xs x -> go env xs `PV0.snoc` go env x
      Append xs ys -> go env xs <> go env ys
      Index xs i ->
        let vec = go env xs
        in fromMaybe (error ("Invalid index: " <> show i <> "\nvector: " <> show vec)) $ vec `PV0.index` i
      Reverse xs -> PV0.reverse (go env xs)
      Shrink xs -> go env xs
      Singleton x -> PV0.singleton (go env x)
      Slice start len xs -> PV0.slice start len $ go env xs
      Take n xs -> PV0.take n $ go env xs
      Update i x xs -> PV0.update i (go env x) (go env xs)

      Let x y -> go (go env x : env) y
      Var n -> env !! n

type family InterpVector a where
  InterpVector [a] = V.Vector (InterpVector a)
  InterpVector a = a

interpVector :: [V.Vector T] -> Expr a -> InterpVector a
interpVector env0 = go env0
  where
    go :: [V.Vector T] -> Expr a -> InterpVector a
    go env = \case
      Const n -> n
      Drop n xs -> V.drop n (go env xs)
      Empty -> V.empty
      FromList xs -> V.fromList xs
      FromRange n -> V.fromList [0..n-1]
      Snoc xs x -> go env xs `V.snoc` go env x
      Append xs ys -> go env xs <> go env ys
      Index xs i -> go env xs V.! i
      Reverse xs -> V.reverse (go env xs)
      Shrink xs -> go env xs
      Singleton x -> V.singleton (go env x)
      Slice start len xs -> V.slice start len $ go env xs
      Take n xs -> V.take n $ go env xs
      Update i x xs -> V.update (go env xs) (V.fromList [(i, go env x)])

      Let x y -> go (go env x : env) y
      Var n -> env !! n

example :: Expr [T] -> IO ()
example expr = do
  let l = interpList [] expr
  let v = toList $ interpPV [] expr
  let !_ = show v
  putStrLn ("list: " <> show l)
  putStrLn ("SUT:  " <> show v)
  putStrLn ("PV0:  " <> show (toList $ interpPV0 [] expr))
  when (l /= v) $ do
    putStrLn $ "FAILED: " <> show expr
    exitWith (ExitFailure 1)

prop_modelsMatch :: (Expr [T] -> [T]) -> Property
prop_modelsMatch interp =
  forAll (sized (listGen [])) $ \expr ->
    counterexample (ppShow expr) $
    let l = interpList [] expr
        v = interp expr
    in
    counterexample ("list: " <> show l) $
    counterexample ("SUT:  " <> show v) $
    counterexample ("PV0:  " <> show (toList $ interpPV0 [] expr)) $
    l === v

prop_PV_ok :: Property
prop_PV_ok = prop_modelsMatch (toList . interpPV [])

prop_Vector_ok :: Property
prop_Vector_ok = prop_modelsMatch (V.toList . interpVector [])

_Snoc xs x = xs
_Drop n xs = xs
_Take n xs = xs
_Slice _ _ xs = xs

ex2 = Slice 5 1 $ Drop 28 $ FromList [ 1..40 ]

ex3 = Drop 1 $ Take 2 $ FromList [0..32]

ex4 = Drop 33 $ Drop 31 $ FromRange 34

main :: IO ()
main = do
  example ex2
--  example ex3
--  example ex4
