{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}

{-# OPTIONS_GHC -Wincomplete-patterns #-}

module Main where

import Data.Foldable
import Data.Maybe
import Data.Monoid
import GHC.TypeLits
import Test.QuickCheck
import qualified Data.List as L
import qualified Data.Vector.Persistent as PV
import Text.Show.Pretty

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
    , FromList <$> arbitrary
    ] ++
    [ Var <$> range (length env) | not (null env) ]
listGen env parentSize =
  let size = parentSize `div` 2 in
  oneof
    -- Drop
    [ do xs <- listGen env size
         ix <- choose (0, exprLen env xs)
         pure (Drop ix xs)

    , Reverse <$> listGen env size
    , Shrink <$> listGen env size
    , Singleton <$> valGen env size

    -- Slice
    , do xs <- listGen env size
         let len = exprLen env xs
         if len == 0 then listGen env size else do
           end <- choose (1, len)
           start <- range end
           pure (Slice start (end-start) xs)
    
    , Snoc <$> listGen env size <*> valGen env size

    -- Take
    , do xs <- listGen env size
         ix <- choose (0, exprLen env xs)
         pure (Take ix xs)

    -- Update
    , do xs <- listGen env size
         let len = exprLen env xs
         if len == 0 then listGen env size else do
           ix <- range (exprLen env xs)
           x <- valGen env size
           pure (Update ix x xs)

    , Append <$> listGen env size <*> listGen env size
    , do
        val <- listGen env size
        body <- listGen (interpList env val : env) size
        pure (Let val body)
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

type family InterpVector a where
  InterpVector [a] = PV.Vector (InterpVector a)
  InterpVector a = a

interpVector :: [PV.Vector T] -> Expr a -> InterpVector a
interpVector env0 = go env0
  where
    go :: [PV.Vector T] -> Expr a -> InterpVector a
    go env = \case
      Const n -> n
      Drop n xs -> PV.drop n (go env xs)
      Empty -> PV.empty
      FromList xs -> PV.fromList xs
      Snoc xs x -> go env xs `PV.snoc` go env x
      Append xs ys -> go env xs <> go env ys
      Index xs i -> fromMaybe (error ("Invalid index: " <> show i)) $ go env xs `PV.index` i
      Reverse xs -> PV.reverse (go env xs)
      Shrink xs -> go env xs
      Singleton x -> PV.singleton (go env x)
      Slice start len xs -> PV.slice start len $ go env xs
      Take n xs -> PV.take n $ go env xs
      Update i x xs -> PV.update i (go env x) (go env xs)

      Let x y -> go (go env x : env) y
      Var n -> env !! n

example :: Expr [T] -> IO ()
example expr = do
  print $ interpList [] expr
  print $ toList $ interpVector [] expr

prop_modelsMatch :: Property
prop_modelsMatch =
  forAll (sized (listGen [])) $ \expr ->
    counterexample (ppShow expr) $
    let l = interpList [] expr
        v = toList (interpVector [] expr)
    in
    counterexample ("list:   " <> show l) $
    counterexample ("vector: " <> show v) $
    l === v


ex1 =
  Snoc
    (Slice
       5
       1
       (Snoc
          (Take
             12
             (Drop
                3
                (Drop
                   25 -- removing 1 here gives correct answer
                   (FromList [ 1, 1, 1, 1, 1, 26 , -46 , -44 , 4 , -33 , -3 , 31 , 40 , 40 , -34 , 8 , 3 , -19 , -42 , -20 , -39 , -36 , 18 , -20 , 25 , 41 , -12 , 1 , -17 , -31 , 34 , -45 , -11 , 47 , -31 , -11 , -31 , -1 , -42 , 32 , 4 , -18 ]))))
          (Index
             (Singleton
                (Index
                   (FromList [ 14 , -16 , -24 , 5 , -14 , 26 , -25 , 24 , -11 , -36 , 40 , -39 , -17 , 4 , 13 , 4 , -27 , -7 , -36 , 6 , -3 , 19 , -3 , -22 , -31 , -10 , 13 , 46 ])
                   14))
             0)))
    (Const 45)

_Snoc xs x = xs
_Drop n xs = xs
_Take n xs = xs
_Slice _ _ xs = xs

ex2 = Slice 5 1 (Drop 28 (FromList [ 1..40 ]))

main :: IO ()
main = example ex2
