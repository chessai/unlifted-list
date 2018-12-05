{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTSyntax #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.List.Unlifted
  ( UList(UNil,UCons)
  , map
  , foldr
  , foldl
  , foldl'
  , null
  , scanl
  , filter
  , length
  , (.)
  ) where

import GHC.Prim
import GHC.Types
import GHC.Magic (oneShot)
import Data.Function (id)
import Data.Semigroup (Semigroup((<>)))
#if MIN_VERSION_base(4,9,0)
import Data.Monoid (Monoid(mempty, mappend))
#endif
import GHC.Num ((+))

(.) :: forall (a :: TYPE 'UnliftedRep) (b :: TYPE 'UnliftedRep) (c :: TYPE 'UnliftedRep). (b -> c) -> (a -> b) -> a -> c
{-# INLINE (.) #-}
(.) f g = \x -> f (g x)

data UList (a :: TYPE 'UnliftedRep) where
  UNil  :: UList a
  UCons :: a -> UList a -> UList a

instance Semigroup (UList a) where
  (<>) = (++)

#if MIN_VERSION_base(4,9,0)
instance Monoid (UList a) where
  mempty = UNil
#if !MIN_VERSION_base(4,11,0)
  mappend = (<>)
#endif
#endif

map :: (a -> b) -> UList a -> UList b
{-# NOINLINE [0] map #-}
map _ UNil = UNil
map f (UCons x xs) = UCons (f x) (map f xs)

mapFB :: forall (a :: TYPE 'UnliftedRep)
                (elt :: TYPE 'UnliftedRep)
                (lst :: Type).
     (elt -> lst -> lst) -> (a -> elt) -> a -> lst -> lst
{-# INLINE [0] mapFB #-}
mapFB c f = \x ys -> c (f x) ys

build :: forall a. (forall b. (a -> b -> b) -> b -> b) -> UList a
{-# INLINE [1] build #-}
build g = g UCons UNil

augment :: forall a. (forall b. (a -> b -> b) -> b -> b) -> UList a -> UList a
{-# INLINE [1] augment #-}
augment g xs = g UCons xs

foldr :: (a -> b -> b) -> b -> UList a -> b
{-# INLINE [0] foldr #-}
foldr k z = go
  where
    go UNil = z
    go (UCons y ys) = y `k` go ys

foldl :: forall a b. (b -> a -> b) -> b -> UList a -> b
{-# INLINE foldl #-}
foldl k z0 xs = foldr
  (\(v :: a) (fn :: b -> b) -> oneShot (\(z :: b) -> fn (k z v)))
  (id :: b -> b)
  xs
  z0

foldl' :: forall a b. (b -> a -> b) -> b -> UList a -> b
{-# INLINE foldl' #-}
foldl' k z0 xs = foldr
  (\(v :: a) (fn :: b -> b) -> oneShot (\(z :: b) -> z `seq` fn (k z v)))
  (id :: b -> b)
  xs
  z0

null :: UList a -> Bool
null UNil = True
null _    = False

scanl :: (b -> a -> b) -> b -> UList a -> UList b
{-# NOINLINE [1] scanl #-}
scanl = scanlGo
  where
    scanlGo f q ls = UCons q
      (case ls of
        UNil -> UNil
        UCons x xs -> scanlGo f (f q x) xs
      )

{-# RULES
"scanl" [~1] forall f a bs. scanl f a bs =
  build (\c n -> a `c` foldr (scanlFB f c) (\_ -> n) bs a)
"scanList" [1] forall f (a::a) bs.
  foldr (scanlFB f UCons) (\_ -> UNil) bs a = tail (scanl f a bs)
  #-}

tail :: UList a -> UList a
tail UNil = UNil
tail (UCons x xs) = xs

{-# INLINE [0] scanlFB #-}
scanlFB :: forall (a :: TYPE 'UnliftedRep)
                  (b :: TYPE 'UnliftedRep)
                  (c :: Type). 
                  (b -> a -> b) -> (b -> c -> c) -> a -> (b -> c) -> b -> c
scanlFB f c = \b g -> oneShot (\x -> let b' = f x b in b' `c` g b')

(++) :: UList a -> UList a -> UList a
{-# NOINLINE [1] (++) #-}
(++) UNil ys = ys
(++) (UCons x xs) ys = UCons x (xs ++ ys)

{-# RULES
"++" [~1] forall xs ys. xs ++ ys = augment (\c n -> foldr c n xs) ys
  #-}

filter :: (a -> Bool) -> UList a -> UList a
{-# NOINLINE [1] filter #-}
filter _ UNil = UNil
filter pred (UCons x xs) = if pred x
  then UCons x (filter pred xs)
  else filter pred xs

length :: UList a -> Int
{-# NOINLINE [1] length #-}
length xs = lenAcc xs 0

lenAcc :: UList a -> Int -> Int
lenAcc UNil n = n
lenAcc (UCons _ ys) n = lenAcc ys (n + 1)

{-# RULES
"map" [~1] forall f xs. map f xs = build (\c n -> foldr (mapFB c f) n xs)
"mapList" [1] forall f. foldr (mapFB UCons f) UNil = map f
"mapFB" forall c f g. mapFB (mapFB c f) g = mapFB c (f . g)
"mapFB/id" forall c. mapFB c (\x -> x) = c
  #-}

-- Coercible (a :: Type) (b :: Type)
-- {-# RULES "map/coerce" [1] map coerce = coerce #-}

-- This needs something like `class Eq (a :: TYPE 'UnliftedRep)`
--elem :: a -> UList a -> Bool
--elem _ UNil = False
--elem x (y:ys) = x == y || elem x ys

