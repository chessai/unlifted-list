{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTSyntax #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wall -Werror #-}

-- | This module defines an API centred around linked lists of unlifted values.
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
  , singleton
  , pure
  , cons
  , traverse_
  , concat
  , concatMap
  , foldMap
  ) where

import qualified Control.Applicative as A
import qualified Data.Foldable as F
import GHC.Prim
import GHC.Types
import GHC.Magic (oneShot)
import Data.Function (id)
import Data.Semigroup (Semigroup((<>)))
#if MIN_VERSION_base(4,9,0)
import Data.Monoid (Monoid(mempty, mappend))
#endif
import GHC.Num ((+))

-- | Function composition.
(.) :: forall (a :: TYPE 'UnliftedRep) (b :: TYPE 'UnliftedRep) (c :: TYPE 'UnliftedRep). (b -> c) -> (a -> b) -> a -> c
{-# INLINE (.) #-}
(.) f g = \x -> f (g x)

-- | A linked list of unlifted values. The values stored in the list
--   are guaranteed to not be thunks.
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

-- | 'map' @f xs@ is the list obtained by applying @f@ to each element
-- of @xs@, i.e.,
--
-- > map f [x1, x2, ..., xn] == [f x1, f x2, ..., f xn]
-- > map f [x1, x2, ...] == [f x1, f x2, ...]
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

-- | 'foldr', applied to a binary operator, a starting value (typically
-- the right-identity of the operator), and a list, reduces the list
-- using the binary operator, from right to left:
--
-- > foldr f z [x1, x2, ..., xn] == x1 `f` (x2 `f` ... (xn `f` z)...)
foldr :: (a -> b -> b) -> b -> UList a -> b
{-# INLINE [0] foldr #-}
foldr k z = go
  where
    go UNil = z
    go (UCons y ys) = y `k` go ys

-- | 'foldl', applied to a binary operator, a starting value (typically
-- the left-identity of the operator), and a list, reduces the list
-- using the binary operator, from left to right:
--
-- > foldl f z [x1, x2, ..., xn] == (...((z `f` x1) `f` x2) `f`...) `f` xn
--
-- The list must be finite.
foldl :: forall a b. (b -> a -> b) -> b -> UList a -> b
{-# INLINE foldl #-}
foldl k z0 xs = foldr
  (\(v :: a) (fn :: b -> b) -> oneShot (\(z :: b) -> fn (k z v)))
  (id :: b -> b)
  xs
  z0

-- | A strict version of 'foldl'.
foldl' :: forall a b. (b -> a -> b) -> b -> UList a -> b
{-# INLINE foldl' #-}
foldl' k z0 xs = foldr
  (\(v :: a) (fn :: b -> b) -> oneShot (\(z :: b) -> z `seq` fn (k z v)))
  (id :: b -> b)
  xs
  z0

-- | Test whether a list is empty.
null :: UList a -> Bool
null UNil = True
null _    = False

-- | 'scanl' is similar to 'foldl', but returns a list of successive
-- reduced values from the left:
--
-- > scanl f z [x1, x2, ...] == [z, z `f` x1, (z `f` x1) `f` x2, ...]
--
-- Note that
--
-- > last (scanl f z xs) == foldl f z xs.

-- This peculiar arrangement is necessary to prevent scanl being rewritten in
-- its own right-hand side.
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
tail (UCons _ xs) = xs

{-# INLINE [0] scanlFB #-}
scanlFB :: forall (a :: TYPE 'UnliftedRep)
                  (b :: TYPE 'UnliftedRep)
                  (c :: Type). 
                  (b -> a -> b) -> (b -> c -> c) -> a -> (b -> c) -> b -> c
scanlFB f c = \b g -> oneShot (\x -> let b' = f x b in b' `c` g b')

-- | Append two lists, i.e.,
--
-- > [x1, ..., xm] ++ [y1, ..., yn] == [x1, ..., xm, y1, ..., yn]
-- > [x1, ..., xm] ++ [y1, ...] == [x1, ..., xm, y1, ...]
--
-- If the first list is not finite, the result is the first list.
(++) :: UList a -> UList a -> UList a
{-# NOINLINE [1] (++) #-}
(++) UNil ys = ys
(++) (UCons x xs) ys = UCons x (xs ++ ys)

{-# RULES
"++" [~1] forall xs ys. xs ++ ys = augment (\c n -> foldr c n xs) ys
  #-}

-- | 'filter', applied to a predicate and a list, returns the list of
-- those elements that satisfy the predicate; i.e.,
--
-- > filter p xs = [ x | x <- xs, p x]
filter :: (a -> Bool) -> UList a -> UList a
{-# NOINLINE [1] filter #-}
filter _ UNil = UNil
filter pred (UCons x xs) = if pred x
  then UCons x (filter pred xs)
  else filter pred xs

-- | /O(n)/. 'length' returns the length of a finite list as an 'Int'.
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
-- elem :: a -> UList a -> Bool
-- elem _ UNil = False
-- elem x (y:ys) = x == y || elem x ys

pure, singleton :: a -> UList a
singleton a = UCons a UNil 
pure = singleton

cons :: a -> UList a -> UList a
cons = UCons

traverse_ :: forall f a b. A.Applicative f => (a -> f b) -> UList a -> f ()
traverse_ f = foldr seqd (A.pure ())
  where
  seqd :: a -> f () -> f ()
  seqd a = (A.*>) (f a)

-- | The concatenation of all the elements of a container of ULists.
concat :: F.Foldable t => t (UList a) -> (UList a)
concat xs = build (\f a -> F.foldr (\x y -> foldr f y x) a xs)
{-# INLINE concat #-}

-- | Map a function over all the elements of a container and concatenate
-- the resulting ULists.
concatMap :: F.Foldable t => (a -> UList b) -> t a -> UList b
concatMap f xs = build (\c n -> F.foldr (\x b -> foldr c b (f x)) n xs)
{-# INLINE concatMap #-}

foldMap :: Monoid m => (a -> m) -> UList a -> m
foldMap f = foldr fun mempty
  where
  fun x = mappend (f x)

