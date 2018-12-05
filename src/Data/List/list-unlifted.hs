{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

module Data.List.Unlifted
  ( UList(UNil,UCons)
  , map
  , foldr
  , (.)
  ) where

import GHC.Prim
import GHC.Types

(.) :: forall (a :: TYPE 'UnliftedRep) (b :: TYPE 'UnliftedRep) (c :: TYPE 'UnliftedRep). (b -> c) -> (a -> b) -> a -> c
{-# INLINE (.) #-}
(.) f g = \x -> f (g x)

data UList (a :: TYPE 'UnliftedRep) where
  UNil  :: UList a
  UCons :: a -> UList a -> UList a

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

foldr :: (a -> b -> b) -> b -> UList a -> b
{-# INLINE [0] foldr #-}
foldr k z = go
  where
    go UNil = z
    go (UCons y ys) = y `k` go ys

-- This needs something like `class Eq (a :: TYPE 'UnliftedRep)`
--elem :: a -> UList a -> Bool
--elem _ UNil = False
--elem x (y:ys) = x == y || elem x ys

{-# RULES
"map" [~1] forall f xs. map f xs = build (\c n -> foldr (mapFB c f) n xs)
"mapList" [1] forall f. foldr (mapFB UCons f) UNil = map f
"mapFB" forall c f g. mapFB (mapFB c f) g = mapFB c (f . g)
"mapFB/id" forall c. mapFB c (\x -> x) = c
  #-}

-- Coercible (a :: Type) (b :: Type)
-- {-# RULES "map/coerce" [1] map coerce = coerce #-}

