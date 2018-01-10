{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -Wall -Werror -fno-warn-unused-imports #-}
module Data.Vicinity
  ( Vicinity
  , insert
  , union
  , fromList
  , uncheckedConcat
  , splitLookup
  , singleton
  , singletonTree
  ) where

import Control.Applicative (Applicative(..),(<$>),(<*>))
import Data.Monoid
import Data.Foldable (Foldable(..),toList)
import Data.Traversable (Traversable(..))
import Data.Kind
import Data.Semigroup (Semigroup)
import Data.Nat (Nat(..))
import Data.Nat.Arithmetic (SNat,Gte,caseGte,natDiff,succSNat,zeroSNat)
import qualified Data.Semigroup

newtype Vicinity a = Vicinity (Tree a)

instance Show a => Show (Vicinity a) where
  show a = "fromList (" ++ show (toList a) ++ ")"

instance Eq a => Eq (Vicinity a) where
  a == b = toList a == toList b

instance Ord a => Ord (Vicinity a) where
  compare a b = compare (toList a) (toList b)

instance Ord a => Semigroup (Vicinity a) where
  (<>) = union

instance Ord a => Monoid (Vicinity a) where
  mempty = Vicinity empty
  mappend = union

instance Foldable Vicinity where
  foldMap f (Vicinity t) = foldMap f t

fromList :: (Foldable t, Ord a) => t a -> Vicinity a
fromList = foldr insert (Vicinity empty)

insert :: Ord a => a -> Vicinity a -> Vicinity a
insert a (Vicinity t) = Vicinity (insertTree a t)

select1 :: Ord a => a -> a -> p -> p -> p -> p
select1 x y lt eq gt
  = case compare x y of { LT -> lt; EQ -> eq; GT -> gt }

select2 :: Ord a => a -> a -> a -> p -> p -> p -> p -> p -> p
select2 x y z xlty xeqy xbtw xeqz xgtz
  = select1 x y xlty xeqy (select1 x z xbtw xeqz xgtz)

t1 :: T n a -> a -> T n a -> T ('S n) a
t1 a b c = BR (T1 a b c)

t2 :: T n a -> a -> T n a -> a -> T n a -> T ('S n) a
t2 a b c d e = BR (T2 a b c d e)

data N n a
  = T1 (T n a) a (T n a)
  | T2 (T n a) a (T n a) a (T n a)

data T n a where
  BR :: N n a -> T ('S n) a
  LF :: T 'Z a

data Tree a where
  Tree :: T n a -> Tree a

type Keep t n a = T n a -> t
type Push t n a = T n a -> a -> T n a -> t

treeToHeight :: T n a -> SNat n 
treeToHeight LF = zeroSNat
treeToHeight (BR n) = case n of
  T1 t _ _ -> succSNat (treeToHeight t)
  T2 t _ _ _ _ -> succSNat (treeToHeight t)

compareTreeHeight :: T n a -> T m a -> Either (Gte n m) (Gte m n)
compareTreeHeight a b = natDiff (treeToHeight a) (treeToHeight b)

union :: Ord a => Vicinity a -> Vicinity a -> Vicinity a
union (Vicinity a) (Vicinity b) = Vicinity (unionTree a b)

unionTree :: Ord a => Tree a -> Tree a -> Tree a
unionTree a (Tree LF) = a
unionTree a (Tree (BR (T1 LF x LF))) = insertTree x a
unionTree (Tree (BR (T1 LF x LF))) b = insertTree x b
unionTree (Tree at) b@(Tree (BR _)) = case at of
  LF -> b
  BR an -> 
    let (aLeft,aRight,aKey) = splitNearMedian an
        (bLeft,_,bRight) = splitTreeAt aKey b
     in link (unionTree aLeft bLeft) (unionTree aRight bRight)

-- Performance-wise, this may be able to be improved by
-- a small constant amount. Also, this could actually work
-- just fine on trees of height zero, but I wrote it to
-- not accept them so that the union function would
-- have to handle the base case correctly instead of
-- blindly recursing forever.
--
-- The returned triple includes the approximate median
-- but does not strip it out. The median goes in the
-- right tree. Changing this could lead to a small
-- performance improvement if linkWithKey were implemented.
splitNearMedian :: N n a -> (Tree a,Tree a,a)
splitNearMedian n = case n of
  T2 treeLeft valLeft treeMid valRight treeRight ->
    (Tree (t1 treeLeft valLeft treeMid), link (singletonTree valRight) (Tree treeRight), valRight)
  T1 treeLeft valMid treeRight ->
    (Tree treeLeft, link (singletonTree valMid) (Tree treeRight), valMid)

splitLookup :: Ord a => a -> Vicinity a -> (Vicinity a, Maybe a, Vicinity a)
splitLookup a (Vicinity t) = case splitTreeAt a t of
  (x,y,z) -> (Vicinity x, y, Vicinity z)

uncheckedConcat :: Vicinity a -> Vicinity a -> Vicinity a
uncheckedConcat (Vicinity a) (Vicinity b) = Vicinity (link a b)

_checkNodeValid :: Ord a => T n a -> T n a
_checkNodeValid LF = LF
_checkNodeValid y@(BR x) = case x of
  T1 treeLeft valMid treeRight ->
    let c1 = case treeLeft of
          LF -> True
          BR (T1 _ a _) -> a < valMid
          BR (T2 _ _ _ a _) -> a < valMid
        c2 = case treeRight of
          LF -> True
          BR (T1 _ a _) -> a > valMid
          BR (T2 _ a _ _ _) -> a > valMid
     in if c1 && c2 then y else error "checkNodeValid: invalid tree in T1 case"
  T2 treeLeft valLeft treeMid valRight treeRight ->
    let c1 = case treeLeft of
          LF -> True
          BR (T1 _ a _) -> a < valLeft
          BR (T2 _ _ _ a _) -> a < valLeft
        c2 = case treeRight of
          LF -> True
          BR (T1 _ a _) -> a > valRight
          BR (T2 _ a _ _ _) -> a > valRight
        c3 = case treeMid of
          LF -> True
          BR (T1 _ a _) -> a > valLeft && a < valRight
          BR (T2 _ a _ b _) -> a > valLeft && b < valRight
     in if c1 && c2 && c3 && valLeft < valRight then y else error "checkNodeValid: invalid tree in T2 case"

-- Everything less than the key goes to the left tree.
-- Everything greater than the key goes into the right
-- tree. The possible matching value goes into the Maybe.
-- Also, the current implemntation is pretty good but leaves
-- a little bit on the table. To improve it, we could:
--
-- 1. Use a variant of link that accepts a middle key
-- 2. Ensure that we link trees of similar size. Currently,
--    we start with the largest and link our way down to
--    the smallest. We could invert this by either foregoing
--    tail recursion or by building up lists on each side
--    instead and folding over them at the end. Linking trees
--    whose size differ by at most a constant is O(1),
--    so we would end up doing O(logn) work instead of O(logn * logn)
--    work, I think.
splitTreeAt :: forall a. Ord a => a -> Tree a -> (Tree a, Maybe a, Tree a)
splitTreeAt a (Tree x) = go x empty empty where
  go :: forall (n :: Nat).
       T n a
    -> Tree a -- accumulated tree left of split
    -> Tree a -- accumulated tree right of split
    -> (Tree a, Maybe a, Tree a)
  go LF accLeft accRight = (accLeft,Nothing,accRight)
  go (BR (T1 treeLeft valMid treeRight)) accLeft accRight =
    case compare valMid a of -- descend rightward when middle less than needle
      LT -> go treeRight (link accLeft (link (Tree treeLeft) (singletonTree valMid))) accRight
      EQ -> (link accLeft (Tree treeLeft), Just valMid, link (Tree treeRight) accRight)
      GT -> go treeLeft accLeft (link (link (singletonTree valMid) (Tree treeRight)) accRight)
  go (BR (T2 treeLeft valLeft treeMid valRight treeRight)) accLeft accRight =
    case compare valRight a of
      LT -> go treeRight (link accLeft (link (Tree (t1 treeLeft valLeft treeMid)) (singletonTree valRight))) accRight
      EQ -> (link accLeft (Tree (t1 treeLeft valLeft treeMid)), Just valRight, link (Tree treeRight) accRight)
      GT -> case compare valLeft a of -- the in-between case is interesting
        LT -> go treeMid
          (link accLeft (link (Tree treeLeft) (singletonTree valLeft))) 
          (link (link (singletonTree valRight) (Tree treeRight)) accRight)
        EQ -> (link accLeft (Tree treeLeft), Just valLeft, link (Tree (t1 treeMid valRight treeRight)) accRight)
        GT -> go treeLeft accLeft (link (link (singletonTree valLeft) (Tree (t1 treeMid valRight treeRight))) accRight)

link :: Tree a -> Tree a -> Tree a
link (Tree n) (Tree m) = case compareTreeHeight n m of
  Left ngtem -> case linkLeft ngtem n m of
    Left r -> Tree r
    Right (tiLeft,valMid,tiRight) -> Tree (t1 tiLeft valMid tiRight)
  Right mgten -> case linkRight mgten n m of
    Left r -> Tree r
    Right (tiLeft,valMid,tiRight) -> Tree (t1 tiLeft valMid tiRight)

linkLeft :: forall n m a. Gte n m -> T n a -> T m a -> Either (T n a) (T n a, a, T n a)
linkLeft gt n m = caseGte
  gt
  (linkLevel n m)
  f
  where
  f :: forall (p :: Nat). ('S p ~ n) => Gte p m -> Either (T n a) (T n a, a, T n a)
  f gte = case n of
    BR t -> case t of
      T1 ti1 v1 ti2 -> case linkLeft gte ti2 m of
        Left tiNew -> Left (t1 ti1 v1 tiNew)
        Right (tiLeft,valMid,tiRight) -> Left (t2 ti1 v1 tiLeft valMid tiRight)
      T2 ti1 v1 ti2 v2 ti3 -> case linkLeft gte ti3 m of
        Left tiNew -> Left (t2 ti1 v1 ti2 v2 tiNew)
        Right (tiLeft,valMid,tiRight) -> Right (t1 ti1 v1 ti2, v2, t1 tiLeft valMid tiRight)


linkRight :: forall n m a. Gte m n -> T n a -> T m a -> Either (T m a) (T m a, a, T m a)
linkRight gt n m = caseGte
  gt
  (linkLevel n m)
  f
  where
  f :: forall (p :: Nat). ('S p ~ m) => Gte p n -> Either (T m a) (T m a, a, T m a)
  f gte = case m of
    BR t -> case t of
      T1 ti1 v1 ti2 -> case linkRight gte n ti1 of
        Left tiNew -> Left (t1 tiNew v1 ti2)
        Right (tiLeft,valMid,tiRight) -> Left (t2 tiLeft valMid tiRight v1 ti2)
      T2 ti1 v1 ti2 v2 ti3 -> case linkRight gte n ti1 of
        Left tiNew -> Left (t2 tiNew v1 ti2 v2 ti3)
        Right (tiLeft,valMid,tiRight) -> Right (t1 tiLeft valMid tiRight, v1, t1 ti2 v2 ti3)

-- This implementation could be CPSed instead. It would probably
-- look cleaner.
linkLevel :: T n a -> T n a -> Either (T n a) (T n a, a, T n a)
linkLevel LF LF = Left LF
linkLevel (BR n1) (BR n2) = case n1 of
  T1 ti1 v1 ti2 -> case n2 of
    T1 ti3 v2 ti4 -> case linkLevel ti2 ti3 of
      Left tNew -> Left (t2 ti1 v1 tNew v2 ti4)
      Right (tLeft,vMid,tRight) -> Right (t1 ti1 v1 tLeft, vMid, t1 tRight v2 ti4)
    T2 ti3 v2 ti4 v3 ti5 -> case linkLevel ti2 ti3 of
      Right (tLeft,vMid,tRight) ->
        Right (t2 ti1 v1 tLeft vMid tRight, v2, t1 ti4 v3 ti5)
      Left tNew ->
        Right (t1 ti1 v1 tNew, v2, t1 ti4 v3 ti5)
  T2 ti1 v1 ti2 v2 ti3 -> case n2 of
    T2 ti4 v3 ti5 v4 ti6 -> case linkLevel ti3 ti4 of
      Left tNew -> Right (t2 ti1 v1 ti2 v2 tNew, v3, t1 ti5 v4 ti6)
      Right (tLeft,vMid,tRight) -> Right (t2 ti1 v1 ti2 v2 tLeft, vMid, t2 tRight v3 ti5 v4 ti6)
    T1 ti4 v3 ti5 -> case linkLevel ti3 ti4 of
      Left tNew ->
        Right (t1 ti1 v1 ti2, v2, t1 tNew v3 ti5)
      Right (tLeft,vMid,tRight) ->
        Right (t2 ti1 v1 ti2 v2 tLeft, vMid, t1 tRight v3 ti5)

insertTree :: forall a. Ord a => a -> Tree a -> Tree a
insertTree x (Tree tree) = ins tree Tree (\a b c -> Tree (t1 a b c))
  where
    ins :: forall n t. T n a -> Keep t n a -> Push t n a -> t
    ins LF = \_ push -> push LF x LF

    ins (BR n) = i n
      where
        i :: forall p m. ('S p ~ m) => N p a -> Keep t m a -> Push t m a -> t
        i (T2 a b c d e) keep push = select2 x b d xltb xeqb xbtw xeqd xgtd
          where
            xltb = ins a (\k -> keep (t2 k b c d e)) (\p q r -> push (t1 p q r) b (t1 c d e))
            xbtw = ins c (\k -> keep (t2 a b k d e)) (\p q r -> push (t1 a b p) q (t1 r d e))
            xgtd = ins e (\k -> keep (t2 a b c d k)) (\p q r -> push (t1 a b c) d (t1 p q r))
            xeqb = keep (t2 a x c d e)
            xeqd = keep (t2 a b c x e)

        i (T1 a b c) keep _ = select1 x b xltb xeqb xgtb
          where
            xltb = ins a (\k -> keep (t1 k b c)) (\p q r -> keep (t2 p q r b c))
            xgtb = ins c (\k -> keep (t1 a b k)) (\p q r -> keep (t2 a b p q r))
            xeqb = keep (t1 a x c)

singletonTree :: a -> Tree a
singletonTree a = Tree (t1 LF a LF)

singleton :: a -> Vicinity a
singleton a = Vicinity (singletonTree a)

empty :: Tree a
empty = Tree LF

instance Foldable Tree where
  foldMap = foldm
    where
      foldm :: forall m a. Monoid m => (a -> m) -> Tree a -> m
      foldm f (Tree t) = fm t
        where
          fm :: forall n. T n a -> m
          fm (BR (T1 a b c)) = fm a <> f b <> fm c
          fm (BR (T2 a b c d e)) = fm a <> f b <> fm c <> f d <> fm e
          fm LF = mempty


