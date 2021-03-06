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
    -- * Query
  , query
  , total
  , lookup
  , splitLookup
    -- * Construct
  , singleton
  , insert
  , union
  , fromList
    -- * Deconstruct
  , foldrWithKey
  , keys
  , toList
    -- * Unsafe
  , uncheckedConcat
    -- * Example
    -- $example
  ) where

import Prelude hiding (lookup)
import Control.Applicative (Applicative(..),(<$>),(<*>))
import Data.Monoid
import Data.Foldable (Foldable)
import Data.Traversable (Traversable(..))
import Data.Kind
import Data.Semigroup (Semigroup)
import Data.Nat (Nat(..))
import Data.Nat.Arithmetic (SNat,Gte,caseGte,natDiff,succSNat,zeroSNat)
import qualified Data.Semigroup
import qualified Data.Foldable as F

-- | A map-like container optimized for the execution of range queries.
--   The key must have an 'Ord' instance and the value must have 'Monoid'
--   instance whose append operation is also commutative.
newtype Vicinity k v = Vicinity (Tree k v)

instance (Show k, Show v) => Show (Vicinity k v) where
  show a = "fromList " ++ show (toList a)

instance (Eq k, Eq v) => Eq (Vicinity k v) where
  a == b = toList a == toList b

instance (Ord k, Ord v) => Ord (Vicinity k v) where
  compare a b = compare (toList a) (toList b)

instance (Ord k, Monoid v) => Semigroup (Vicinity k v) where
  (<>) = union

-- the value constraint should technically be weakened to Semigroup
instance (Ord k, Monoid v) => Monoid (Vicinity k v) where
  mempty = Vicinity empty
  mappend = union

instance Foldable (Vicinity k) where
  foldMap f (Vicinity t) = foldMap f t

-- | O(1). The monoidal concatenation of all values in the map. This
--   is equivalent to @'query' 'Nothing' 'Nothing'@.
total :: Monoid v => Vicinity k v -> v
total (Vicinity (Tree t)) = totalInternal t

totalInternal :: Monoid v => T n k v -> v
totalInternal LF = mempty
totalInternal (BR _ _ v _) = v

lookup :: (Ord k, Monoid v) => k -> Vicinity k v -> v
lookup x (Vicinity (Tree tree)) = lookupInternal x tree

lookupInternal :: forall n k v. (Ord k, Monoid v) => k -> T n k v -> v
lookupInternal x tree = mem tree where
  mem :: forall m. T m k v -> v
  mem (BR _ _ _ (T1 a b v c)) = select1 x b (mem a) v (mem c)
  mem (BR _ _ _ (T2 a b v1 c d v2 e)) = select2 x b d (mem a) v1 (mem c) v2 (mem e)
  mem LF = mempty

-- | Get the monoidal concatenation of all values in the range. The bounds
--   are both inclusive. Either bound can be omitted.
query :: (Ord k, Monoid v)
  => Maybe k -- ^ Lower bound
  -> Maybe k -- ^ Upper bound
  -> Vicinity k v -- ^ Vicinity
  -> v
query lo hi (Vicinity (Tree t)) = queryInternal lo hi t

queryInternal :: (Ord k, Monoid v) => Maybe k -> Maybe k -> T n k v -> v
queryInternal Nothing Nothing t = totalInternal t
queryInternal Nothing (Just hi) t = queryUpTo hi t
queryInternal (Just lo) Nothing t = queryDownTo lo t
queryInternal (Just lo) (Just hi) t = case compare lo hi of
  GT -> mempty
  EQ -> lookupInternal lo t
  LT -> queryBounds lo hi t

-- both a low bound and a high bound are given
queryBounds :: (Ord k, Monoid v) => k -> k -> T n k v -> v
queryBounds _ _ LF = mempty
queryBounds loBound hiBound br@(BR loChild hiChild v t) = if loBound <= loChild
  then if hiBound >= hiChild
    then v
    else queryUpTo hiBound br
  else if hiBound >= hiChild
    then queryDownTo loBound br
    else case t of
      T1 tiLeft keyMid valMid tiRight -> case compare hiBound keyMid of
        LT -> queryBounds loBound hiBound tiLeft
        EQ -> mappend (queryDownTo loBound tiLeft) valMid
        GT -> case compare loBound keyMid of
          LT -> mappend (queryDownTo loBound tiLeft) (mappend valMid (queryUpTo hiBound tiRight))
          EQ -> mappend (queryUpTo hiBound tiRight) valMid
          GT -> queryBounds loBound hiBound tiRight
      T2 tiLeft keyLeft valLeft tiMid keyRight valRight tiRight -> case compare hiBound keyLeft of
        LT -> queryBounds loBound hiBound tiLeft
        EQ -> mappend (queryDownTo loBound tiLeft) valLeft
        GT -> case compare hiBound keyRight of
          LT -> case compare loBound keyLeft of
            LT -> mappend (queryDownTo loBound tiLeft) (mappend valLeft (queryUpTo hiBound tiMid))
            EQ -> mappend valLeft (queryUpTo hiBound tiMid)
            GT -> queryBounds loBound hiBound tiMid
          EQ -> case compare loBound keyLeft of
            LT -> mappend (queryDownTo loBound tiLeft) (mappend valLeft (mappend (totalInternal tiMid) valRight))
            EQ -> mappend valLeft (mappend (totalInternal tiMid) valRight)
            GT -> mappend (queryDownTo loBound tiMid) valRight
          GT -> case compare loBound keyLeft of
            LT -> mappend (queryDownTo loBound tiLeft) (mappend valLeft (mappend (totalInternal tiMid) (mappend valRight (queryUpTo hiBound tiRight))))
            EQ -> mappend valLeft (mappend (totalInternal tiMid) (mappend valRight (queryUpTo hiBound tiRight)))
            GT -> case compare loBound keyRight of
              LT -> mappend (queryDownTo loBound tiMid) (mappend valRight (queryUpTo hiBound tiRight))
              EQ -> mappend valRight (queryUpTo hiBound tiRight)
              GT -> queryBounds loBound hiBound tiRight

queryDownTo :: (Ord k, Monoid v) => k -> T n k v -> v
queryDownTo _ LF = mempty
queryDownTo loBound (BR loChild _ v t) = if loBound <= loChild
  then v
  else case t of
    T1 tiLeft keyMid valMid tiRight -> case compare loBound keyMid of
      LT -> mappend (queryDownTo loBound tiLeft) (mappend valMid (totalInternal tiRight))
      EQ -> mappend valMid (totalInternal tiRight)
      GT -> queryDownTo loBound tiRight
    T2 tiLeft keyLeft valLeft tiMid keyRight valRight tiRight -> case compare loBound keyLeft of
      LT -> mappend (queryDownTo loBound tiLeft) (mappend valLeft (mappend (totalInternal tiMid) (mappend valRight (totalInternal tiRight))))
      EQ -> mappend valLeft (mappend (totalInternal tiMid) (mappend valRight (totalInternal tiRight)))
      GT -> case compare loBound keyRight of
        LT -> mappend (queryDownTo loBound tiMid) (mappend valRight (totalInternal tiRight))
        EQ -> mappend valRight (totalInternal tiRight)
        GT -> queryDownTo loBound tiRight

queryUpTo :: (Ord k, Monoid v) => k -> T n k v -> v
queryUpTo _ LF = mempty
queryUpTo hiBound (BR _ hiChild v t) = if hiBound >= hiChild
  then v
  else case t of
    T1 tiLeft keyMid valMid tiRight -> case compare hiBound keyMid of
      LT -> queryUpTo hiBound tiLeft
      EQ -> mappend (totalInternal tiLeft) valMid
      GT -> mappend (totalInternal tiLeft) (mappend valMid (queryUpTo hiBound tiRight))
    T2 tiLeft keyLeft valLeft tiMid keyRight valRight tiRight -> case compare hiBound keyLeft of
      LT -> queryUpTo hiBound tiLeft
      EQ -> mappend (totalInternal tiLeft) valLeft
      GT -> case compare hiBound keyRight of
        LT -> mappend (totalInternal tiLeft) (mappend valLeft (totalInternal tiMid))
        EQ -> mappend (totalInternal tiLeft) (mappend valLeft (mappend (totalInternal tiMid) valRight))
        GT -> mappend (totalInternal tiLeft) (mappend valLeft (mappend (totalInternal tiMid) (mappend valRight (queryUpTo hiBound tiRight))))
        
-- | Fold over the keys in the map along with their values.
foldrWithKey :: (k -> v -> a -> a) -> a -> Vicinity k v -> a
foldrWithKey f a (Vicinity (Tree x)) = foldrWithKeyInternal f a x

-- | Get the keys of the map.
keys :: Vicinity k v -> [k]
keys = foldrWithKey (\k _ ks -> k : ks) []

foldrWithKeyInternal :: (k -> v -> a -> a) -> a -> T n k v -> a
foldrWithKeyInternal _ a LF = a
foldrWithKeyInternal f a (BR _ _ _ (T1 x k v y)) = foldrWithKeyInternal f (f k v (foldrWithKeyInternal f a y)) x
foldrWithKeyInternal f a (BR _ _ _ (T2 x k1 v1 y k2 v2 z)) = 
  foldrWithKeyInternal f (f k1 v1 (foldrWithKeyInternal f (f k2 v2 (foldrWithKeyInternal f a z)) y)) x

-- | Convert the map to a list of key-value pairs.
toList :: Vicinity k v -> [(k,v)]
toList = foldrWithKey (\k v a -> (k,v) : a) []

-- | Build a map from a list of key-value pairs.
fromList :: (Ord k, Monoid v) => [(k,v)] -> Vicinity k v
fromList = foldr (\(k,v) -> insert k v) (Vicinity empty)

-- | Insert a key associated with a value into the map. If the key
--   already exists, the existing value and the new value are combined
--   using the 'Monoid' instance for @v@. The implementation of 'mappend'
--   is expected to be commutative, so the order in which the old and
--   new values are combined is not specified.
insert :: (Ord k, Monoid v) => k -> v -> Vicinity k v -> Vicinity k v
insert k v (Vicinity t) = Vicinity (insertTree k v t)

select1 :: Ord a => a -> a -> p -> p -> p -> p
select1 x y lt eq gt
  = case compare x y of { LT -> lt; EQ -> eq; GT -> gt }

select2 :: Ord a => a -> a -> a -> p -> p -> p -> p -> p -> p
select2 x y z xlty xeqy xbtw xeqz xgtz
  = select1 x y xlty xeqy (select1 x z xbtw xeqz xgtz)

t1 :: Monoid v => T n k v -> k -> v -> T n k v -> T ('S n) k v
t1 a bk bv c = case a of
  LF -> BR bk bk bv node
  BR farLeft _ aggA _ -> case c of
    BR _ farRight aggC _ -> BR farLeft farRight (mappend aggA (mappend bv aggC)) node
  where
  node = T1 a bk bv c

t2 :: Monoid v => T n k v -> k -> v -> T n k v -> k -> v -> T n k v -> T ('S n) k v
t2 a bk bv c dk dv e = case a of
  LF -> BR bk dk (mappend bv dv) node
  BR farLeft _ aggA _ -> case c of
    BR _ _ aggC _ -> case e of
      BR _ farRight aggE _ -> BR farLeft farRight (mappend aggA (mappend bv (mappend aggC (mappend dv aggE)))) node
  where
  node = T2 a bk bv c dk dv e

data N n k v
  = T1 (T n k v) k v (T n k v)
  | T2 (T n k v) k v (T n k v) k v (T n k v)
  deriving (Show)

data T n k v where
  BR :: k -- recursively left child
     -> k -- recursively right child
     -> v -- concatenation of self and all child values
     -> N n k v
     -> T ('S n) k v
  LF :: T 'Z k v

-- This exists for debugging purposes
instance (Show k, Show v) => Show (T n k v) where
  showsPrec _ LF = showString "LF"
  showsPrec d (BR _ _ v n) = showParen (d > 10)
    $ showString "BR "
    . showsPrec 11 v
    . showChar ' '
    . showsPrec 11 n

data Tree k v where
  Tree :: T n k v -> Tree k v

-- Exists for debugging purposes
instance (Show k, Show v) => Show (Tree k v) where
  showsPrec d (Tree x) = showsPrec d x

type Keep t n k v = T n k v -> t
type Push t n k v = T n k v -> k -> v -> T n k v -> t

treeToHeight :: T n k v -> SNat n 
treeToHeight LF = zeroSNat
treeToHeight (BR _ _ _ n) = case n of
  T1 t _ _ _ -> succSNat (treeToHeight t)
  T2 t _ _ _ _ _ _ -> succSNat (treeToHeight t)

compareTreeHeight :: T n k v -> T m k v -> Either (Gte n m) (Gte m n)
compareTreeHeight a b = natDiff (treeToHeight a) (treeToHeight b)

-- | Combine two maps. If the same key exists in both maps, the values
--   associated with it are combined using the 'Monoid' instance for @v@.
--   Note that the 'Monoid' instance of 'Vicinity' defines 'mappend' as
--   'union'.
union :: (Ord k, Monoid v) => Vicinity k v -> Vicinity k v -> Vicinity k v
union (Vicinity a) (Vicinity b) = Vicinity (unionTree a b)

-- we might actually be able to use the left-recursive and
-- right-recursive child information to decide to terminate
-- early
unionTree :: (Ord k, Monoid v) => Tree k v -> Tree k v -> Tree k v
unionTree a (Tree LF) = a
unionTree a (Tree (BR _ _ _ (T1 LF k v LF))) = insertTree k v a
unionTree (Tree (BR _ _ _ (T1 LF k v LF))) b = insertTree k v b
unionTree (Tree at) b@(Tree (BR _ _ _ _)) = case at of
  LF -> b
  BR _ _ _ an -> 
    let (aLeft,aRight,aKey) = splitNearMedian an
        (bLeft,mbVal,bRight) = splitTreeAt aKey b
        -- The weird insert in the right argument to link is
        -- a poorly performing way to make sure the middle
        -- value doesn't get discarded.
     in link (unionTree aLeft bLeft) (unionTree (maybe aRight (\bVal -> insertTree aKey bVal aRight) mbVal) bRight)

-- Performance-wise, this may be able to be improved by
-- a small constant amount. Also, this could actually work
-- just fine on trees of height zero, but I wrote it to
-- not accept them so that the union function would
-- have to handle the base case correctly instead of
-- blindly recursing forever. Actually, nevermind,
-- this would not work on trees of height zero since
-- it could not return the key.
--
-- The returned triple includes the approximate median
-- but does not strip it out. The median goes in the
-- right tree. Changing this could lead to a small
-- performance improvement if linkWithKey were implemented.
splitNearMedian :: Monoid v => N n k v -> (Tree k v,Tree k v,k)
splitNearMedian n = case n of
  T2 treeLeft keyLeft valLeft treeMid keyRight valRight treeRight ->
    (Tree (t1 treeLeft keyLeft valLeft treeMid), link (singletonTree keyRight valRight) (Tree treeRight), keyRight)
  T1 treeLeft keyMid valMid treeRight ->
    (Tree treeLeft, link (singletonTree keyMid valMid) (Tree treeRight), keyMid)

-- | Split the map at the target key. The map that is the first element of the tuple
--   has keys lower than the target. The map that is the third element of the tuple
--   has keys higher than the target. The second element of the tuple is the value
--   at the key if the key was found.
splitLookup :: (Ord k, Monoid v) => k -> Vicinity k v -> (Vicinity k v, Maybe v, Vicinity k v)
splitLookup a (Vicinity t) = case splitTreeAt a t of
  (x,y,z) -> (Vicinity x, y, Vicinity z)

-- | Combine two vicinities. All keys is the first one must be
--   less than all keys in the second one.
uncheckedConcat :: Monoid v => Vicinity k v -> Vicinity k v -> Vicinity k v
uncheckedConcat (Vicinity a) (Vicinity b) = Vicinity (link a b)

_checkNodeValid :: Ord k => T n k v -> T n k v
_checkNodeValid LF = LF
_checkNodeValid y@(BR _ _ _ x) = case x of
  T1 treeLeft keyMid _ treeRight ->
    let c1 = case treeLeft of
          LF -> True
          BR _ _ _ (T1 _ a _ _) -> a < keyMid
          BR _ _ _ (T2 _ _ _ _ a _ _) -> a < keyMid
        c2 = case treeRight of
          LF -> True
          BR _ _ _ (T1 _ a _ _) -> a > keyMid
          BR _ _ _ (T2 _ a _ _ _ _ _) -> a > keyMid
     in if c1 && c2 then y else error "checkNodeValid: invalid tree in T1 case"
  T2 treeLeft keyLeft _ treeMid keyRight _ treeRight ->
    let c1 = case treeLeft of
          LF -> True
          BR _ _ _ (T1 _ a _ _) -> a < keyLeft
          BR _ _ _ (T2 _ _ _ _ a _ _) -> a < keyLeft
        c2 = case treeRight of
          LF -> True
          BR _ _ _ (T1 _ a _ _) -> a > keyRight
          BR _ _ _ (T2 _ a _ _ _ _ _) -> a > keyRight
        c3 = case treeMid of
          LF -> True
          BR _ _ _ (T1 _ a _ _) -> a > keyLeft && a < keyRight
          BR _ _ _ (T2 _ a _ _ b _ _) -> a > keyLeft && b < keyRight
     in if c1 && c2 && c3 && keyLeft < keyRight then y else error "checkNodeValid: invalid tree in T2 case"

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
splitTreeAt :: forall k v. (Ord k, Monoid v) => k -> Tree k v -> (Tree k v, Maybe v, Tree k v)
splitTreeAt a (Tree x) = go x empty empty where
  go :: forall (n :: Nat).
       T n k v
    -> Tree k v -- accumulated tree left of split
    -> Tree k v -- accumulated tree right of split
    -> (Tree k v, Maybe v, Tree k v)
  go LF accLeft accRight = (accLeft,Nothing,accRight)
  go (BR _ _ _ (T1 treeLeft keyMid valMid treeRight)) accLeft accRight =
    case compare keyMid a of -- descend rightward when middle less than needle
      LT -> go treeRight (link accLeft (link (Tree treeLeft) (singletonTree keyMid valMid))) accRight
      EQ -> (link accLeft (Tree treeLeft), Just valMid, link (Tree treeRight) accRight)
      GT -> go treeLeft accLeft (link (link (singletonTree keyMid valMid) (Tree treeRight)) accRight)
  go (BR _ _ _ (T2 treeLeft keyLeft valLeft treeMid keyRight valRight treeRight)) accLeft accRight =
    case compare keyRight a of
      LT -> go treeRight (link accLeft (link (Tree (t1 treeLeft keyLeft valLeft treeMid)) (singletonTree keyRight valRight))) accRight
      EQ -> (link accLeft (Tree (t1 treeLeft keyLeft valLeft treeMid)), Just valRight, link (Tree treeRight) accRight)
      GT -> case compare keyLeft a of -- the in-between case is interesting
        LT -> go treeMid
          (link accLeft (link (Tree treeLeft) (singletonTree keyLeft valLeft))) 
          (link (link (singletonTree keyRight valRight) (Tree treeRight)) accRight)
        EQ -> (link accLeft (Tree treeLeft), Just valLeft, link (Tree (t1 treeMid keyRight valRight treeRight)) accRight)
        GT -> go treeLeft accLeft (link (link (singletonTree keyLeft valLeft) (Tree (t1 treeMid keyRight valRight treeRight))) accRight)

link :: Monoid v => Tree k v -> Tree k v -> Tree k v
link (Tree n) (Tree m) = case compareTreeHeight n m of
  Left ngtem -> case linkLeft ngtem n m of
    Left r -> Tree r
    Right (tiLeft,keyMid,valMid,tiRight) -> Tree (t1 tiLeft keyMid valMid tiRight)
  Right mgten -> case linkRight mgten n m of
    Left r -> Tree r
    Right (tiLeft,keyMid,valMid,tiRight) -> Tree (t1 tiLeft keyMid valMid tiRight)

linkLeft :: forall n m k v. Monoid v => Gte n m -> T n k v -> T m k v -> Either (T n k v) (T n k v, k, v, T n k v)
linkLeft gt n m = caseGte
  gt
  (linkLevel n m)
  f
  where
  f :: forall (p :: Nat). ('S p ~ n) => Gte p m -> Either (T n k v) (T n k v, k, v, T n k v)
  f gte = case n of
    BR _ _ _ t -> case t of
      T1 ti1 k1 v1 ti2 -> case linkLeft gte ti2 m of
        Left tiNew -> Left (t1 ti1 k1 v1 tiNew)
        Right (tiLeft,keyMid,valMid,tiRight) -> Left (t2 ti1 k1 v1 tiLeft keyMid valMid tiRight)
      T2 ti1 k1 v1 ti2 k2 v2 ti3 -> case linkLeft gte ti3 m of
        Left tiNew -> Left (t2 ti1 k1 v1 ti2 k2 v2 tiNew)
        Right (tiLeft,keyMid,valMid,tiRight) -> Right (t1 ti1 k1 v1 ti2, k2, v2, t1 tiLeft keyMid valMid tiRight)


linkRight :: forall n m k v. Monoid v => Gte m n -> T n k v -> T m k v -> Either (T m k v) (T m k v, k, v, T m k v)
linkRight gt n m = caseGte
  gt
  (linkLevel n m)
  f
  where
  f :: forall (p :: Nat). ('S p ~ m) => Gte p n -> Either (T m k v) (T m k v, k, v, T m k v)
  f gte = case m of
    BR _ _ _ t -> case t of
      T1 ti1 k1 v1 ti2 -> case linkRight gte n ti1 of
        Left tiNew -> Left (t1 tiNew k1 v1 ti2)
        Right (tiLeft,keyMid,valMid,tiRight) -> Left (t2 tiLeft keyMid valMid tiRight k1 v1 ti2)
      T2 ti1 k1 v1 ti2 k2 v2 ti3 -> case linkRight gte n ti1 of
        Left tiNew -> Left (t2 tiNew k1 v1 ti2 k2 v2 ti3)
        Right (tiLeft,keyMid,valMid,tiRight) -> Right (t1 tiLeft keyMid valMid tiRight, k1, v1, t1 ti2 k2 v2 ti3)

-- This implementation could be CPSed instead. It would probably
-- look cleaner.
linkLevel :: Monoid v => T n k v -> T n k v -> Either (T n k v) (T n k v, k, v, T n k v)
linkLevel LF LF = Left LF
linkLevel (BR _ _ _ n1) (BR _ _ _ n2) = case n1 of
  T1 ti1 v1k v1v ti2 -> case n2 of
    T1 ti3 v2k v2v ti4 -> case linkLevel ti2 ti3 of
      Left tNew -> Left (t2 ti1 v1k v1v tNew v2k v2v ti4)
      Right (tLeft,kMid,vMid,tRight) -> Right (t1 ti1 v1k v1v tLeft, kMid,vMid, t1 tRight v2k v2v ti4)
    T2 ti3 v2k v2v ti4 v3k v3v ti5 -> case linkLevel ti2 ti3 of
      Right (tLeft,kMid,vMid,tRight) ->
        Right (t2 ti1 v1k v1v tLeft kMid vMid tRight, v2k, v2v, t1 ti4 v3k v3v ti5)
      Left tNew ->
        Right (t1 ti1 v1k v1v tNew, v2k, v2v, t1 ti4 v3k v3v ti5)
  T2 ti1 v1k v1v ti2 v2k v2v ti3 -> case n2 of
    T2 ti4 v3k v3v ti5 v4k v4v ti6 -> case linkLevel ti3 ti4 of
      Left tNew -> Right (t2 ti1 v1k v1v ti2 v2k v2v tNew, v3k, v3v, t1 ti5 v4k v4v ti6)
      Right (tLeft,kMid,vMid,tRight) -> Right (t2 ti1 v1k v1v ti2 v2k v2v tLeft, kMid,vMid, t2 tRight v3k v3v ti5 v4k v4v ti6)
    T1 ti4 v3k v3v ti5 -> case linkLevel ti3 ti4 of
      Left tNew ->
        Right (t1 ti1 v1k v1v ti2, v2k, v2v, t1 tNew v3k v3v ti5)
      Right (tLeft,kMid,vMid,tRight) ->
        Right (t2 ti1 v1k v1v ti2 v2k v2v tLeft, kMid,vMid, t1 tRight v3k v3v ti5)

insertTree :: forall k v. (Ord k, Monoid v) => k -> v -> Tree k v -> Tree k v
insertTree k v (Tree tree) = ins tree Tree (\a bk bv c -> Tree (t1 a bk bv c))
  where
    ins :: forall n t. T n k v -> Keep t n k v -> Push t n k v -> t
    ins LF = \_ push -> push LF k v LF
    ins (BR _ _ _ n) = i n
      where
        i :: forall p m. ('S p ~ m) => N p k v -> Keep t m k v -> Push t m k v -> t
        i (T2 a bk bv c dk dv e) keep push = select2 k bk dk xltb xeqb xbtw xeqd xgtd
          where
            xltb = ins a (\x -> keep (t2 x bk bv c dk dv e)) (\p qk qv r -> push (t1 p qk qv r) bk bv (t1 c dk dv e))
            xbtw = ins c (\x -> keep (t2 a bk bv x dk dv e)) (\p qk qv r -> push (t1 a bk bv p) qk qv (t1 r dk dv e))
            xgtd = ins e (\x -> keep (t2 a bk bv c dk dv x)) (\p qk qv r -> push (t1 a bk bv c) dk dv (t1 p qk qv r))
            xeqb = keep (t2 a k (mappend bv v) c dk dv e)
            xeqd = keep (t2 a bk bv c k (mappend v dv) e)

        i (T1 a bk bv c) keep _ = select1 k bk xltb xeqb xgtb
          where
            xltb = ins a (\x -> keep (t1 x bk bv c)) (\p qk qv r -> keep (t2 p qk qv r bk bv c))
            xgtb = ins c (\x -> keep (t1 a bk bv x)) (\p qk qv r -> keep (t2 a bk bv p qk qv r))
            xeqb = keep (t1 a k (mappend v bv) c)

singletonTree :: k -> v -> Tree k v
singletonTree k v = Tree (BR k k v (T1 LF k v LF))

-- | Create a map with a single key-value pair.
singleton :: k -> v -> Vicinity k v
singleton k v = Vicinity (singletonTree k v)

empty :: Tree k v
empty = Tree LF

instance Foldable (Tree k) where
  foldMap = foldm
    where
      foldm :: forall m v. Monoid m => (v -> m) -> Tree k v -> m
      foldm f (Tree t) = fm t
        where
          fm :: forall n. T n k v -> m
          fm (BR _ _ _ (T1 a _ bv c)) = fm a <> f bv <> fm c
          fm (BR _ _ _ (T2 a _ bv c _ dv e)) = fm a <> f bv <> fm c <> f dv <> fm e
          fm LF = mempty


{- $example
A 'Vicinity' performs lookups of a commutative monoid over a key range in optimal
time. Consider a collection of books in print that share a common set of properties:

>>> data Book = Book { title :: String, author :: String, year :: Int, cost :: Int }
>>> let b1 = Book "The Wings of Vanessa" "Diana Alexander" 1974 7
>>> let b2 = Book "Dweller and a Card" "Diana Alexander" 1977 4
>>> let b3 = Book "The Weeping Blight" "Diana Alexander" 1980 8
>>> let b4 = Book "The Northern Dog" "Thomas Brown" 1982 2
>>> let b5 = Book "Bridge and Blade" "Thomas Brown" 1988 3
>>> let b6 = Book "The Manor" "Bernice McNeilly" 1983 11
>>> let b7 = Book "Southern Pirate" "Donna Arnold" 1985 23
>>> let b8 = Book "Without the Mesa" "Donna Arnold" 1991 25
>>> let b9 = Book "The Hollywood Sky" "Preston Richey" 1975 10
>>> let books = [b1,b2,b3,b4,b5,b6,b7,b8,b9]

We would like to find the cheapest books published within various time ranges.
So, we must also define a price metric that has a commutative semigroup instance:

>>> data Price = Price { ptitle :: String, pcost :: Int } deriving (Show)
>>> appendPrice (Price t1 c1) (Price t2 c2) = case compare c1 c2 of {LT -> Price t1 c1; EQ -> Price (min t1 t2) c1; GT -> Price t2 c2}
>>> instance Semigroup Price where { (<>) = appendPrice }

What does the append operator do here? It chooses the information for the
value with the lower price. In the event of a tie (handled by the @EQ@ case),
it choose the lexographically lower title. Breaking the tie this way
ensures that append is commutative. However, we're still missing
a @Monoid@ instance. Notice that @Price@ cannot be made into a @Monoid@,
since there is no sensible and law-abiding @mempty@. We will
need to lift @Price@ to get a @Monoid@. We can do this with
@Data.Semigroup.Option@. Let\'s write a function to turn our
collection of books into @Option Price@:

>>> import Data.Semigroup (Option(..))
>>> toPrice (Book t _ _ c) = Option (Just (Price t c))
>>> :t toPrice
toPrice :: Book -> Option Price

Now, we can fold over the collection of books to build our index of
the cheapest book in each time range:

>>> let ixc = foldMap (\b -> singleton (year b) (toPrice b)) books
>>> :t ixc
ixc :: Vicinity Int (Option Price)
>>> query (Just 1977) (Just 1986) ixc
Option {getOption = Just (Price {ptitle = "The Northern Dog", pcost = 2})}

Cool. We could pick other commutative monoidal metrics as wells. We could
handle things like the set of authors that published during the time
range or the total number of books published during the time range. Or we
could just do them all at once using the monoid instance of a three-tuple:

>>> import Data.Set (Set)
>>> import qualified Data.Set as S
>>> type Metrics = (Option Price, Set String, Sum Int)
>>> printMetrics (a,b,c) = print a >> print b >> print c
>>> toMetrics b = (toPrice b, S.singleton (author b), Sum (1 :: Int))
>>> :t toMetrics
toMetrics :: Book -> (Option Price, Set String, Sum Int)
>>> let ixa = foldMap (\b -> singleton (year b) (toMetrics b)) books
>>> printMetrics (query (Just 1974) (Just 1989) ixa)
Option {getOption = Just (Price {ptitle = "The Northern Dog", pcost = 2})}
fromList ["Bernice McNeilly","Diana Alexander","Donna Arnold","Preston Richey","Thomas Brown"]
Sum {getSum = 8}
>>> printMetrics (query (Just 1982) (Just 1985) ixa)
Option {getOption = Just (Price {ptitle = "The Northern Dog", pcost = 2})}
fromList ["Bernice McNeilly","Donna Arnold","Thomas Brown"]
Sum {getSum = 3}

-}
