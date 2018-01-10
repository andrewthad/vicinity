{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Data.Nat.Arithmetic
  ( SNat
  , Gte
  , caseGte
  , natDiff
  , succSNat
  , zeroSNat
  ) where

import Data.Nat (Nat(..))
import Data.Type.Equality
import Data.Kind (Type)

zeroSNat :: SNat 'Z
zeroSNat = SZ

succSNat :: SNat n -> SNat ('S n)
succSNat = SS

caseGte :: forall (n :: Nat) (m :: Nat) a.
     Gte n m
  -> ((n ~ m) => a)
  -> (forall (p :: Nat). ('S p ~ n) => Gte p m -> a)
  -> a
caseGte GteEq a _ = a
caseGte (GteGt gt) _ f = f gt

data Gte :: Nat -> Nat -> Type where
  GteEq :: Gte n n 
  GteGt :: Gte n m -> Gte ('S n) m

data SNat :: Nat -> Type where
  SZ :: SNat 'Z
  SS :: SNat n -> SNat ('S n)

data Addition :: Nat -> Nat -> Nat -> Type where
  AdditionBase :: Addition 'Z n n
  AdditionStep :: Addition n ('S m) p -> Addition ('S n) m p

type family Plus (n :: Nat) (m :: Nat) :: Nat where
  Plus 'Z m = m
  Plus ('S n) m = 'S (Plus n m)

sucRightProof :: SNat n -> SNat m -> (Plus n ('S m) :~: 'S (Plus n m))
sucRightProof SZ _ = Refl
sucRightProof (SS n) m = case sucRightProof n m of
  Refl -> Refl

additionToProof :: SNat n -> SNat m -> Addition n m p -> (Plus n m :~: p)
additionToProof _ _ AdditionBase = Refl
additionToProof (SS np) m (AdditionStep a) = case additionToProof np (SS m) a of
  Refl -> case sucRightProof np m of
    Refl -> Refl

rightIdentity :: SNat n -> (Plus n 'Z :~: n)
rightIdentity SZ = Refl
rightIdentity (SS n) = case rightIdentity n of
  Refl -> Refl

makeGte :: SNat n -> SNat k -> Gte (Plus k n) n
makeGte _ SZ = GteEq
makeGte n (SS k) = GteGt (makeGte n k)

incAddition :: Addition n m p -> Addition ('S n) m ('S p)
incAddition AdditionBase = AdditionStep AdditionBase
incAddition (AdditionStep a) = AdditionStep (incAddition a)

decAddition :: SNat n -> SNat m -> Addition ('S n) m ('S p) -> Addition n m p
decAddition SZ _ (AdditionStep AdditionBase) = AdditionBase
decAddition (SS SZ) _ (AdditionStep (AdditionStep AdditionBase)) = AdditionStep AdditionBase
decAddition (SS (SS npp)) m (AdditionStep a) = AdditionStep (decAddition (SS npp) (SS m) a)

incAdditionSecond :: Addition n m p -> Addition n ('S m) ('S p)
incAdditionSecond AdditionBase = AdditionBase
incAdditionSecond (AdditionStep a) = AdditionStep (incAdditionSecond a)

tweakAddition :: SNat n -> SNat m -> Addition ('S n) m p -> Addition n ('S m) p
tweakAddition n m a = decAddition n (SS m) (incAdditionSecond a)

addZero :: SNat n -> Addition n 'Z n
addZero SZ = AdditionBase
addZero (SS np) = incAddition (addZero np)

flipAddition :: SNat n -> SNat m -> Addition n m p -> Addition m n p
flipAddition SZ m AdditionBase = addZero m
flipAddition (SS np) m (AdditionStep a) = tweakAddition m np (flipAddition np (SS m) a)

emptyAddition :: SNat n -> Addition n 'Z p -> (n :~: p)
emptyAddition n a = case additionToProof n SZ a of
  Refl -> case rightIdentity n of
    Refl -> Refl

natDiff :: forall (n :: Nat) (m :: Nat). SNat n -> SNat m -> Either (Gte n m) (Gte m n)
natDiff n m = go SZ n AdditionBase m AdditionBase
  where
  go :: forall acc n2 m2. SNat acc -> SNat n2 -> Addition acc n2 n -> SNat m2 -> Addition acc m2 m -> Either (Gte n m) (Gte m n)
  go acc (SS n2p) na (SS m2p) ma = go (SS acc) n2p (AdditionStep na) m2p (AdditionStep ma)
  go acc n2@(SS _) na SZ ma = case emptyAddition acc ma of
    Refl -> case flipAddition m n2 na of
      addFlipped -> case additionToProof n2 m addFlipped of
        Refl -> Left (makeGte m n2)
  go acc SZ na m2 ma = case emptyAddition acc na of
    Refl -> case flipAddition n m2 ma of
      addFlipped -> case additionToProof m2 n addFlipped of
        Refl -> Right (makeGte n m2)

