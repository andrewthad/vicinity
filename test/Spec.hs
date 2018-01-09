{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Data.Vicinity (Vicinity)
import Data.Foldable
import Data.Functor.Identity
import Data.Proxy
import Data.Semigroup (Semigroup (..))
import Test.QuickCheck
import Test.QuickCheck.Classes as QC
import qualified Data.Vicinity as VC

main :: IO ()
main = props

props :: IO ()
props = lawsCheckMany allPropsApplied

instance (Ord k, Arbitrary k) => Arbitrary (Vicinity k) where
  arbitrary = do
    (i :: [k]) <- arbitrary
    pure (VC.fromList i)
  shrink s = map VC.fromList (shrink (toList s))

typeclassProps :: (Ord a, Eq a, Monoid a, Show a, Arbitrary a) => Proxy a -> [Laws]
typeclassProps p =
  [ QC.eqLaws p
  , QC.ordLaws p
  , QC.commutativeMonoidLaws p 
  ]

allPropsApplied :: [(String,[Laws])]
allPropsApplied =
  [ ("Vicinity",typeclassProps (Proxy :: Proxy (Vicinity Integer)))
  ]
