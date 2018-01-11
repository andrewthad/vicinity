{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns #-}

import Data.Vicinity (Vicinity)
import Data.Foldable
import Data.Functor.Identity
import Data.Proxy
import Data.Semigroup (Semigroup (..))
import Test.QuickCheck
import Control.Monad
import Data.Monoid
import Numeric.Natural (Natural)
import Test.QuickCheck.Classes as QC
import qualified Data.Vicinity as VC
import qualified Data.Map.Strict as M

main :: IO ()
main = props

props :: IO ()
props = do
  lawsCheckMany allPropsApplied
  putStrLn "Split-Link Identity"
  quickCheck $ \(v :: Vicinity Integer (Sum Integer)) (i :: Integer) -> case VC.splitLookup i v of
    (x,m,y) -> case m of
      Just c -> VC.uncheckedConcat x (VC.uncheckedConcat (VC.singleton i c) y) == v
      Nothing -> VC.uncheckedConcat x y == v
  putStrLn "Insert-Fold Identity"
  quickCheck $ \(v :: Vicinity Integer (Sum Integer)) ->
    VC.foldrWithKey VC.insert mempty v == v
  putStrLn "fromList agrees with Data.Map"
  quickCheck $ \(xs :: [(Word,Sum Word)]) ->
    let expectation = M.toList (M.fromListWith mappend xs)
        actual = VC.toList (VC.fromList xs)
     in expectation == actual

instance (Ord k, Arbitrary k, Arbitrary v, Monoid v) => Arbitrary (Vicinity k v) where
  arbitrary = do
    (i :: [(k,v)]) <- arbitrary
    pure (VC.fromList i)
  shrink s = map VC.fromList (shrink (VC.toList s))

typeclassProps :: (Ord a, Eq a, Monoid a, Show a, Arbitrary a) => Proxy a -> [Laws]
typeclassProps p =
  [ QC.eqLaws p
  , QC.ordLaws p
  , QC.commutativeMonoidLaws p 
  ]

allPropsApplied :: [(String,[Laws])]
allPropsApplied =
  [ ("Vicinity",typeclassProps (Proxy :: Proxy (Vicinity Word (Sum Word))))
  ]
