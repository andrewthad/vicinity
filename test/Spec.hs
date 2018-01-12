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
import Control.Exception (Exception,toException)
import Test.QuickCheck.Property (exception)
import Data.Bool (bool)
import Data.Map (Map)
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
  putStrLn "Element lookup"
  quickCheck propLookup
  putStrLn "Range Query"
  quickCheck propQuery

propLookup :: Property
propLookup = forAllShrink arbitrary shrink $ \(vic :: Vicinity Int (Sum Word)) -> do
  case mapM_ (\(k,v) -> bool (Left k) (Right ()) (VC.lookup k vic == v)) (VC.toList vic) of
    Left k -> do
      let msg = show vic ++ " mangles lookup of key " ++ show k
      property $ exception msg (toException PropLookupException)
    Right () -> property True

genMapAndInnerBounds :: Gen (Map Word Word, Word, Word)
genMapAndInnerBounds = do
  xs <- vector 20
  let m = M.fromList xs
  case M.lookupMin m of
    Nothing -> error "genMapAndInnerBounds: not possible"
    Just (theMin,_) -> case M.lookupMax m of
      Nothing -> error "genMapAndInnerBounds: not possible"
      Just (theMax,_) -> do
        a <- choose (theMin,theMax)
        b <- choose (theMin,theMax)
        let lo = min a b
        let hi = max a b
        return (m,lo,hi)

propQuery :: Property
propQuery = forAll genMapAndInnerBounds $ \(m,lo,hi) ->
  let (_,m1,x) = M.splitLookup lo m
      (y,m2,_) = M.splitLookup hi x
      extra1 = maybe M.empty (M.singleton lo) m1
      extra2 = maybe M.empty (M.singleton hi) m2
      submap = M.unionsWith (+) [y,extra1,extra2]
      Sum expected = foldMap Sum (M.elems submap)
      vic = M.foldrWithKey (\k v xs -> VC.insert k (Sum v) xs) mempty m
      Sum actual = VC.query (Just lo) (Just hi) vic
   in if expected == actual
        then property True
        else do
          let msg = unlines
                [ show m ++ " mangles range query for [" ++ show lo ++ "," ++ show hi ++ "]: expected " ++ show expected ++ ", actual: " ++ show actual
                , "Trimmed map: " ++ show submap
                ]
          property $ exception msg (toException PropQueryException)

data PropLookupException = PropLookupException
  deriving (Show,Eq)
instance Exception PropLookupException

data PropQueryException = PropQueryException
  deriving (Show,Eq)
instance Exception PropQueryException

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
