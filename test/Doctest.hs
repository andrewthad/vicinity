import Test.DocTest

main :: IO ()
main = doctest
  [ "-isrc-fast"
  , "-isrc"
  , "src/Data/Vicinity.hs"
  ]

