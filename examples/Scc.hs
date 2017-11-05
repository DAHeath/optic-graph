import Data.Optic.Graph

example :: Graph Int Int Int
example = fromLists
  (zip [0..4] [0..4])
  [ (0, 3, 5)
  , (0, 2, 6)
  , (1, 0, 7)
  , (2, 1, 8)
  , (3, 4, 9)
  , (0, 0, 10)
  ]

test :: IO ()
test =
  let acs = iscc (\i1 i2 e -> putStrLn (show i1 ++ " " ++ show i2) >> return e)
                 (\i v -> print i >> return (v + 1)) example
  in do
    g' <- acs !! 2
    print g'
