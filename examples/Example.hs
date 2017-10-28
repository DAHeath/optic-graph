import Data.Optic.Graph
import Control.Monad

test :: Graph Int Double String
test = fromLists
  [(0, "a"), (1, "b"), (2, "c")]
  [(0, 1, 1.7), (0, 2, 3.5), (1, 2, 2.1)]

thing =
  let f = itop (\_ _ -> print) (const print) test
  in maybe (print "blah") void f

t = fromLists [ ('a', 10)
              , ('b', 17)
              , ('c', 8)
              , ('d', 3)
              , ('e', 27)
              , ('f', 4)
              , ('g', 9)
              , ('i', 13)
              ]
              [ ('a', 'b', "this")
              , ('a', 'c', "is")
              , ('b', 'd', "so")
              , ('d', 'f', "neat")
              , ('d', 'g', "cool")
              , ('f', 'g', "swell")
              -- , ('b', 'e', "fun")
              , ('c', 'i', "whoa")
              ]
