import Data.Optic.Graph
import Control.Monad

test :: Graph Int Double String
test = fromLists
  [(0, "a"), (1, "b"), (2, "c")]
  [(0, 1, 1.7), (0, 2, 3.5), (1, 2, 2.1)]

thing =
  let f = itop (\_ _ -> print) (const print) test
  in maybe (print "blah") void f
