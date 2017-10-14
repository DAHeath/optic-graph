# ord-graph

Directed graphs with ordered indices, vertex labels, and edge labels.

Here's a quick example in ghci:
```haskell
let g = fromLists [(0, "foo"), (1, "bar"), (2, "baz")]
                  [(0, 1, True), (1, 1, True), (1, 0 False)]
g ^@.. labEdgesFrom 1
  ==> [(0,False)],(1,True)]

let g' = mapEdges no g
g' ^@.. labEdgesFrom 1
  ==> [(0,True)],(1,False)]

let g'' = g' & allVerts . traverse %~ succ
void $ ibfs (\k1 k2 e -> print (k1, k2, e))
            (\k v -> print (k, v)) g''
  ==> (0,"gpp")
      (0,1,False)
      (1,"cbs")
      (1,0,True)
      (1,1,False)
      (2,"cb{")
```
