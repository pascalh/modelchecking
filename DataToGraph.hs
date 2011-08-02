module DataToGraph(dataToGraph) where
import Data.Graph.Inductive
import Data.Tree
import Data.Data
import Data.Generics.Aliases

dataToGraph :: Data a => a -> Gr String ()
dataToGraph = treeToGraph . dataToTree

treeToGraph :: Tree a -> Gr a () 
treeToGraph t = let n = head $ newNodes 1 (empty::Gr a ()) in
  toCG n t $ insNode (n,rootLabel t) empty 

toCG :: Int -> Tree a -> Gr a () -> Gr a ()
toCG j (Node _ cs) g = 
  foldr (\(c,i) -> toCG i c . insEdge (j,i,()) . insNode (i,rootLabel c)) g $
    zip cs $ newNodes (length cs) g 

test = treeToGraph $ 
  Node "root" [Node "inner1" [Node "leaf1" []]
              ,Node "inner2" [Node "leaf2" []]]

dataToTree :: Data a => a -> Tree String 
dataToTree t = Node (showConstr (toConstr t)) (gmapQ dataToTree t) 

