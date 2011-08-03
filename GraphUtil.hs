module GraphUtil where
import Data.Graph.Inductive
import Control.Arrow (first)
import Data.Maybe (mapMaybe,fromJust)

-- |removes a given node from graph, but forwards all edges from pres to succs
removeNode :: DynGraph gr => Node -> gr a () -> gr a ()
removeNode n g = delNode n $ 
  foldr (\(p,s) g -> insEdgeUnique (p,s,()) g) g 
    [(p,s) | p<- pre g n, s <- suc g n] 

-- |like insEdge, but does not insert multiple edges between two nodes
insEdgeUnique :: DynGraph gr => LEdge b -> gr a b -> gr a b
insEdgeUnique (u,v,l) g | elem v (suc g u) = g
                        | otherwise        = insEdge (u,v,l) g

-- |returns all node labels of a graph
nodeLabels :: Graph g => g a b -> [a]
nodeLabels g = mapMaybe (lab g) (nodes g) 
