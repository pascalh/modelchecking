module DataToGraph(dataToKripke) where
import Data.Tree
import Data.Data
import Data.Generics.Aliases
import Kripke 

dataToKripke :: (Data a,Kripke k) => a -> k String 
dataToKripke = treeToKripke . dataToTree

-- |transforms a tree into a kripke structure where every former tree leafs @l@
-- lies on a infinite path @(l,l,l,l)@. This is needed for the property
-- of a kripke structure that every state has a successor.
treeToKripke :: Kripke k => Tree l -> k l
treeToKripke t = 
  let s = 1 
      g = toKS s t $ addLabel s (rootLabel t) $ addInitState s empty
  in foldr (\l -> addRel l l) g $ leafs g

-- |transforms a tree into a kripke structure representing the tree
toKS :: Kripke k => Int -> Tree l -> k l -> k l
toKS j (Node _ cs) k =
  foldr (\(c,i) -> toKS i c . addRel j i . 
                   addStateWithLabel  i (rootLabel c)) 
        k $
        zip cs $ newNodes (length cs) k

-- |creates a tree labeled with constructor names
dataToTree :: Data a => a -> Tree String 
dataToTree t = Node (showConstr (toConstr t)) (gmapQ dataToTree t) 

