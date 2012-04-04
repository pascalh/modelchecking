{-# LANGUAGE PackageImports #-}
module ModelChecking.AstToKripke
  (AstToKripke(..)
  ,Label(Ident,Constr)
  ,fromLabel
  )
where
import Data.Tree (Tree(..))
import Data.Data (Data,gmapQ,showConstr,toConstr)
import ModelChecking.Kripke (Kripke(..)
                            ,KripkeDyn(..)
                            ,KripkeState,KripkeGr,AdjList(AdjList)
                            ,addLabel'
                            ,addInitState'
                            ,addRel'
                            ,addStateWithLabel'
                            )
import Data.Maybe (mapMaybe)
import Data.Monoid (Monoid(..))
import Data.Foldable (fold)
import "mtl" Control.Monad.State
import Data.Array(array)

-- |'AstToKripke' offers an interface to create kripke structures containing 
-- labels of type @l@ out ofsyntax trees.
--  The outcoming kripke structure
-- should represent the given abstract syntax tree, i.e.
-- the structure of the syntax tree should be preserved substantially. 
class Kripke k => AstToKripke k where
  -- |kripke structure construction function
  astToKripke :: Data ast => ast -> k Label 
  astToKripke = astToKripkeIgSubtr []

  -- |ignores all subtrees constructed by constructors whose
  -- names are an element of string list
  astToKripkeIgSubtr :: Data ast => [String] -> ast -> k Label

-- |distinguish constructor names and identifiers in the syntax tree, i.e.
-- constructors are represented by its name using 'Constr' and strings are
-- identified by 'Ident'.
data Label = Constr String -- ^ a constructors name
           | Ident  String -- ^ a identifier in syntax tree
           deriving Eq

instance Monoid Label where
  mempty = Ident []
  Ident i1 `mappend` Ident i2 = Ident $ i1++i2
  _        `mappend` Ident i  = Ident i
  Ident i  `mappend` _        = Ident i
  _        `mappend` _        = mempty

-- |returns the underlying string
fromLabel :: Label -> String
fromLabel (Constr l) = l
fromLabel (Ident  l) = l

instance Show Label where
  show (Constr s) = s
  show (Ident i)  = i

instance AstToKripke KripkeGr where
  astToKripkeIgSubtr cs = treeToKripke . toLabel . dataToTree cs

-- |folds degenerated lists of chars to a single string
-- > (Ident 'f': Ident'o':Ident'o':[]) ==> Ident "foo"
shrink :: Tree Label -> Tree Label
shrink n = Node (fold n) []

-- |builds a tree which distinguishes between identifiers and 
-- constructor names in abstract syntax tress
toLabel :: Tree String -> Tree Label
toLabel (Node ('\'':c:'\'':[]) cs)
  | isIdent c = Node (Ident [c]) (map toLabel cs)
toLabel (Node "(:)" cs) 
  | any isCharacter cs = shrink $ Node (Constr "(:)") (map toLabel cs)
  | otherwise          = Node (Constr "(:)") (map toLabel cs) 
toLabel (Node i cs) = Node (Constr i) (map toLabel cs)

-- |returns whether label of current tree represents a character
isCharacter :: Tree String -> Bool
isCharacter (Node ('\'':_:'\'':[]) _) = True
isCharacter _                         = False

-- |returns whether char represents an identifier
isIdent :: Char -> Bool
isIdent c = c `elem` ['a'..'z']++['A'..'Z']++['1'..'9']++['0']++[' ','_']

-- |transforms a tree into a kripke structure where every former tree leafs @l@
-- lies on a infinite path @(l,l,l,l)@. This is needed for the property
-- of a kripke structure that every state has a successor.
treeToKripke :: KripkeDyn k => Tree l -> k l
treeToKripke t = 
  let s = 1 
      g = toKS s t $ addLabel' s (rootLabel t) $ addInitState' s empty
  in foldr (\l -> addRel' l l) g $ leafs g

instance AstToKripke AdjList where
  astToKripkeIgSubtr cs = treeToAdj . toLabel . dataToTree cs

treeToAdj :: Tree Label -> AdjList Label
treeToAdj t@(Node lab _) = 
  let 
      iState    = AdjState [] [] [(z,lab)] [z+1,z+2..]
      (AdjState ps ss ls ms) = execState (toAdj z t) iState
      z         = 1
      s         = array (z,head ms-1) ss
      p         = array (z,head ms-1) $ (z,[]):ps
      l         = array (z,head ms-1) ls
  in AdjList p s l [z]

toAdj :: KripkeState -> Tree Label -> State AdjState ()
toAdj parent (Node _ cs) = do
  ns <- getNewNodes $ length cs
  addRelM parent ns
  foldM 
    (\_ (c,n)->do 
      addStateWithLabelM n (rootLabel c)
      toAdj n c
    )
    () 
    (zip cs ns)
  

data AdjState = AdjState 
  [(KripkeState,[KripkeState])] -- ^ predecessor
  [(KripkeState,[KripkeState])] -- ^ successor
  [(KripkeState, Label)]        -- ^ labeling relation
  [KripkeState]                 -- ^ new states

addStateWithLabelM :: KripkeState -> Label -> State AdjState ()
addStateWithLabelM s l = do
  (AdjState ps ss ls ns) <- get 
  put $ AdjState ps ss ((s,l):ls) ns

addRelM :: KripkeState -> [KripkeState] -> State AdjState ()
addRelM i xs = do
  (AdjState ps ss ls ns) <- get 
  let s = if null xs then (i,i:xs) else (i,xs)
  put $ AdjState ((map (\x->(x,return i)) xs)++ps) (s:ss) ls ns

getNewNodes :: Int -> State AdjState [KripkeState]
getNewNodes i = do
  (AdjState ps ss lbl ns) <- get
  let (xs,ys) = splitAt i ns
  put $ AdjState ps ss lbl ys
  return xs


-- |transforms a tree into a kripke structure representing the tree
toKS :: KripkeDyn k => Int -> Tree l -> k l -> k l
toKS j (Node _ cs) k =
  foldr (\(c,i) -> toKS i c . addRel' j i . 
                   addStateWithLabel'  i (rootLabel c)) 
        k $
        zip cs $ newNodes (length cs) k

-- |creates a tree labeled with constructor names
dataToTree :: Data a => [String] -> a -> Tree String 
dataToTree cs t = let c = showConstr $ toConstr t in
  if elem c cs then Node [] []
               else Node c (gmapQ (dataToTree cs) t) 

-- |returns all states without a successor. 'leafs' will return an empty
-- list for correct kripke structures. We need all leafs here, in order
-- to create a correct kripke structure.
leafs :: Kripke k => k l -> [KripkeState]
leafs k =
  mapMaybe (\s -> if null $ suc k s then Just s else Nothing) $ states k

