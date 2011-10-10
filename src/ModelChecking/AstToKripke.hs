{-# LANGUAGE PackageImports #-}
module ModelChecking.AstToKripke
  (AstToKripke(..)
  ,Label(Ident,Constr)
  )
where
import Data.Tree (Tree(..))
import Data.Data (Data,gmapQ,showConstr,toConstr)
import ModelChecking.Kripke (Kripke(..)
                            ,KripkeDyn(..)
                            ,KripkeState,KripkeGr,AdjList(AdjList))
import Data.Maybe (mapMaybe)
import Data.Monoid (Monoid(..))
import Data.Foldable (fold)
import Data.Array (Array,array)
import "mtl" Control.Monad.State

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

instance Show Label where
  show (Constr s) = "C|"++s
  show (Ident i)  = "I|"++i

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
      g = toKS s t $ addLabel s (rootLabel t) $ addInitState s empty
  in foldr (\l -> addRel l l) g $ leafs g

instance AstToKripke AdjList where
  astToKripkeIgSubtr cs = treeToAdj . toLabel . dataToTree cs

treeToAdj :: Tree Label -> AdjList Label
treeToAdj t@(Node lab cs) = 
  let 
      iState    = AdjState [] [(s,lab)] [s+1,s+2..]
      (AdjState as ls ms) = execState (toAdj s t) iState
      s         = 1
      a         = array (s,head ms-1) as
      l         = array (s,head ms-1) ls
  in AdjList a l [s]

toAdj :: KripkeState -> Tree Label -> State AdjState ()
toAdj parent (Node l cs) = do
  ns <- getNewNodes $ length cs
  addRelM parent ns
  foldM 
    (\_ (c,n)->do 
      addStateWithLabelM n (rootLabel c)
      if null cs then addRelM n [n] else return ()
      toAdj n c
    )
    () 
    (zip cs ns)
  

data AdjState = AdjState 
  { sAdj :: [(KripkeState,[KripkeState])]
  , sLbl :: [(KripkeState, Label)]
  , sNewNode :: [KripkeState]
  }

addStateWithLabelM :: KripkeState -> Label -> State AdjState ()
addStateWithLabelM s l = do
  (AdjState as ls ns) <- get 
  put $ AdjState as ((s,l):ls) ns

addRelM :: KripkeState -> [KripkeState] -> State AdjState ()
addRelM i xs = do
  (AdjState as ls ns) <- get 
  put $ AdjState ((i,xs):as) ls ns

getNewNode :: State AdjState KripkeState
getNewNode = do
  (AdjState adj lbl (n:ns)) <- get 
  put $ AdjState adj lbl ns
  return n

getNewNodes :: Int -> State AdjState [KripkeState]
getNewNodes i = do
  (AdjState adj lbl ns) <- get
  let (xs,ys) = splitAt i ns
  put $ AdjState adj lbl ys
  return xs


-- |transforms a tree into a kripke structure representing the tree
toKS :: KripkeDyn k => Int -> Tree l -> k l -> k l
toKS j (Node _ cs) k =
  foldr (\(c,i) -> toKS i c . addRel j i . 
                   addStateWithLabel  i (rootLabel c)) 
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

