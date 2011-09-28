module ModelChecking.AstToKripke
  (AstToKripke(..)
  ,ConstructorLabels(ConstructorLabels)
  ,Label(Ident,Constr)
  )
where
import Data.Tree (Tree(..))
import Data.Data (Data,gmapQ,showConstr,toConstr)
import ModelChecking.Kripke (Kripke(..),KripkeState,KripkeGr)
import Data.Maybe (mapMaybe)
import Data.Monoid (Monoid(..))
import Data.Foldable (fold)

-- |'AstToKripke' offers an interface to create kripke structures containing 
-- labels of type @a@ out ofsyntax trees.
--  The outcoming kripke structure
-- should represent the given abstract syntax tree, i.e.
-- the structure of the syntax tree should be preserved substantially. 
class AstToKripke a where
  -- |kripke structure construction function
  astToKripke :: (Data ast,Kripke k) => ast -> k a 

-- |Every constructor is represented by its name
newtype ConstructorLabels = ConstructorLabels String 

instance Show ConstructorLabels where
  show (ConstructorLabels s) = s

instance AstToKripke ConstructorLabels where
  astToKripke = treeToKripke . fmap ConstructorLabels . dataToTree 

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
  show (Constr s) = s
  show (Ident i)  = i

instance AstToKripke Label where
  astToKripke = treeToKripke . toLabel . dataToTree

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
isIdent c = c `elem` ['a'..'z']++['A'..'Z']++['1'..'9']++['0']

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

-- |returns all states without a successor. 'leafs' will return an empty
-- list for correct kripke structures. We need all leafs here, in order
-- to create a correct kripke structure.
leafs :: Kripke k => k l -> [KripkeState]
leafs k =
  mapMaybe (\s -> if null $ suc k s then Just s else Nothing) $ states k

