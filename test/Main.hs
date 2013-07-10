{-# LANGUAGE NoMonomorphismRestriction, DeriveDataTypeable #-}
module Main where

import Test.Framework (defaultMain, testGroup,TestName,Test)
import Test.Framework.Providers.HUnit(testCase)
import Test.Framework.Providers.QuickCheck2 (testProperty)
import Test.QuickCheck hiding (labels)
import Test.HUnit((@=?))

import ModelChecking.Kripke
  (Kripke(..),AdjList,KripkeIntMap,KripkeGr,KripkeState)
import ModelChecking.AstToKripke(AstToKripke(..),Label(..),termToTree)

import Control.Applicative((<$>),Applicative(..))
import Data.List(sort)
import Data.Tree(Tree(Node))
import Data.Set(fromList)

import Data.Data(Data)
import Data.Typeable(Typeable)

main = defaultMain [testSize,testRels,testLbls{-,testProps-}]--,testBetween]

-- * simple hunit tests

-- ** simple tests

-- *** test size of state set

testSize = testGroup "size of states" [sizeGrs,sizeMap,sizeAdj]

buildSizeTestgroup:: Kripke k => [(k Label,String,Expected)] -> String -> Test
buildSizeTestgroup ks name = testGroup name $ map f ks where
  f (k,i,(Expected size _ _)) = testCase i $ [1..size] @=? (sort $ states k)

sizeMap = buildSizeTestgroup krMap "IntMap"
sizeGrs = buildSizeTestgroup krGrs "Inductive graph" 
sizeAdj = buildSizeTestgroup krAdj "AdjList" 

-- *** test relations

testRels = testGroup "size of relation set" [relMap,relGrs,relAdj]

buildRelTestgroup ks name = testGroup name $ map f ks where
  f (k,i,(Expected _ r _)) = testCase i $ r @=? (length $ rels k)

relMap = buildRelTestgroup krMap "IntMap"
relGrs = buildRelTestgroup krGrs "Inductive graph" 
relAdj = buildRelTestgroup krAdj "AdjList" 


-- *** labeling function

testLbls = testGroup "labeling function" [lblGrs ,lblAdj,lblMap]

lblMap = buildLabelTestgroup krMap "IntMap"
lblGrs = buildLabelTestgroup krGrs "Inductive graph" 
lblAdj = buildLabelTestgroup krAdj "AdjList" 

buildLabelTestgroup ks name = testGroup name $ map f ks where
  f (k,i,(Expected _ _ ls)) = 
    testCase i $ sort ls @=? (sort $ concatMap (\s -> labels s k) $ states k)


-- ** test data

data Expected = Expected Int Int [Label] deriving Show

expectedValues :: [Expected]
expectedValues = expValues where

  expValues :: [Expected ]
  expValues = map (\i -> Expected (sizes !! i) (relations !! i) (labelss !! i)) 
                  [0,1..5]

  labelss :: [[Label]]
  labelss   = [[Constr "[]"]
              ,[Constr "Just",Constr "2"]
              ,[Constr "(,)", Constr "True",Constr "False"]
              ,[Constr "Just",Ident "yoo"]
              ,[Constr "(,,)",Ident "a",Ident "bc",Ident "de"]
              ,lbls5
              ]

  sizes     = map length labelss 
  relations = [0,1,2,1,3,8]

  lbls5 :: [Label]
  lbls5 = sort $ [Constr "Binary",Constr "Unary"
          ,Constr "Binary" ,Constr "Id",Constr "Unit",Ident "Q",Constr "Unary"
          ,Constr "Number"
          ,Constr "2" ]

t0 = []::[()]
t1 = Just $ (2::Int)
t2 = (True,False)
t3 = Just $ "yoo"
t4 = ("a","bc","de")
t5 = Binary (Unary (Unary (Number 2))) (Binary (Id "Q") Unit)

ks = [astToKripke t0
     ,astToKripke t1
     ,astToKripke t2
     ,astToKripke t3
     ,astToKripke t4
     ,astToKripke t5
     ]

ts = [show t0
     ,show t1
     ,show t2
     ,show t3
     ,show t4
     ,show t5
     ]

krAdj :: [(AdjList Label,String,Expected)]
krAdj = zip3 ks ts expectedValues

krGrs ::[(KripkeGr Label,String,Expected)]
krGrs = zip3 ks ts expectedValues


krMap ::[(KripkeIntMap Label,String,Expected)]
krMap  = zip3 ks ts expectedValues

-- * quickcheck

-- |a simple data type for testing purposes
data Term 
  = Unit
  | Unary Term 
  | Binary Term Term 
  | Nary [Term]
  | Id String
  | Number Int
  deriving (Show,Typeable,Data)

-- |transform a 'test' term to a tree 
testToTree :: Term -> Tree Label
testToTree Unit      = Node (Constr "Unit") []
testToTree (Unary t) = Node (Constr "Unary") [testToTree t]
testToTree (Binary t1 t2) = 
  Node (Constr "Binary") [testToTree t1,testToTree t2]
testToTree (Nary ts) = Node (Constr "Nary")  $ return $ 
  foldr (\t acc -> Node (Constr "(:)") [testToTree t,acc]) 
        (Node (Constr "[]") []) 
        ts
testToTree (Id s) = Node (Constr "Id") $  return $ Node (Ident s) []
testToTree (Number i) = 
  Node (Constr "Number") $ return $ Node (Constr (show i)) []

instance Arbitrary Term where
  arbitrary = arbSized 20 where
{-
  arbitrary = oneof 
   [ return Unit
   , Unary <$> arbitrary
   , Binary <$> arbitrary <*> arbitrary
   , Nary <$> listOf arbitrary 
   , Id <$> (listOf1 $ elements $ ['a'..'z']++['A'..'Z'])
   , Number <$> arbitrary
   ] where
  -}
   arbSized s = let s' = s `div` 2 in oneof
    [ return Unit
    , Unary <$> (arbSized (s-1))
    , Binary <$> arbSized s' <*> arbSized s'
    , choose (2,4) >>= \l -> Nary <$> vector l -- in den teillisten die anzahl beschränken
    , Id <$> (listOf1 $ elements $ ['a'..'z']++['A'..'Z'])
    , Number <$> arbitrary 
    ]
-- ** black box testing 'termToTree' against 'testToTree'

prop_tree_equal :: Term -> Bool
prop_tree_equal term = (testToTree term) == (termToTree [] term)

testProps = testGroup "Properties" [testTermToTree]

testTermToTree = testProperty "termToTree" prop_tree_equal

-- ** testing isomorphy between different kripke implementations

testBetween = testGroup "Properties between implementations" [testInit,testIso]

testIso = testGroup "Isomorphic kripke strucutes" 
                      [testProperty "adj <-> intmap" prop_iso_adj_map
                      ,testProperty "intmap <-> gr"  prop_iso_map_gr
                      ,testProperty "gr <-> adj"     prop_iso_gr_adj
                      ]

testInit = testProperty "initial state sets" prop_Init

toAdj :: Data t => t -> AdjList Label
toAdj = astToKripke

toGr :: Data t => t -> KripkeGr Label
toGr = astToKripke

toIntMap :: Data t => t -> KripkeIntMap Label
toIntMap = astToKripke

prop_Init :: Term -> Bool
prop_Init t = 
  let a = toAdj t
      i = toIntMap t
      g = toGr t
  in initial a i && initial i g && initial g a 

prop_iso_adj_map :: Term -> Bool
prop_iso_adj_map t = iso (toAdj t) (toIntMap t)

prop_iso_map_gr :: Term -> Bool
prop_iso_map_gr t = iso (toIntMap t) (toGr t)

prop_iso_gr_adj :: Term -> Bool
prop_iso_gr_adj t = iso (toGr t) (toAdj t)

-- ** desired properties of kripke structures

initial :: (Kripke k1,Kripke k2) => k1 Label -> k2 Label -> Bool
initial k1 k2 = sort(initStates k1) == (sort $ initStates k2) 

iso :: (Kripke k1, Kripke k2) => k1 Label -> k2 Label -> Bool
iso k1 k2 = and $ zipWith (\x1 x2 -> kripkeIso x1 k1 x2 k2) 
                               (initStates k1) 
                               (initStates k2) 

kripkeIso :: (Kripke k1,Kripke k2) 
  => KripkeState -> k1 Label -> KripkeState -> k2 Label -> Bool
kripkeIso s1 k1 s2 k2 = 
  let suc1 = sort $ suc k1 s1
      suc2 = sort $ suc k2 s2
  in (labels s1 k1) == (labels s2 k2) && 
     suc1 == suc2 &&
     and (zipWith (\x1 x2 -> kripkeIso x1 k1 x2 k2) suc1 suc2)
  
