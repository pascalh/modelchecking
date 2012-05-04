{-# LANGUAGE NoMonomorphismRestriction, DeriveDataTypeable #-}
module Main where

import Test.Framework (defaultMain, testGroup)
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

import Data.Data(Data)
import Data.Typeable(Typeable)

main = defaultMain [testSize,testRels,testLbls,testProps,testBetween]

-- * simple hunit tests

-- ** simple tests

-- *** test size of state set

testSize = testGroup "set size" [sizeGrs,sizeMap,sizeAdj]

buildSizeTestgroup ks name = testGroup name $ zipWith f ks sizes where
  f (k,i) s = testCase (name++":"++i) $ [1..s] @=? (sort $ states k)

sizeMap = buildSizeTestgroup krMap "IntMap"
sizeGrs = buildSizeTestgroup krGrs "Inductive graph" 
sizeAdj = buildSizeTestgroup krAdj "AdjList" 

-- *** test relations

testRels = testGroup "relation set" [relMap,relGrs,relAdj]

buildRelTestgroup ks name = testGroup name $ zipWith f ks relations where
  f (k,i) r = testCase (name++":"++i) $ r @=? (length $ rels k)

relMap = buildRelTestgroup krMap "IntMap"
relGrs = buildRelTestgroup krGrs "Inductive graph" 
relAdj = buildRelTestgroup krAdj "AdjList" 


-- *** labeling function

testLbls = testGroup "labeling function" [lblMap,lblGrs,lblAdj]

buildLabelTestgroup ks name = testGroup name $ zipWith f ks labelss where
  f (k,i) ls = 
    testCase (name++":"++i) $ (sort ls) @=? 
      (sort $ map (\s -> head $ labels s k) $ states k)

lblMap = buildLabelTestgroup krMap "IntMap"
lblGrs = buildLabelTestgroup krGrs "Inductive graph" 
lblAdj = buildLabelTestgroup krAdj "AdjList" 

-- ** test data
labelss   = [[Constr "[]"]
            ,[Constr "Just",Constr "2"]
            ,[Constr "True",Constr "False",Constr "(,)"]
            ,[Constr "Just",Ident "yoo"]
            ,[Constr "(,,)",Ident "a",Ident "bc",Ident "de"]
            ]
sizes     = [1,2,3,2,4]
relations = [0,1,2,1,3]

values = zip ks $ map show ts

t0 = []::[()]
t1 = Just $ (2::Int)
t2 = (True,False)
t3 = Just $ "yoo"
t4 = ("a","bc","de")

ks = [astToKripke t0
     ,astToKripke t1
     ,astToKripke t2
     ,astToKripke t3
     ,astToKripke t4
     ]

ts = [show t0
     ,show t1
     ,show t2
     ,show t3
     ,show t4
     ]
krAdj :: [(AdjList Label,String)]
krAdj = values

krGrs ::[(KripkeGr Label,String)]
krGrs = values


krMap ::[(KripkeIntMap Label,String)]
krMap = values 

-- * quickcheck

-- |a simple data type for testing purposes
data Test 
  = Unit
  | Unary Test
  | Binary Test Test
  | Nary [Test]
  | Id String
  | Number Int
  deriving (Show,Typeable,Data)

-- |transform a 'test' term to a tree 
testToTree :: Test -> Tree Label
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

instance Arbitrary Test where
 arbitrary = oneof 
   [ return Unit
   , Unary <$> arbitrary
   , Binary <$> arbitrary <*> arbitrary
   , frequency [(1,Nary <$> listOf arbitrary),(6,Nary <$> return [])]
   , Id <$> (listOf1 $ elements $ ['a'..'z']++['A'..'Z'])
   , Number <$> arbitrary
   ]

-- ** black box testing 'termToTree' against 'testToTree'

prop_tree_equal :: Test -> Bool
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

prop_Init :: Test -> Bool
prop_Init t = 
  let a = toAdj t
      i = toIntMap t
      g = toGr t
  in initial a i && initial i g && initial g a 

prop_iso_adj_map :: Test -> Bool
prop_iso_adj_map t = iso (toAdj t) (toIntMap t)

prop_iso_map_gr :: Test -> Bool
prop_iso_map_gr t = iso (toIntMap t) (toGr t)

prop_iso_gr_adj :: Test -> Bool
prop_iso_gr_adj t = iso (toGr t) (toAdj t)

-- ** desired properties of kripke kripke structures

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
  
