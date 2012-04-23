{-# LANGUAGE NoMonomorphismRestriction #-}
module Main where

import Test.Framework (defaultMain, testGroup)
import Test.Framework.Providers.HUnit(testCase)
import Test.HUnit((@=?))

import ModelChecking.Kripke(Kripke(..),AdjList,KripkeIntMap,KripkeGr)
import ModelChecking.AstToKripke(AstToKripke(..),Label(..))
import Data.List(sort)

main = defaultMain [testSize,testRels,testLbls]

-- * test size of state set

testSize = testGroup "set size" [sizeGrs,sizeMap,sizeAdj]

buildSizeTestgroup ks name = testGroup name $ zipWith f ks sizes where
  f (k,i) s = testCase (name++":"++i) $ [1..s] @=? (sort $ states k)

sizeMap = buildSizeTestgroup krMap "IntMap"
sizeGrs = buildSizeTestgroup krGrs "Inductive graph" 
sizeAdj = buildSizeTestgroup krAdj "AdjList" 

-- * test relations

testRels = testGroup "relation set" [relMap,relGrs,relAdj]

buildRelTestgroup ks name = testGroup name $ zipWith f ks relations where
  f (k,i) r = testCase (name++":"++i) $ r @=? (length $ rels k)

relMap = buildRelTestgroup krMap "IntMap"
relGrs = buildRelTestgroup krGrs "Inductive graph" 
relAdj = buildRelTestgroup krAdj "AdjList" 


-- * labeling function

testLbls = testGroup "labeling function" [lblMap,lblGrs,lblAdj]

buildLabelTestgroup ks name = testGroup name $ zipWith f ks labelss where
  f (k,i) ls = 
    testCase (name++":"++i) $ (sort ls) @=? 
      (sort $ map (\s -> head $ labels s k) $ states k)

lblMap = buildLabelTestgroup krMap "IntMap"
lblGrs = buildLabelTestgroup krGrs "Inductive graph" 
lblAdj = buildLabelTestgroup krAdj "AdjList" 

-- * test data
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

