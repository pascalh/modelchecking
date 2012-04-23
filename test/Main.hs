{-# LANGUAGE NoMonomorphismRestriction #-}
module Main where

import Test.Framework (defaultMain, testGroup)
import Test.Framework.Providers.HUnit
import Test.HUnit
import System.Exit (exitFailure)

import ModelChecking.Kripke
import ModelChecking.AstToKripke
import Data.List(sort)

main = defaultMain [sizeGrs,sizeMap,sizeAdj,relGrs,relAdj,relMap]

-- * test size of state set

buildSizeTestgroup ks name = testGroup name $ zipWith f ks sizes where
  f (k,i) s = testCase ("Size "++name++":"++i) $ (sort $ states k) @=? [1..s]

sizeMap = buildSizeTestgroup krMap "IntMap"
sizeGrs = buildSizeTestgroup krGrs "Inductive graph" 
sizeAdj = buildSizeTestgroup krAdj "AdjList" 

-- * test relations

buildRelTestgroup ks name = testGroup name $ zipWith f ks relations where
  f (k,i) r = testCase ("Rels "++name++":"++i) $ (length $ rels k) @=? r

relMap = buildRelTestgroup krMap "IntMap"
relGrs = buildRelTestgroup krGrs "Inductive graph" 
relAdj = buildRelTestgroup krAdj "AdjList" 

-- * test data

sizes = [1,2,3,2,4]
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

krGrs ::[(KripkeGr Label,String)]
krGrs = values

krAdj :: [(AdjList Label,String)]
krAdj = values

krMap ::[(KripkeIntMap Label,String)]
krMap = values 
