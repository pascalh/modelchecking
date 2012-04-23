{-# LANGUAGE FlexibleContexts , TemplateHaskell , DeriveDataTypeable#-}
module BuildKripke where

import Criterion.Main

import Data.DeriveTH
import Data.Derive.NFData

import Control.Applicative ((<$>),(<*>))
import Control.DeepSeq(NFData(..))

import ModelChecking.Kripke
import ModelChecking.AstToKripke

import Test.QuickCheck(Arbitrary(..),listOf,oneof,sample')
import Data.Data(Data)
import Data.Typeable(Typeable)

$(derive makeNFData ''Label)
$(derive makeNFData ''AdjList)



data Test 
  = Unit
  | Unary Test
  | Binary Test Test
  | Nary [Test]
  | Id String
  | Number Int
  deriving (Show,Typeable,Data)

instance Arbitrary Test where
 arbitrary = oneof 
   [ return Unit
   , Unary <$> arbitrary
   , Binary <$> arbitrary <*> arbitrary
   , Nary <$> listOf arbitrary 
   , Id <$> arbitrary
   , Number <$> arbitrary
   ]

toAdj :: Data t => t -> AdjList Label
toAdj = astToKripke

toGr :: Data t => t -> KripkeGr Label
toGr = astToKripke

toIntMap :: Data t => t -> KripkeIntMap Label
toIntMap = astToKripke

main = benchmarkBuild

benchmarkBuild = do 
  samples <- sample' arbitrary
  defaultMain $ createBench $ take 10 samples

createBench :: [Test] -> [Benchmark]
createBench ts =  zipWith f ts [1..] where
  f :: Test -> Int -> Benchmark
  f t i = bgroup ("bench "++show i) [bAdj,bGr,bMap] where
    bAdj = bench "adj" (nf rels $ toAdj t)
    bGr  = bench "gr"  (nf rels $ toGr t)
    bMap = bench "map" (nf rels $ toIntMap t)
