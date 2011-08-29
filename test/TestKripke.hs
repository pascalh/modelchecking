{-# LANGUAGE ScopedTypeVariables #-}
module TestKripke(main) where

import Kripke
import DataToGraph (dataToKripke)
import Language.While.Abswhile (Program)
import WhileMisc -- arbitrary instance for while language
import CTL
import Cfg(programs,run)

import Test.Framework.Runners.Console (defaultMain)
import Test.Framework.Providers.QuickCheck2 (testProperty)
import Test.Framework.Providers.HUnit(testCase)
import Test.Framework (testGroup,Test)

import Control.Monad(liftM2)

main = defaultMain tests

tests :: [Test]
tests = [props , examples,examplesVar] 

props = testGroup "hasSucc" $
        [ testProperty "hasSucc_dataToKripke" propPHasSucc
        , testProperty "hasSucc_varCfg" propPHasSuccVar
        ]

examples :: Test
examples = testGroup "DataToKripke" $ map 
  (\(p,phi) -> testCase ("DataToKripke "++p) $ 
    run (dataToKripke::Program -> KripkeGr String) p (Just phi))
  (liftM2 (,) programs phisString) 

examplesVar = testGroup "VarCfg" $ map 
  (\(p,phi) -> testCase ("VarCfg "++p) $ run varCFG p (Just phi))
  (liftM2 (,) programs phisVar) 

-- * properties of a kripke structure

propKHasSucc :: Kripke k => k l -> Bool
propKHasSucc k = all (not . null . suc k) $ states k

propPHasSucc :: Program -> Bool
propPHasSucc p = 
  let (k::KripkeGr String) = dataToKripke p in
  propKHasSucc k

propPHasSuccVar :: Program -> Bool
propPHasSuccVar = propKHasSucc . varCFG

-- * example CTl formulae
phisString = [phi1,phi2]

phi1 = EG $ Disj (AP "[]") (AP "(:)")
phi2 = EG $ AP "[]"

phisVar = [] -- TODO








