{-# LANGUAGE MultiParamTypeClasses , TypeSynonymInstances , FlexibleInstances, FlexibleContexts , TypeFamilies , ScopedTypeVariables #-}

module Cfg where
import Language.While.Abswhile
import Language.While.ErrM
import Language.While.Parwhile

import WhileMisc
import Kripke
import CTL
import DataToGraph
import PrintKripke (showKripke)
import Control.Monad (forM_)

programs = zipWith (++) (repeat "Examples/program") 
                        (map show [1,2,3,4,5,6])  

run :: (Eq l,Kripke k,Show l)
    => (Program -> k l) -> FilePath -> Maybe (Ctl l) -> IO ()
run f file phi = do
  content <- readFile file
  let ast::Program = read content
      k = f ast 
  print $ pretty ast
  showKripke k
  case phi of 
    Just pp -> print $ eval k pp
    Nothing -> return ()

testExamples :: IO ()
testExamples = forM_ programs $ \p -> 
  run (dataToKripke::Program -> KripkeGr String ) p (Just $ EG $ AP "[]")
