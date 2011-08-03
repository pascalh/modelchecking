module CTL where

import Kripke

data Ctl a = TT 
           | FF
           | AP a
           | Neg (Ctl a)
           | Disj (Ctl a) (Ctl a) 
           | Conj (Ctl a) (Ctl a)
           | ForAll (CtlPath a)
           | Exists (CtlPath a)

data CtlPath a = X (Ctl a)
               | U (Ctl a) (Ctl a)

eval :: (Kripke k s, Eq a) => s -> k a -> Ctl a -> Bool
eval _ _ TT = True
eval _ _ FF = False
eval s k (AP a) = a `elem` labels s k
