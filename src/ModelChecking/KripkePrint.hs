module ModelChecking.KripkePrint(showKripke) where

import qualified ModelChecking.Kripke as K

import Data.GraphViz hiding (toNode)
import Data.Graph.Inductive
import Data.GraphViz.Attributes.Complete

-- |transforms a kripke structure to dotgraph representation
toDotgraph :: (K.Kripke k,Show l) => Settings -> k l -> IO (DotGraph Node)
toDotgraph s g = do
    let g_dot = DotGraph True True Nothing dstmts 
    runGraphvizCanvas' g_dot Xlib
    return g_dot
  where
  dstmts = DotStmts [nodeAttrs s,edgeAttrs s] [] dnodes dedges 
  dnodes = map (toNode g) $ K.states g 
  dedges =  map toEdge  $ K.rels g

-- |transforms a component to dotnode
toNode :: (K.Kripke k, Show l) 
       => k l -> K.KripkeState -> DotNode K.KripkeState
toNode g n = DotNode n [Center True, Label $ toLabelValue m ] where
  m :: String
  m = case K.labels n g of
    (l:_) -> show n ++ "|"++show l
    _     -> []

-- |creates a directed edge
toEdge :: (K.KripkeState,K.KripkeState) -> DotEdge Node
toEdge (u,v) = DotEdge  u v edgeAtt

-- |global node attribute
nodeAttrs :: Settings -> GlobalAttributes
nodeAttrs s = NodeAttrs [ Shape Ellipse 
                        , FontSize $ fontSize s
                        , FontColor $ X11Color RoyalBlue4
                        ]

-- |global edge attribute
edgeAttrs :: Settings -> GlobalAttributes
edgeAttrs s = EdgeAttrs 
  [ FontSize $ fontSize s
  , Style $ return $ SItem Dotted []
  , ArrowHead $ AType [(ArrMod OpenArrow BothSides,Vee)]
  ]

edgeAtt ::[Attribute]
edgeAtt = [Dir Forward]

-- |shows a kripke structure using 'show' to create state labels
showKripke :: (K.Kripke k,Show l) => k l -> IO () 
showKripke k = toDotgraph defaultSettings k >> return ()

-- |default settings
defaultSettings :: Settings
defaultSettings = Settings 9 

-- |print settings for a kripke structure
data Settings = Settings 
              { fontSize :: Double -- ^font size of kripke labels
              } 

