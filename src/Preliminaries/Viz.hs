module Preliminaries.Viz where 
import Meta



class HasDiagram a where 
    toDiagram :: a -> Diagram B

class Rule a where 
    type T a
    inType  :: a -> [T] 
    outType :: a -> [T] 

data BlockDiagram a where 
    Block       :: a -> BlockDiagram a
    Composition :: BlockDiagram a -> BlockDiagram a -> BlockDiagram a
    RepComp     :: BlockDiagram a -> Meta -> [BlockDiagram a] -> BlockDiagram a

