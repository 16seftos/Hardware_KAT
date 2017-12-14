{-# LANGUAGE GADTs, MultiParamTypeClasses #-}
module AST where

class Field f where

class Value v where

class (Field f, Value v) => Instruction i f v where
  { getInstructionField :: i -> f -> v
  }

class (Field f, Value v) => Result r f v where
  { getResultField :: r -> f -> v
  }

data Pred fi vi i fr vr r where
  PZero :: Pred fi vi i fr vr r
  POne :: Pred fi vi i fr vr r
  PTestInstruction :: Instruction i fi vi => i -> fi -> vi -> Pred fi vi i fr vr r
  PTestResult :: Result r fr vr => r -> fr -> vr -> Pred fi vi i fr vr r
  PSum :: Pred fi vi i fr vr r -> Pred fi vi i fr vr r -> Pred fi vi i fr vr r
  PProd :: Pred fi vi i fr vr r -> Pred fi vi i fr vr r -> Pred fi vi i fr vr r
  PNeg :: Pred fi vi i fr vr r -> Pred fi vi i fr vr r 

data Policy fi vi i fr vr r where
  PlTest :: Pred fi vi i fr vr r -> Policy fi vi i fr vr r -> Policy fi vi i fr vr r
  PlSliceA :: Policy fi vi i fr vr r -> Policy fi vi i fr vr r
  PlSliceR :: Policy fi vi i fr vr r -> Policy fi vi i fr vr r
  PlInjA :: Instruction inew finew vinew => inew -> finew -> vinew -> Policy fi vi i fr vr r -> Policy fi vi i fr vr r
  PlInjR :: Result rnew frnew vrnew => rnew -> frnew -> vrnew -> Policy fi vi i fr vr r -> Policy fi vi i fr vr r
  PlUpdateInstruction :: Instruction i fi vi => i -> fi -> vi -> Policy fi vi i fr vr r -> Policy fi vi i fr vr r
  PlUpdateResult :: Result r fr vr => r -> fr -> vr -> Policy fi vi i fr vr r -> Policy fi vi i fr vr r
  PlChoice :: Policy fi vi i fr vr r -> Policy fi vi i fr vr r -> Policy fi vi i fr vr r
  PlConat :: Policy fi vi i fr vr r -> Policy fi vi i fr vr r -> Policy fi vi i fr vr r
  
class Reg r where

