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

  
    
