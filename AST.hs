{-# LANGUAGE GADTs, MultiParamTypeClasses #-}
module AST where

import Control.Monad.Trans.State.Lazy

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
  PlConcat :: Policy fi vi i fr vr r -> Policy fi vi i fr vr r -> Policy fi vi i fr vr r
  
class Reg r where

type Buffer = String

data Id where
  MkId :: String -> Id

data Exp where
  ERead :: Buffer -> Exp
  EWrite :: Buffer -> Id -> Exp
  ELet :: Id -> Exp -> Exp -> Exp
  EPar :: Exp -> Exp -> Exp
  EITE :: (Field f, Value v) => Id -> f -> v -> Exp -> Exp
  EUpd :: (Field f, Value v) => Id -> f -> v -> Exp
  ESeq :: Exp -> Exp -> Exp
  EForever :: Exp -> Exp
  

type CompileM a = State Int a

--Implement function mux dmux

new_buf :: CompileM Buffer
new_buf =
  do { n<- get
     ; return $ "buf" ++ show n
     }

new_id :: CompileM Id
new_id =
  do { n<- get
     ; return $ MkId("x" ++ show n)
     }

compile_pred :: 
  Buffer -> Buffer -> Buffer -> Buffer ->
  Pred fi vi i fr vr r -> 
  CompileM Exp
compile_pred iin iout rin rout PZero = 
  return $ EForever (EPar (ERead iin) (ERead rin))

compile_pred iin iout rin rout POne = 
  do{ x1 <- new_id
    ; x2 <- new_id
    ;return $ 
      EForever (
      EPar (ELet x1 (ERead iin) (EWrite iout x1))
           (ELet x2 (ERead rin) (EWrite rout x2))
      )
    }

--compile_pred iin iout rin rout PTestInstruction 