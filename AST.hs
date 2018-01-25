{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module AST where

import Control.Monad.Trans.State.Lazy

class Field f where

class Value v where

class (Field f, Value v) => Record f v t where
  { getField :: t -> f -> v
  }

data Binop = Sum | Prod

data Unop = Neg

data Pred fi vi i fr vr r where
  PZero :: Pred fi vi i fr vr r
  POne :: Pred fi vi i fr vr r
  PTestInstruction :: Record i fi vi =>
    fi -> vi ->
    Pred fi vi i fr vr r
  PTestResult :: Record r fr vr =>
    fr -> vr ->
    Pred fi vi i fr vr r
  PBin ::
    Binop -> 
    Pred fi vi i fr vr r ->
    Pred fi vi i fr vr r ->
    Pred fi vi i fr vr r
  PUn ::
    Unop -> 
    Pred fi vi i fr vr r ->
    Pred fi vi i fr vr r

pprod = PBin Prod
psum = PBin Sum
pneg = PUn Neg

data Slice = Action | Result

data Policy fi vi i fr vr r where
  PlTest ::
    Pred fi vi i fr vr r ->
    Policy fi vi i fr vr r ->
    Policy fi vi i fr vr r
  PlSlice ::
    Slice -> 
    Policy fi vi i fr vr r ->
    Policy fi vi i fr vr r
  PlInjA ::
    i -> 
    Policy fi vi i fr vr r
  PlInjR :: 
    r -> 
    Policy fi vi i fr vr r
  PlUpdateInstruction :: Record i fi vi =>
    fi -> vi ->
    Policy fi vi i fr vr r ->
    Policy fi vi i fr vr r
  PlUpdateResult :: Record r fr vr =>
    fr -> vr ->
    Policy fi vi i fr vr r ->
    Policy fi vi i fr vr r
  PlBin ::
    Binop -> 
    Policy fi vi i fr vr r ->
    Policy fi vi i fr vr r ->
    Policy fi vi i fr vr r
  
class Reg r where

data Id where 
  MkId :: String -> Id

type Buffer = String

data Exp where 
  ERead :: Buffer -> Exp
  EWrite :: Buffer -> Id -> Exp
  EPar :: Exp -> Exp -> Exp
  ELet :: Id -> Exp -> Exp -> Exp
  EITE :: (Field f, Value v) => Id -> f -> v -> Exp -> Exp 
  EUpd :: (Field f, Value v) => Id -> f -> v -> Exp
  ESeq :: Exp -> Exp -> Exp
  EForever :: Exp -> Exp
 
type CompileM a = State Int a

new_buf :: CompileM Buffer
new_buf = 
  do { n <- get
     ; return $ "buf" ++ show n 
     }

new_id :: CompileM Id
new_id = 
  do { n <- get 
     ; return $ MkId ("x" ++ show n)
     } 

compile_pred ::
  Buffer -> Buffer -> Buffer -> Buffer ->  
  Pred fi vi i fr vr r -> 
  CompileM Exp
compile_pred iin iout rin rout PZero = 
  return $ EForever (EPar (ERead iin) (ERead rin))

compile_pred iin iout rin rout POne =
  do { x1 <- new_id
     ; x2 <- new_id
     ; return $ 
         EForever 
           (EPar (ELet x1 (ERead iin) (EWrite iout x1))
                 (ELet x2 (ERead rin) (EWrite rout x2)))
     }  
     
mux :: Buffer -> Buffer -> Buffer -> CompileM Exp
mux b _ _ = return $ EForever (EWrite b (MkId "BOGUS"))

demux :: Buffer -> Buffer -> Buffer -> CompileM Exp
demux b _ _ = return $ EForever (EWrite b (MkId "BOGUS"))


