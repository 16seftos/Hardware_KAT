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
  { (==) :: (Value v) => v -> v -> Bool
  }

class (Field f, Value v) => Record f v t where
  { getField :: t -> f -> v
  }

data Binop = Sum | Prod

data Unop = Neg

{- Predicate Definitions -}
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

{- Policy Definitions -}
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
  

{- Intermediate Language Definitions -}
class Reg r where

data Id where 
  MkId :: String -> Id

type Buffer = String

data Exp where
  ERead :: Buffer -> Exp                                      {- Read Reg -}
  EWrite :: Buffer -> Id -> Exp                               {- Write Value to Reg -}
  ELet :: Id -> Exp -> Exp -> Exp                             {- Assignment -}
  EPar :: Exp -> Exp -> Exp                                   {- Parallel -}
  EITE :: (Field f, Value v) => Id -> f -> v -> Exp -> Exp    {- "If then Else" (test) If only -}
  EUpd :: (Field f, Value v) => Id -> f -> v -> Exp           {- ? -}
  EIf  :: Bool -> Exp -> Exp -> Exp                           {- Conditional -}
  EBinop :: Binop -> Exp -> Exp -> Exp                        {- Product (AND) -}
  ESeq :: Exp -> Exp -> Exp                                   {- Concatination -}
  EForever :: Exp -> Exp                                      {- Hardwire -}
  {- Didn't we decide that EForever is obsolete because Steams not Sets? -}
  EMux :: CompileM Exp -> CompileM Exp -> Buffer -> Buffer -> Exp {- Requires CompileM otherwise it can't be nested -}
 
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

isSum :: Binop -> Bool
isSum Sum = True
isSum _ = False

demux :: Buffer -> Buffer -> Buffer -> CompileM Exp
demux b _ _ = return $ EForever (EWrite b (MkId "BOGUS"))

{- Compile to Intermediate Language -}

{- Compile Predicates -}
compile_pred ::
  Buffer -> Buffer -> Buffer -> Buffer ->  
  Pred fi vi i fr vr r -> 
  CompileM Exp

  {- PZero -}
compile_pred iin iout rin rout PZero = 
  return $ EForever (EPar (ERead iin) (ERead rin))
  
  {- POne -}
compile_pred iin iout rin rout POne =
  do{ x1 <- new_id
    ; x2 <- new_id
    ; return $ 
        EForever 
           (EPar (ELet x1 (ERead iin) (EWrite iout x1))
                 (ELet x2 (ERead rin) (EWrite rout x2)))
     } 

{- IMPORTANT NOTE:  These are not equivalent to C[] as C[] will allow Instr and Res to go in parallel -}
  {- PTestInstruction -}
compile_pred iin iout rin rout (PTestInstruction fi vi) = 
  do{ x1 <- new_id
    ; x2 <- new_id
    ; return $ 
        EIf {-(vi AST.== vi)-}
        True {- I can't figure out how to test the equality of two values -}
          (EForever 
              {-(EPar-} (ELet x1 (ERead iin) (EWrite iout x1)) 
                    {- Ambiguous based on C[] : (ELet x2 (ERead rin) (EWrite rout x2))) -}
          )
          (EForever (ERead iin)) {- Ambiguous based on C[] : (EPar (ERead iin) (ERead rin)) -}
    }

  {- PTestResult -}
compile_pred iin iout rin rout (PTestResult fr vr) = 
  do{ x1 <- new_id
    ; x2 <- new_id
    ; return $ 
        EIf {-(vr AST.== vr)-}
        True {- I can't figure out how to test the equality of two values -}
          (EForever 
              {-(EPar (ELet x1 (ERead iin) (EWrite iout x1))-}
                    (ELet x2 (ERead rin) (EWrite rout x2)) {- Ambiguous based on C[] : ) -}
          )
          (EForever (ERead rin)) {- Ambiguous based on C[] : (EPar (ERead iin) (ERead rin)) -}
    }

  {- PBin -}
compile_pred iin iout rin rout (PBin bop pred1 pred2) =
  case bop of
    Sum  -> do{ eaii <- new_buf
              ; eari <- new_buf
              ; ebii <- new_buf
              ; ebri <- new_buf
              ; eaio <- new_buf
              ; earo <- new_buf
              ; ebio <- new_buf
              ; ebro <- new_buf
              ; demux iin eaii ebii
              ; demux rin eari ebri
              ; return $ EForever (EMux 
                (compile_pred eaii eaio eari earo pred1)
                (compile_pred ebii ebio ebri ebro pred2)
                iout rout)
              }
              {- The definition of C[prod] as per the paper is a bit badly described.  && of Exp isn't simplifying the Predicate?  Maybe it is -}
    Prod ->
      do { 


return $ EForever (EAnd 
                (compile_pred iin iout rin rout pred1)
                (compile_pred iin iout rin rout pred2)
              )

compile_pred iin iout rin rout (PUn uop pred1) =
  case uop of
    Neg -> do { x1 <- new_id
              ; x2 <- new_id
              ; return $ EForever ({- Test A -}
                  EIf {- (ETest A) -} (not False)
                  ( EPar (ERead iin) (ERead rin)
                  )

                  ( EPar (ELet x1 (ERead iin) (EWrite iout x1))
                         (ELet x2 (ERead rin) (EWrite rout x2))
                  )
                )
              }


{- Compile Policies -}
compile_policy ::
  Buffer -> Buffer -> Buffer -> Buffer ->  
  Policy fi vi i fr vr r -> 
  CompileM Exp

compile_policy iin iout rin rout (PlTest pred policy) =
  return $ EForever (EPar (ERead iin) (ERead rin))

compile_policy iin iout rin rout (PlSlice sliceT policy) =
  case sliceT of
  Action -> return $ EForever (EPar (ERead iin) (ERead rin))
  Result -> return $ EForever (EPar (ERead iin) (ERead rin))

compile_policy iin iout rin rout (PlInjA instr) =
  return $ EForever (EPar (ERead iin) (ERead rin))

compile_policy iin iout rin rout (PlInjR res) =
  return $ EForever (EPar (ERead iin) (ERead rin))

compile_policy iin iout rin rout (PlUpdateInstruction fi vi policy) =
  return $ EForever (EPar (ERead iin) (ERead rin))

compile_policy iin iout rin rout (PlUpdateResult fr vr policy) =
  return $ EForever (EPar (ERead iin) (ERead rin))

compile_policy iin iout rin rout (PlBin bop policy1 policy2) =
  case bop of
  Sum  -> return $ EForever (EPar (ERead iin) (ERead rin))
  Prod -> return $ EForever (EPar (ERead iin) (ERead rin))


     
mux :: Buffer -> Buffer -> Buffer -> CompileM Exp
mux b _ _ = return $ EForever (EWrite b (MkId "BOGUS"))




