{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}
module CEK where

import Common  
import Lang
import MonadFD4
import Eval (semOp)
import Subst (open, open2)

-- Tipo de dato para los valores
data ValCEK info var =
    N info Const
  | Clos (ClosCEK info var)
  deriving Show

data ClosCEK info var =
    ClosFun Env Name (Scope info var)
  | ClosFix Env Name Name (Scope2 info var)
  deriving Show 

-- Env
type Env = [ValCEK (Pos,Ty) Var]

-- Frames 
data Frame =
    KArg Env TTerm
  | ClosFrame (ClosCEK (Pos,Ty) Var)
  | IfZFrame Env TTerm TTerm
  | RBinFrame Env BinaryOp TTerm
  | LBinFrame BinaryOp (ValCEK (Pos,Ty) Var)
  | PrintFrame String

-----
seek :: MonadFD4 m => TTerm -> m TTerm
seek t  = do
  v <- seek' t [] []
  return (valCEK2TTerm v)

-----
seek' :: MonadFD4 m => TTerm -> Env -> [Frame] -> m (ValCEK (Pos,Ty) Var)
seek' (Print _ s t) env kont = seek' t env (PrintFrame s:kont)
seek' (BinaryOp _ op t1 t2) env kont = seek' t1 env (RBinFrame env op t2:kont)
seek' (IfZ _ t1 t2 t3) env kont = seek' t1 env (IfZFrame env t2 t3:kont)
seek' (App _ t1 t2) env kont = seek' t1 env (KArg env t2:kont)
seek' (V _ (Bound i)) env kont = destroy (env!!i) kont
seek' (V _ (Global n)) env kont = do
  mt <- lookupDecl n
  case mt of
    Just t -> do
      v <- seek' t env kont
      destroy v kont
    Nothing -> failFD4 "error"
seek' (Const i n) env kont = destroy (N i n) kont
seek' (Lam _ n _ scope) env kont =
  destroy (Clos $ ClosFun env  n scope) kont
seek' (Fix _ n1 _ n2 _ scope) env kont =
  destroy (Clos $ ClosFix env n1 n2 scope) kont

-----
destroy :: MonadFD4 m => ValCEK (Pos,Ty) Var -> [Frame] -> m (ValCEK (Pos,Ty) Var)
destroy v [] = return v
destroy v ((PrintFrame s):kont) = do
  printFD4 (s++show v)
  destroy v kont
destroy (N i n) ((RBinFrame env op u):kont) = seek' u env (LBinFrame op (N i n):kont)
destroy (N i (CNat n')) ((LBinFrame op (N _ (CNat n)):kont)) = destroy (N i (CNat $ semOp op n' n)) kont
destroy (N _ (CNat 0)) ((IfZFrame env t e):kont) = seek' t env kont
destroy (N _ _) ((IfZFrame env t e):kont) = seek' e env kont
destroy (Clos c) ((KArg env t):kont) = seek' t env (ClosFrame c:kont)
destroy v (ClosFrame (ClosFun env n scope):kont) = seek' (open n scope) (v:env) kont
destroy v (ClosFrame c@(ClosFix env n1 n2 scope):kont) = seek' (open2 n1 n2 scope) (f:v:env) kont
  where f = Clos c

-----
valCEK2TTerm :: ValCEK (Pos,Ty) Var -> TTerm 
valCEK2TTerm (N i c) = Const i c
valCEK2TTerm (Clos (ClosFun env n scope)) = open n scope
valCEK2TTerm (Clos (ClosFix env n1 n2 scope)) = open2 n1 n2 scope


