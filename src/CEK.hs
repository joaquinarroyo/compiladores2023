{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}
module CEK where

import Common  
import Lang
import MonadFD4
import Eval (semOp)

-- Tipo de dato para los valores
data ValCEK info var =
    N info Const
  | Clos (ClosCEK info var)
  deriving Show

data ClosCEK info var =
    ClosFun info Env (Name, Ty) (Scope info var)
  | ClosFix info Env (Name, Ty) (Name, Ty) (Scope2 info var)
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
  deriving Show

--
seek :: MonadFD4 m => TTerm -> m TTerm
seek t  = do
  v <- seek' t [] []
  return (valCEK2TTerm v)

--
seek' :: MonadFD4 m => TTerm -> Env -> [Frame] -> m (ValCEK (Pos,Ty) Var)
seek' (Print _ s t) env kont = seek' t env (PrintFrame s:kont)
seek' (BinaryOp _ op t1 t2) env kont = seek' t1 env (RBinFrame env op t2:kont)
seek' (IfZ _ t1 t2 t3) env kont = seek' t1 env (IfZFrame env t2 t3:kont)
seek' (App _ t1 t2) env kont = seek' t1 env (KArg env t2:kont)
seek' (V _ (Bound i)) env kont = destroy (env!!i) kont
seek' (V _ (Global n)) env kont = do
  mt <- lookupDecl n
  case mt of
    Just t -> seek' t env kont
    Nothing -> failFD4 "error"
seek' (Const i n) env kont = destroy (N i n) kont
seek' (Lam i n ty scope) env kont =
  destroy (Clos $ ClosFun i env (n, ty) scope) kont
seek' (Fix i n1 ty1 n2 ty2 scope) env kont =
  destroy (Clos $ ClosFix i env (n1, ty1) (n2, ty2) scope) kont

--
destroy :: MonadFD4 m => ValCEK (Pos,Ty) Var -> [Frame] -> m (ValCEK (Pos,Ty) Var)
destroy v [] = do
  return v
destroy v ((PrintFrame s):kont) = do
  printFD4 (s++show v)
  destroy v kont
destroy (N i n) ((RBinFrame env op u):kont) = seek' u env (LBinFrame op (N i n):kont)
destroy (N i (CNat n')) ((LBinFrame op (N _ (CNat n)):kont)) = destroy (N i (CNat $ semOp op n n')) kont
destroy (N _ (CNat 0)) ((IfZFrame env t e):kont) = seek' t env kont
destroy (N _ _) ((IfZFrame env t e):kont) = seek' e env kont
destroy (Clos c) ((KArg env t):kont) = seek' t env (ClosFrame c:kont)
destroy v (ClosFrame (ClosFun i env (n, ty) (Sc1 t)):kont) = seek' t (v:env) kont
destroy v (ClosFrame c@(ClosFix i env (n1, ty1) (n2, ty2) (Sc2 t)):kont) = seek' t (v:f:env) kont
  where f = Clos c

--
valCEK2TTerm :: ValCEK (Pos,Ty) Var -> TTerm 
valCEK2TTerm (N i c) = Const i c
valCEK2TTerm (Clos (ClosFun i env (n, ty) scope)) = Lam i n ty scope
valCEK2TTerm (Clos (ClosFix i env (n1, ty1) (n2, ty2) scope)) = Fix i n1 ty1 n2 ty2 scope 

