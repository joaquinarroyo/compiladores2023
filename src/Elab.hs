{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-|
Module      : Elab
Description : Elabora un término fully named a uno locally closed.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo permite elaborar términos y declaraciones para convertirlas desde
fully named (@STerm) a locally closed (@Term@)
-}

module Elab ( elab, elabDecl) where

import Lang
import Subst

-- | 'elab' transforma variables ligadas en índices de de Bruijn
-- en un término dado. 
elab :: STerm -> Term
elab = elab' []

elab' :: [Name] -> STerm -> Term
elab' env (SV p v) =
  -- Tenemos que ver si la variable es Global o es un nombre local
  -- En env llevamos la lista de nombres locales.
  if v `elem` env 
    then V p (Free v)
    else V p (Global v)

elab' _ (SConst p c) = Const p c
elab' env (SLam p (v, ty) t) = Lam p v ty (close v (elab' (v:env) t))
elab' env (SSugarLam p [(v, ty)] t) = Lam p v ty (close v (elab' (v:env) t))
elab' env (SSugarLam p ((v, ty):bs) t) = Lam p v ty (close v (elab' (v:env) (SSugarLam p bs t)))
elab' env (SFix p (f,fty) (x,xty) t) = Fix p f fty x xty (close2 f x (elab' (x:f:env) t))
elab' env (SIfZ p c t e) = IfZ p (elab' env c) (elab' env t) (elab' env e)
-- Operadores binarios
elab' env (SBinaryOp i o t u) = BinaryOp i o (elab' env t) (elab' env u)
-- Operador Print
elab' env (SPrint i str t) = Print i str (elab' env t)
-- Aplicaciones generales
elab' env (SApp p h a) = App p (elab' env h) (elab' env a)
elab' env (SLet p (v,vty) def body) =  
  Let p v vty (elab' env def) (close v (elab' (v:env) body))
elab' env (SFunLet p (v,vty) bs def body) =  
  Let p v (bindingToType bs vty) (elab' env (SSugarLam p bs def)) (close v (elab' (v:env) body))

elabDecl :: Decl STerm -> Decl Term
elabDecl = fmap elab

------------------------ helpers (Ver donde poner)
bindingToType :: [(Name, Ty)] -> Ty -> Ty
bindingToType [(_, t)] ty = FunTy t ty
bindingToType ((_, t):bs) ty = FunTy t (bindingToType bs ty)