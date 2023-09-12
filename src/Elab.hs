{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant bracket" #-}
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

module Elab ( elab, elabDecl, elabSDecl, elabSynTy ) where

import Lang
import Subst
import MonadFD4 ( MonadFD4, failPosFD4, lookupSinTy, addSinTy, failFD4 )

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
-- Syntax Sugar
elab' env (SSugarLam p [vty] t) = elab' env (SLam p vty t)
elab' env (SSugarLam p (vty:vs) t) = elab' env (SLam p vty (SSugarLam p vs t))
elab' env (SSugarLet p (v,vty) bs def body) = elab' env (SLet p (v, bindingToType bs vty) (SSugarLam p bs def) body)
elab' env (SSugarFix p fty (xty:xs) t) = elab' env (SFix p fty xty (SSugarLam p xs t))
elab' env (SSugarLetRec p (v,vty) [(x,xty)] def body) =
  elab' env (SLet p fty (SFix p fty (x,xty) def) body)
  where fty = (v, FunTy xty vty)
elab' env (SSugarLetRec p (v,vty) (xty:bs) def body) =
  elab' env (SSugarLetRec p (v, (bindingToType bs vty)) [xty] (SSugarLam p bs def) body)

elabDecl :: Decl STerm -> Decl Term
elabDecl = fmap elab

elabSDecl :: MonadFD4 m => SDecl -> m (Maybe (Decl STerm))
elabSDecl (SDecl p n ty [] body False) = return $ Just $ Decl p n ty body
elabSDecl (SDecl p n ty bs body False) =
  return $ Just $ Decl p n (bindingToType bs ty) (SSugarLam p bs body)
elabSDecl (SDecl p n ty [(x, xty)] body True) =
  return $ Just $ Decl p n fty (SFix p (n, fty) (x,xty) body)
    where fty = FunTy xty ty
elabSDecl (SDecl p n ty (xty:bs) body True) =
  elabSDecl (SDecl p n (bindingToType bs ty) [xty] (SSugarLam p bs body) True)
elabSDecl (IndirectTypeDecl p n tyn) = do
      mty <- lookupSinTy tyn
      case mty of
        Nothing -> failPosFD4 p "Type synonym not declared"
        Just ty -> elabSDecl (DirectTypeDecl p n ty)
elabSDecl d@(DirectTypeDecl p n ty) = do 
      addSinTy d
      return Nothing

elabSynTy :: MonadFD4 m => STerm -> m STerm
elabSynTy var@(SV p v) = return var
elabSynTy cn@(SConst p c) = return cn
elabSynTy (SLam p (v, ty) t) = do
    ty' <- checkSin ty
    t' <- elabSynTy t
    return $ SLam p (v, ty') t'
elabSynTy (SFix p (f,fty) (x,xty) t) = do
    fty' <- checkSin fty
    xty' <- checkSin xty
    t' <- elabSynTy t
    return $ SFix p (f, fty') (x, xty') t'

------------------------ helpers (Ver donde poner)
bindingToType :: [(Name, Ty)] -> Ty -> Ty
bindingToType [(_, t)] ty = FunTy t ty
bindingToType ((_, t):bs) ty = FunTy t (bindingToType bs ty)

checkSin :: MonadFD4 m => Ty -> m Ty
checkSin (SynTy n) = do
  mty <- lookupSinTy n
  case mty of
    Nothing -> failFD4 "Type synonym not declared"
    Just ty -> return ty
checkSin ty = return ty

