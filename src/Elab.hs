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
import MonadFD4 ( MonadFD4, failPosFD4, lookupSinTy, addSinTy, printFD4, failFD4 )
import Common ( Pos )

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
  where fty = (v, FunTy xty vty Nothing)
elab' env (SSugarLetRec p (v,vty) (xty:bs) def body) =
  elab' env (SSugarLetRec p (v, (bindingToType bs vty)) [xty] (SSugarLam p bs def) body)

elabDecl :: Decl STerm -> Decl Term
elabDecl = fmap elab

-- | elaborador de declaraciones superficiales
elabSDecl :: MonadFD4 m => SDecl -> m (Maybe (Decl STerm))
elabSDecl (SDecl p n ty [] body False) = do
    ty' <- checkSin p ty
    body' <- elabSynTy body
    return $ Just $ Decl p n ty' body'
elabSDecl (SDecl p n ty bs body False) = do
    ty' <- checkSin p ty
    sslam <- elabSynTy (SSugarLam p bs body)
    return $ Just $ Decl p n (bindingToType bs ty') sslam
elabSDecl (SDecl p n ty [(x, xty)] body True) = do
    ty' <- checkSin p ty
    sfix <- elabSynTy (SFix p (n, (FunTy xty ty' Nothing)) (x,xty) body)
    return $ Just $ Decl p n (FunTy xty ty' Nothing) sfix
elabSDecl (SDecl p n ty (xty:bs) body True) = do
    ty' <- checkSin p ty
    sslam <- elabSynTy (SSugarLam p bs body)
    elabSDecl (SDecl p n (bindingToType bs ty') [xty] sslam True)
elabSDecl (IndirectTypeDecl p n (FunTy a b s)) = do
    a' <- checkSin p a
    b' <- checkSin p b
    elabSDecl (DirectTypeDecl p n (FunTy a' b' s))
elabSDecl (IndirectTypeDecl p n (SynTy tyn)) = do
    mty <- lookupSinTy tyn
    case mty of
        Nothing -> failPosFD4 p "Type synonym not declared"
        Just ty -> elabSDecl (DirectTypeDecl p n ty)
elabSDecl (IndirectTypeDecl p n ty) = failFD4 "IndirectTypeDecl: No deberia pasar"
elabSDecl d@(DirectTypeDecl p n ty) = do 
      addSinTy d
      return Nothing

-- | elaborador de sinonimos de tipos
--   se corre antes de 'elab' para transformar sinonimos
--   en tipos base
elabSynTy :: MonadFD4 m => STerm -> m STerm
elabSynTy var@(SV p v) = return var
elabSynTy cn@(SConst p c) = return cn
elabSynTy (SLam p (v, ty) t) = do
    ty' <- checkSin p ty
    t'  <- elabSynTy t
    return $ SLam p (v, ty') t'
elabSynTy (SFix p (f,fty) (x,xty) t) = do
    fty' <- checkSin p fty 
    xty' <- checkSin p xty
    t'   <- elabSynTy t
    return $ SFix p (f, fty') (x, xty') t'
elabSynTy (SIfZ p c t e) = do
    c' <- elabSynTy c 
    t' <- elabSynTy t
    e' <- elabSynTy e
    return $ SIfZ p c' t' e'
elabSynTy (SBinaryOp i o t u) = do
    t' <- elabSynTy t 
    u' <- elabSynTy u
    return $ SBinaryOp i o t' u'
elabSynTy (SPrint i str t) = do
    t' <- elabSynTy t
    return $ SPrint i str t'
elabSynTy (SApp p h a) = do
    h' <- elabSynTy h
    a' <- elabSynTy a
    return $ SApp p h' a'
elabSynTy (SLet p (v,vty) def body) = do
    vty'  <- checkSin p vty
    def'  <- elabSynTy def
    body' <- elabSynTy body
    return $ SLet p (v, vty') def' body'
elabSynTy (SSugarLam p vs t) = do
    vs' <- checkSins p vs
    t'  <- elabSynTy t
    return $ SSugarLam p vs' t'
elabSynTy (SSugarLet p (v,vty) vs def body) = do
    vty'  <- checkSin p vty
    vs'   <- checkSins p vs
    def'  <- elabSynTy def
    body' <- elabSynTy body
    return $ SSugarLet p (v, vty') vs' def' body'
elabSynTy (SSugarFix p (f, fty) vs t) = do
    fty' <- checkSin p fty
    vs'  <- checkSins p vs
    t'   <- elabSynTy t
    return $ SSugarFix p (f, fty') vs' t'
elabSynTy (SSugarLetRec p (v,vty) vs def body) = do
    vty'  <- checkSin p vty
    vs'   <- checkSins p vs
    def'  <- elabSynTy def
    body' <- elabSynTy body
    return $ SSugarLetRec p (v, vty') vs' def' body'


------------------------ helpers (Ver donde poner) ------------------------
bindingToType :: [(Name, Ty)] -> Ty -> Ty
bindingToType [(_, t)] ty = FunTy t ty Nothing
bindingToType ((_, t):bs) ty = FunTy t (bindingToType bs ty) Nothing

checkSin :: MonadFD4 m => Pos -> Ty -> m Ty
checkSin p (SynTy n) = do
  mty <- lookupSinTy n
  case mty of
    Nothing -> failPosFD4 p "Type synonym not declared"
    Just ty -> return ty
checkSin p (FunTy a b n) = do
    a' <- checkSin p a
    b' <- checkSin p b
    return $ FunTy a' b' n
checkSin _ ty = return ty

checkSins :: MonadFD4 m => Pos -> [(Name, Ty)] -> m [(Name, Ty)]
checkSins p [(v, vty)] = do
    vty' <- checkSin p vty
    return [(v, vty')]
checkSins p ((v, vty):vs) = do
    vty' <- checkSin p vty
    vs' <- checkSins p vs
    return $ (v, vty') : vs
