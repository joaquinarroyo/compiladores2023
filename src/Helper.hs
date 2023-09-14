{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module Helper where 

import Lang
import Common
import MonadFD4

-- | Transforma bindings a tipos
bindingToType :: [(Name, Ty)] -> Ty -> Ty
bindingToType [(_, t)] ty = FunTy t ty Nothing
bindingToType ((_, t):bs) ty = FunTy t (bindingToType bs ty) Nothing

-- | Chequea que un tipo (sinonimo) este definido
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

-- | Chequea que una lista de tipos (sinonimos) esten definidos
checkSins :: MonadFD4 m => Pos -> [(Name, Ty)] -> m [(Name, Ty)]
checkSins p [(v, vty)] = do
    vty' <- checkSin p vty
    return [(v, vty')]
checkSins p ((v, vty):vs) = do
    vty' <- checkSin p vty
    vs' <- checkSins p vs
    return $ (v, vty') : vs'