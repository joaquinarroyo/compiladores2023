{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module Optimizer where
import MonadFD4 ( MonadFD4, lookupDecl, failFD4, printFD4 )
import Lang ( Tm(..), TTerm, Decl (declBody), Const (..), BinaryOp (..), Var (..), Name, getTy, Scope (Sc1), Scope2 (Sc2) )
import Subst ( close, close2, open, open2 )
import Eval (semOp, eval)
import PPrint (ppName, freshen)
import Helper (hasEffects, getUsedVarsNames)

-- | Max optimization iterations
maxIt :: Int
maxIt = 10

-- |
optimize :: MonadFD4 m => Decl TTerm -> m (Decl TTerm)
optimize d = do
    oBody <- optimize' maxIt (declBody d)
    return $ d { declBody = oBody }

optimize' :: MonadFD4 m => Int -> TTerm -> m TTerm
optimize' 0 t = return t
optimize' i t = constantFolding t >>= constantPropagation [] >>= inlineExpansion >>= optimize' (i - 1)

-- CAMBIAR OPEN/CLOSE DE SCOPES CUANDO NO SEA NECEASRIO USARLOS

-- | Constant Folding
constantFolding :: MonadFD4 m => TTerm ->  m TTerm
constantFolding v@(V _ _) = return v
constantFolding c@(Const _ _) = return c
constantFolding (Lam i n ty scope) = do
    let t = open n scope
    t' <- constantFolding t
    return $ Lam i n ty (close n t')
constantFolding (App i t1 t2) = do
    t1' <- constantFolding t1
    t2' <- constantFolding t2
    return $ App i t1' t2'
constantFolding (Print i s t) = do
    t' <- constantFolding t
    return $ Print i s t'
constantFolding (Fix i n1 ty1 n2 ty2 scope) = do
    let t = open2 n1 n2 scope
    t' <- constantFolding t
    return $ Fix i n1 ty1 n2 ty2 (close2 n1 n2 t')
constantFolding (IfZ i t1 t2 t3) = do
    t1' <- constantFolding t1
    t2' <- constantFolding t2
    t3' <- constantFolding t3
    return $ IfZ i t1' t2' t3'
constantFolding (Let i n ty t1 scope) = do
    t1' <- constantFolding t1
    let t2 = open n scope
    t2' <- constantFolding t2
    return $ Let i n ty t1' (close n t2')
constantFolding (BinaryOp i op (Const _ (CNat n1)) (Const _ (CNat n2))) =
    return $ Const i (CNat (semOp op n1 n2))
constantFolding (BinaryOp i Add t (Const _ (CNat 0))) = return t
constantFolding (BinaryOp i Add (Const _ (CNat 0)) t) = return t
constantFolding (BinaryOp i Sub t (Const _ (CNat 0))) = return t
constantFolding b@(BinaryOp i Sub (Const _ (CNat 0)) t) =
    if hasEffects t then return b else return $ Const i (CNat 0)
constantFolding t = return t -- ver si falta algun caso 

-- | Constant Propagation
constantPropagation :: MonadFD4 m => [(Name, TTerm)] -> TTerm -> m TTerm
constantPropagation _ v@(V i (Global n)) = do
  mtm <- lookupDecl n
  case mtm of
    Nothing -> failFD4 $ "Error en optimizacion (CP): variable no declarada: " ++ ppName n
    Just c@(Const {}) -> return c
    Just _ -> return v
constantPropagation env v@(V i (Free n)) =
  case lookup n env of
    Nothing -> return v
    Just t -> return t
constantPropagation _ v@(V i (Bound n)) = return v
constantPropagation _ c@(Const _ _) = return c
constantPropagation env (Lam i n ty scope) = do
  let t = open n scope
  t' <- constantPropagation env t
  return $ Lam i n ty (close n t')
constantPropagation env (App i t1 t2) = do
  t1' <- constantPropagation env t1
  t2' <- constantPropagation env t2
  return $ App i t1' t2'
constantPropagation env (Print i s t) = do
  t' <- constantPropagation env t
  return $ Print i s t'
constantPropagation env (BinaryOp i op t1 t2) = do
  t1' <- constantPropagation env t1
  t2' <- constantPropagation env t2
  return $ BinaryOp i op t1' t2'
constantPropagation env (Fix i n1 ty1 n2 ty2 scope) = do
  let t = open2 n1 n2 scope
  t' <- constantPropagation env t
  return $ Fix i n1 ty2 n2 ty2 (close2 n1 n2 t')
constantPropagation env (IfZ i t1 t2 t3) = do
  t1' <- constantPropagation env t1
  t2' <- constantPropagation env t2
  t3' <- constantPropagation env t3
  return $ IfZ i t1' t2' t3'
constantPropagation env (Let i n ty t scope) = do
  t' <- constantPropagation env t
  case t' of
    c@(Const _ v) -> constantPropagation ((n, c):env) (open n scope)
    _ -> do
      scope' <- constantPropagation env (open n scope)
      return $ Let i n ty t' (close n scope')

-- | Inline Expansion
inlineExpansion :: MonadFD4 m => TTerm -> m TTerm
inlineExpansion t = inlineExpansion' (getUsedVarsNames t) t

inlineExpansion' :: MonadFD4 m => [Name] -> TTerm -> m TTerm
inlineExpansion' _ v@(V _ _) = return v
inlineExpansion' _ c@(Const _ _) = return c
inlineExpansion' nms (Lam i n ty (Sc1 t)) = do
  t' <- inlineExpansion' nms t
  return $ Lam i n ty (Sc1 t')
inlineExpansion' nms (Print i s t) = do
  t' <- inlineExpansion' nms t
  return $ Print i s t'
inlineExpansion' nms (BinaryOp i op t1 t2) = do
  t1' <- inlineExpansion' nms t1
  t2' <- inlineExpansion' nms t2
  return $ BinaryOp i op t1' t2'
inlineExpansion' nms (Fix i n1 ty1 n2 ty2 (Sc2 t)) = do
  t' <- inlineExpansion' nms t
  return $ Fix i n1 ty1 n2 ty2 (Sc2 t')
inlineExpansion' nms (IfZ i t1 t2 t3) = do
  t1' <- inlineExpansion' nms t1
  t2' <- inlineExpansion' nms t2
  t3' <- inlineExpansion' nms t3
  return $ IfZ i t1' t2' t3'
inlineExpansion' nms (Let i n ty t1 (Sc1 t2)) = do
  t1' <- inlineExpansion' nms t1
  t2' <- inlineExpansion' nms t2
  return $ Let i n ty t1' (Sc1 t2')
inlineExpansion' nms t@(App _ (Lam {}) (Const {})) = eval t
-- Se asume que la variable es siempre funcion
inlineExpansion' nms t@(App _ (V _ (Bound i)) (Const {})) = return t
inlineExpansion' nms t@(App _ (V {}) (Const {})) = eval t
-- Caso Aplicacion con t' complejo
-- Falta caso (Free f) (Llevar entorno local?)
inlineExpansion' nms (App i (V _ (Global f)) t') = do
  mtm <- lookupDecl f
  case mtm of
    Nothing -> failFD4 $ "Error en optimizacion (IE): variable no declarada: " ++ ppName f
    Just t -> inlineExpansion' nms (App i t t')
inlineExpansion' nms t@(App i (Lam _ _ _ scope) t') = 
  let z = freshen nms "x"
  in return $ Let i z (getTy t') t' (Sc1 (open z scope))
inlineExpansion' nms (App i t1 t2) = do
  t1' <- inlineExpansion' nms t1
  t2' <- inlineExpansion' nms t2
  return $ App i t1' t2'