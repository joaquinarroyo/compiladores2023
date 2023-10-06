{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}
module CEK where

import Common (Pos)
import Lang 
import MonadFD4 (MonadFD4, failFD4, printFD4, lookupDecl)
import Eval (semOp)

-- | Tipo de dato para los valores
data ValCEK info var =
    N info Const
  | Clos (ClosCEK info var)

instance (Show info, Show var) => Show (ValCEK info var) where
  show (N _ c) = show c
  show (Clos c) = show c

data ClosCEK info var =
    ClosFun info Env (Name, Ty) (Scope info var)
  | ClosFix info Env (Name, Ty) (Name, Ty) (Scope2 info var)
  deriving Show 

-- | Info
type Info = (Pos, Ty)

-- | Env
type Env = [ValCEK Info Var]

-- | Frames 
data Frame =
    KArg Env TTerm
  | ClosFrame (ClosCEK Info Var)
  | IfZFrame Env TTerm TTerm
  | RBinFrame Env BinaryOp TTerm
  | LBinFrame BinaryOp (ValCEK Info Var)
  | PrintFrame String
  | LetFrame Env (Scope Info Var)
  deriving Show

-- | Funcion seek expuesta, llamada desde el main. Evalua un termino en la maquina CEK y devuelve un termino.
seek :: MonadFD4 m => TTerm -> m TTerm
seek t  = do
  v <- seek' t [] []
  v' <- valCEK2TTerm v
  return v'
 
-- | Funcion seek de la maquina CEK
seek' :: MonadFD4 m => TTerm -> Env -> [Frame] -> m (ValCEK (Pos, Ty) Var)
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
seek' (Let i n ty t scope) env kont = seek' t env (LetFrame env scope:kont)

-- | Funcion destroy de la maquina CEK
destroy :: MonadFD4 m => ValCEK Info Var -> [Frame] -> m (ValCEK (Pos, Ty) Var)
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
destroy v (ClosFrame (ClosFun _ env _ (Sc1 t)):kont) = seek' t (v:env) kont
destroy v (ClosFrame c@(ClosFix _ env _ _ (Sc2 t)):kont) = seek' t (v:f:env) kont
  where f = Clos c
destroy v (LetFrame env (Sc1 scope):kont) = seek' scope (v:env) kont

-- | Funcion auxiliar que convierte un valor de la maquina CEK a un termino
valCEK2TTerm :: MonadFD4 m => ValCEK Info Var -> m TTerm 
valCEK2TTerm (N i c) = return $ Const i c
valCEK2TTerm (Clos (ClosFun i env (n, ty) scope)) = do
  scope' <- replaceEnvScope scope (length env) env
  return $ Lam i n ty scope'
valCEK2TTerm (Clos (ClosFix i env (n1, ty1) (n2, ty2) scope)) = do
  scope' <- replaceEnvScope2 scope (length env) env
  return $ Fix i n1 ty1 n2 ty2 scope'

-- | Funcion que reemplaza los valores que quedaron en el env en sus variables correspondientes en el scope
replaceEnvScope :: MonadFD4 m => Scope Info Var -> Int -> Env -> m (Scope (Pos, Ty) Var)
replaceEnvScope (Sc1 (Lam i n ty scope)) c env = do
  scope' <- replaceEnvScope scope (c+1) env
  return $ Sc1 $ Lam i n ty scope'
replaceEnvScope (Sc1 t) c env = do
  t' <- replaceEnv' t c env
  return $ Sc1 t'

-- | Funcion que reemplaza los valores que quedaron en el env en sus variables correspondientes en el scope2
replaceEnvScope2 :: MonadFD4 m => Scope2 Info Var -> Int -> Env -> m (Scope2 (Pos, Ty) Var)
replaceEnvScope2 (Sc2 (Fix i n1 ty1 n2 ty2 scope)) c env = do
  scope' <- replaceEnvScope2 scope (c+2) env
  return $ Sc2 $ Fix i n1 ty1 n2 ty2 scope'
replaceEnvScope2 (Sc2 t) c env = do
  t' <- replaceEnv' t c env
  return $ Sc2 t'


-- | Funcion auxiliar para el reemplazo de valores del env en los terminos
replaceEnv' :: MonadFD4 m => TTerm -> Int -> Env -> m TTerm
replaceEnv' t c [] = return t 
replaceEnv' v@(V _ (Bound i)) c env | c-i < length env = do
                                      v' <- valCEK2TTerm $ env'!!(c-i)
                                      return v' 
                                    | otherwise = return $ v
    where
      env' = reverse env
replaceEnv' v@(V _ (Free n)) _ _ = return v -- revisar el caso
replaceEnv' v@(V _ (Global n)) _ _= return v
replaceEnv' c@(Const _ _) _ _ = return c
replaceEnv' (Lam i n ty scope) c env = do
  scope' <- replaceEnvScope scope (c+1) env
  return $ Lam i n ty scope'
replaceEnv' (App i t1 t2) c env = do
  t1' <- replaceEnv' t1 c env
  t2' <- replaceEnv' t2 c env
  return $ App i t1' t2'
replaceEnv' (Print i s t) c env = do
  t' <- replaceEnv' t c env
  return $ Print i s t'
replaceEnv' (BinaryOp i op t1 t2) c env = do
  t1' <- replaceEnv' t1 c env
  t2' <- replaceEnv' t2 c env
  case (t1', t2') of
    (Const _ (CNat n1), Const _ (CNat n2)) -> return $ Const i (CNat $ semOp op n1 n2)
    _ -> return $ BinaryOp i op t1' t2'
replaceEnv' (Fix i n1 ty1 n2 ty2 scope) c env = do
  scope' <- replaceEnvScope2 scope (c+2) env
  return $ Fix i n1 ty1 n2 ty2 scope'
replaceEnv' (IfZ i t1 t2 t3) c env = do
  t1' <- replaceEnv' t1 c env
  t2' <- replaceEnv' t2 c env
  t3' <- replaceEnv' t3 c env
  return $ IfZ i t1' t2' t3'
replaceEnv' (Let i n ty t scope) c env = do
  t' <- replaceEnv' t c env
  scope' <- replaceEnvScope scope (c+1) env
  return $ Let i n ty t' scope'
