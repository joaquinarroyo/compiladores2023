module IR where

import Lang
import Control.Monad.State
import Control.Monad.Writer

data Ir = IrVar Name
        | IrGlobal Name
        | IrCall Ir [Ir] IrTy
                        -- ^ Tipo de expr final
        | IrConst Const
        | IrPrint String Ir
        | IrBinaryOp BinaryOp Ir Ir 
        | IrLet Name IrTy Ir Ir
        | IrIfZ Ir Ir Ir
        | MkClosure Name [Ir]
        | IrAccess Ir IrTy Int
  deriving Show

data IrTy = IrInt
          | IrClo
          | IrFunTy
  deriving Show

data IrDecl =
    IrFun { irDeclName :: Name
          , irRetTy :: IrTy
          , irDeclArgs :: [(Name, IrTy)]
          , irDeclBody :: Ir
    }
  | IrVal { irDeclName :: Name
          , irDeclTy :: IrTy
          , irDeclDef :: Ir
          }
  deriving Show

newtype IrDecls = IrDecls { irDecls :: [IrDecl] }

{-
La siguiente instancia es sólo para debugging
-}
instance Show IrDecls where
  show (IrDecls decls) =
   concatMap (\d -> show d ++ "\n") decls

runCC :: [Decl Term] -> [IrDecl]
runCC = concatMap runCC'

runCC' :: Decl Term -> [IrDecl]
runCC' d = execWriter (runStateT (closureConvert (declBody d)) 0)


--
closureConvert :: Term -> StateT Int (Writer [IrDecl]) Ir
closureConvert (V i (Bound n)) = undefined
closureConvert (V i (Free n)) = return $ IrVar n
closureConvert (V i (Global n)) = return $ IrGlobal n
closureConvert (Const i c) = return $ IrConst c
closureConvert (Lam i n ty (Sc1 t)) = do
  t' <- closureConvert t
  return $ MkClosure "fun" [t', IrVar n]
closureConvert (App i t1 t2) = undefined
closureConvert (Print i s t) = do
  t' <- closureConvert t
  return $ IrPrint s t'
closureConvert (BinaryOp i op t1 t2) = do
  t1' <- closureConvert t1
  t2' <- closureConvert t2
  return $ IrBinaryOp op t1' t2'
closureConvert (Fix i n1 ty1 n2 ty2 (Sc2 t)) = undefined
closureConvert (IfZ i t1 t2 t3) = do
  t1' <- closureConvert t1
  t2' <- closureConvert t2
  t3' <- closureConvert t3
  return $ IrIfZ t1' t2' t3'
closureConvert (Let i n ty t1 (Sc1 t2)) = do
  t1' <- closureConvert t1
  t2' <- closureConvert t2 -- VER
  return $ IrLet n (ty2IrTy ty) t1' t2'

ty2IrTy :: Ty -> IrTy
ty2IrTy (NatTy _) = IrInt
ty2IrTy (FunTy {}) = IrFunTy
