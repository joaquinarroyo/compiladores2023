module IR where

import Lang
import Control.Monad.State
import Control.Monad.Writer
import Subst

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

-- |
runCC :: [Decl TTerm] -> IrDecls
runCC decls = let ((ir, _), irs) = runWriter $ runStateT (mapM ccDecl decls) 0
              in IrDecls (irs ++ ir)

-- |
ccDecl :: Decl TTerm -> StateT Int (Writer [IrDecl]) IrDecl
ccDecl (Decl _ name ty t) = IrVal name (getIrTy ty) <$> closureConvert t

-- |
ccWrite :: String -> FilePath -> IO ()
ccWrite p filename = writeFile filename p

-- |
getVarName :: Name -> StateT Int (Writer [IrDecl]) Name
getVarName n = do
  i <- get
  put (i+1)
  return $ n ++ show i

-- |
getIrTy :: Ty -> IrTy
getIrTy (NatTy _) = IrInt
getIrTy (FunTy _ _ _) = IrFunTy
getIrTy (SynTy _) = undefined

-- |
replaceFreeVars :: [(Name, Ty)] -> Name -> Ir -> Ir
replaceFreeVars fvs clo t = foldr (\((x, ty), i) t' -> IrLet x (getIrTy ty) (IrAccess (IrVar clo) (getIrTy ty) i) t') t (zip fvs [1..])

-- |
closureConvert :: TTerm -> StateT Int (Writer [IrDecl]) Ir
closureConvert (V i (Bound n)) = undefined
closureConvert (V i (Free n)) = return $ IrVar n
closureConvert (V i (Global n)) = return $ IrGlobal n
closureConvert (Const i c) = return $ IrConst c
closureConvert (BinaryOp i op t1 t2) = do
  t1' <- closureConvert t1
  t2' <- closureConvert t2
  return $ IrBinaryOp op t1' t2'
closureConvert (IfZ i t1 t2 t3) = do
  t1' <- closureConvert t1
  t2' <- closureConvert t2
  t3' <- closureConvert t3
  return $ IrIfZ t1' t2' t3'
closureConvert (Let i n ty t1 (Sc1 t)) = do
  var <- getVarName n
  t1' <- closureConvert t1
  t' <- closureConvert t
  return $ IrLet var (getIrTy ty) t1' t'
closureConvert (Print i s t) =  do
  t' <- closureConvert t
  var <- getVarName "print"
  return $ IrLet var IrInt t' (IrPrint s (IrVar var))
closureConvert (App i t1 t2) = do
  clos <- closureConvert t1
  t2' <- closureConvert t2
  fun <- getVarName "fun"
  return $ IrLet fun IrClo clos $ IrCall (IrAccess (IrVar fun) IrClo 0) [IrVar fun, t2'] IrInt
closureConvert (Lam i n ty scope@(Sc1 t)) = do
  fun <- getVarName "f"
  var <- getVarName n
  let t' = open var scope
  t'' <- closureConvert t'

  -- Buscar variables libres en t
  let fvs = freeVarsWithTy t -- [(x1, ty1), (x2, ty2), ...]

  clo <- getVarName $ fun ++ "_clos"

  -- Reemplazar en t'' las variables libres por irAccess a la clausura
  let t''' = replaceFreeVars fvs clo t''

  let decl = IrFun fun (getIrTy ty) [(clo, IrClo), (var, IrInt)] t'''
  tell [decl]
  return $ MkClosure fun (map (IrVar . fst) fvs)
closureConvert (Fix i n1 ty1 n2 ty2 scope@(Sc2 t)) = do
    fun <- getVarName ("fix_" ++ n1)
    var <- getVarName n2
    clos <- getVarName (fun ++ "_clos")
    let t' = open2 clos var scope
    t'' <- closureConvert t'

    -- Buscar variables libres en t
    let fvs = freeVarsWithTy t -- [(x1, ty1), (x2, ty2), ...]

    -- Reemplazar en t'' las variables libres por irAccess a la clausura
    let t''' = replaceFreeVars fvs clos t''

    let decl = IrFun fun (getIrTy ty1) [(clos, IrClo), (var, IrInt)] t'''
    tell [decl]
    return $ MkClosure fun $ map (IrVar . fst) fvs