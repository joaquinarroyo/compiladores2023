{-# LANGUAGE PatternSynonyms #-}

{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-missing-signatures #-}

module Bytecompile8 where

{- Module 8ByteCompile -}

import Lang
import MonadFD4
import qualified Data.ByteString.Lazy as BS
import Data.Binary ( Word8, Binary(put, get), decode, encode )
import Data.Binary.Put ( putWord8 )
import Data.Binary.Get ( getWord8, isEmpty )
import Data.List ( intercalate )
import Data.Char
import Subst

type Opcode = Int
type Bytecode = [Int]

newtype Bytecode8 = BC8 { un8 :: [Word8] }

{- Esta instancia explica como codificar y decodificar Bytecode de 8 bits -}
instance Binary Bytecode8 where
  put (BC8 bs) = mapM_ putWord8 bs
  get = go
    where
      go = do
        empty <- isEmpty
        if empty
          then return $ BC8 []
          else do
            x <- getWord8
            BC8 xs <- go
            return $ BC8 (x:xs)


pattern NULL     = 0
pattern RETURN   = 1
pattern ACCESS   = 3
pattern FUNCTION = 4
pattern CALL     = 5
pattern ADD      = 6
pattern SUB      = 7
pattern FIX      = 9
pattern STOP     = 10
pattern SHIFT    = 11
pattern DROP     = 12
pattern PRINT    = 13
pattern PRINTN   = 14
pattern JUMP     = 15
-- | Nuevos patterns para IFZ
pattern CJUMP    = 16
pattern TAILCALL = 17
-- | Nuevos patterns para Enteros
pattern SHORT    = 18  -- 8bytes
pattern INT      = 19 -- 16bytes
pattern LONG     = 20 -- 32bytes
pattern LONGLONG = 21 -- 64bytes


-- función util para debugging: muestra el Bytecode de forma más legible.
showOps8 :: Bytecode -> [String]
showOps8 [] = []
showOps8 (NULL:xs)        = "NULL" : showOps8 xs
showOps8 (RETURN:xs)      = "RETURN" : showOps8 xs
showOps8 (ACCESS:i:xs)    = ("ACCESS " ++ show i) : showOps8 xs
showOps8 (FUNCTION:i:xs)  = ("FUNCTION len=" ++ show i) : showOps8 xs
showOps8 (CALL:xs)        = "CALL" : showOps8 xs
showOps8 (ADD:xs)         = "ADD" : showOps8 xs
showOps8 (SUB:xs)         = "SUB" : showOps8 xs
showOps8 (FIX:xs)         = "FIX" : showOps8 xs
showOps8 (STOP:xs)        = "STOP" : showOps8 xs
showOps8 (JUMP:i:xs)      = ("JUMP off=" ++ show i) : showOps8 xs
showOps8 (SHIFT:xs)       = "SHIFT" : showOps8 xs
showOps8 (DROP:xs)        = "DROP" : showOps8 xs
showOps8 (PRINT:xs)       = let (msg,_:rest) = span (/=NULL) xs
                           in ("PRINT " ++ show (bc2string8 msg)) : showOps8 rest
showOps8 (PRINTN:xs)      = "PRINTN" : showOps8 xs
showOps8 (ADD:xs)         = "ADD" : showOps8 xs
showOps8 (CJUMP:i:xs)     = ("CJUMP off=" ++ show i) : showOps8 xs
showOps8 (TAILCALL:xs)    = "TAILCALL" : showOps8 xs
showOps8 (x:xs)           = show x : showOps8 xs

showBC8 :: Bytecode -> String
showBC8 = intercalate "; " . showOps8

-- ord/chr devuelven los codepoints unicode, o en otras palabras
-- la codificación UTF-8 del caracter.
string2bc8 :: String -> Bytecode
string2bc8 = map ord

bc2string8 :: Bytecode -> String
bc2string8 = map chr

-- | Toma un bytecode, lo codifica y lo escribe un archivo
bcWrite8 :: Bytecode -> FilePath -> IO ()
bcWrite8 bs filename = BS.writeFile filename (encode $ BC8 $ fromIntegral <$> bs)

---------------------------
-- Ejecución de bytecode --
---------------------------

-- | Lee de un archivo y lo decodifica a bytecode
bc8Read :: FilePath -> IO Bytecode
bc8Read filename = (map fromIntegral <$> un8) . decode <$> BS.readFile filename

-- | Transforma un Term en Bytecode
bc8 :: MonadFD4 m => TTerm -> m Bytecode
bc8 t = do
  t' <- bc8' t
  return $ t' ++ [STOP]

bc8' :: MonadFD4 m => TTerm -> m Bytecode
bc8' term = case term of
  (V _ (Bound i))                 -> return [ACCESS, i]
  (V _ (Free n))                  -> failFD4 "bc: Free"
  -- (Const _ (CNat i))              -> return [CONST, i]
  (Lam _ _ _ (Sc1 t))             -> do
    t' <- tc8 t
    return $ [FUNCTION, length t'] ++ t'
  (App _ t1 t2)                   -> do
    t1' <- bc8' t1
    t2' <- bc8' t2
    return $ t1' ++ t2' ++ [CALL]
  (Print _ s t)                   -> do
    t' <- bc8' t
    return $ [PRINT] ++ string2bc8 s ++ [NULL] ++ t' ++ [PRINTN]
  (BinaryOp _ op t1 t2)           -> do
    t1' <- bc8' t1
    t2' <- bc8' t2
    case op of
      Add -> return $ t1' ++ t2' ++ [ADD]
      Sub -> return $ t1' ++ t2' ++ [SUB]
  (Fix _ _ _ _ _ (Sc2 t))         -> do
    t' <- bc8' t
    return $ [FUNCTION, length t' + 1] ++
             t' ++ [RETURN, FIX]
  (IfZ _ t1 t2 t3)                -> do
    t1' <- bc8' t1
    t2' <- bc8' t2
    t3' <- bc8' t3
    return $ t1' ++ [CJUMP, length t2' + 2] ++
             t2' ++ [JUMP, length t3'] ++ t3'
  (Let _ n ty t1 (Sc1 t2))        -> do
    t1' <- bc8' t1
    t2' <- bc8' t2
    return $ t1' ++ [SHIFT] ++ t2' ++ [DROP]

tc8 :: MonadFD4 m => TTerm -> m Bytecode
tc8 term = case term of
  (App _ t1 t2) -> do
    t1' <- bc8' t1
    t2' <- bc8' t2
    return $ t1' ++ t2' ++ [TAILCALL]
  (IfZ _ t1 t2 t3) -> do
    t1' <- bc8' t1
    t2' <- tc8 t2
    t3' <- tc8 t3
    return $ t1' ++ [CJUMP, length t2' + 2] ++
             t2' ++ [JUMP, length t3'] ++ t3'
  (Let _ n ty t1 (Sc1 t2)) -> do
    t1' <- bc8' t1
    t2' <- tc8 t2
    return $ t1' ++ [SHIFT] ++ t2' ++ [DROP]
  _ -> do
    term' <- bc8' term
    return $ term' ++ [RETURN]

-- | Bytecode Vals
-- data ValBytecode =
--     I Int
--   | Fun Env Bytecode
--   | RA Env Bytecode

-- instance Show ValBytecode where
--   show (I i) = show i
--   show (Fun e b) = "Clos" ++ show (showOps b)
--   show (RA e b) = "RA" ++ show (showOps b)

-- type Env = [ValBytecode]
-- type Stack = [ValBytecode]

-- -- | Ejecuta un bytecode
-- runBC :: MonadFD4 m => Bytecode -> m ()
-- runBC b = runBC' b [] []

-- runBC' :: MonadFD4 m => Bytecode -> Env -> Stack -> m ()
-- runBC' (RETURN:_) _ (v:(RA e c):stack)      = runBC' c e (v:stack)
-- runBC' (CONST:i:xs) env stack               = runBC' xs env (I i:stack)
-- runBC' (ACCESS:i:xs) env stack              = runBC' xs env (env!!i:stack)
-- runBC' (FUNCTION:i:xs) env stack            =
--   let drop' = drop i xs
--       take' = take i xs
--   in runBC' drop' env (Fun env take':stack)
-- runBC' (CALL:xs) env (v:(Fun ef cf):stack)  = runBC' cf (v:ef) (RA env xs:stack)
-- runBC' (ADD:xs) env ((I i1):(I i2):stack)   = runBC' xs env (I (i1 + i2):stack)
-- runBC' (SUB:xs) env ((I i1):(I i2):stack)   = runBC' xs env (I (max 0 (i2 - i1)):stack)
-- runBC' (FIX:xs) env ((Fun ef cf):stack)     =
--   let envFix = Fun envFix cf:env
--   in runBC' xs env (Fun envFix cf:stack)
-- runBC' (STOP:xs) env (v:stack)              = return ()
-- runBC' (JUMP:i:xs) env stack                = runBC' (drop i xs) env stack
-- runBC' (SHIFT:xs) env (v:stack)             = runBC' xs (v:env) stack
-- runBC' (DROP:xs) (v:env) stack              = runBC' xs env stack
-- runBC' (PRINT:xs) env stack                 =
--   let (msg, _:xs') = span (/=NULL) xs
--       s = bc2string msg
--   in do printFD4nobreak s
--         runBC' xs' env stack
-- runBC' (PRINTN:xs) env s@(I i:stack)        =
--   do printFD4 (show i)
--      runBC' xs env s
-- runBC' (CJUMP:i:xs) env ((I c):stack)       =
--   case c of
--     0 -> runBC' xs env stack
--     _ -> runBC' (drop i xs) env stack
-- runBC' (TAILCALL:xs) env (v:(Fun ef cf):stack) =
--   runBC' cf (v:ef) stack

-- -- caso de fallo
-- runBC' i env stack = do
--   printFD4 $ show (showOps i)
--   printFD4 $ show env
--   printFD4 $ show stack
--   failFD4 "runBC': non-exhaustive patterns"

-- | Modulo
type Module = [Decl TTerm]

-- | Bytecompile
byte8compile :: MonadFD4 m => Module -> m Bytecode
byte8compile m = bc8 $ openModule m

-- | Traduce una lista de declaraciones en una unica expresion "let in"
openModule :: Module -> TTerm
openModule [Decl _ n _ t]      = global2free n t
openModule ((Decl i n ty t):xs) = Let (i, getTy t) n ty t (close n (global2free n (openModule xs))) -- ver si hace falta hacer global2free sobre 't'

-- | Cambia las variables globales por variables libres
global2free :: Name -> TTerm -> TTerm
global2free name = varChangerGlobal (\v p n -> if n == name then V p (Free n) else V p (Global n))
