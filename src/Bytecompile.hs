{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-|
Module      : Bytecompile
Description : Compila a bytecode. Ejecuta bytecode.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo permite compilar módulos a la Macchina. También provee
una implementación de la Macchina para ejecutar el bytecode.
-}
module Bytecompile
  (Bytecode, runBC, bcWrite, bcRead, bytecompileModule, showBC)
 where

import Lang
import MonadFD4

import qualified Data.ByteString.Lazy as BS
import Data.Binary ( Word32, Binary(put, get), decode, encode )
import Data.Binary.Put ( putWord32le )
import Data.Binary.Get ( getWord32le, isEmpty )

import Data.List (intercalate)
import Data.Char

type Opcode = Int
type Bytecode = [Int]

newtype Bytecode32 = BC { un32 :: [Word32] }

{- Esta instancia explica como codificar y decodificar Bytecode de 32 bits -}
instance Binary Bytecode32 where
  put (BC bs) = mapM_ putWord32le bs
  get = go
    where go =
           do
            empty <- isEmpty
            if empty
              then return $ BC []
              else do x <- getWord32le
                      BC xs <- go
                      return $ BC (x:xs)

{- Estos sinónimos de patrón nos permiten escribir y hacer
pattern-matching sobre el nombre de la operación en lugar del código
entero, por ejemplo:

   f (CALL : cs) = ...

 Notar que si hubieramos escrito algo como
   call = 5
 no podríamos hacer pattern-matching con `call`.

 En lo posible, usar estos códigos exactos para poder ejectutar un
 mismo bytecode compilado en distintas implementaciones de la máquina.
-}
pattern NULL     = 0
pattern RETURN   = 1
pattern CONST    = 2
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
-- |
pattern IFZ      = 16

--función util para debugging: muestra el Bytecode de forma más legible.
showOps :: Bytecode -> [String]
showOps [] = []
showOps (NULL:xs)        = "NULL" : showOps xs
showOps (RETURN:xs)      = "RETURN" : showOps xs
showOps (CONST:i:xs)     = ("CONST " ++  show i) : showOps xs
showOps (ACCESS:i:xs)    = ("ACCESS " ++ show i) : showOps xs
showOps (FUNCTION:i:xs)  = ("FUNCTION len=" ++ show i) : showOps xs
showOps (CALL:xs)        = "CALL" : showOps xs
showOps (ADD:xs)         = "ADD" : showOps xs
showOps (SUB:xs)         = "SUB" : showOps xs
showOps (FIX:xs)         = "FIX" : showOps xs
showOps (STOP:xs)        = "STOP" : showOps xs
showOps (JUMP:i:xs)      = ("JUMP off=" ++ show i) : showOps xs
showOps (SHIFT:xs)       = "SHIFT" : showOps xs
showOps (DROP:xs)        = "DROP" : showOps xs
showOps (PRINT:xs)       = let (msg,_:rest) = span (/=NULL) xs
                           in ("PRINT " ++ show (bc2string msg)) : showOps rest
showOps (PRINTN:xs)      = "PRINTN" : showOps xs
showOps (ADD:xs)         = "ADD" : showOps xs
showOps (x:xs)           = show x : showOps xs

showBC :: Bytecode -> String
showBC = intercalate "; " . showOps

bcc :: MonadFD4 m => TTerm -> m Bytecode
bcc t = failFD4 "implementame!"

-- ord/chr devuelven los codepoints unicode, o en otras palabras
-- la codificación UTF-32 del caracter.
string2bc :: String -> Bytecode
string2bc = map ord

bc2string :: Bytecode -> String
bc2string = map chr

bytecompileModule :: MonadFD4 m => Module -> m Bytecode
bytecompileModule m = failFD4 "implementame!"

-- | Toma un bytecode, lo codifica y lo escribe un archivo
bcWrite :: Bytecode -> FilePath -> IO ()
bcWrite bs filename = BS.writeFile filename (encode $ BC $ fromIntegral <$> bs)

---------------------------
-- * Ejecución de bytecode
---------------------------

-- | Lee de un archivo y lo decodifica a bytecode
bcRead :: FilePath -> IO Bytecode
bcRead filename = (map fromIntegral <$> un32) . decode <$> BS.readFile filename

runBC :: MonadFD4 m => Bytecode -> m ()
runBC bs = failFD4 "implementame!"

-- | Transforma un Term en Bytecode
bc :: MonadFD4 m => Term -> m Bytecode
bc (V _ (Bound i)) = return (ACCESS:i)
bc (V _ (Global n)) = do
  mt <- lookupDecl n
  case mt of
    Just t -> seek' t env kont
    Nothing -> failFD4 "seek: no deberia llegar una variable global que no este en el entorno"
bc (Const _ (CNat n)) = return (CONST:n)
bc (Lam _ _ _ (Sc1 t)) = do
  t' <- bc t
  return (FUNCTION:i:t':RETURN)
  where
    i = length t'
bc (App _ t1 t2) = do
  t1' <- bc t1
  t2' <- bc t2
  return (t1':t2':CALL)
bc (Print _ s t) = do
  t' <- bc t
  return (PRINT:s':NULL)
  where
    s' = string2bc s
bc (BinaryOp _ op t1 t2) = do
  t1' <- bc t1
  t2' <- bc t2
  case op of
    Add -> return (t1':t2':ADD)
    Sub -> return (t1':t2':SUB)
bc (Fix _ _ _ _ _ (Sc2 t)) = do
  t' <- bc t
  return (FUNCTION:i:t':RETURN:FIX) -- REVISAR
  where
    i = length t'
bc (IfZ _ t1 t2 t3) = do
  t1' <- bc t1
  t2' <- bc t2
  t3' <- bc t3
  return (IFZ:t1':i:t2':t3') -- ver de usar JUMP (?)
  where
    i = length t2'
bc (Let _ n ty t1 (Sc1 t2)) = do
  t1' <- bc t1
  t2' <- bc t2
  return (t1':SHIFT:t2':DROP)

-- | 
data ValBytecode =
    I Const
  | Fun Env Bytecode
  | RA Env Bytecode
  deriving Show

type Env = [ValBytecode]

runBC' :: MonadFD4 m => Bytecode -> Env -> [ValBytecode] -> m ()
runBC' (RETURN:_) _ (v:(RA e c):env) = runBC' c e (v:stack)  
runBC' (CONST:i:xs) env stack = runBC' xs env ((I i):stack)
runBC' (ACCESS:i:xs) env stack = runBC' xs env (env!!i:stack)
runBC' (FUNCTION:i:xs) env stack = runBC' drop env (Fun env take:stack)
  where
    drop = drop i xs
    take = take i xs
runBC' (CALL:xs) env (v:(Fun ef cf)) = runBC' cf (v:ef) (RA env xs:stack)
runBC' (ADD:xs) env ((I i1):(I i2):stack) = runBC' xs env (i1 + i2:stack) 
runBC' (SUB:xs) env ((I i1):(I i2):stack) | i1 > i2 = runBC' xs env (i1 - i2:stack)
                                          | otherwise = runBC' xs env (0:stack) 
runBC' (FIX:xs) env stack = failFD4 "Implementar: FIX"
runBC' (STOP:xs) env (v:stack) = do
  printFD4 v
  return () -- 
runBC' (JUMP:i:xs) env stack = runBC' (drop i xs) env stack -- chequear
runBC' (SHIFT:xs) env (v:stack) = runBC' xs (v:env) stack 
runBC' (DROP:xs) (v:env) stack = runBC' xs env stack  
runBC' (PRINT:xs) env stack = do
  let (msg,_:xs') = span (/=NULL) xs
  printFD4 $ bc2string msg
  runBC' xs' env stack
runBC' (PRINTN:xs) env s@(v:stack)= do
  printFD4 v
  runBC' xs env s
runBC (IFZ:xs) env stack = failFD4 "Implementar:IFZ"
