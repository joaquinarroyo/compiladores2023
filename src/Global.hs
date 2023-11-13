{-|
Module      : Global
Description : Define el estado global del compilador
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}
module Global where

import Lang

{-
 Tipo para representar las banderas disponibles en línea de comando.
-}
data Mode =
    Interactive
  | Typecheck
  | Eval
  | InteractiveCEK
  | CEK
  | Bytecompile
  | Bytecompile8
  | RunVM
  | RunVM8
  | CC
  -- | Canon
  -- | Assembler
  -- | Build
  deriving Show

data Conf = Conf {
  opt :: Bool,          --  ^ True, si estan habilitadas las optimizaciones.
  pro :: Bool,          --  ^ True, si estaa habilitado el profilling.
  mode :: Mode
}

-- |
data GlEnv = GlEnv {
  inter :: Bool,        --  ^ True, si estamos en modo interactivo.
                        -- Este parámetro puede cambiar durante la ejecución:
                        -- Es falso mientras se cargan archivos, pero luego puede ser verdadero.
  lfile :: String,      -- ^ Último archivo cargado.
  cantDecl :: Int,      -- ^ Cantidad de declaraciones desde la última carga
  glb :: [Decl TTerm],  -- ^ Entorno con declaraciones globales
  tysin :: [SDecl],     -- ^ Entorno con declaraciones de sinonimos de tipos
  profile :: Profile    -- ^ Profile
}

-- | Entorno de tipado de declaraciones globales
tyEnv :: GlEnv ->  [(Name,Ty)]
tyEnv g = map (\(Decl _ n ty b) -> (n, ty))  (glb g)

-- | Entorno de sinonimos de tipos
tySinEnv :: GlEnv -> [(Name, Ty)]
tySinEnv g = map (\(DirectTypeDecl _ n ty) -> (n, ty))  (tysin g)

-- | Valor del estado inicial
initialEnv :: GlEnv
initialEnv = GlEnv False "" 0 [] [] NoneProfile

initialEnvWithProfile :: Mode -> GlEnv
initialEnvWithProfile m = GlEnv False "" 0 [] [] (getProfile m)

-- | Profile
data Profile = CEKProfile { cekSteps :: Int } | BytecodeProfile { bcOps :: Int, maxStackSize :: Int, clousures :: Int } | NoneProfile

instance Show Profile where
  show (CEKProfile n) = "CEK PROFILE: steps = " ++ show n
  show (BytecodeProfile n m k) = "Bytecode PROFILE: steps = " ++ show n ++ ", max stack size = " ++ show m ++ ", clousures = " ++ show k
  show NoneProfile = ""

getProfile :: Mode -> Profile
getProfile CEK = CEKProfile 0
getProfile RunVM = BytecodeProfile 0 0 0
getProfile RunVM8 = BytecodeProfile 0 0 0
getProfile _ = NoneProfile

tickProfile :: Profile -> Profile
tickProfile (CEKProfile n) = CEKProfile (n + 1)
tickProfile (BytecodeProfile n m k) = BytecodeProfile (n + 1) m k
tickProfile NoneProfile = NoneProfile

maxStackProfile :: Profile -> Int -> Profile
maxStackProfile (BytecodeProfile n m k) m' = BytecodeProfile n (max m m') k
maxStackProfile p _ = p

addClousureProfile :: Profile -> Int -> Profile
addClousureProfile (BytecodeProfile n m k) k' = BytecodeProfile n m (k + k')
addClousureProfile p _ = p