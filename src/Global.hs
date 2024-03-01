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
  tysin :: [SDecl]      -- ^ Entorno con declaraciones de sinonimos de tipos
} deriving Show

-- | Entorno de tipado de declaraciones globales
tyEnv :: GlEnv ->  [(Name,Ty)]
tyEnv g = map (\(Decl _ n ty b) -> (n, ty))  (glb g)

-- | Entorno de sinonimos de tipos
tySinEnv :: GlEnv -> [(Name, Ty)]
tySinEnv g = map (\(DirectTypeDecl _ n ty) -> (n, ty))  (tysin g)

-- | Valor del estado inicial
initialEnv :: GlEnv
initialEnv = GlEnv False "" 0 [] []

-- | Profile
data Profile = CEKProfile { cekSteps :: Int } | BytecodeProfile { bcOps :: Int, maxStackSize :: Int, clousures :: Int } | NoneProfile

instance Semigroup Profile where
  (<>) = mappend

instance Monoid Profile where
  mempty = NoneProfile
  mappend NoneProfile p = p
  mappend p NoneProfile = p
  mappend (CEKProfile n) (CEKProfile m) = CEKProfile (n + m)
  mappend (BytecodeProfile n m k) (BytecodeProfile n' m' k') = BytecodeProfile (n + n') (max m m') (k + k')

instance Show Profile where
  show (CEKProfile n) = "CEK PROFILE: steps = " ++ show n
  show (BytecodeProfile n m k) = "Bytecode PROFILE: steps = " ++ show n ++ ", max stack size = " ++ show m ++ ", clousures = " ++ show k
  show NoneProfile = ""

getProfile :: Mode -> Profile
getProfile CEK = CEKProfile 0
getProfile RunVM = BytecodeProfile 0 0 0
getProfile RunVM8 = BytecodeProfile 0 0 0
getProfile _ = NoneProfile

tickProfile :: Mode -> Profile
tickProfile CEK = CEKProfile 1
tickProfile RunVM = BytecodeProfile 1 0 0
tickProfile RunVM8 = BytecodeProfile 1 0 0
tickProfile _ = NoneProfile

maxStackProfile :: Mode -> Int -> Profile
maxStackProfile RunVM s = BytecodeProfile 0 s 0
maxStackProfile RunVM8 s = BytecodeProfile 0 s 0
maxStackProfile m _ = NoneProfile

addClousureProfile :: Mode -> Int -> Profile
addClousureProfile RunVM c = BytecodeProfile 0 0 c
addClousureProfile RunVM8 c = BytecodeProfile 0 0 c
addClousureProfile m _ = NoneProfile