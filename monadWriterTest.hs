module MonadWriterTest where

-- From http://learnyouahaskell.com/for-a-few-monads-more
-- This example no longer works without tweaking - see
-- http://stackoverflow.com/questions/11684321/how-to-play-with-control-monad-writer-in-haskell
-- just replace the data constructor "Writer" with the function "writer" in the line marked "here"
-- That changed with mtl going from major version 1.* to 2.*, shortly after LYAH and RWH were written

import Control.Monad.Writer

-- |
data Profile = CEKProfile { cekSteps :: Int } | BytecodeProfile { bcOps :: Int, maxStackSize :: Int, totalClousures :: Int } | NoneProfile deriving Show

instance Semigroup Profile where
    (<>) = mappend

instance Monoid Profile where
    mempty = NoneProfile
    mappend NoneProfile p = p
    mappend p NoneProfile = p
    mappend (CEKProfile s1) (CEKProfile s2) = CEKProfile (s1 + s2)
    mappend (BytecodeProfile o1 s1 c1) (BytecodeProfile o2 s2 c2) = BytecodeProfile (o1 + o2) (max s1 s2) (c1 + c2)
    mappend (CEKProfile s1) (BytecodeProfile o2 s2 c2) = BytecodeProfile o2 (max s1 s2) c2
    mappend (BytecodeProfile o1 s1 c1) (CEKProfile s2) = BytecodeProfile o1 (max s1 s2) c1

tick :: Profile -> Writer Profile Profile  
tick p = writer (p, p { cekSteps = cekSteps p + 1 })      
      
multWithLog :: Profile -> Writer Profile Profile  
multWithLog p = tick p >>= tick >>= tick >>= return
    
main :: IO ()
main = print $ runWriter (multWithLog (CEKProfile 0))