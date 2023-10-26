module Optimizer where
import MonadFD4 (MonadFD4)
import Lang (TTerm, Decl (..))

maxIt :: Int
maxIt = 10

optimize :: MonadFD4 m => Decl TTerm -> m (Decl TTerm)
optimize d = do
    o <- optimize' maxIt (declBody d)
    return $ d {declBody = o}

optimize' :: MonadFD4 m => Int -> TTerm -> m TTerm
optimize' 0 t = return t
optimize' i t = constantFolding t >>= constantPropagation >>= optimize' (i - 1)

constantFolding :: MonadFD4 m => TTerm ->  m TTerm
constantFolding = return

constantPropagation :: MonadFD4 m => TTerm ->  m TTerm
constantPropagation = return