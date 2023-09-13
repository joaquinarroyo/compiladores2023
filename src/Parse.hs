{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use <$>" #-}
{-|
Module      : Parse
Description : Define un parser de términos FD40 a términos fully named.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module Parse (tm, Parse.parse, sdecl, runP, P, program, declOrTm) where

import Prelude hiding ( const )
import Lang hiding (getPos)
import Common
import Text.Parsec hiding (runP,parse)
--import Data.Char ( isNumber, ord )
import qualified Text.Parsec.Token as Tok
import Text.ParserCombinators.Parsec.Language --( GenLanguageDef(..), emptyDef )
import qualified Text.Parsec.Expr as Ex
import Text.Parsec.Expr (Operator, Assoc)
import Control.Monad.Identity (Identity)

type P = Parsec String ()

-----------------------
-- Lexer
-----------------------
-- | Analizador de Tokens
lexer :: Tok.TokenParser u
lexer = Tok.makeTokenParser langDef

langDef :: LanguageDef u
langDef = emptyDef {
         commentLine    = "#",
         reservedNames = ["let", "rec","fun", "fix", "then", "else","in",
                           "ifz", "print","Nat","type"],
         reservedOpNames = ["->",":","=","+","-"]
        }

whiteSpace :: P ()
whiteSpace = Tok.whiteSpace lexer

natural :: P Integer
natural = Tok.natural lexer

stringLiteral :: P String
stringLiteral = Tok.stringLiteral lexer

parens :: P a -> P a
parens = Tok.parens lexer

identifier :: P String
identifier = Tok.identifier lexer

reserved :: String -> P ()
reserved = Tok.reserved lexer

reservedOp :: String -> P ()
reservedOp = Tok.reservedOp lexer

tyIdentifier :: P String
tyIdentifier = Tok.lexeme lexer $ do
  c  <- upper
  cs <- many (identLetter langDef)
  return (c:cs)

-----------------------
-- Parsers
-----------------------

num :: P Int
num = fromInteger <$> natural

var :: P Name
var = identifier

getPos :: P Pos
getPos = do pos <- getPosition
            return $ Pos (sourceLine pos) (sourceColumn pos)

tyatom :: P Ty
tyatom = (reserved "Nat" >> return (NatTy Nothing))
         <|> try (parens typeP)
         <|> do 
          n <- var
          return (SynTy n)

typeP :: P Ty
typeP = try (do
          x <- tyatom
          reservedOp "->"
          y <- typeP
          return (FunTy x y Nothing))
      <|> try tyatom

const :: P Const
const = CNat <$> num

printOp :: P STerm
printOp = do
  i <- getPos
  reserved "print"
  str <- option "" stringLiteral
  a <- atom
  return (SPrint i str a)

binary :: String -> BinaryOp -> Assoc -> Operator String () Identity STerm
binary s f = Ex.Infix (reservedOp s >> return (SBinaryOp NoPos f))

table :: [[Operator String () Identity STerm]]
table = [[binary "+" Add Ex.AssocLeft,
          binary "-" Sub Ex.AssocLeft]]

expr :: P STerm
expr = Ex.buildExpressionParser table tm

atom :: P STerm
atom =     (flip SConst <$> const <*> getPos)
       <|> flip SV <$> var <*> getPos
       <|> parens expr
       <|> printOp

-- parsea un par (variable : tipo)
binding :: P (Name, Ty)
binding = do v <- var
             reservedOp ":"
             ty <- typeP
             return (v, ty)

multipleBinding :: P [(Name, Ty)]
multipleBinding = many1 (parens binding)

functionBinding :: P (Name, Ty, [(Name, Ty)])
functionBinding = do v <- var
                     bs <- multipleBinding
                     reservedOp ":"
                     ty <- typeP
                     return (v, ty, bs)

lam :: P STerm
lam = do i <- getPos
         reserved "fun"
         bs <- multipleBinding
         reservedOp "->"
         t <- expr
         case bs of
            [b] -> return (SLam i b t)
            _   -> return (SSugarLam i bs t)

-- Nota el parser app también parsea un solo atom.
app :: P STerm
app = do i <- getPos
         f <- atom
         args <- many atom
         return (foldl (SApp i) f args)

ifz :: P STerm
ifz = do i <- getPos
         reserved "ifz"
         c <- expr
         reserved "then"
         t <- expr
         reserved "else"
         e <- expr
         return (SIfZ i c t e)

fix :: P STerm
fix = do
  i <- getPos
  reserved "fix"
  (f, fty) <- parens binding
  xs <- many1 (parens binding)
  reservedOp "->"
  t <- expr
  case xs of
    [x] -> return (SFix i (f,fty) x t)
    _   -> return (SSugarFix i (f,fty) xs t)

letexp :: P STerm
letexp = try commonLet
  <|> try sugarLet
  <|> sugarLetRec

commonLet :: P STerm
commonLet = do
  i <- getPos
  reserved "let"
  (v,ty) <- try binding <|> parens binding
  reservedOp "="
  def <- expr
  reserved "in"
  body <- expr
  return (SLet i (v,ty) def body)

sugarLet :: P STerm
sugarLet = do
  i <- getPos
  reserved "let"
  (v, ty, bs) <- functionBinding
  reservedOp "="
  p <- getPos
  def <- expr
  reserved "in"
  body <- expr
  return (SSugarLet i (v,ty) bs def body)

sugarLetRec :: P STerm
sugarLetRec = do
  i <- getPos
  reserved "let"
  reserved "rec"
  (v, ty, bs) <- functionBinding
  reservedOp "="
  p <- getPos
  def <- expr
  reserved "in"
  body <- expr
  return (SSugarLetRec i (v,ty) bs def body)

-- | Parser de términos
tm :: P STerm
tm = app <|> lam <|> ifz <|> printOp <|> fix <|> letexp

-- | Parser de declaraciones superficiales y sinonimos de tipos
sdecl :: P SDecl
sdecl = try recDecl
    <|> try noRecDecl
    <|> stype

noRecDecl :: P SDecl
noRecDecl = do
    i <- getPos
    reserved "let"
    (v, ty, bs) <- try declArgsBinding <|> parens declArgsBinding
    reservedOp "="
    t <- expr
    return (SDecl i v ty bs t False)

recDecl :: P SDecl
recDecl = do
     i <- getPos
     reserved "let"
     reserved "rec"
     (v, ty, bs) <- declArgsBinding
     reservedOp "="
     t <- expr
     return (SDecl i v ty bs t True)

declArgsBinding :: P (Name, Ty, [(Name, Ty)])
declArgsBinding = do v <- var
                     bs <- many (parens binding)
                     reservedOp ":"
                     ty <- typeP
                     return (v, ty, bs)

-- | Parser de sinonimos de tipos
stype :: P SDecl
stype = do
  p <- getPos
  reserved "type"
  n <- var
  reserved "="
  ty <- typeP
  case ty of
    ts@(SynTy refTy) -> return (IndirectTypeDecl p n ts)
    (NatTy _) -> return (DirectTypeDecl p n (NatTy (Just n)))
    f@(FunTy a b _) -> case checkDirect f of
                        False -> return (DirectTypeDecl p n (FunTy a b (Just n)))
                        True -> return (IndirectTypeDecl p n (FunTy a b (Just n)))
    where
      checkDirect (FunTy (SynTy _) _ _) = True
      checkDirect (FunTy _ (SynTy _) _) = True
      checkDirect (FunTy f1@(FunTy {}) f2@(FunTy {}) _) = checkDirect f1 && checkDirect f2
      checkDirect (FunTy f1@(FunTy {}) _ _) = checkDirect f1
      checkDirect (FunTy _ f2@(FunTy {}) _) = checkDirect f2
      checkDirect _ = False


-- | Parser de programas (listas de declaraciones) 
program :: P [SDecl]
program = many sdecl

-- | Parsea una declaración a un término
-- Útil para las sesiones interactivas
declOrTm :: P (Either SDecl STerm)
declOrTm =  try (Left <$> sdecl) <|> (Right <$> expr)

-- Corre un parser, chequeando que se pueda consumir toda la entrada
runP :: P a -> String -> String -> Either ParseError a
runP p s filename = runParser (whiteSpace *> p <* eof) () filename s

--para debugging en uso interactivo (ghci)
parse :: String -> STerm
parse s = case runP expr s "" of
            Right t -> t
            Left e -> error ("no parse: " ++ show s)



