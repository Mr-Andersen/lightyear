-- ------------------------------------------------------------- [ Strings.idr ]
-- Module      : Lightyear.Strings
-- Description : String-related parsers.
--
-- This code is distributed under the BSD 2-clause license.
-- See the file LICENSE in the root directory for its full text.
-- --------------------------------------------------------------------- [ EOH ]
module Lightyear.Strings

import        Data.List
import public Data.Fin
import public Data.Vect
import        Data.String

import public Control.Monad.Identity

import Lightyear.Position
import Lightyear.Core
import Lightyear.Combinators

import Lightyear.Char

-- %access export

-- --------------------------------------------------------- [ A String Parser ]
||| Parsers, specialised to Strings
public export
Parser : Type -> Type
Parser = ParserT String Identity

||| Run a parser against an input string
export
parseGeneric : (src_ident : Maybe String)
            -> (tab_width : Nat)
            -> (parser    : Parser a)
            -> (source    : String)
            -> Either String a
parseGeneric src tw f s = let Id r = execParserT f (initialState src s tw)
                           in case r of
                               MkReply _ (Success x)  => Right x
                               MkReply _ (Failure es) => Left $ concat $ intersperse "\n" $ map display es

||| Run a parser against an input string with a custom tab-width.
export
parseCustom : (tab_width : Nat)
           -> (parser    : Parser a)
           -> (source    : String)
           -> Either String a
parseCustom = parseGeneric Nothing


||| Run a parser against an input string assuming that tab-widths are
||| eight characters in length.
export
parse : (parser : Parser a)
     -> (source : String)
     -> Either String a
parse = parseGeneric Nothing 8

namespace File

  ||| Run a parser against an input string taken from the named file
  ||| with a custom tab-width.
  export
  parseCustom : (fname     : String)
             -> (tab_width : Nat)
             -> (parser    : Parser a)
             -> (source    : String)
             -> Either String a
  parseCustom fname = parseGeneric (Just fname)


  ||| Run a parser against an input string taken from the named file,
  ||| such that tab-widths are assumed to be eight characters in
  ||| length.
  export
  parse : (fname  : String)
       -> (parser : Parser a)
       -> (source : String)
       -> Either String a
  parse fname = parseGeneric (Just fname) 8


public export
implementation Stream Char String where
  uncons s with (strM s)
    uncons ""             | StrNil       = Nothing
    uncons (strCons x xs) | StrCons x xs = Just (x, xs)
  updatePos tw pos tk = (increment tw pos tk, pos)

-- ---------------------------------------------------------- [ Reserved Stuff ]

||| A parser that matches a particular string
export
string : Monad m => String -> ParserT String m String
string s = pack <$> (traverse char $ unpack s) <?> "string " ++ show s

-- ------------------------------------------------------------------- [ Space ]

||| A simple lexer that strips white space from tokens
export
lexeme : Monad m => ParserT String m a -> ParserT String m a
lexeme p = p <* spaces

-- ------------------------------------------------------------------ [ Tokens ]

||| A parser that matches a specific string, then skips following whitespace
export
token : Monad m => String -> ParserT String m ()
token s = lexeme (skip (string s)) <?> "token " ++ show s

||| Parses ',' and trailing whitespace.
export
comma : Monad m => ParserT String m ()
comma = token "," <?> "Comma"

||| Parses '=' and trailing whitespace.
export
equals : Monad m => ParserT String m ()
equals = token "=" <?> "equals"

||| Parses '.' and trailing whitespace.
export
dot : Monad m => ParserT String m ()
dot = token "." <?> "dot"

||| Parses ':' and trailing whitespace.
export
colon : Monad m => ParserT String m ()
colon = token ":" <?> "colon"

||| Parses ';' and trailing whitespace.
export
semi : Monad m => ParserT String m ()
semi = token ";" <?> "semi colon"

-- -------------------------------------------------- [ Delineated Expressions ]

||| Parses `p` enclosed in parentheses and returns result of `p`.
export
parens : Monad m => ParserT String m a -> ParserT String m a
parens p = between (token "(") (token ")") p

||| Parses `p` enclosed in brackets and returns result of `p`.
export
brackets : Monad m => ParserT String m a -> ParserT String m a
brackets p = between (token "[") (token "]") p

||| Parses `p` enclosed in braces and returns the result of `p`.
export
braces : Monad m => ParserT String m a -> ParserT String m a
braces p = between (token "{") (token "}") p

||| Parses `p` enclosed in angles and returns the result of `p`.
export
angles : Monad m => ParserT String m a -> ParserT String m a
angles p = between (token "<") (token ">") p

||| Parses `p` enclosed in single quotes and returns the result of `p`.
||| Not to be used for charLiterals.
export
squote : Monad m => ParserT String m a -> ParserT String m a
squote p = between (char '\'') (lexeme $ char '\'') p

||| Parses `p` enclosed in double quotes and returns the result of `p`.
||| Not to be used for `stringLiterals`.
export
dquote : Monad m => ParserT String m a -> ParserT String m a
dquote p = between (char '\"') (lexeme $ char '\"') p

||| Collect the literal string contained between two characters
export
quoted' : Monad m => Char -> Char -> ParserT String m String
quoted' l r = map pack $ between (char l) (lexeme $ char r) (some (satisfy (/= r)))

||| Literal string between two identical characters
export
quoted : Monad m => Char -> ParserT String m String
quoted c = quoted' c c

-- --------------------------------------------------- [ Separated Expressions ]
||| Parses /one/ or more occurrences of `p` separated by `comma`.
export
commaSep1 : Monad m => ParserT String m a -> ParserT String m (List a)
commaSep1 p = p `sepBy1` comma

||| Parses /zero/ or more occurrences of `p` separated by `comma`.
export
commaSep : Monad m => ParserT String m a -> ParserT String m (List a)
commaSep p = p `sepBy` comma

||| Parses /one/ or more occurrences of `p` separated by `semi`.
export
semiSep1 : Monad m => ParserT String m a -> ParserT String m (List a)
semiSep1 p = p `sepBy1` semi

||| Parses /zero/ or more occurrences of `p` separated by `semi`.
export
semiSep : Monad m => ParserT String m a -> ParserT String m (List a)
semiSep p = p `sepBy` semi

||| Run some parser `p` until the second parser is encountered,
||| collecting a list of success for `p`, and the result of the second
||| parser is dropped.
|||
||| Primarily useful for collecting single line comments and other
||| similar verbatim environments.
export
manyTill : Monad m => ParserT String m a
                   -> ParserT String m b
                   -> ParserT String m (List a)
manyTill p end = scan
  where
    scan : ParserT String m (List a)
    scan = do { _ <- end; pure [] } <|>
           do { x <- p; xs <- scan; pure (x::xs)}


-- -------------------------------------------------------- [ Testing Function ]

testParser : Parser a -> String -> IO (Maybe a)
testParser p s = case parse p s of
  Left  e => putStrLn e *> pure Nothing
  Right x => pure (Just x)
-- --------------------------------------------------------------------- [ EOF ]
