{-# LANGUAGE FlexibleContexts #-}

module Parse
  ( tlP, fomloP
  , ParseError, parseText, parseString
  )
where

import Data.Char
import Data.Functor (($>))
import Data.Functor.Identity
import Data.Text (Text)
import Text.Parsec
import qualified Data.Text as Text
import BooleanCombination
import FOMLO
import TL
import Util

--------------------------------------------------------------------------------
choiceTry :: Stream s m t => [ParsecT s u m a] -> ParsecT s u m a
choiceTry = choice . map try

parse_ :: Stream s Identity t => Parsec s () a -> s -> Either ParseError a
parse_ p = parse p ""

--------------------------------------------------------------------------------
manyTill1 :: Stream s m t => ParsecT s u m a -> ParsecT s u m end -> ParsecT s u m ([a], end)
manyTill1 p end = p >>= \x -> go (x :)
  where
    go k =  (try end >>= \e -> pure (k [], e))
        <|> (p >>= \x -> go (k . (x :)))

many2 :: Stream s m t => ParsecT s u m a -> ParsecT s u m [a]
many2 p = (:) <$> p <*> many1 p

list2 :: Stream s m Char => ParsecT s u m a -> ParsecT s u m [a]
list2 p = many2 (spaces *> p)

spaces1 :: Stream s m Char => ParsecT s u m ()
spaces1 = skipMany1 space

parens :: Stream s m Char => ParsecT s u m a -> ParsecT s u m a
parens p = spaces *> between (char '(' *> spaces) (spaces *> char ')') p

identifierP :: Stream s m Char => ParsecT s u m String
identifierP = many1 (satisfy (\c -> isAlphaNum c || elem c ("_-" :: [Char])))

predicateNameP :: Stream s m Char => ParsecT s u m String
predicateNameP = identifierP

variableNameP :: Stream s m Char => ParsecT s u m String
variableNameP = identifierP

bcP :: (Ord a) => Stream s m Char => ParsecT s u m a -> ParsecT s u m (BC a)
bcP primP = spaces *> choiceTry [ botP
                                , topP
                                , negP
                                , orP
                                , andP
                                , implP
                                , biimplP
                                , Prim <$> primP]
  where
    variadicOp names constructor = parens $ do
      _ <- choiceTry $ string <$> names
      constructor <$> many (spaces1 *> bcP primP)
    variadic1Op names constructor = parens $ do
      _ <- choiceTry $ string <$> names
      constructor <$> many1 (spaces1 *> bcP primP)
    botP = choiceTry (string <$> ["⊥", "bot", "Bot", "false", "False"]) $> bot
    topP = choiceTry (string <$> ["⊤", "top", "Top", "true", "True"]) $> top
    negP = parens $ do
      _ <- choiceTry $ string <$> ["¬", "not", "Not", "neg", "Neg"]
      spaces1
      Not <$> bcP primP
    orP = variadicOp ["∨", "or", "Or"] disjList
    andP = variadicOp ["∧", "and", "And"] conjList
    implP = variadic1Op ["→", "->", "implies", "Implies"] impl
    biimplP = variadic1Op ["↔", "<->"] biimpl

--------------------
simpleTlP :: Stream s m Char => ParsecT s u m (TL String)
simpleTlP = spaces *> choiceTry [ variableP
                                , sinceP
                                , untilP
                                , nextPastP
                                , nextP
                                , eventuallyPastP
                                , eventuallyP
                                , foreverPastP
                                , foreverP
                                ]
  where
    variableP = Var <$> predicateNameP
    binaryOpP names constructor = parens $ do
      _ <- choiceTry $ string <$> names
      constructor <$> (spaces1 *> tlP) <*> (spaces1 *> tlP)
    sinceP = binaryOpP ["since", "Since", "s", "S"] S
    untilP = binaryOpP ["until", "Until", "u", "U"] U
    unaryOp names constructor = parens $ do
      _ <- choiceTry $ string <$> names
      constructor <$> (spaces1 *> tlP)
    nextPastP = unaryOp ["●", "x-1", "X-1", "prev", "Prev"] nextPast
    nextP = unaryOp ["○", "x", "X", "next", "Next"] next
    eventuallyPastP = unaryOp ["⧫", "f-1", "F-1", "eventually-past", "Eventually-Past"] eventuallyPast
    eventuallyP = unaryOp ["◊", "f", "F", "eventually", "Eventually"] eventually
    foreverPastP = unaryOp ["■", "g", "G-1", "forever-past", "Forever-Past"] foreverPast
    foreverP = unaryOp ["□", "g", "G", "forever", "Forever"] forever

tlP :: Stream s m Char => ParsecT s u m (TL String)
tlP = bcJoin <$> bcP simpleTlP

--------------------
simpleFomloP :: Stream s m Char => ParsecT s u m (FOMLO String String)
simpleFomloP = spaces *> choiceTry [ equalP
                                   , lessThanP
                                   , lessEqP
                                   , greaterThanP
                                   , greaterEqP
                                   , existentialP
                                   , universalP
                                   , predicateP
                                   ]
  where
    binaryPredP names constructor = parens $ do
      _ <- choiceTry $ string <$> names
      args <- spaces *> list2 variableNameP
      pure $ conjList (zipWith constructor args (tail args))
    equalP = binaryPredP ["="] Eq
    lessThanP = binaryPredP ["<"] Less
    lessEqP = binaryPredP ["≤", "<="] (\x y -> Less x y ∨ Eq x y)
    greaterThanP = binaryPredP [">"] (flip Less)
    greaterEqP = binaryPredP ["≥", ">="] (\x y -> Eq x y ∨ Less y x)
    quantifierP names constructor = parens $ do
      _ <- choiceTry $ string <$> names
      spaces
      (vars, body) <- manyTill1 (spaces *> variableNameP) fomloP
      pure $ ($ body) . foldl1' (.) . map constructor $ vars
    existentialP = quantifierP ["∃", "exists", "Exists"] Exists
    universalP = quantifierP ["∀", "forall", "Forall"] Forall
    predicateP = parens (Pred <$> (spaces *> predicateNameP) <*> (spaces *> variableNameP))

fomloP :: Stream s m Char => ParsecT s u m (FOMLO String String)
fomloP = bcJoin <$> bcP simpleFomloP

--------------------------------------------------------------------------------
parseText :: Parsec String () a -> Text -> Either ParseError a
parseText p = parse_ p . Text.unpack

parseString :: Parsec String () a -> String -> Either ParseError a
parseString = parse_
