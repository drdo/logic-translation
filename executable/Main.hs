{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiWayIf #-}

import Control.Exception
import Data.Functor (($>))
import Data.List (intercalate)
import System.Console.GetOpt
import System.Environment
import Text.Parsec
import Parse
import Pretty
import Separation
import Translation

--------------------------------------------------------------------------------
instance Exception ParseError

data Flags
  = Help
  | NoSimplification
  | Sep
  | Translate
  | TranslateLTL
  deriving
    (Eq, Show)

optionDescription :: [OptDescr Flags]
optionDescription =
  [ Option ['h'] ["help"] (NoArg Help) "Help"
  , Option ['n'] ["no-simplification"] (NoArg NoSimplification) "Disable simplification"
  , Option ['s'] ["sep"] (NoArg Sep) "Run the Sep algorithm"
  , Option ['t'] ["translate"] (NoArg Translate) "Run the Translate algorithm"
  , Option ['l'] ["translateLTL"] (NoArg TranslateLTL) "Run the TranslateLTL algorithm"
  ]

main :: IO ()
main = do
  (options, _, _) <- getOpt Permute optionDescription <$> getArgs
  let mkParser p = spaces *> choice [ eof $> Nothing
                                    , Just <$> ((,) <$> p <*> getInput) ]
      sepAlg = if NoSimplification `elem` options
               then sep
               else sepWithSimplify
      translateAlg = if NoSimplification `elem` options
                     then translate
                     else translateWithSimplify
      translateLTLAlg = if NoSimplification `elem` options
                        then translateLTL
                        else translateLTLWithSimplify
      loop parser alg printSeparator str = case parseString parser str of
        Left e -> throwIO e
        Right Nothing -> pure ()
        Right (Just (x, str')) -> do
          let y = alg x
          printSeparator
          putStrLn . ppTL $ y
          loop parser alg (putStrLn "") str'
  if Help `elem` options
    then let headerLines =
               [ "Reads formulas from standard input and outputs to standard output."
               , "The default is to run the Translate algorithm with simplification."
               , ""
               , "Formulas in both TL and FOMLO are denoted by s-expressions."
               , "  Available Boolean operators:"
               , "    - False. Names: ⊥, bot, Bot, false, False"
               , "    - True. Names: ⊤, top, Top, true, True"
               , "    - Negation (unary). Names: ¬, not, Not, neg, Neg"
               , "    - Disjunction (any number of arguments). Names: ∨, or, Or"
               , "    - Conjunction (any number of arguments). Names: ∧, and, And"
               , "    - Implication (at least one argument). Names: →, ->, implies, Implies"
               , "    - Bi-implication (at least one argument). Names: ↔, <->"
               , "  Available TL operators:"
               , "    - Variable. String consisting of alphanumeric characters"
               , "    - Since. Names: since, Since, s, S"
               , "    - Until. Names: until, Until, u, U"
               , "    - Previous. Names: ●, x-1, X-1, prev, Prev"
               , "    - Next. Names: ○, x, X, next, Next"
               , "    - Eventually in the past. Names: ⧫, f-1, F, eventually-past, Eventually-Past"
               , "    - Eventually. Names: ◊, f, F, eventually, Eventually"
               , "    - Forever in the past. Names: ■, g-1, G-1, forever-past, Forever-Past"
               , "    - Forever. Names: □, g, G, forever, Forever"
               , "  Available FOMLO operators:"
               , "    - Predicate (one alphanumeric variable).\
                 \ The predicate name itself is also a string of alphanumeric characters.\
                 \ Example: (P x)"
               , "    - Equality (at least two arguments). Names: ="
               , "    - Less (at least two arguments). Names: <"
               , "    - Less or equal (at least two arguments). Names: ≤, <="
               , "    - Greater (at least two arguments). Names: >"
               , "    - Greater or equal (at least two arguments). Names: ≥, >="
               , "    - Existential (one or more alphanumeric variables followed by a formula).\
                 \ Names: ∃, exists, Exists"
               , "    - Universal (one or more alphanumeric variables followed by a formula).\
                 \ Names: ∀, forall, Forall"
               , "  Examples:"
               , "    - FOMLO: (∀ x y z (→ (∧ (< x y) (< y z)) (< x z)))\
                 \ is a formula denoting transitivity"
               , "    - TL: (→ E1 (∧ (¬ E2) (Until (¬ E2) L1)))"
               , "Options:"
               ]
             header = intercalate "\n" headerLines
         in putStr $ usageInfo header optionDescription
    else getContents >>= if | Translate `elem` options ->
                                loop (mkParser fomloP) translateAlg (pure ())
                            | TranslateLTL `elem` options ->
                                loop (mkParser fomloP) translateLTLAlg (pure ())
                            | Sep `elem` options ->
                                loop (mkParser tlP) sepAlg (pure ())
                            | otherwise ->
                                loop (mkParser fomloP) translateAlg (pure ())
