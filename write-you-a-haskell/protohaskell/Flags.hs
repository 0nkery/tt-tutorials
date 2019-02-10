module Flags (
  Flag(..),
  Flags,

  isSet,
  set,
  unset,

  flagOpts,
  flagFor
) where

import           Control.Monad (msum)
import           Data.List     (isPrefixOf)
import qualified Data.Set      as S

type Flags = S.Set Flag

data Flag
  = DumpC
  | DumpLLVM
  | DumpASM
  | DumpParsed
  | DumpDesugar
  | DumpInfer
  | DumpCore
  | DumpTypes
  | DumpKinds
  | DumpStg
  | DumpImp
  | DumpRenamer
  | DumpToFile
  deriving (Eq, Ord, Show)

isSet :: Flags -> Flag -> Bool
isSet = flip S.member

set :: Flags -> Flag -> Flags
set = flip S.insert

unset :: Flags -> Flag -> Flags
unset = flip S.delete

flags :: [(String, Flag)]
flags = [
    ("ddump-parsed", DumpParsed),
    ("ddump-ds", DumpDesugar),
    ("ddump-core", DumpCore),
    ("ddump-infer", DumpInfer),
    ("ddump-types", DumpTypes),
    ("ddump-kinds", DumpKinds),
    ("ddump-stg", DumpStg),
    ("ddump-imp", DumpImp),
    ("ddump-c", DumpC),
    ("ddump-rn", DumpRenamer),
    ("ddump-to-file", DumpToFile)
  ]

matches :: String -> (String, Flag) -> Maybe Flag
matches s (flagstr, flag)
  | ('-' : flagstr) `isPrefixOf` s = Just flag
  | otherwise = Nothing

flagOpts :: [String]
flagOpts = fmap fst flags

flagFor :: String -> Maybe Flags.Flag
flagFor s = msum $ fmap (matches s) flags
