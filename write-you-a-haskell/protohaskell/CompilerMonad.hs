{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module CompilerMonad (
  CompilerM,
  runCompilerM,
  CompilerState(..),
  emptyCompilerState,
  Pos,
  Msg,
  inIO,
  ifSet
) where

import           Control.Applicative
import           Control.Monad.Except
import           Control.Monad.State
import           Data.Monoid
import qualified Data.Text.Lazy       as L

import qualified Flags
import qualified Frontend             as Syn

-- Compiler monad

type CompilerMonad = ExceptT Msg (StateT CompilerState IO)

newtype CompilerM a = Compiler { runCompiler :: CompilerMonad a }
  deriving (
    Functor,
    Applicative,
    Alternative,
    Monad,
    MonadFix,
    MonadPlus,
    MonadIO,
    MonadState CompilerState,
    MonadError Msg
  )

-- Compiler state

data CompilerState = CompilerState {
  _fname   :: Maybe FilePath,
  _imports :: [FilePath],
  _src     :: Maybe L.Text,
  _ast     :: Maybe Syn.Module,
  _flags   :: Flags.Flags
} deriving (Eq, Show)

emptyCompilerState :: CompilerState
emptyCompilerState = CompilerState {
  _fname = Nothing,
  _imports = mempty,
  _src = Nothing,
  _ast = Nothing,
  _flags = mempty
}

-- Types

type Pos = String

type Msg = String

runCompilerM :: CompilerM a -> CompilerState -> IO (Either Msg a, CompilerState)
runCompilerM = runStateT . runExceptT . runCompiler

inIO :: IO a -> CompilerM a
inIO = Compiler . liftIO

ifSet :: Flags.Flag -> CompilerM a -> CompilerM ()
ifSet flag m = do
  flags <- gets _flags
  when (Flags.isSet flags flag) (void m)
