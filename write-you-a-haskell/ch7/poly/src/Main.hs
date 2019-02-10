{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE TypeSynonymInstances  #-}

import qualified Env
import           Eval
import           Infer
import           Parser
import           Pretty
import           Syntax

import qualified Data.Map                   as Map
import           Data.Monoid
import qualified Data.Text.Lazy             as L
import qualified Data.Text.Lazy.IO          as L

import           Control.Monad.Identity
import           Control.Monad.State.Strict

import           Text.Parsec

import           Data.List                  (foldl', isPrefixOf)

import           System.Console.Repline
import           System.Environment
import           System.Exit

-------------------------------------------------------------------------------
-- Types
-------------------------------------------------------------------------------

data IState = IState {
    tyctx :: Env.Env,
    tmctx :: TermEnv
  }

initState :: IState
initState = IState Env.empty emptyTmenv

type Repl a = HaskelineT (StateT IState IO) a

hoistErr :: Show e => Either e a -> Repl a
hoistErr (Right val) = return val
hoistErr (Left err) = do
  liftIO $ print err
  abort

showSyntaxError :: L.Text -> ParseError -> String
showSyntaxError s err = L.unpack $ L.unlines [
    " ",
    " " <> lineContents,
    " " <> ((L.replicate col " ") <> "^"),
    (L.pack $ show err)
  ]
  where
    lineContents = (L.lines s) !! line
    pos = errorPos err
    line = sourceLine pos - 1
    col = fromIntegral $ sourceColumn pos - 1

hoistSyntaxErr :: L.Text -> Either ParseError a -> Repl a
hoistSyntaxErr source (Right val) = return val
hoistSyntaxErr source (Left err) = do
  let prettyPrintedError = showSyntaxError source err
  liftIO $ putStr prettyPrintedError
  abort

-------------------------------------------------------------------------------
-- Execution
-------------------------------------------------------------------------------

evalDef :: TermEnv -> (String, Expr) -> TermEnv
evalDef env (nm, ex) = tmctx'
  where
    (val, tmctx') = runEval env nm ex

showOutput :: String -> IState -> Repl ()
showOutput arg st = do
  case Env.lookup "it" (tyctx st) of
    Just val -> liftIO $ putStrLn $ ppsignature (arg, val)
    Nothing  -> return ()

exec :: Bool -> L.Text -> Repl ()
exec update source = do
  -- Get the current interpreter state
  st <- get

  -- Parser ( returns AST )
  mod <- hoistSyntaxErr source $ parseModule "<stdin>" source

  -- Type Inference ( returns Typing Environment )
  tyctx' <- hoistErr $ inferTop (tyctx st) mod
  let st' = st {
    tmctx = foldl' evalDef (tmctx st) mod,
    tyctx = tyctx' <> tyctx st
  }

  -- Update the interpreter state
  when update (put st')

  -- If a value is entered, print it.
  case lookup "it" mod of
    Nothing -> return ()
    Just ex -> do
      let (val, _) = runEval (tmctx st') "it" ex
      showOutput (show val) st'

cmd :: String -> Repl ()
cmd source = exec True (L.pack source)

-------------------------------------------------------------------------------
-- Commands
-------------------------------------------------------------------------------

-- :browse command
browse :: [String] -> Repl ()
browse _ = do
  st <- get
  liftIO $ mapM_ putStrLn $ ppenv (tyctx st)

-- :load command
load :: [String] -> Repl ()
load args = do
  contents <- liftIO $ L.readFile (unwords args)
  exec True contents

-- :type command
typeof :: [String] -> Repl ()
typeof args = do
  st <- get
  let arg = unwords args
  case Env.lookup arg (tyctx st) of
    Just val -> liftIO $ putStrLn $ ppsignature (arg, val)
    Nothing  -> exec False (L.pack arg)

-- :quit command
quit :: a -> Repl ()
quit _ = liftIO exitSuccess

-------------------------------------------------------------------------------
-- Interactive Shell
-------------------------------------------------------------------------------

-- Prefix tab completer
defaultMatcher :: MonadIO m => [(String, CompletionFunc m)]
defaultMatcher = [
    (":load", fileCompleter)
  ]

-- Default tab completer
comp :: (Monad m, MonadState IState m) => WordCompleter m
comp n = do
  let cmds = [":load", ":type", ":browse", ":quit"]
  Env.TypeEnv ctx <- gets tyctx
  let defs = Map.keys ctx
  return $ filter (isPrefixOf n) (cmds ++ defs)

options :: [(String, [String] -> Repl ())]
options = [
    ("load", load),
    ("browse", browse),
    ("quit", quit),
    ("type", Main.typeof)
  ]

-------------------------------------------------------------------------------
-- Entry Point
-------------------------------------------------------------------------------

completer :: CompleterStyle (StateT IState IO)
completer = Prefix (wordCompleter comp) defaultMatcher

shell :: Repl a -> IO ()
shell pre = flip evalStateT initState $ evalRepl "Poly> " cmd options completer pre

main :: IO ()
main = do
  args <- getArgs
  case args of
    []              -> shell (return ())
    [fname]         -> shell (load [fname])
    ["test", fname] -> shell (load [fname] >> browse [] >> quit ())
    _               -> putStrLn "invalid arguments"
