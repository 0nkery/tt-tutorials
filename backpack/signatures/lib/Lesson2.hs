module Lesson2
    ( compile
    , Template
    , format
    )
where

import           Str                            ( Str
                                                , splitOn
                                                )

newtype Template = Template [Str] deriving (Show)

compile :: Str -> Template
compile = Template . splitOn '%'

format :: Template -> [Str] -> Str
format (Template strs) vals =
    mconcat $ zipWith mappend strs (vals ++ repeat mempty)
