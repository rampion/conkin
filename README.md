```haskell
module Continuation.Kind where
```

# Literate Haskell

This README.md file is a literate haskell file, for use with [`markdown-unlit`](https://github.com/sol/markdown-unlit#readme).
To allow GHC to recognize it, it's softlinked as `Continuation/Kind.lhs`, which you can compile with

    $ ghc -pgmL markdown-unlit Continuation/Kind.lhs

Many of the above examples are [`doctest`](https://github.com/sol/doctest#readme)-compatible, and can be run with

    $ doctest -pgmL markdown-unlit Continuation/Kind.lhs

Alternately, you can have cabal manage the dependencies and compile and test this with:

    $ cabal install --dependencies-only --enable-tests
    $ cabal build
    $ cabal test
