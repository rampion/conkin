module Main where
import Test.DocTest

main :: IO ()
main = doctest $ words "-pgmL markdown-unlit Continuation/Kind.lhs"
