module ex01 where

open import IO
open import Algebra

record BoringMonoid : Set where
  constructor MkBoringMonoid

bmExample : BoringMonoid
bmExample = MkBoringMonoid

main = run (putStrLn "Hello, World!")
