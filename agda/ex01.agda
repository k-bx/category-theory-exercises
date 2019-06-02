{-# OPTIONS --without-K --safe #-}
module ex01 where

-- open import IO
open import Algebra
open import Categories.Category
open import Level

record BoringMonoid (o : Level) : Set o where
  constructor MkBoringMonoid

bmExample : {o : Level} -> BoringMonoid o
bmExample = MkBoringMonoid

-- Category Theory by Steve Awodey
-- Page 12. Example 12:
-- ...
-- Equivalently, a monoid is a category with just one object. The arrows of
-- the category are the elements of the monoid. In particular, the identity
-- arrow is the unit element u. Composition of arrows is the binary operation
-- m * n of the monoid.

monoidToCategoryEx01 : {o ℓ e : Level} → ∀ {ml2} (m : Monoid ℓ ml2) → Category o ℓ e
monoidToCategoryEx01 {o} {ℓ} {e} m =
  record
    { Obj = BoringMonoid o
    ; _⇒_ = λ bm1 bm2 -> Monoid.Carrier m
    ; _≈_ = {!!}
    ; id = Monoid.ε m
    ; _∘_ = {!!}
    ; assoc = {!!}
    ; identityˡ = {!!}
    ; identityʳ = {!!}
    ; equiv = {!!}
    ; ∘-resp-≈ = {!!}
    }

-- main = run (putStrLn "Hello, World!")
