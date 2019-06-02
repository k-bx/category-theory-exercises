{-# OPTIONS --without-K --safe #-}
module ex01 where

-- open import IO
open import Algebra
open import Categories.Category
open import Level

-- Category Theory by Steve Awodey
-- Page 12. Example 12:
-- ...
-- Equivalently, a monoid is a category with just one object. The arrows of
-- the category are the elements of the monoid. In particular, the identity
-- arrow is the unit element u. Composition of arrows is the binary operation
-- m ∙ n of the monoid.

record BoringMonoid (o : Level) : Set o where
  constructor MkBoringMonoid

monoidToCategoryEx01 : {o ℓ e : Level} → (m : Monoid ℓ e) → Category o ℓ e
monoidToCategoryEx01 {o} {ℓ} {e} m =
  record
    { Obj = BoringMonoid o
    ; _⇒_ = λ bm1 bm2 -> Monoid.Carrier m
    ; _≈_ = Monoid._≈_ m
    ; id = Monoid.ε m
    ; _∘_ = Monoid._∙_ m
    ; assoc = {!!}
    ; identityˡ = {!!}
    ; identityʳ = {!!}
    ; equiv = {!!}
    ; ∘-resp-≈ = {!!}
    }

bmExample : {o : Level} -> BoringMonoid o
bmExample = MkBoringMonoid

-- main = run (putStrLn "Hello, World!")
