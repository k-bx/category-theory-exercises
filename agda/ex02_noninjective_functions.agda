module ex02_noninjective_functions where

-- | Category Theory by Steve Awodey
--
-- Page 6. Book mentions injective functions, but just to clarify we
-- will confirm that non-injective functions work just as well.
--

open import Algebra
open import Function using (_∘_)
open import Algebra.Structures
open import Categories.Category
open import Level
open import Relation.Binary.Core
open import Agda.Builtin.Equality

data FiniteSet (o : Level) : Set o where
  MkFiniteSet1 : FiniteSet o
  MkFiniteSet2 : FiniteSet o

record AnyFiniteSetFunc (ℓ : Level) : Set ℓ where
  constructor MkAnyFiniteSetFunc
  field
    func : (FiniteSet ℓ → FiniteSet ℓ)

noninjCat : {o ℓ e : Level} → Category o ℓ e
noninjCat {o} {ℓ} {e} =
  record
    { Obj = FiniteSet o
    ; _⇒_ = λ _ _ → AnyFiniteSetFunc ℓ
    ; _≈_ = λ x₂ x₁ → {!(_≡_) x₁ x₂!}
    ; id = MkAnyFiniteSetFunc (\(el : FiniteSet ℓ) → el)
    ; _∘_ = λ f1 f2 →
            MkAnyFiniteSetFunc
              ( AnyFiniteSetFunc.func f1
              ∘ AnyFiniteSetFunc.func f2
              )
    ; assoc = λ {A} {B} {C} {D} {f} {g} {h} → {!!}
    ; identityˡ = {!!}
    ; identityʳ = {!!}
    ; equiv = {!!}
    ; ∘-resp-≈ = {!!}
    }
