module ex02_noninjective_functions where

-- | Category Theory by Steve Awodey
--
-- Page 6. Book mentions injective functions, but just to clarify we
-- will confirm that non-injective functions work just as well.
--

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)
open import Algebra
open import Function using (_∘_)
open import Algebra.Structures
open import Categories.Category
open import Level
open import Relation.Binary.Core
--open import Agda.Builtin.Equality

data FiniteSet (o : Level) : Set o where
  MkFiniteSet1 : FiniteSet o
  MkFiniteSet2 : FiniteSet o

record AnyFiniteSetFunc (ℓ : Level) : Set ℓ where
  constructor MkAnyFiniteSetFunc
  field
    func : (FiniteSet ℓ → FiniteSet ℓ)

∘-resp-≈-hole₁ : (ℓ₁ : Level)
       → (d : AnyFiniteSetFunc ℓ₁)
       → (e : AnyFiniteSetFunc ℓ₁)
       → (f : AnyFiniteSetFunc ℓ₁)
       → (g : AnyFiniteSetFunc ℓ₁)
       → (λ x → AnyFiniteSetFunc.func d (AnyFiniteSetFunc.func g x))
          ≡
          (λ x → AnyFiniteSetFunc.func d (AnyFiniteSetFunc.func f x))
       → (x₂ : e ≡ d)
       → MkAnyFiniteSetFunc (λ x → AnyFiniteSetFunc.func e (AnyFiniteSetFunc.func g x))
          ≡
          MkAnyFiniteSetFunc (λ x → AnyFiniteSetFunc.func d (AnyFiniteSetFunc.func f x))
∘-resp-≈-hole₁ ℓ₁ d e f g xf₁ x₂ rewrite sym x₂ = cong MkAnyFiniteSetFunc xf₁

noninjCat : {o ℓ : Level} → Category o ℓ ℓ
noninjCat {o} {ℓ} =
  record
    { Obj = FiniteSet o
    ; _⇒_ = λ _ _ → AnyFiniteSetFunc ℓ
    ; _≈_ = λ {A} {B} x₂ x₁ → x₁ ≡ x₂
    ; id = MkAnyFiniteSetFunc (\(el : FiniteSet ℓ) → el)
    ; _∘_ = λ f1 f2 →
            MkAnyFiniteSetFunc
              ( AnyFiniteSetFunc.func f1
              ∘ AnyFiniteSetFunc.func f2
              )
    ; assoc = λ {A} {B} {C} {D} {f} {g} {h} → refl
    ; identityˡ = refl
    ; identityʳ = refl
    ; equiv = λ {A} {B} → record { refl = refl ; sym = λ x → sym x ; trans = λ x₂ x₁ → trans x₁ x₂ }
    ; ∘-resp-≈ = λ {a} {b} {c} {d} {e} {f} {g} x₂ x₁ →
        let x₁f = cong AnyFiniteSetFunc.func x₁
            x₂f = cong AnyFiniteSetFunc.func x₂
            xf₁ = cong (AnyFiniteSetFunc.func d ∘_) x₁f
        in ∘-resp-≈-hole₁ ℓ d e f g xf₁ x₂
    }
