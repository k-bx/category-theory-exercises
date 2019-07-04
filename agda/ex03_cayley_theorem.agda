module ex03_cayley_theorem where

-- | Category Theory by Steve Awodey
--
-- Page 14. Theorem (Cayley). I was quite confused with it, so with
-- help of Wikipedia and Agda I hope to make all things clear.
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

-- | From: https://en.wikipedia.org/wiki/Cayley%27s_theorem
-- | In group theory, Cayley's theorem, named in honour of Arthur
-- | Cayley, states that every group G is isomorphic to a subgroup of
-- | the symmetric group acting on G.

-- | TODO and open questions:
--
--   - [ ] which "group" definition should be taken?
--         agda-stdlib/src/Algebra.agda` doesn't seem to have a notion
--         of a subgroup. So maybe this one?
--         https://github.com/HoTT/HoTT-Agda/blob/master/core/lib/groups/Subgroup.agda
--

-- cayley : {c ℓ : Level} → (g : Group c ℓ) →
