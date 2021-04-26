module Dual.DenotationalSemantics.Evaluation (R : Set) where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym; trans)
open import Dual.Syntax.Core
open import Dual.Syntax.Duality
open import Dual.Syntax.Substitution
open import Dual.Syntax.Values
open import Dual.DenotationalSemantics.CPSTransformation R

ex1 : ∀ {A B} → ∅ , A , B ⟶ ∅ ∣ A `× B
ex1 = `⟨ γ 1 , γ 0 ⟩

ex1ⱽ : ∀ {A B} x y → (((A `× B) ⱽᵀ → R) → R)
ex1ⱽ {A} {B} x y = (ex1 {A}{B} ⱽᴸ) ⟨ ⟨ ⟨ tt , x ⟩ , y ⟩ , tt ⟩

ex2 : ∀ {A B} → ∅ , (A `× B) ⟶ ∅ ∣ A
ex2 = μθ (γ 0 ● fst[ θ 0 ])

ex2ⱽ : ∀ {A B} x → ((A ⱽᵀ → R) → R)
ex2ⱽ {A}{B} x = (ex2 {A}{B} ⱽᴸ) ⟨ ⟨ tt , x ⟩ , tt ⟩

ex3 : ∀ {A B} → (∅ , A `× B) ⟶ ∅ ∣ A `× B
ex3 = `⟨ μθ ( γ 0 ● fst[ θ 0 ] ) , μθ ( γ 0 ● snd[ θ 0 ] ) ⟩

ex3ⱽ : ∀ {A B} x → (((A `× B) ⱽᵀ → R) → R)
ex3ⱽ {A}{B} x = ((ex3 {A}{B}) ⱽᴸ) ⟨ ⟨ tt , x ⟩ , tt ⟩

ex4 : ∀ {A} → (∅ , A) ↦ (∅ , A)
ex4 = (γ 0) ● (θ 0)

ex4ⱽ : ∀ {A} x α → R
ex4ⱽ {A} x α = (ex4 {A} ⱽˢ) ⟨ ⟨ tt , x ⟩ , ⟨ tt , α ⟩ ⟩

ex5 : ∀ {A} → (∅ , A) ↦ (∅ , A)
ex5 = not[ (θ 0) ] ● not⟨ (γ 0) ⟩ 

ex5ⱽ : ∀ {A} x α → R
ex5ⱽ {A} x α = (ex5 {A} ⱽˢ) ⟨ ⟨ tt , x ⟩ , ⟨ tt , α ⟩ ⟩