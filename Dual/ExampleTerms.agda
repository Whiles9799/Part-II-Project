module Dual.ExampleTerms where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Relation.Nullary using (¬_)
open import Dual.Syntax
open import Dual.DualTranslation
open import Dual.CPSTransformation

lem : ∀ {A} → ∅ ⟶ ∅ ∣ A `+ `¬ A
lem = μθ (inr⟨ not[ μγ (inl⟨ γ 0 ⟩ ● (θ 0) ) ] ⟩ ● (θ 0))

lemⱽ : ∀ {A} → ((A ⱽᵀ ⊎ (A ⱽᵀ → ⊥)) → ⊥) → ⊥
lemⱽ {A} = (lem {A} ⱽᴸ) ⟨ tt , tt ⟩ 

lemᴺ : ∀ {A} → ((A ᴺᵀ × (A ᴺᵀ → ⊥)) → ⊥)
lemᴺ = (lem ᴺᴸ) ⟨ tt , tt ⟩ 


