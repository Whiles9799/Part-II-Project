module Dual.Syntax.Evaluation where

open import Data.Empty using (⊥; ⊥-elim)
open import Dual.Syntax.Core
open import Dual.Syntax.Duality
open import Dual.Syntax.Substitution
open import Dual.Syntax.Implication
open import Dual.DenotationalSemantics.CPSTransformation ⊥


lem : ∀ {A} → ∅ ⟶ ∅ ∣ A `+ `¬ A
lem = μθ (inr⟨ not[ μγ (inl⟨ γ 0 ⟩ ● (θ 0) ) ] ⟩ ● (θ 0))

lemⱽ : ∀ {A} → ((A ⱽᵀ ⊎ (A ⱽᵀ → ⊥)) → ⊥) → ⊥
lemⱽ {A} = (lem {A} ⱽᴸ) ⟨ tt , tt ⟩ 

lemⱽ-norm : ∀ {A} → ((A ⊎ (A → ⊥)) → ⊥) → ⊥
lemⱽ-norm {A} = λ α → α (inj₂ (λ x → α (inj₁ x)))

lemᴺ : ∀ {A} → ((A ᴺᵀ × (A ᴺᵀ → ⊥)) → ⊥)
lemᴺ = (lem ᴺᴸ) ⟨ tt , tt ⟩ 

lemᴺ-norm : ∀ {A} → (A × (A → ⊥)) → ⊥
lemᴺ-norm = λ α → proj₂ α (proj₁ α)

dnl : ∀ {A} → ∅ ⟶ ∅ ∣ (`¬ (`¬ A)) ⇒ⱽ A
dnl = ƛⱽ (μθ (ƛⱽ γ 0 ● ( γ 0 ·ⱽ μγ (γ 0 ● not⟨ not[ θ 0 ] ⟩))))

lnc : ∀ {A} → ∅ ⟶ ∅ ∣ `¬(A `× (`¬ A))
lnc = not[ μγ ( γ 0 ● fst[ (μγ ((γ 1) ● snd[ not⟨ γ 0 ⟩ ])) ]) ]

coc : ∀ {P Q} → ∅ ⟶ ∅ ∣ ((P `× Q) ⇒ⱽ (Q `× P)) `× ((Q `× P) ⇒ⱽ (P `× Q))
coc = `⟨ ƛⱽ `⟨ (μθ ((γ 0) ● snd[ (θ 0) ])) , (μθ ((γ 0) ● fst[ (θ 0) ])) ⟩ , ƛⱽ `⟨ (μθ ((γ 0) ● snd[ (θ 0) ])) , μθ ((γ 0) ● fst[ (θ 0) ]) ⟩ ⟩ 

pierce : ∀ {A B} → ∅ ⟶ ∅ ∣ (((A ⇒ⱽ B) ⇒ⱽ A) ⇒ⱽ A)
pierce = ƛⱽ (μθ (γ 0 ● ((ƛⱽ (μθ (γ 0 ● (θ 1)))) ·ⱽ θ 0)))

