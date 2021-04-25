module Dual.OperationalSemantics.Evaluation where

open import Dual.Syntax.Core
open import Dual.Syntax.Substitution
open import Dual.Syntax.Values
open import Dual.OperationalSemantics.CBVReduction
open import Data.Product using (Σ; _×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

lem : ∀ {A} → ∅ ⟶ ∅ ∣ A `+ `¬ A
lem = μθ (inr⟨ not[ μγ (inl⟨ γ 0 ⟩ ● (θ 0) ) ] ⟩ ● (θ 0))

lem-ref : ∀ {A} → ∅ ⟶ ∅ ∣ A  → A ∣ ∅ ⟶ ∅ → A `+ `¬ A ∣ ∅ ⟶ ∅
lem-ref M K = `[ K , not⟨ M ⟩ ]

lem-comp : ∀ {A} → (M : ∅ ⟶ ∅ ∣ A) → Value M → (K : A ∣ ∅ ⟶ ∅)
     → (lem ● lem-ref M K) ˢ—↠ⱽ M ● K
lem-comp M M:V K = beginˢⱽ
      μθ (inr⟨ not[ μγ (inl⟨ γ 0 ⟩ ● (θ 0) ) ] ⟩ ● (θ 0))
    ● `[ K , not⟨ M ⟩ ]
  ˢ⟶ⱽ⟨ βR ⟩
      inr⟨ not[ μγ (inl⟨ γ 0 ⟩ ● `[ wkΓᶜ K , not⟨ wkΓᵗ M ⟩ ] ) ] ⟩
    ● `[ K , not⟨ M ⟩ ]
  ˢ⟶ⱽ⟨ β+₂ V-not ⟩
      not[ μγ (inl⟨ γ 0 ⟩ ● `[ wkΓᶜ K , not⟨ wkΓᵗ M ⟩ ] ) ]
    ● not⟨ M ⟩
  ˢ⟶ⱽ⟨ β¬ ⟩
      M
    ● μγ (inl⟨ γ 0 ⟩ ● `[ wkΓᶜ K , not⟨ wkΓᵗ M ⟩ ] )
  ˢ⟶ⱽ⟨ βL M:V ⟩
      ((inl⟨ γ 0 ⟩ ● `[ (wkΓᶜ K) , not⟨ (wkΓᵗ M) ⟩ ]) ⱽ⟨ ⟨ M , M:V ⟩ /⟩ˢ)
  ˢ⟶ⱽ⟨ {!   !} ⟩
      inl⟨ M ⟩
    ● `[ K , not⟨ M ⟩ ]
  ˢ⟶ⱽ⟨ β+₁ M:V ⟩
    M ● K
  ∎ˢⱽ
