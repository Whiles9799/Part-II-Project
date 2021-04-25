module Dual.OperationalSemantics.CBVReduction where

open import Dual.Syntax.Core
open import Dual.Syntax.Substitution
open import Dual.Syntax.Duality
open import Dual.Syntax.Values
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Product using (Σ; _×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

infix 2 _ˢ⟶ⱽ_
infix 2 _ᶜ⟶ⱽ_
infix 2 _ᵗ⟶ⱽ_

data _ˢ⟶ⱽ_ : ∀ {Γ Θ} → (Γ ↦ Θ) → (Γ ↦ Θ) → Set where

  β×₁ : ∀ {Γ Θ A B} {V : Γ ⟶ Θ ∣ A} {W : Γ ⟶ Θ ∣ B} {K : A ∣ Γ ⟶ Θ}
    → Value V → Value W
      ------------------------------
    → `⟨ V , W ⟩ ● fst[ K ] ˢ⟶ⱽ V ● K

  β×₂ : ∀ {Γ Θ A B} {V : Γ ⟶ Θ ∣ A} {W : Γ ⟶ Θ ∣ B} {L : B ∣ Γ ⟶ Θ}
    → Value V → Value W
      ------------------------------
    → `⟨ V , W ⟩ ● snd[ L ] ˢ⟶ⱽ W ● L

  β+₁ : ∀ {Γ Θ A B} {V : Γ ⟶ Θ ∣ A} {K : A ∣ Γ ⟶ Θ} {L : B ∣ Γ ⟶ Θ}
    → Value V
      ------------------------------
    → inl⟨ V ⟩ ● `[ K , L ] ˢ⟶ⱽ V ● K

  β+₂ : ∀ {Γ Θ A B} {W : Γ ⟶ Θ ∣ B} {K : A ∣ Γ ⟶ Θ} {L : B ∣ Γ ⟶ Θ}
    → Value W
      ------------------------------
    → inr⟨ W ⟩ ● `[ K , L ] ˢ⟶ⱽ W ● L

  β¬ : ∀ {Γ Θ A} {M : Γ ⟶ Θ ∣ A} {K : A ∣ Γ ⟶ Θ}
      -----------------------------
    → not[ K ] ● not⟨ M ⟩ ˢ⟶ⱽ M ● K

  βL : ∀ {Γ Θ A} {V : Γ ⟶ Θ ∣ A} {S : Γ , A ↦ Θ} (v : Value V)
      ------------------------------
    → V ● (μγ S) ˢ⟶ⱽ S ⱽ⟨ ⟨ V , v ⟩ /⟩ˢ

  βR : ∀ {Γ Θ A} {K : A ∣ Γ ⟶ Θ} {S : Γ ↦ Θ , A}
      ------------------------
    → (μθ S) ● K ˢ⟶ⱽ S [ K /]ˢ

data _ᶜ⟶ⱽ_ : ∀ {Γ Θ A} → (A ∣ Γ ⟶ Θ) → (A ∣ Γ ⟶ Θ) → Set where
  
  ηL : ∀ {Γ Θ A} {K : A ∣ Γ ⟶ Θ} 
      ------------------------
    → K ᶜ⟶ⱽ μγ ((γ 0) ● wkΓᶜ K)

data _ᵗ⟶ⱽ_ : ∀ {Γ Θ A} → (Γ ⟶ Θ ∣ A) → (Γ ⟶ Θ ∣ A) → Set where

  ηR : ∀ {Γ Θ A} {M : Γ ⟶ Θ ∣ A}
      ------------------------
    → M ᵗ⟶ⱽ μθ (wkΘᵗ M ● (θ 0))




infix  2 _ˢ—↠ⱽ_
infix  1 beginˢⱽ_
infixr 2 _ˢ⟶ⱽ⟨_⟩_
infix  3 _∎ˢⱽ

data _ˢ—↠ⱽ_ {Γ Θ} : (Γ ↦ Θ) → (Γ ↦ Θ) → Set where
  
  _∎ˢⱽ : (S : Γ ↦ Θ)
      --------
    → S ˢ—↠ⱽ S

  _ˢ⟶ⱽ⟨_⟩_ : (S : Γ ↦ Θ) {S′ S″ : Γ ↦ Θ}
    → S ˢ⟶ⱽ S′
    → S′ ˢ—↠ⱽ S″
      -----------
    → S ˢ—↠ⱽ S″

beginˢⱽ_ : ∀ {Γ Θ} {S S′ : Γ ↦ Θ}
  → S ˢ—↠ⱽ S′
    ---------
  → S ˢ—↠ⱽ S′
beginˢⱽ S—↠S′ = S—↠S′

infix  2 _ᶜ—↠ⱽ_
infix  1 beginᶜⱽ_
infixr 2 _ᶜ⟶ⱽ⟨_⟩_
infix  3 _∎ᶜⱽ

data _ᶜ—↠ⱽ_ {Γ Θ A} : (A ∣ Γ ⟶ Θ) → (A ∣ Γ ⟶ Θ) → Set where
  
  _∎ᶜⱽ : (K : A ∣ Γ ⟶ Θ)
      --------
    → K ᶜ—↠ⱽ K

  _ᶜ⟶ⱽ⟨_⟩_ : (K : A ∣ Γ ⟶ Θ) {K′ K″ : A ∣ Γ ⟶ Θ}
    → K ᶜ⟶ⱽ K′
    → K′ ᶜ—↠ⱽ K″
      -----------
    → K ᶜ—↠ⱽ K″

beginᶜⱽ_ : ∀ {A Γ Θ} {K K′ : A ∣ Γ ⟶ Θ}
  → K ᶜ—↠ⱽ K′
    ---------
  → K ᶜ—↠ⱽ K′
beginᶜⱽ K—↠K′ = K—↠K′

infix  2 _ᵗ—↠ⱽ_
infix  1 beginᵗⱽ_
infixr 2 _ᵗ⟶ⱽ⟨_⟩_
infix  3 _∎ᵗⱽ

data _ᵗ—↠ⱽ_ {Γ Θ A} : (Γ ⟶ Θ ∣ A) → (Γ ⟶ Θ ∣ A) → Set where
  
  _∎ᵗⱽ : (M : Γ ⟶ Θ ∣ A)
      ---------
    → M ᵗ—↠ⱽ M

  _ᵗ⟶ⱽ⟨_⟩_ : (M : Γ ⟶ Θ ∣ A) {M′ M″ : Γ ⟶ Θ ∣ A}
    → M ᵗ⟶ⱽ M′
    → M′ ᵗ—↠ⱽ M″
      -----------
    → M ᵗ—↠ⱽ M″

beginᵗⱽ_ : ∀ {A Γ Θ} {M M′ : Γ ⟶ Θ ∣ A}
  → M ᵗ—↠ⱽ M′
    ---------
  → M ᵗ—↠ⱽ M′
beginᵗⱽ M—↠M′ = M—↠M′


