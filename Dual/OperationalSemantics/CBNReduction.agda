module Dual.OperationalSemantics.CBNReduction where

open import Dual.Syntax.Core
open import Dual.Syntax.Substitution
open import Dual.Syntax.Duality
open import Dual.Syntax.Values
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Product using (Σ; _×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

infix 2 _ˢ⟶ᴺ_
infix 2 _ᶜ⟶ᴺ_
infix 2 _ᵗ⟶ᴺ_

data _ˢ⟶ᴺ_ : ∀ {Γ Θ} → (Γ ↦ Θ) → (Γ ↦ Θ) → Set where
  
  β×₁ : ∀ {Γ Θ A B} {M : Γ ⟶ Θ ∣ A} {N : Γ ⟶ Θ ∣ B} {P : A ∣ Γ ⟶ Θ}
    → Covalue P
      -------------------------------
    → `⟨ M , N ⟩ ● fst[ P ] ˢ⟶ᴺ M ● P

  β×₂ : ∀ {Γ Θ A B} {M : Γ ⟶ Θ ∣ A} {N : Γ ⟶ Θ ∣ B} {Q : B ∣ Γ ⟶ Θ}
    → Covalue Q
      --------------------------------
    → `⟨ M , N ⟩ ● snd[ Q ] ˢ⟶ᴺ N ● Q

  β+₁ : ∀ {Γ Θ A B} {M : Γ ⟶ Θ ∣ A} {P : A ∣ Γ ⟶ Θ} {Q : B ∣ Γ ⟶ Θ}
    → Covalue P → Covalue Q
      --------------------------------
    → inl⟨ M ⟩ ● `[ P , Q ] ˢ⟶ᴺ M ● P

  β+₂ : ∀ {Γ Θ A B} {N : Γ ⟶ Θ ∣ B} {P : A ∣ Γ ⟶ Θ} {Q : B ∣ Γ ⟶ Θ}
    → Covalue P → Covalue Q
      --------------------------------
    → inr⟨ N ⟩ ● `[ P , Q ] ˢ⟶ᴺ N ● Q

  β¬ : ∀ {Γ Θ A} {M : Γ ⟶ Θ ∣ A} {K : A ∣ Γ ⟶ Θ}
      -----------------------------
    → not[ K ] ● not⟨ M ⟩ ˢ⟶ᴺ M ● K 
  
  βL : ∀ {Γ Θ A} {M : Γ ⟶ Θ ∣ A} {S : Γ , A ↦ Θ}
      ------------------------
    → M ● (μγ S) ˢ⟶ᴺ S ⟨ M /⟩ˢ 

  βR : ∀ {Γ Θ A} {S : Γ ↦ Θ , A} {P : A ∣ Γ ⟶ Θ} (p : Covalue P)
      -------------------------
    → (μθ S) ● P ˢ⟶ᴺ S ⱽ[ ⟨ P , p ⟩ /]ˢ

data _ᶜ⟶ᴺ_ : ∀ {Γ Θ A} → (A ∣ Γ ⟶ Θ) → (A ∣ Γ ⟶ Θ) → Set where
  
  ηL : ∀ {Γ Θ A} {K : A ∣ Γ ⟶ Θ} 
      ------------------------
    → K ᶜ⟶ᴺ μγ ((γ 0) ● wkΓᶜ K)

data _ᵗ⟶ᴺ_ : ∀ {Γ Θ A} → (Γ ⟶ Θ ∣ A) → (Γ ⟶ Θ ∣ A) → Set where

  ηR : ∀ {Γ Θ A} {M : Γ ⟶ Θ ∣ A}
      ------------------------
    → M ᵗ⟶ᴺ μθ (wkΘᵗ M ● (θ 0))

infix  2 _ˢ—↠ᴺ_
infix  1 beginˢᴺ_
infixr 2 _ˢ⟶ᴺ⟨_⟩_
infix  3 _∎ˢᴺ

data _ˢ—↠ᴺ_ {Γ Θ} : (Γ ↦ Θ) → (Γ ↦ Θ) → Set where
  
  _∎ˢᴺ : (S : Γ ↦ Θ)
      --------
    → S ˢ—↠ᴺ S

  _ˢ⟶ᴺ⟨_⟩_ : (S : Γ ↦ Θ) {S′ S″ : Γ ↦ Θ}
    → S ˢ⟶ᴺ S′
    → S′ ˢ—↠ᴺ S″
      -----------
    → S ˢ—↠ᴺ S″

beginˢᴺ_ : ∀ {Γ Θ} {S S′ : Γ ↦ Θ}
  → S ˢ—↠ᴺ S′
    ---------
  → S ˢ—↠ᴺ S′
beginˢᴺ S—↠S′ = S—↠S′

infix  2 _ᶜ—↠ᴺ_
infix  1 beginᶜᴺ_
infixr 2 _ᶜ⟶ᴺ⟨_⟩_
infix  3 _∎ᶜᴺ

data _ᶜ—↠ᴺ_ {Γ Θ A} : (A ∣ Γ ⟶ Θ) → (A ∣ Γ ⟶ Θ) → Set where
  
  _∎ᶜᴺ : (K : A ∣ Γ ⟶ Θ)
      --------
    → K ᶜ—↠ᴺ K

  _ᶜ⟶ᴺ⟨_⟩_ : (K : A ∣ Γ ⟶ Θ) {K′ K″ : A ∣ Γ ⟶ Θ}
    → K ᶜ⟶ᴺ K′
    → K′ ᶜ—↠ᴺ K″
      -----------
    → K ᶜ—↠ᴺ K″

beginᶜᴺ_ : ∀ {A Γ Θ} {K K′ : A ∣ Γ ⟶ Θ}
  → K ᶜ—↠ᴺ K′
    ---------
  → K ᶜ—↠ᴺ K′
beginᶜᴺ K—↠K′ = K—↠K′

infix  2 _ᵗ—↠ᴺ_
infix  1 beginᵗᴺ_
infixr 2 _ᵗ⟶ᴺ⟨_⟩_
infix  3 _∎ᵗᴺ

data _ᵗ—↠ᴺ_ {Γ Θ A} : (Γ ⟶ Θ ∣ A) → (Γ ⟶ Θ ∣ A) → Set where
  
  _∎ᵗᴺ : (M : Γ ⟶ Θ ∣ A)
      ---------
    → M ᵗ—↠ᴺ M

  _ᵗ⟶ᴺ⟨_⟩_ : (M : Γ ⟶ Θ ∣ A) {M′ M″ : Γ ⟶ Θ ∣ A}
    → M ᵗ⟶ᴺ M′
    → M′ ᵗ—↠ᴺ M″
      -----------
    → M ᵗ—↠ᴺ M″

beginᵗᴺ_ : ∀ {A Γ Θ} {M M′ : Γ ⟶ Θ ∣ A}
  → M ᵗ—↠ᴺ M′
    ---------
  → M ᵗ—↠ᴺ M′
beginᵗᴺ M—↠M′ = M—↠M′