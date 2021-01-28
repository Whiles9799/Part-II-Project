module Dual.Semantics where

open import Dual.Syntax
open import Dual.Substitution
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)


infix 2 _ˢ⟶ⱽ_
infix 2 _ᶜ⟶ⱽ_
infix 2 _ᵗ⟶ⱽ_

infix 2 _ˢ⟶ᴺ_
infix 2 _ᶜ⟶ᴺ_
infix 2 _ᵗ⟶ᴺ_

data Value : ∀ {Γ Θ A} → Γ ⟶ Θ ∣ A → Set 
data Covalue : ∀ {Γ Θ A} → A ∣ Γ ⟶ Θ → Set

data Value where

  V-var : ∀ {Γ Θ A} {x : Γ ∋ A}
      ---------
    → Value {Θ = Θ} (` x)

  V-prod : ∀ {Γ Θ A B} {M : Γ ⟶ Θ ∣ A} {N : Γ ⟶ Θ ∣ B}
    → Value M
    → Value N
      ---------------
    → Value `⟨ M , N ⟩

  V-inl : ∀ {Γ Θ A B} {M : Γ ⟶ Θ ∣ A}
    → Value M
      -------------
    → Value (inl⟨_⟩ {B = B} M)

  V-inr : ∀ {Γ Θ A B} {M : Γ ⟶ Θ ∣ B}
    → Value M
      -------------
    → Value (inr⟨_⟩ {A = A} M)

  V-not : ∀ {Γ Θ A} {K : A ∣ Γ ⟶ Θ}
      --------------
    → Value not[ K ]


data Covalue where
  
  CV-covar : ∀ {Γ Θ A} {α : Θ ∋ A}
      -------
    → Covalue {Γ = Γ} (` α)

  CV-sum : ∀ {Γ Θ A B} {K : A ∣ Γ ⟶ Θ} {L : B ∣ Γ ⟶ Θ}
    → Covalue K
    → Covalue L
      ------------------
    → Covalue `[ K , L ]

  CV-fst : ∀ {Γ Θ A B} {K : A ∣ Γ ⟶ Θ}
    → Covalue K
      ----------------
    → Covalue (fst[_] {B = B} K)

  CV-snd : ∀ {Γ Θ A B} {K : B ∣ Γ ⟶ Θ}
    → Covalue K
      ----------------
    → Covalue (snd[_] {A = A} K)

  CV-not : ∀ {Γ Θ A} {M : Γ ⟶ Θ ∣ A}
      --------------
    → Covalue not⟨ M ⟩


_⟨_/⟩ᵗ : ∀ {Γ Θ A B} 
  → Γ , A ⟶ Θ ∣ B
  → Γ ⟶ Θ ∣ A
    --------------
  → Γ ⟶ Θ ∣ B   

_⟨_/⟩ᶜ : ∀ {Γ Θ A B}
  → B ∣ Γ , A ⟶ Θ
  → Γ ⟶ Θ ∣ A
    --------------
  → B ∣ Γ ⟶ Θ

_⟨_/⟩ˢ : ∀ {Γ Θ A}
  → Γ , A ↦ Θ
  → Γ ⟶ Θ ∣ A
    ----------
  → Γ ↦ Θ

_[_/]ᵗ : ∀ {Γ Θ A B}
  → Γ ⟶ Θ , A ∣ B
  → A ∣ Γ ⟶ Θ
    --------------
  → Γ ⟶ Θ ∣ B

_[_/]ᶜ : ∀ {Γ Θ A B}
  → B ∣ Γ ⟶ Θ , A
  → A ∣ Γ ⟶ Θ
    --------------
  → B ∣ Γ ⟶ Θ

_[_/]ˢ : ∀ {Γ Θ A}
  → Γ ↦ Θ , A
  → A ∣ Γ ⟶ Θ
    ----------
  → Γ ↦ Θ

N ⟨ M /⟩ᵗ = sub-term TermKit CotermKit (λ{`Z → M ; (`S x) → ` x}) id-coterm N

L ⟨ M /⟩ᶜ = sub-coterm TermKit CotermKit (λ{`Z → M ; (`S x) → ` x}) id-coterm L

S ⟨ M /⟩ˢ = sub-statement TermKit CotermKit (λ{`Z → M ; (`S x) → ` x}) id-coterm S

N [ K /]ᵗ = sub-term TermKit CotermKit id-term (λ{`Z → K ; (`S x) → ` x}) N

L [ K /]ᶜ = sub-coterm TermKit CotermKit id-term (λ{`Z → K ; (`S x) → ` x}) L

S [ K /]ˢ = sub-statement TermKit CotermKit id-term (λ{`Z → K ; (`S x) → ` x}) S


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

  βL : ∀ {Γ Θ A} {V : Γ ⟶ Θ ∣ A} {S : Γ , A ↦ Θ}
    → Value V
      ------------------------------
    → V ● (μγ S) ˢ⟶ⱽ S ⟨ V /⟩ˢ

  βR : ∀ {Γ Θ A} {K : A ∣ Γ ⟶ Θ} {S : Γ ↦ Θ , A}
      ------------------------
    → (μθ S) ● K ˢ⟶ⱽ S [ K /]ˢ

data _ᶜ⟶ⱽ_ : ∀ {Γ Θ A} → (A ∣ Γ ⟶ Θ) → (A ∣ Γ ⟶ Θ) → Set where
  
  ηL : ∀ {Γ Θ A} {K : A ∣ Γ ⟶ Θ} 
      ------------------------
    → K ᶜ⟶ⱽ μγ ((γ 0) ● rename-coterm (rename-weaken id-var) id-var K)

data _ᵗ⟶ⱽ_ : ∀ {Γ Θ A} → (Γ ⟶ Θ ∣ A) → (Γ ⟶ Θ ∣ A) → Set where

  ηR : ∀ {Γ Θ A} {M : Γ ⟶ Θ ∣ A}
      ------------------------
    → M ᵗ⟶ⱽ μθ (rename-term id-var (rename-weaken id-var) M ● (θ 0))


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

  βR : ∀ {Γ Θ A} {S : Γ ↦ Θ , A} {P : A ∣ Γ ⟶ Θ}
    → Covalue P
      -------------------------
    → (μθ S) ● P ˢ⟶ᴺ S [ P /]ˢ

data _ᶜ⟶ᴺ_ : ∀ {Γ Θ A} → (A ∣ Γ ⟶ Θ) → (A ∣ Γ ⟶ Θ) → Set where
  
  ηL : ∀ {Γ Θ A} {K : A ∣ Γ ⟶ Θ} 
      ------------------------
    → K ᶜ⟶ᴺ μγ ((γ 0) ● rename-coterm (rename-weaken id-var) id-var K)

data _ᵗ⟶ᴺ_ : ∀ {Γ Θ A} → (Γ ⟶ Θ ∣ A) → (Γ ⟶ Θ ∣ A) → Set where

  ηR : ∀ {Γ Θ A} {M : Γ ⟶ Θ ∣ A}
      ------------------------
    → M ᵗ⟶ᴺ μθ (rename-term id-var (rename-weaken id-var) M ● (θ 0))

infix  2 _ˢ—↠ⱽ_
infix  1 beginˢⱽ_
infixr 2 _ˢ⟶ⱽ⟨_⟩_
infix  3 _∎ˢⱽ

-- infix  2 _—↠ᴺ_
-- infix  1 beginᴺ_
-- infixr 2 _ˢ⟶ᴺ⟨_⟩_
-- infix  3 _∎ᴺ

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
    → K′ ᶜ—↠ⱽ K″
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

lem : ∀ {A} → ∅ ⟶ ∅ ∣ A `+ `¬ A
lem = μθ (inr⟨ not[ μγ (inl⟨ γ 0 ⟩ ● (θ 0) ) ] ⟩ ● (θ 0))

lem-ref : ∀ {A} → ∅ ⟶ ∅ ∣ A  → A ∣ ∅ ⟶ ∅ → A `+ `¬ A ∣ ∅ ⟶ ∅
lem-ref M K = `[ K , not⟨ M ⟩ ]

-- lem-comp : ∀ {A} → (M : ∅ ⟶ ∅ ∣ A) → Value M → (K : A ∣ ∅ ⟶ ∅)
--      → (lem ● lem-ref M K) ˢ—↠ⱽ M ● K
-- lem-comp M M:V K = beginⱽ
--       μθ (inr⟨ not[ μγ (inl⟨ γ 0 ⟩ ● (θ 0) ) ] ⟩ ● (θ 0))
--     ● `[ K , not⟨ M ⟩ ]
--   ˢ⟶ⱽ⟨ βR ⟩
--       inr⟨ not[ μγ (inl⟨ γ 0 ⟩ ● `[ wkΓᶜ K , not⟨ wkΓᵗ M ⟩ ] ) ] ⟩
--     ● `[ K , not⟨ M ⟩ ]
--   ˢ⟶ⱽ⟨ β+₂ V-not ⟩
--       not[ μγ (inl⟨ γ 0 ⟩ ● `[ wkΓᶜ K , not⟨ wkΓᵗ M ⟩ ] ) ]
--     ● not⟨ M ⟩
--   ˢ⟶ⱽ⟨ β¬ ⟩
--       M
--     ● μγ (inl⟨ γ 0 ⟩ ● `[ wkΓᶜ K , not⟨ wkΓᵗ M ⟩ ] )
--   ˢ⟶ⱽ⟨ βL M:V ⟩
--       inl⟨ M ⟩
--     ● `[ (wkΓᶜ K) ⟨ M /⟩ᶜ , not⟨ (wkΓᵗ M) ⟨ M /⟩ᵗ ⟩ ]
--   ˢ⟶ⱽ⟨ {!   !} ⟩
--       inl⟨ M ⟩
--     ● `[ K , not⟨ M ⟩ ]
--   ˢ⟶ⱽ⟨ β+₁ M:V ⟩
--     M ● K
--   ∎ⱽ