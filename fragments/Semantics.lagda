\begin{code}
{-# OPTIONS --rewriting #-}
{-# OPTIONS --allow-unsolved-metas #-}

module fragments.Semantics where

open import Dual.Syntax.Core
open import Dual.Syntax.Substitution
open import Dual.Syntax.Duality
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Product using (Σ; _×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Dual.Syntax.Values
open import Axiom.Extensionality.Propositional using (Extensionality; ExtensionalityImplicit)
open import Level as L hiding (lift) public



infix 2 _ˢ⟶ⱽ_
infix 2 _ᶜ⟶ⱽ_
infix 2 _ᵗ⟶ⱽ_

infix 2 _ˢ⟶ᴺ_
infix 2 _ᶜ⟶ᴺ_
infix 2 _ᵗ⟶ᴺ_
\end{code}
%<*cbvrty>
\begin{code}
data _ˢ⟶ⱽ_ : ∀ {Γ Θ} → (Γ ↦ Θ) → (Γ ↦ Θ) → Set where
\end{code}
%</cbvrty>

%<*cbvr>
\begin{code}
  β×₁ : ∀ {Γ Θ A B} {V : Γ ⟶ Θ ∣ A} {W : Γ ⟶ Θ ∣ B} {K : A ∣ Γ ⟶ Θ} (v : Value V) (w : Value W)
    → `⟨ V , W ⟩ ● fst[ K ] ˢ⟶ⱽ V ● K

  β×₂ : ∀ {Γ Θ A B} {V : Γ ⟶ Θ ∣ A} {W : Γ ⟶ Θ ∣ B} {L : B ∣ Γ ⟶ Θ} (v : Value V) (w : Value W)
    → `⟨ V , W ⟩ ● snd[ L ] ˢ⟶ⱽ W ● L

  β+₁ : ∀ {Γ Θ A B} {V : Γ ⟶ Θ ∣ A} {K : A ∣ Γ ⟶ Θ} {L : B ∣ Γ ⟶ Θ} (v : Value V)
    → inl⟨ V ⟩ ● `[ K , L ] ˢ⟶ⱽ V ● K

  β+₂ : ∀ {Γ Θ A B} {W : Γ ⟶ Θ ∣ B} {K : A ∣ Γ ⟶ Θ} {L : B ∣ Γ ⟶ Θ} (w : Value W)
    → inr⟨ W ⟩ ● `[ K , L ] ˢ⟶ⱽ W ● L

  β¬ : ∀ {Γ Θ A} {M : Γ ⟶ Θ ∣ A} {K : A ∣ Γ ⟶ Θ}
    → not[ K ] ● not⟨ M ⟩ ˢ⟶ⱽ M ● K

  βL : ∀ {Γ Θ A} {V : Γ ⟶ Θ ∣ A} {S : Γ , A ↦ Θ} (v : Value V)

    → V ● (μγ S) ˢ⟶ⱽ S ⱽ⟨ ⟨ V , v ⟩ /⟩ˢ

  βR : ∀ {Γ Θ A} {K : A ∣ Γ ⟶ Θ} {S : Γ ↦ Θ , A}
    → (μθ S) ● K ˢ⟶ⱽ S [ K /]ˢ
\end{code}
%</cbvr>

\begin{code}
data _ᶜ⟶ⱽ_ : ∀ {Γ Θ A} → (A ∣ Γ ⟶ Θ) → (A ∣ Γ ⟶ Θ) → Set where
  
  ηL : ∀ {Γ Θ A} {K : A ∣ Γ ⟶ Θ} 
      ------------------------
    → K ᶜ⟶ⱽ μγ ((γ 0) ● wkΓᶜ K)

data _ᵗ⟶ⱽ_ : ∀ {Γ Θ A} → (Γ ⟶ Θ ∣ A) → (Γ ⟶ Θ ∣ A) → Set where

  ηR : ∀ {Γ Θ A} {M : Γ ⟶ Θ ∣ A}
      ------------------------
    → M ᵗ⟶ⱽ μθ (wkΘᵗ M ● (θ 0))


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

\end{code}

\begin{code}
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
\end{code}

%<*example>
\begin{code}
example : ∀ {A B} → (V : ∅ ⟶ ∅ ∣ A) → (W : ∅ ⟶ ∅ ∣ B) → (K : A ∣ ∅ ⟶ ∅)
     → Value V → Value W
     → (not[ fst[ K ] ] ● not⟨ `⟨ V , W ⟩ ⟩) ˢ—↠ⱽ V ● K
example V W K v w = beginˢⱽ
  (not[ fst[ K ] ]) ● (not⟨ `⟨ V , W ⟩ ⟩)  ˢ⟶ⱽ⟨ β¬ ⟩
  `⟨ V , W ⟩ ● fst[ K ]                   ˢ⟶ⱽ⟨ β×₁ v w ⟩
  V ● K                                   ∎ˢⱽ
\end{code}
%</example>

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

%<*lem>
\begin{code}
lem-proof : ∀ {A} → ∅ ⟶ ∅ ∣ A `+ `¬ A
lem-proof = μθ (inr⟨ not[ μγ (inl⟨ γ 0 ⟩ ● (θ 0) ) ] ⟩ ● (θ 0))
\end{code}
%</lem>
\begin{code}
lem-ref : ∀ {A} → ∅ ⟶ ∅ ∣ A  → A ∣ ∅ ⟶ ∅ → A `+ `¬ A ∣ ∅ ⟶ ∅
lem-ref M K = `[ K , not⟨ M ⟩ ]
\end{code}

%<*lem-comp>
\begin{code}
lem-comp : ∀ {A} → (M : ∅ ⟶ ∅ ∣ A) → Value M → (K : A ∣ ∅ ⟶ ∅)
     → (lem-proof ● lem-ref M K) ˢ—↠ⱽ M ● K
lem-comp M M:V K = beginˢⱽ
    μθ (inr⟨ not[ μγ (inl⟨ γ 0 ⟩ ● (θ 0) ) ] ⟩ ● (θ 0)) ● `[ K , not⟨ M ⟩ ]
  ˢ⟶ⱽ⟨ βR ⟩
    inr⟨ not[ μγ (inl⟨ γ 0 ⟩ ● `[ wkΓᶜ K , not⟨ wkΓᵗ M ⟩ ] ) ] ⟩ ● `[ K , not⟨ M ⟩ ]
  ˢ⟶ⱽ⟨ β+₂ V-not ⟩
    not[ μγ (inl⟨ γ 0 ⟩ ● `[ wkΓᶜ K , not⟨ wkΓᵗ M ⟩ ] ) ] ● not⟨ M ⟩
  ˢ⟶ⱽ⟨ β¬ ⟩
    M ● μγ (inl⟨ γ 0 ⟩ ● `[ wkΓᶜ K , not⟨ wkΓᵗ M ⟩ ] )
  ˢ⟶ⱽ⟨ βL M:V ⟩
    ((inl⟨ γ 0 ⟩ ● `[ (wkΓᶜ K) , not⟨ (wkΓᵗ M) ⟩ ]) ⱽ⟨ ⟨ M , M:V ⟩ /⟩ˢ)
  ˢ⟶ⱽ⟨ {!   !} ⟩
    inl⟨ M ⟩ ● `[ K , not⟨ M ⟩ ]
  ˢ⟶ⱽ⟨ β+₁ M:V ⟩
    M ● K
  ∎ˢⱽ
\end{code}
%</lem-comp>