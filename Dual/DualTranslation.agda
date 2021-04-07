{-# OPTIONS --rewriting #-}

module Dual.DualTranslation where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Agda.Builtin.Equality.Rewrite
open import Dual.Syntax
open import Dual.Substitution
open import Dual.Values
open import Data.Product using (Σ; _×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)


infix 12 _ᵒᵀ
infix 12 _ᵒⱽ 
infix 12 _ᵒˣ 
infix 12 _ᵒᴸ 
infix 12 _ᵒᴿ 
infix 12 _ᵒˢ 


--Dual Translation--

_ᵒᵀ : Type → Type
_ᵒˣ : Context → Context

(A `+ B)ᵒᵀ  = (A ᵒᵀ `× B ᵒᵀ)
(A `× B)ᵒᵀ  = (A ᵒᵀ `+ B ᵒᵀ)
(`¬ A)ᵒᵀ    = (`¬ (A)ᵒᵀ) 
(`ℕ)ᵒᵀ      = `ℕ

(∅ ᵒˣ)     = ∅
(Γ , A) ᵒˣ = ((Γ ᵒˣ) , (A ᵒᵀ))

_ᵒⱽ : ∀ {Γ A} → (Γ ∋ A) → (Γ ᵒˣ ∋ A ᵒᵀ)  

`Z ᵒⱽ     = `Z
(`S x) ᵒⱽ = `S (x ᵒⱽ)


_ᵒˢ : ∀ {Γ Θ} → (Γ ↦ Θ) → (Θ ᵒˣ ↦ Γ ᵒˣ)
_ᵒᴸ : ∀ {Γ Θ A} → (Γ ⟶ Θ ∣ A) → (A ᵒᵀ ∣ Θ ᵒˣ ⟶ Γ ᵒˣ)
_ᵒᴿ : ∀ {Γ Θ A} → (A ∣ Γ ⟶ Θ) → (Θ ᵒˣ ⟶ Γ ᵒˣ ∣ A ᵒᵀ)

(` x)ᵒᴸ                 = ` x ᵒⱽ
(`⟨ M , N ⟩) ᵒᴸ           = `[ M ᵒᴸ , N ᵒᴸ ]
(inl⟨ M ⟩) ᵒᴸ            = fst[ M ᵒᴸ ] 
(inr⟨ M ⟩) ᵒᴸ            = snd[ M ᵒᴸ ]
(not[ K ]) ᵒᴸ           = not⟨ K ᵒᴿ ⟩
(μθ {Γ} {Θ} {A} (S)) ᵒᴸ = μγ( _ᵒˢ {Γ} {(Θ , A)} S )


(` α) ᵒᴿ                = ` α ᵒⱽ
(`[ K , L ]) ᵒᴿ          = `⟨ K ᵒᴿ , L ᵒᴿ ⟩
(fst[ K ]) ᵒᴿ           = inl⟨ K ᵒᴿ ⟩
(snd[ K ]) ᵒᴿ           = inr⟨ K ᵒᴿ ⟩
(not⟨ M ⟩) ᵒᴿ            = not[ M ᵒᴸ ]
(μγ {Γ} {Θ} {A} (S)) ᵒᴿ = μθ( _ᵒˢ {(Γ , A)} {Θ} (S) )

(M ● K) ᵒˢ = K ᵒᴿ ● M ᵒᴸ

Vᵒ≡P : ∀ {Γ Θ A} (V : Γ ⟶ Θ ∣ A) → Value V → (Covalue (V ᵒᴸ))
Vᵒ≡P (` x) V-var = CV-covar
Vᵒ≡P (`⟨ V , W ⟩) (V-prod v w) = CV-sum (Vᵒ≡P V v) (Vᵒ≡P W w)
Vᵒ≡P (inl⟨ V ⟩) (V-inl v) = CV-fst (Vᵒ≡P V v)
Vᵒ≡P (inr⟨ W ⟩) (V-inr w) = CV-snd (Vᵒ≡P W w)
Vᵒ≡P (not[ K ]) V-not = CV-not

Pᵒ≡V : ∀ {Γ Θ A} (P : A ∣ Γ ⟶ Θ) → Covalue P → (Value (P ᵒᴿ))
Pᵒ≡V (` α) CV-covar = V-var
Pᵒ≡V (`[ P , Q ]) (CV-sum p q) = V-prod (Pᵒ≡V P p) (Pᵒ≡V Q q)
Pᵒ≡V (fst[ P ]) (CV-fst p) = V-inl (Pᵒ≡V P p)
Pᵒ≡V (snd[ Q ]) (CV-snd q) = V-inr (Pᵒ≡V Q q)
Pᵒ≡V (not⟨ M ⟩) CV-not = V-not

dual-ren : ∀ Γ Γ′ → Γ ↝ Γ′ → (Γ ᵒˣ) ↝ (Γ′ ᵒˣ)
dual-ren ∅ Γ′ ρ ()
dual-ren (Γ , A) Γ′ ρ `Z = (ρ `Z) ᵒⱽ
dual-ren (Γ , A) Γ′ ρ (`S x) = dual-ren Γ Γ′ (ren-skip ρ) x

dual-coterm-sub : ∀ Γ Θ Θ′ → Θ –[(λ Θ A → A ∣ Γ ⟶ Θ)]→ Θ′ → (Θ ᵒˣ) –[ (λ Θ A → Θ ⟶ Γ ᵒˣ ∣ A) ]→ (Θ′ ᵒˣ)
dual-coterm-sub Γ (Θ , A) Θ′ σ `Z = (σ `Z) ᵒᴿ
dual-coterm-sub Γ (Θ , A) Θ′ σ (`S x) = dual-coterm-sub Γ Θ Θ′ (sub-skip (λ Θ A → A ∣ Γ ⟶ Θ) σ) x

dual-termval-sub : ∀ Γ Γ′ Θ → Γ –[(λ Γ A → TermValue Γ Θ A)]→ Γ′ → (Γ ᵒˣ) –[(λ Γ A → CotermValue (Θ ᵒˣ) Γ A)]→ (Γ′ ᵒˣ)
dual-termval-sub (Γ , A) Γ′ Θ σ `Z = ⟨ ((proj₁ (σ `Z )) ᵒᴸ) , Vᵒ≡P (proj₁ (σ `Z)) (proj₂ (σ `Z)) ⟩
dual-termval-sub (Γ , A) Γ′ Θ σ (`S x) = dual-termval-sub Γ Γ′ Θ (sub-skip (λ Γ A → TermValue Γ Θ A) σ) x

--Properties of the Dual Translation--

--The Dual Translation is an Involution--

[Aᵒᵀ]ᵒᵀ≡A : ∀ {A} → (A ᵒᵀ) ᵒᵀ ≡ A
[Aᵒᵀ]ᵒᵀ≡A {`ℕ}     = refl
[Aᵒᵀ]ᵒᵀ≡A {`¬ A}   = cong `¬_   [Aᵒᵀ]ᵒᵀ≡A 
[Aᵒᵀ]ᵒᵀ≡A {A `+ B} = cong₂ _`+_ ([Aᵒᵀ]ᵒᵀ≡A {A}) ([Aᵒᵀ]ᵒᵀ≡A {B})
[Aᵒᵀ]ᵒᵀ≡A {A `× B} = cong₂ _`×_ ([Aᵒᵀ]ᵒᵀ≡A {A}) ([Aᵒᵀ]ᵒᵀ≡A {B})

[Γᵒˣ]ᵒˣ≡Γ : ∀ {Γ} → (Γ ᵒˣ) ᵒˣ ≡ Γ
[Γᵒˣ]ᵒˣ≡Γ {∅}       = refl
[Γᵒˣ]ᵒˣ≡Γ {(Γ , A)} = cong₂ _,_ [Γᵒˣ]ᵒˣ≡Γ [Aᵒᵀ]ᵒᵀ≡A

--we use these rewrite rules to handle equality between a term and a dual translated term
--as those two terms will be indexed by different contexts and type
{-# REWRITE [Aᵒᵀ]ᵒᵀ≡A #-}
{-# REWRITE [Γᵒˣ]ᵒˣ≡Γ #-}

[xᵒⱽ]ᵒⱽ≡x : ∀ {Γ A} (x : Γ ∋ A) → ((x ᵒⱽ) ᵒⱽ) ≡ x
[xᵒⱽ]ᵒⱽ≡x (`Z)   = refl
[xᵒⱽ]ᵒⱽ≡x (`S x) = cong `S ([xᵒⱽ]ᵒⱽ≡x x)

[Kᵒᴿ]ᵒᴸ≡K : ∀ {Γ Θ A} (K : A ∣ Γ ⟶ Θ) → (K ᵒᴿ) ᵒᴸ ≡ K
[Mᵒᴸ]ᵒᴿ≡M : ∀ {Γ Θ A} (M : Γ ⟶ Θ ∣ A) → (M ᵒᴸ) ᵒᴿ ≡ M 
[Sᵒˢ]ᵒˢ≡S : ∀ {Γ Θ}   (S : Γ ↦ Θ)     → (S ᵒˢ) ᵒˢ ≡ S

[Mᵒᴸ]ᵒᴿ≡M (` x)        = cong `_     ([xᵒⱽ]ᵒⱽ≡x x)
[Mᵒᴸ]ᵒᴿ≡M (`⟨ M , N ⟩)  = cong₂ `⟨_,_⟩ ([Mᵒᴸ]ᵒᴿ≡M M) ([Mᵒᴸ]ᵒᴿ≡M N)
[Mᵒᴸ]ᵒᴿ≡M (inl⟨ M ⟩)    = cong inl⟨_⟩ ([Mᵒᴸ]ᵒᴿ≡M M)
[Mᵒᴸ]ᵒᴿ≡M (inr⟨ M ⟩)    = cong inr⟨_⟩ ([Mᵒᴸ]ᵒᴿ≡M M)
[Mᵒᴸ]ᵒᴿ≡M (not[ K ])   = cong not[_] ([Kᵒᴿ]ᵒᴸ≡K K)
[Mᵒᴸ]ᵒᴿ≡M (μθ S)       = cong μθ     ([Sᵒˢ]ᵒˢ≡S S)

[Kᵒᴿ]ᵒᴸ≡K (` α)        = cong `_     ([xᵒⱽ]ᵒⱽ≡x α)
[Kᵒᴿ]ᵒᴸ≡K (`[ K , L ]) = cong₂ `[_,_] ([Kᵒᴿ]ᵒᴸ≡K K) ([Kᵒᴿ]ᵒᴸ≡K L)
[Kᵒᴿ]ᵒᴸ≡K (fst[ K ])   = cong fst[_] ([Kᵒᴿ]ᵒᴸ≡K K)
[Kᵒᴿ]ᵒᴸ≡K (snd[ K ])   = cong snd[_] ([Kᵒᴿ]ᵒᴸ≡K K)
[Kᵒᴿ]ᵒᴸ≡K (not⟨ M ⟩)    = cong not⟨_⟩ ([Mᵒᴸ]ᵒᴿ≡M M)
[Kᵒᴿ]ᵒᴸ≡K (μγ S)       = cong μγ     ([Sᵒˢ]ᵒˢ≡S S)

[Sᵒˢ]ᵒˢ≡S (M ● K)     = cong₂ _●_   ([Mᵒᴸ]ᵒᴿ≡M M) ([Kᵒᴿ]ᵒᴸ≡K K)

--A Dual Calculus term is derivable iff its dual is derivable--

Γ⟶Θ∣A⇒Aᵒ∣Θᵒ⟶Γᵒ : ∀ {Γ Θ A} → (Γ ⟶ Θ ∣ A) → A ᵒᵀ ∣ Θ ᵒˣ ⟶ Γ ᵒˣ
Γ⟶Θ∣A⇒Aᵒ∣Θᵒ⟶Γᵒ M = M ᵒᴸ

Γ⟶Θ∣A⇐Aᵒ∣Θᵒ⟶Γᵒ : ∀ {Γ Θ A} → (A ᵒᵀ ∣ Θ ᵒˣ ⟶ Γ ᵒˣ) → Γ ⟶ Θ ∣ A
Γ⟶Θ∣A⇐Aᵒ∣Θᵒ⟶Γᵒ Mᵒᴸ = Mᵒᴸ ᵒᴿ 

A∣Γ⟶Θ⇒Θᵒ⟶Γᵒ∣Aᵒ : ∀ {Γ Θ A} → (A ∣ Γ ⟶ Θ) → Θ ᵒˣ ⟶ Γ ᵒˣ ∣ A ᵒᵀ
A∣Γ⟶Θ⇒Θᵒ⟶Γᵒ∣Aᵒ K = K ᵒᴿ

A∣Γ⟶Θ⇐Θᵒ⟶Γᵒ∣Aᵒ : ∀ {Γ Θ A} → (Θ ᵒˣ ⟶ Γ ᵒˣ ∣ A ᵒᵀ) → A ∣ Γ ⟶ Θ
A∣Γ⟶Θ⇐Θᵒ⟶Γᵒ∣Aᵒ Kᵒᴿ = Kᵒᴿ ᵒᴸ

Γ↦Θ⇒Θᵒ↦Γᵒ : ∀ {Γ Θ} → (Γ ↦ Θ) → Θ ᵒˣ ↦ Γ ᵒˣ
Γ↦Θ⇒Θᵒ↦Γᵒ S = S ᵒˢ

Γ↦Θ⇐Θᵒ↦Γᵒ : ∀ {Γ Θ} → (Θ ᵒˣ ↦ Γ ᵒˣ) → Γ ↦ Θ
Γ↦Θ⇐Θᵒ↦Γᵒ Sᵒˢ = Sᵒˢ ᵒˢ
