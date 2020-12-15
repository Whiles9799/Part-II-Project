{-# OPTIONS --rewriting #-}

module Dual.CPSTransformation where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_ ; z≤n; s≤s)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Relation.Nullary using (¬_)
open import Agda.Builtin.Equality.Rewrite
open import Axiom.Extensionality.Propositional using (Extensionality; ExtensionalityImplicit)
open import Level as L hiding (lift) public
open import Dual.Syntax
open import Dual.DualTranslation

infix 12 _ⱽᵀ
infix 12 _ⱽⱽ
infix 12 _ⱽˣ
infix 12 _ⱽᴸ
infix 12 _ⱽᴿ
infix 12 _ⱽᶜ

infix 12 _ᴺᵀ
infix 12 _ᴺⱽ
infix 12 _ᴺˣ
infix 12 _ᴺᴸ
infix 12 _ᴺᴿ
infix 12 _ᴺᶜ


--Call-by-Value CPS Transformation--


--Types and Contexts--

_ⱽᵀ : Type → Set
_ⱽˣ : Context → Set

`ℕ ⱽᵀ       = ℕ
(A `× B) ⱽᵀ = (A ⱽᵀ) × (B ⱽᵀ)
(A `+ B) ⱽᵀ = (A ⱽᵀ) ⊎ (B ⱽᵀ)
(`¬ A) ⱽᵀ   = (A ⱽᵀ) → ⊥

∅ ⱽˣ       = ⊤
(Γ , A) ⱽˣ = Γ ⱽˣ  × A ⱽᵀ  


--Variables--

_ⱽⱽ : ∀ {Γ A} → (Γ ∋ A) → ((Γ ⱽˣ) → (A ⱽᵀ))
_ⱽⱽ `Z     = λ x → proj₂ x 
_ⱽⱽ (`S x) = λ c → ((x ⱽⱽ) (proj₁ c))

Γ∋A⇒¬Γ∋¬A : ∀ {Γ A} → (Γ ∋ A) → (`¬ˣ Γ) ∋ (`¬ A)
Γ∋A⇒¬Γ∋¬A `Z     = `Z
Γ∋A⇒¬Γ∋¬A (`S x) = `S (Γ∋A⇒¬Γ∋¬A x)


--Terms--

_ⱽᴸ : ∀ {Γ Θ A} → (Γ ⟶ Θ ∣ A) → (Γ ⱽˣ × (`¬ˣ Θ) ⱽˣ) → ((`¬ `¬ A) ⱽᵀ)
_ⱽᴿ : ∀ {Γ Θ A} → (A ∣ Γ ⟶ Θ) → (Γ ⱽˣ × (`¬ˣ Θ) ⱽˣ) → ((`¬ A) ⱽᵀ)
_ⱽᶜ : ∀ {Γ Θ}   → (Γ ↦ Θ)     → (Γ ⱽˣ × (`¬ˣ Θ) ⱽˣ) → ⊥

_ⱽᴸ (` x)            = λ c k → k ((x ⱽⱽ) (proj₁ c))
`⟨ M , N ⟩ ⱽᴸ         = λ c k → (M ⱽᴸ) c (λ x → (N ⱽᴸ) c (λ y → k ⟨ x , y ⟩))
inl⟨ M ⟩ ⱽᴸ           = λ c k → (M ⱽᴸ) c (λ x → k (inj₁ x))
inr⟨ M ⟩ ⱽᴸ           = λ c k → (M ⱽᴸ) c (λ x → k (inj₂ x))
not[ K ] ⱽᴸ          = λ c k → k (λ z → (K ⱽᴿ) c z)
_ⱽᴸ {Γ}{Θ}{A} (μθ S) = λ c α → (S ⱽᶜ) ⟨ (proj₁ c) , ⟨ (proj₂ c) , α ⟩ ⟩

(` α) ⱽᴿ             = λ c z → ((Γ∋A⇒¬Γ∋¬A α) ⱽⱽ) (proj₂ c) z 
`[ K , L ] ⱽᴿ        = λ c → λ{ (inj₁ x) → (K ⱽᴿ) c x ; (inj₂ y) → (L ⱽᴿ) c y}
fst[ K ] ⱽᴿ          = λ c → λ{ ⟨ x , _ ⟩ → (K ⱽᴿ) c x} 
snd[ L ] ⱽᴿ          = λ c → λ{ ⟨ _ , y ⟩ → (L ⱽᴿ) c y}
not⟨ M ⟩ ⱽᴿ           = λ c z → (λ k → (M ⱽᴸ) c k) z
_ⱽᴿ {Γ}{Θ}{A} (μγ S) = λ c x →  (S ⱽᶜ) ⟨ ⟨ proj₁ c , x ⟩ , (proj₂ c) ⟩

(M ● K) ⱽᶜ           = λ c → ((M ⱽᴸ) c) ((K ⱽᴿ) c)


--Call-by-Name CPS Transformation--


--Types and Contexts--
_ᴺᵀ : Type → Set
_ᴺˣ : Context → Set

`ℕ ᴺᵀ        = ℕ
(A `× B) ᴺᵀ  = (A ᴺᵀ) ⊎ (B ᴺᵀ)
(A `+ B) ᴺᵀ  = (A ᴺᵀ) × (B ᴺᵀ)
(`¬ A) ᴺᵀ    = (A ᴺᵀ) → ⊥

∅ ᴺˣ       = ⊤
(Γ , A) ᴺˣ =  Γ ᴺˣ × A ᴺᵀ 


--Variables--
_ᴺⱽ : ∀ {Θ A} → (Θ ∋ A) → (Θ ᴺˣ) → (A ᴺᵀ)
_ᴺⱽ `Z     = λ x → proj₂ x 
_ᴺⱽ (`S x) = λ c → ((x ᴺⱽ) (proj₁ c))


--Terms--
_ᴺᴸ : ∀ {Γ Θ A} → (Γ ⟶ Θ ∣ A) → (Θ ᴺˣ × (`¬ˣ Γ) ᴺˣ) → (`¬ A) ᴺᵀ
_ᴺᴿ : ∀ {Γ Θ A} → (A ∣ Γ ⟶ Θ) → (Θ ᴺˣ × (`¬ˣ Γ) ᴺˣ) → (`¬ `¬ A) ᴺᵀ
_ᴺᶜ : ∀ {Γ Θ}   → (Γ ↦ Θ)     → (Θ ᴺˣ × (`¬ˣ Γ) ᴺˣ) → ⊥

(` x) ᴺᴸ             = λ c k → ((Γ∋A⇒¬Γ∋¬A x) ᴺⱽ) (proj₂ c) k
`⟨ M , N ⟩ ᴺᴸ         = λ c → λ{(inj₁ α) → (M ᴺᴸ) c α ; (inj₂ β) → (N ᴺᴸ) c β}
inl⟨ M ⟩ ᴺᴸ           = λ c → λ{⟨ α , _ ⟩ → (M ᴺᴸ) c α}
inr⟨ N ⟩ ᴺᴸ           = λ c → λ{⟨ _ , β ⟩ → (N ᴺᴸ) c β}
not[ K ] ᴺᴸ          = λ c k → (λ z → (K ᴺᴿ) c z) k
_ᴺᴸ {Γ}{Θ}{A} (μθ S) = λ c α → (S ᴺᶜ) ⟨ ⟨ proj₁ c , α ⟩ , proj₂ c ⟩

(` α) ᴺᴿ             = λ c z → z ((α ᴺⱽ) (proj₁ c))
`[ K , L ] ᴺᴿ        = λ c z → (K ᴺᴿ) c (λ α → (L ᴺᴿ) c (λ β → z ⟨ α , β ⟩))
fst[ K ] ᴺᴿ          = λ c z → (K ᴺᴿ) c (λ α → z (inj₁ α))
snd[ L ] ᴺᴿ          = λ c z → (L ᴺᴿ) c (λ β → z (inj₂ β))
not⟨ M ⟩ ᴺᴿ           = λ c z → z(λ k → (M ᴺᴸ) c k)
_ᴺᴿ {Γ}{Θ}{A} (μγ S) = λ c x →  (S ᴺᶜ) ⟨ proj₁ c , ⟨ proj₂ c , x ⟩ ⟩

(M ● K) ᴺᶜ           = λ c → ((K ᴺᴿ) c) ((M ᴺᴸ) c)


--Proofs of Duality--

--Types and Contexts--

Aⱽ≡Aᵒᴺ : ∀ {A} → A ⱽᵀ ≡ (A ᵒᵀ) ᴺᵀ
Aⱽ≡Aᵒᴺ {`ℕ}     = refl 
Aⱽ≡Aᵒᴺ {A `+ B} = cong₂ _⊎_ (Aⱽ≡Aᵒᴺ {A}) (Aⱽ≡Aᵒᴺ {B})
Aⱽ≡Aᵒᴺ {A `× B} = cong₂ _×_ (Aⱽ≡Aᵒᴺ {A}) (Aⱽ≡Aᵒᴺ {B})
Aⱽ≡Aᵒᴺ {`¬ A}   = cong ¬_ Aⱽ≡Aᵒᴺ

Γⱽ≡Γᵒᴺ : ∀ {Γ} → Γ ⱽˣ ≡ (Γ ᵒˣ) ᴺˣ
Γⱽ≡Γᵒᴺ {∅}       = refl
Γⱽ≡Γᵒᴺ {(Γ , A)} = cong₂ _×_ Γⱽ≡Γᵒᴺ Aⱽ≡Aᵒᴺ

{-# REWRITE Aⱽ≡Aᵒᴺ #-}
{-# REWRITE Γⱽ≡Γᵒᴺ #-}


postulate
  ext  : Extensionality 0ℓ 0ℓ

--Lemmas required for following proofs--

[¬Γ]ᵒ≡¬[Γᵒ] : ∀ {Γ} → (`¬ˣ Γ) ᵒˣ ≡ `¬ˣ (Γ ᵒˣ)
[¬Γ]ᵒ≡¬[Γᵒ] {∅}       = refl
[¬Γ]ᵒ≡¬[Γᵒ] {(Γ , A)} = cong₂ _,_ ([¬Γ]ᵒ≡¬[Γᵒ] {Γ}) refl

{-# REWRITE [¬Γ]ᵒ≡¬[Γᵒ] #-}

[Γ∋A⇒¬Γ∋¬Ax]ᵒ≡Γ∋A⇒¬Γ∋¬A[xᵒ] : ∀ {Γ A} (x : Γ ∋ A) → Γ∋A⇒¬Γ∋¬A x ᵒⱽ ≡ Γ∋A⇒¬Γ∋¬A (x ᵒⱽ)
[Γ∋A⇒¬Γ∋¬Ax]ᵒ≡Γ∋A⇒¬Γ∋¬A[xᵒ] `Z     = refl
[Γ∋A⇒¬Γ∋¬Ax]ᵒ≡Γ∋A⇒¬Γ∋¬A[xᵒ] (`S x) = cong `S ([Γ∋A⇒¬Γ∋¬Ax]ᵒ≡Γ∋A⇒¬Γ∋¬A[xᵒ] x)

{-# REWRITE [Γ∋A⇒¬Γ∋¬Ax]ᵒ≡Γ∋A⇒¬Γ∋¬A[xᵒ] #-}

--Variables--

xⱽ≡xᵒᴺ : ∀ {Γ A} (x : Γ ∋ A) → x ⱽⱽ ≡ ((x ᵒⱽ) ᴺⱽ)
xⱽ≡xᵒᴺ `Z         = refl
xⱽ≡xᵒᴺ (`S x)     = ext (λ c → cong (λ - → - (proj₁ c)) (xⱽ≡xᵒᴺ x))

--Terms--

Mⱽ≡Mᵒᴺ : ∀ {Γ Θ A} (M : Γ ⟶ Θ ∣ A) (c : Γ ⱽˣ × (`¬ˣ Θ) ⱽˣ) (k : ((`¬ A) ⱽᵀ)) → (M ⱽᴸ) c k ≡ ((M ᵒᴸ) ᴺᴿ) c k
Kⱽ≡Kᵒᴺ : ∀ {Γ Θ A} (K : A ∣ Γ ⟶ Θ) (c : Γ ⱽˣ × (`¬ˣ Θ) ⱽˣ) (k : (A) ⱽᵀ)      → (K ⱽᴿ) c k ≡ ((K ᵒᴿ) ᴺᴸ) c k
Sⱽ≡Sᵒᴺ : ∀ {Γ Θ}   (S : Γ ↦ Θ)     (c : Γ ⱽˣ × (`¬ˣ Θ) ⱽˣ)                   → (S ⱽᶜ) c   ≡ ((S ᵒᶜ) ᴺᶜ) c

Mⱽ≡Mᵒᴺ (` x) ⟨ c , _ ⟩ k       = cong  (λ - → k(-  c)) (xⱽ≡xᵒᴺ x)
Mⱽ≡Mᵒᴺ `⟨ M , N ⟩ c k          = trans (Mⱽ≡Mᵒᴺ M c (λ x → (N ⱽᴸ) c ((λ y → k ⟨ x , y ⟩)))) (cong (λ - → ((M ᵒᴸ) ᴺᴿ) c - ) (ext (λ x → Mⱽ≡Mᵒᴺ N c (λ y → k ⟨ x , y ⟩))))
  -- begin
  --   ((`⟨ M , N ⟩ ⱽᴸ) c k)
  -- ≡⟨⟩
  --   ((M ⱽᴸ) c (λ x → (N ⱽᴸ) c (λ y → k ⟨ x , y ⟩)))
  -- ≡⟨ Mⱽ≡Mᵒᴺ M c (λ x → (N ⱽᴸ) c ((λ y → k ⟨ x , y ⟩))) ⟩ 
  --   ((M ᵒᴸ) ᴺᴿ) c (λ x → (N ⱽᴸ) c (λ y → k ⟨ x , y ⟩))  
  -- ≡⟨ cong (λ - → ((M ᵒᴸ) ᴺᴿ) c - ) (ext (λ x → Mⱽ≡Mᵒᴺ N c (λ y → k ⟨ x , y ⟩))) ⟩ --((M ᵒᴸ) ᴺᴿ) c (λ x → (N ⱽᴸ) c (λ y → k ⟨ x , y ⟩)) ≡ ((M ᵒᴸ) ᴺᴿ) c (λ x → ((N ᵒᴸ) ᴺᴿ) c (λ y → k ⟨ x , y ⟩))
  --   (((M ᵒᴸ) ᴺᴿ) c (λ x → ((N ᵒᴸ) ᴺᴿ) c (λ y → k ⟨ x , y ⟩)))
  -- ∎ 
Mⱽ≡Mᵒᴺ inl⟨ M ⟩ c k            = Mⱽ≡Mᵒᴺ M c λ x → k (inj₁ x ) 
Mⱽ≡Mᵒᴺ inr⟨ M ⟩ c k            = Mⱽ≡Mᵒᴺ M c λ x → k (inj₂ x )
Mⱽ≡Mᵒᴺ not[ K ] c k           = cong k (ext (λ x → Kⱽ≡Kᵒᴺ K c x))
Mⱽ≡Mᵒᴺ (μθ α) c k             = Sⱽ≡Sᵒᴺ α ⟨ proj₁ c , ⟨ proj₂ c , k ⟩ ⟩ 

Kⱽ≡Kᵒᴺ (` α) c k             = cong (λ x → x (proj₂ c) k) (xⱽ≡xᵒᴺ (Γ∋A⇒¬Γ∋¬A α)) 
Kⱽ≡Kᵒᴺ fst[ K ] c ⟨ k , _ ⟩   = Kⱽ≡Kᵒᴺ K c k
Kⱽ≡Kᵒᴺ snd[ K ] c ⟨ _ , k ⟩   = Kⱽ≡Kᵒᴺ K c k
Kⱽ≡Kᵒᴺ `[ K , L ] c (inj₁ k) = Kⱽ≡Kᵒᴺ K c k
Kⱽ≡Kᵒᴺ `[ K , L ] c (inj₂ k) = Kⱽ≡Kᵒᴺ L c k
Kⱽ≡Kᵒᴺ not⟨ M ⟩ c k           = Mⱽ≡Mᵒᴺ M c k
Kⱽ≡Kᵒᴺ (μγ x) c k            = Sⱽ≡Sᵒᴺ x ⟨ ⟨ proj₁ c , k ⟩ , proj₂ c ⟩

Sⱽ≡Sᵒᴺ (M ● K) c             = trans (Mⱽ≡Mᵒᴺ M c ((K ⱽᴿ) c)) (cong (λ - → ((M ᵒᴸ) ᴺᴿ) c -) (ext (λ x → Kⱽ≡Kᵒᴺ K c x)))
--  begin
--    (M ⱽᴸ) c ((K ⱽᴿ) c)
--   ≡⟨ Mⱽ≡Mᵒᴺ M c ((K ⱽᴿ) c) ⟩
--     ((M ᵒᴸ) ᴺᴿ) c ((K ⱽᴿ) c)
--   ≡⟨ cong (λ - → ((M ᵒᴸ) ᴺᴿ) c -) (ext (λ x → Kⱽ≡Kᵒᴺ K c x)) ⟩ --((M ᵒᴸ) ᴺᴿ) c ((K ⱽᴿ) c) ≡ ((M ᵒᴸ) ᴺᴿ) c (((K ᵒᴿ) ᴺᴸ) c)
--     ((M ᵒᴸ) ᴺᴿ) c (((K ᵒᴿ) ᴺᴸ) c)
--   ∎
