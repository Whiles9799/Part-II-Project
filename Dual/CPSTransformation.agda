{-# OPTIONS --rewriting #-}

module Dual.CPSTransformation (R : Set) where

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
open import Dual.Semantics
open import Dual.Substitution
open import Dual.Values

infix 12 _ⱽᵀ
infix 12 _ⱽⱽ
infix 12 _ⱽˣ
infix 12 _ⱽᴸ
infix 12 _ⱽᴿ
infix 12 _ⱽˢ

infix 12 _ᴺᵀ
infix 12 _ᴺⱽ
infix 12 _ᴺˣ
infix 12 _ᴺᴸ
infix 12 _ᴺᴿ
infix 12 _ᴺˢ


--Call-by-Value CPS Transformation--


--Types and Contexts--

_ⱽᵀ : Type → Set
_ⱽˣ : Context → Set

`⊤ ⱽᵀ       = ⊤
`ℕ ⱽᵀ       = ℕ
(A `× B) ⱽᵀ = (A ⱽᵀ) × (B ⱽᵀ)
(A `+ B) ⱽᵀ = (A ⱽᵀ) ⊎ (B ⱽᵀ)
(`¬ A) ⱽᵀ   = (A ⱽᵀ) → R

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
_ⱽᴸⱽ : ∀ {Γ Θ A} → TermValue Γ Θ A → (Γ ⱽˣ × (`¬ˣ Θ) ⱽˣ) → (A ⱽᵀ)
_ⱽᴸ : ∀ {Γ Θ A} → (Γ ⟶ Θ ∣ A) → (Γ ⱽˣ × (`¬ˣ Θ) ⱽˣ) → ((`¬ `¬ A) ⱽᵀ)
_ⱽᴿ : ∀ {Γ Θ A} → (A ∣ Γ ⟶ Θ) → (Γ ⱽˣ × (`¬ˣ Θ) ⱽˣ) → ((`¬ A) ⱽᵀ)
_ⱽˢ : ∀ {Γ Θ}   → (Γ ↦ Θ)     → (Γ ⱽˣ × (`¬ˣ Θ) ⱽˣ) → R

⟨ ` x , V-var ⟩ ⱽᴸⱽ = λ c → (x ⱽⱽ) (proj₁ c)
⟨ `⟨ M , N ⟩ , V-prod V W ⟩ ⱽᴸⱽ = λ c → ⟨ ((⟨ M , V ⟩ ⱽᴸⱽ) c) , (⟨ N , W ⟩ ⱽᴸⱽ) c ⟩
⟨ inl⟨ M ⟩ , V-inl V ⟩ ⱽᴸⱽ = λ c → inj₁ ((⟨ M , V ⟩ ⱽᴸⱽ) c)
⟨ inr⟨ M ⟩ , V-inr V ⟩ ⱽᴸⱽ = λ c → inj₂ ((⟨ M , V ⟩ ⱽᴸⱽ) c)
⟨ not[ K ] , V-not ⟩ ⱽᴸⱽ = λ c k → (K ⱽᴿ) c k

_ⱽᴸ (` x)            = λ c k → k ((x ⱽⱽ) (proj₁ c))
`⟨ M , N ⟩ ⱽᴸ         = λ c k → (M ⱽᴸ) c (λ x → (N ⱽᴸ) c (λ y → k ⟨ x , y ⟩))
inl⟨ M ⟩ ⱽᴸ           = λ c k → (M ⱽᴸ) c (λ x → k (inj₁ x))
inr⟨ M ⟩ ⱽᴸ           = λ c k → (M ⱽᴸ) c (λ x → k (inj₂ x))
not[ K ] ⱽᴸ          = λ c k → k (λ z → (K ⱽᴿ) c z)
_ⱽᴸ {Γ}{Θ}{A} (μθ S) = λ c α → (S ⱽˢ) ⟨ (proj₁ c) , ⟨ (proj₂ c) , α ⟩ ⟩

(` α) ⱽᴿ             = λ c z → ((Γ∋A⇒¬Γ∋¬A α) ⱽⱽ) (proj₂ c) z 
`[ K , L ] ⱽᴿ        = λ c → λ{ (inj₁ x) → (K ⱽᴿ) c x ; (inj₂ y) → (L ⱽᴿ) c y}
fst[ K ] ⱽᴿ          = λ c → λ{ ⟨ x , _ ⟩ → (K ⱽᴿ) c x} 
snd[ L ] ⱽᴿ          = λ c → λ{ ⟨ _ , y ⟩ → (L ⱽᴿ) c y}
not⟨ M ⟩ ⱽᴿ           = λ c z → (λ k → (M ⱽᴸ) c k) z
_ⱽᴿ {Γ}{Θ}{A} (μγ S) = λ c x →  (S ⱽˢ) ⟨ ⟨ proj₁ c , x ⟩ , (proj₂ c) ⟩

(M ● K) ⱽˢ           = λ c → ((M ⱽᴸ) c) ((K ⱽᴿ) c)


--Call-by-Name CPS Transformation--


--Types and Contexts--
_ᴺᵀ : Type → Set
_ᴺˣ : Context → Set

`⊤ ᴺᵀ        = ⊤
`ℕ ᴺᵀ        = ℕ
(A `× B) ᴺᵀ  = (A ᴺᵀ) ⊎ (B ᴺᵀ)
(A `+ B) ᴺᵀ  = (A ᴺᵀ) × (B ᴺᵀ)
(`¬ A) ᴺᵀ    = (A ᴺᵀ) → R

∅ ᴺˣ       = ⊤
(Γ , A) ᴺˣ =  Γ ᴺˣ × A ᴺᵀ 


--Variables--
_ᴺⱽ : ∀ {Γ A} → (Γ ∋ A) → (Γ ᴺˣ) → (A ᴺᵀ)
_ᴺⱽ `Z     = λ x → proj₂ x 
_ᴺⱽ (`S x) = λ c → ((x ᴺⱽ) (proj₁ c))


--Terms--
_ᴺᴸ : ∀ {Γ Θ A} → (Γ ⟶ Θ ∣ A) → (Θ ᴺˣ × (`¬ˣ Γ) ᴺˣ) → (`¬ A) ᴺᵀ
_ᴺᴿ : ∀ {Γ Θ A} → (A ∣ Γ ⟶ Θ) → (Θ ᴺˣ × (`¬ˣ Γ) ᴺˣ) → (`¬ `¬ A) ᴺᵀ
_ᴺˢ : ∀ {Γ Θ}   → (Γ ↦ Θ)     → (Θ ᴺˣ × (`¬ˣ Γ) ᴺˣ) → R

(` x) ᴺᴸ             = λ c k → ((Γ∋A⇒¬Γ∋¬A x) ᴺⱽ) (proj₂ c) k
`⟨ M , N ⟩ ᴺᴸ         = λ c → λ{(inj₁ α) → (M ᴺᴸ) c α ; (inj₂ β) → (N ᴺᴸ) c β}
inl⟨ M ⟩ ᴺᴸ           = λ c → λ{⟨ α , _ ⟩ → (M ᴺᴸ) c α}
inr⟨ N ⟩ ᴺᴸ           = λ c → λ{⟨ _ , β ⟩ → (N ᴺᴸ) c β}
not[ K ] ᴺᴸ          = λ c k → (λ z → (K ᴺᴿ) c z) k
_ᴺᴸ {Γ}{Θ}{A} (μθ S) = λ c α → (S ᴺˢ) ⟨ ⟨ proj₁ c , α ⟩ , proj₂ c ⟩

(` α) ᴺᴿ             = λ c z → z ((α ᴺⱽ) (proj₁ c))
`[ K , L ] ᴺᴿ        = λ c z → (K ᴺᴿ) c (λ α → (L ᴺᴿ) c (λ β → z ⟨ α , β ⟩))
fst[ K ] ᴺᴿ          = λ c z → (K ᴺᴿ) c (λ α → z (inj₁ α))
snd[ L ] ᴺᴿ          = λ c z → (L ᴺᴿ) c (λ β → z (inj₂ β))
not⟨ M ⟩ ᴺᴿ           = λ c z → z(λ k → (M ᴺᴸ) c k)
_ᴺᴿ {Γ}{Θ}{A} (μγ S) = λ c x →  (S ᴺˢ) ⟨ proj₁ c , ⟨ proj₂ c , x ⟩ ⟩

(M ● K) ᴺˢ           = λ c → ((K ᴺᴿ) c) ((M ᴺᴸ) c)


--Proofs of Duality--

--Types and Contexts--

Aⱽ≡Aᵒᴺ : ∀ {A} → A ⱽᵀ ≡ (A ᵒᵀ) ᴺᵀ
Aⱽ≡Aᵒᴺ {`⊤}     = refl
Aⱽ≡Aᵒᴺ {`ℕ}     = refl 
Aⱽ≡Aᵒᴺ {A `+ B} = cong₂ _⊎_ (Aⱽ≡Aᵒᴺ {A}) (Aⱽ≡Aᵒᴺ {B})
Aⱽ≡Aᵒᴺ {A `× B} = cong₂ _×_ (Aⱽ≡Aᵒᴺ {A}) (Aⱽ≡Aᵒᴺ {B})
Aⱽ≡Aᵒᴺ {`¬ A}   = cong (λ - → - → R) Aⱽ≡Aᵒᴺ

Γⱽ≡Γᵒᴺ : ∀ {Γ} → Γ ⱽˣ ≡ (Γ ᵒˣ) ᴺˣ
Γⱽ≡Γᵒᴺ {∅}       = refl
Γⱽ≡Γᵒᴺ {(Γ , A)} = cong₂ _×_ Γⱽ≡Γᵒᴺ Aⱽ≡Aᵒᴺ

{-# REWRITE Aⱽ≡Aᵒᴺ #-}
{-# REWRITE Γⱽ≡Γᵒᴺ #-}


postulate
  ext  : Extensionality 0ℓ 0ℓ

--Mⱽcλz→X≡Xs required for following proofs--

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
Sⱽ≡Sᵒᴺ : ∀ {Γ Θ}   (S : Γ ↦ Θ)     (c : Γ ⱽˣ × (`¬ˣ Θ) ⱽˣ)                   → (S ⱽˢ) c   ≡ ((S ᵒˢ) ᴺˢ) c

Mⱽ≡Mᵒᴺ (` x) ⟨ c , _ ⟩ k       = cong  (λ - → k(-  c)) (xⱽ≡xᵒᴺ x)
Mⱽ≡Mᵒᴺ `⟨ M , N ⟩ c k          = trans (Mⱽ≡Mᵒᴺ M c (λ x → (N ⱽᴸ) c ((λ y → k ⟨ x , y ⟩)))) (cong (λ - → (((M ᵒᴸ) ᴺᴿ) c) - ) (ext (λ x → Mⱽ≡Mᵒᴺ N c (λ y → k ⟨ x , y ⟩))))
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

Mⱽcλz→X≡X : ∀ {Γ Θ A} (M : Γ ⟶ Θ ∣ A) (c : Γ ⱽˣ × (`¬ˣ Θ) ⱽˣ) (X : R) → (M ⱽᴸ) c (λ z → X) ≡ X
Kⱽcλz→X≡X : ∀ {Γ Θ A} (K : A ∣ Γ ⟶ Θ) (c : Γ ⱽˣ × (`¬ˣ Θ) ⱽˣ) (X : R) → (K ⱽᴿ) c ≡ (λ z → X)
Sⱽcλz→X≡X : ∀ {Γ Θ}   (S : Γ ↦ Θ)     (c : Γ ⱽˣ × (`¬ˣ Θ) ⱽˣ) (X : R) → {!   !}
Mⱽcλz→X≡X (` x) c X = refl
Mⱽcλz→X≡X `⟨ M , N ⟩ c X = trans (Mⱽcλz→X≡X M c ((N ⱽᴸ) c (λ z → X))) (Mⱽcλz→X≡X N c X)
Mⱽcλz→X≡X inl⟨ M ⟩ c X = Mⱽcλz→X≡X M c X
Mⱽcλz→X≡X inr⟨ M ⟩ c X = Mⱽcλz→X≡X M c X
Mⱽcλz→X≡X not[ K ] c X = refl
Mⱽcλz→X≡X (μθ S) c X = {!   !} --⟨ proj₁ c , ⟨ proj₂ c , (λ z → X) ⟩ ⟩ X

Kⱽcλz→X≡X (` α) c X = {!   !}
Kⱽcλz→X≡X fst[ K ] c X = {!   !}
Kⱽcλz→X≡X snd[ K ] c X = {!   !}
Kⱽcλz→X≡X `[ K , L ] c X = {!   !}
Kⱽcλz→X≡X not⟨ M ⟩ c X = {!  !}
Kⱽcλz→X≡X (μγ S) c X = {!   !}

Sⱽcλz→X≡X (M ● K) c X = {!   !}

ren-int : ∀ Γ Γ′ → Γ ↝ Γ′ → (Γ′ ⱽˣ) → (Γ ⱽˣ)
ren-int ∅ Γ′ ρ γ = tt
ren-int (Γ , x) Γ′ ρ γ = ⟨ (ren-int Γ Γ′ (λ z → ρ (`S z)) γ) , ((ρ `Z ⱽⱽ) γ) ⟩

neg-ren-int : ∀ Γ Γ′ → Γ ↝ Γ′ → ((`¬ˣ Γ′) ⱽˣ) → ((`¬ˣ Γ) ⱽˣ)
neg-ren-int ∅ Γ′ ρ γ = tt
neg-ren-int (Γ , x) Γ′ ρ γ = ⟨ (neg-ren-int Γ Γ′ (λ z → ρ (`S z)) γ) , (ρ (`S {!   !}) ⱽⱽ) {!   !} ⟩
 
termvalue-sub-int : ∀ Γ Γ′ Θ → Γ –[ (λ Γ A → TermValue Γ Θ A) ]→ Γ′ → ((`¬ˣ Θ) ⱽˣ) → (Γ′ ⱽˣ) → (Γ ⱽˣ)
termvalue-sub-int ∅ Γ′ Θ σ θ γ = tt
termvalue-sub-int (Γ , A) Γ′ Θ σ θ γ = ⟨ (termvalue-sub-int Γ Γ′ Θ (λ x → σ (`S x)) θ γ) , ((σ `Z ⱽᴸⱽ) ⟨ γ , θ ⟩) ⟩

coterm-sub-int : ∀ Γ Θ Θ′ → Θ –[ (λ Θ A → A ∣ Γ ⟶ Θ) ]→ Θ′ → Γ ⱽˣ → ((`¬ˣ Θ′) ⱽˣ) → ((`¬ˣ Θ) ⱽˣ)
coterm-sub-int Γ ∅ Θ′ σ γ _ = tt
coterm-sub-int Γ (Θ , A) Θ′ σ γ θ = ⟨ (coterm-sub-int Γ Θ Θ′ (λ z → σ (`S z)) γ θ)  , (((σ `Z) ⱽᴿ) ⟨ γ , θ ⟩) ⟩

_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
  → (B → C) → (A → B) → A → C
(g ∘ f) x  =  g (f x)

sub-lemma-var : ∀ {Γ Γ′ Θ Θ′ A} (s : Γ –[ (λ Γ A → TermValue Γ Θ′ A) ]→ Γ′) (t : Θ –[ (λ Θ A → A ∣ Γ′ ⟶ Θ) ]→ Θ′) (x : Γ ∋ A) (γ : Γ′ ⱽˣ) (θ : (`¬ˣ Θ′) ⱽˣ ) →
  (proj₁ (s x) ⱽᴸ) ⟨ γ , θ ⟩ ≡ (λ k → k ((x ⱽⱽ) (termvalue-sub-int Γ Γ′ Θ′ s θ γ)))

sub-lemma-var s t `Z γ θ = ext (λ x → {! !})
sub-lemma-var s t (`S x) γ θ = {!   !}

sub-lemma-term : ∀ {Γ Γ′ Θ Θ′ A} (s : Γ –[ (λ Γ A → TermValue Γ Θ′ A) ]→ Γ′) (t : Θ –[ (λ Θ A → A ∣ Γ′ ⟶ Θ) ]→ Θ′) (M : Γ ⟶ Θ ∣ A) (γ : Γ′ ⱽˣ) (θ : (`¬ˣ Θ′) ⱽˣ ) →
  ((sub-term TermValueKit CotermKit s t M) ⱽᴸ) ⟨ γ , θ ⟩ ≡ (M ⱽᴸ) ⟨ termvalue-sub-int Γ Γ′ Θ′ s θ γ , coterm-sub-int Γ′ Θ Θ′ t γ θ ⟩

sub-lemma-coterm : ∀ {Γ Γ′ Θ Θ′ A} (s : Γ –[ (λ Γ A → TermValue Γ Θ′ A) ]→ Γ′) (t : Θ –[ (λ Θ A → A ∣ Γ′ ⟶ Θ) ]→ Θ′) (K : A ∣ Γ ⟶ Θ) (γ : Γ′ ⱽˣ) (θ : (`¬ˣ Θ′) ⱽˣ ) →
  ((sub-coterm TermValueKit CotermKit s t K) ⱽᴿ) ⟨ γ , θ ⟩ ≡ (K ⱽᴿ) ⟨ termvalue-sub-int Γ Γ′ Θ′ s θ γ , coterm-sub-int Γ′ Θ Θ′ t γ θ ⟩

sub-lemma-statement : ∀ {Γ Γ′ Θ Θ′} (s : Γ –[ (λ Γ A → TermValue Γ Θ′ A) ]→ Γ′) (t : Θ –[ (λ Θ A → A ∣ Γ′ ⟶ Θ) ]→ Θ′) (S : Γ ↦ Θ) (γ : Γ′ ⱽˣ) (θ : (`¬ˣ Θ′) ⱽˣ ) →
  ((sub-statement TermValueKit CotermKit s t S) ⱽˢ) ⟨ γ , θ ⟩ ≡ (S ⱽˢ) ⟨ termvalue-sub-int Γ Γ′ Θ′ s θ γ , coterm-sub-int Γ′ Θ Θ′ t γ θ ⟩

sub-lemma-term s t (` x) γ θ = {!   !} 
sub-lemma-term {Γ}{Γ′}{Θ}{Θ′} s t `⟨ M , N ⟩ γ θ = ext (λ k → trans 
  (cong (λ - → - (λ x → (sub-term TermValueKit CotermKit s t N ⱽᴸ) ⟨ γ , θ ⟩ (λ y → k ⟨ x , y ⟩))) (sub-lemma-term s t M γ θ)) 
  (cong (λ - → (M ⱽᴸ) ⟨ termvalue-sub-int Γ Γ′ Θ′ s θ γ , coterm-sub-int Γ′ Θ Θ′ t γ θ ⟩ (λ x → - (λ y → k ⟨ x , y ⟩))) (sub-lemma-term s t N γ θ)))
sub-lemma-term s t inl⟨ M ⟩ γ θ = ext (λ k → cong (λ - → - (λ x → k (inj₁ x))) (sub-lemma-term s t M γ θ))
sub-lemma-term s t inr⟨ M ⟩ γ θ = ext (λ k → cong (λ - → - (λ x → k (inj₂ x))) (sub-lemma-term s t M γ θ))
sub-lemma-term s t not[ K ] γ θ = ext (λ k → cong k (sub-lemma-coterm s t K γ θ))
sub-lemma-term s t (μθ S) γ θ = ext (λ x → sub-lemma-statement ({!   !}) ({!   !}) {!   !} {!   !} {!   !} )

sub-lemma-coterm s t (` α) γ θ = {!   !}
sub-lemma-coterm s t fst[ K ] γ θ = cong (λ - → λ { ⟨ x , _ ⟩ → - x }) (sub-lemma-coterm s t K γ θ)
sub-lemma-coterm s t snd[ K ] γ θ = cong (λ - → λ { ⟨ _ , y ⟩ → - y }) (sub-lemma-coterm s t K γ θ) --ext (λ{⟨ _ , y ⟩ → cong ((λ - → λ { ⟨ _ , y ⟩ → - y }) ⟨ _ , y ⟩) (sub-lemma-coterm s t K γ θ)})
sub-lemma-coterm {Γ} {Γ′} {Θ} {Θ′} {A `+ B} s t `[ K , L ] γ θ = ext (λ{(inj₁ x) → cong (λ - → - x) (sub-lemma-coterm s t K γ θ) ; (inj₂ y) → cong (λ - → - y) (sub-lemma-coterm s t L γ θ)})
sub-lemma-coterm s t not⟨ M ⟩ γ θ = sub-lemma-term s t M γ θ
sub-lemma-coterm s t (μγ S) γ θ = ext (λ x → sub-lemma-statement {!   !} {!   !} ({!   !}) {!   !} {!   !})

sub-lemma-statement {Γ} {Γ′} {Θ} {Θ′} s t (M ● K) γ θ = 
  begin
    (sub-term TermValueKit CotermKit s t M ⱽᴸ) ⟨ γ , θ ⟩ ((sub-coterm TermValueKit CotermKit s t K ⱽᴿ) ⟨ γ , θ ⟩)
  ≡⟨ cong (λ - → - ((sub-coterm TermValueKit CotermKit s t K ⱽᴿ) ⟨ γ , θ ⟩)) (sub-lemma-term s t M γ θ) ⟩
    (M ⱽᴸ) ⟨ termvalue-sub-int Γ Γ′ Θ′ s θ γ , coterm-sub-int Γ′ Θ Θ′ t γ θ ⟩ ((sub-coterm TermValueKit CotermKit s t K ⱽᴿ) ⟨ γ , θ ⟩)
  ≡⟨ cong (λ - → (M ⱽᴸ) ⟨ termvalue-sub-int Γ Γ′ Θ′ s θ γ , coterm-sub-int Γ′ Θ Θ′ t γ θ ⟩ -) (sub-lemma-coterm s t K γ θ) ⟩
    (M ⱽᴸ) ⟨ termvalue-sub-int Γ Γ′ Θ′ s θ γ , coterm-sub-int Γ′ Θ Θ′ t γ θ ⟩ ((K ⱽᴿ) ⟨ termvalue-sub-int Γ Γ′ Θ′ s θ γ , coterm-sub-int Γ′ Θ Θ′ t γ θ ⟩)
  ∎

id-termvalue-sub-int : ∀ Γ Θ γ θ → termvalue-sub-int Γ Γ Θ id-termvalue θ γ ≡ γ
id-termvalue-sub-int ∅ Θ γ θ = refl
id-termvalue-sub-int (Γ , A) Θ ⟨ γ₁ , γ₂ ⟩ θ = cong (λ - → ⟨ - , γ₂ ⟩) {!   !}

id-coterm-sub-int : ∀ Γ Θ γ θ → coterm-sub-int Γ Θ Θ id-coterm γ θ ≡ θ
id-coterm-sub-int Γ ∅ γ θ = refl
id-coterm-sub-int Γ (Θ , A) γ ⟨ θ₁ , θ₂ ⟩ = cong (λ - → ⟨ - , θ₂ ⟩) {!   !}



S⟶ⱽT⇒Sⱽ≡Tⱽ : ∀ {Γ Θ} (S T : Γ ↦ Θ) (c : (Γ ᵒˣ) ᴺˣ × `¬ˣ (Θ ᵒˣ) ᴺˣ) → S ˢ⟶ⱽ T → (S ⱽˢ) c ≡ (T ⱽˢ) c
S⟶ⱽT⇒Sⱽ≡Tⱽ (`⟨ V , W ⟩ ● fst[ K ]) (V ● K) c (β×₁ x x₁) = cong ((V ⱽᴸ) c) (ext (λ - → Mⱽcλz→X≡X W c ((K ⱽᴿ) c -)))
S⟶ⱽT⇒Sⱽ≡Tⱽ (`⟨ V , W ⟩ ● snd[ L ]) (W ● L) c (β×₂ x x₁) = Mⱽcλz→X≡X V c ((W ⱽᴸ) c ((L ⱽᴿ) c))
S⟶ⱽT⇒Sⱽ≡Tⱽ (inl⟨ V ⟩ ● `[ K , L ]) (V ● K) c (β+₁ x) = cong ((V ⱽᴸ) c) refl
S⟶ⱽT⇒Sⱽ≡Tⱽ (inr⟨ W ⟩ ● `[ K , L ]) (W ● L) c (β+₂ x) = cong ((W ⱽᴸ) c) refl
S⟶ⱽT⇒Sⱽ≡Tⱽ (not[ K ] ● not⟨ M ⟩) (M ● K) c (β¬) = refl
S⟶ⱽT⇒Sⱽ≡Tⱽ {Γ} {Θ} (V ● μγ {Γ}{Θ}{A} S) .(S ⱽ⟨ ⟨ V , v ⟩ /⟩ˢ) ⟨ c₁ , c₂ ⟩ (βL v) = sym (
  begin
    ((S ⱽ⟨ ⟨ V , v ⟩ /⟩ˢ) ⱽˢ) ⟨ c₁ , c₂ ⟩
  ≡⟨⟩
    (sub-statement TermValueKit CotermKit (add (λ Γ A → TermValue Γ Θ A) ⟨ V , v ⟩ id-termvalue) id-coterm S ⱽˢ) ⟨ c₁ , c₂ ⟩
  ≡⟨ sub-lemma-statement (add (λ Γ A → TermValue Γ Θ A) ⟨ V , v ⟩ id-termvalue) id-coterm S c₁ c₂ ⟩
    (S ⱽˢ) ⟨ termvalue-sub-int (Γ , A) Γ Θ (add (λ Γ A → TermValue Γ Θ A) ⟨ V , v ⟩ id-termvalue) c₂ c₁ , coterm-sub-int Γ Θ Θ id-coterm c₁ c₂ ⟩
  ≡⟨ cong (λ - → (S ⱽˢ) ⟨ ⟨ termvalue-sub-int Γ Γ Θ (λ x → id-termvalue x) c₂ c₁ , (⟨ V , v ⟩ ⱽᴸⱽ) ⟨ c₁ , c₂ ⟩ ⟩ , - ⟩) (id-coterm-sub-int Γ Θ c₁ c₂) ⟩
    (S ⱽˢ) ⟨ ⟨ termvalue-sub-int Γ Γ Θ (λ x → id-termvalue x) c₂ c₁ , (⟨ V , v ⟩ ⱽᴸⱽ) ⟨ c₁ , c₂ ⟩ ⟩ , c₂ ⟩
  ≡⟨ cong (λ - → (S ⱽˢ) ⟨ ⟨ - , (⟨ V , v ⟩ ⱽᴸⱽ) ⟨ c₁ , c₂ ⟩ ⟩ , c₂ ⟩) (id-termvalue-sub-int Γ Θ c₁ c₂) ⟩
    (S ⱽˢ) ⟨ ⟨ c₁ , (⟨ V , v ⟩ ⱽᴸⱽ) ⟨ c₁ , c₂ ⟩ ⟩ , c₂ ⟩
  ≡⟨ {!   !} ⟩
    (V ⱽᴸ) ⟨ c₁ , c₂ ⟩ (λ x → (S ⱽˢ) ⟨ ⟨ c₁ , x ⟩ , c₂ ⟩)
  ∎)
S⟶ⱽT⇒Sⱽ≡Tⱽ {Γ}{Θ}(μθ {Γ}{Θ}{A} S ● K) .(S [ K /]ˢ) ⟨ c₁ , c₂ ⟩ (βR) = sym (
  begin
    ((S [ K /]ˢ) ⱽˢ) ⟨ c₁ , c₂ ⟩
  ≡⟨⟩
    (sub-statement TermValueKit CotermKit id-termvalue (add (λ Θ A → A ∣ Γ ⟶ Θ) K id-coterm) S ⱽˢ) ⟨ c₁ , c₂ ⟩
  ≡⟨ sub-lemma-statement id-termvalue ((add (λ Θ A → A ∣ Γ ⟶ Θ) K id-coterm)) S c₁ c₂ ⟩
    (S ⱽˢ) ⟨ (termvalue-sub-int Γ Γ Θ id-termvalue c₂ c₁) , (coterm-sub-int Γ (Θ , A) Θ (add (λ Θ A → A ∣ Γ ⟶ Θ) K id-coterm) c₁ c₂) ⟩
  ≡⟨ cong (λ - → (S ⱽˢ) ⟨ - , coterm-sub-int Γ (Θ , A) Θ (add (λ Θ A → A ∣ Γ ⟶ Θ) K id-coterm) c₁ c₂ ⟩) (id-termvalue-sub-int Γ Θ c₁ c₂) ⟩
    (S ⱽˢ) ⟨ c₁ , (coterm-sub-int Γ (Θ , A) Θ (add (λ Θ A → A ∣ Γ ⟶ Θ) K id-coterm) c₁ c₂) ⟩
  ≡⟨ cong (λ - → (S ⱽˢ) ⟨ c₁ , ⟨ - , (K ⱽᴿ) ⟨ c₁ , c₂ ⟩ ⟩ ⟩) (id-coterm-sub-int Γ Θ c₁ c₂) ⟩
    (S ⱽˢ) ⟨ c₁ , ⟨ c₂ , (K ⱽᴿ) ⟨ c₁ , c₂ ⟩ ⟩ ⟩
  ∎)
S—↠ⱽT⇒Sⱽ≡Tⱽ : ∀ {Γ Θ} (S T : Γ ↦ Θ) (c : (Γ ᵒˣ) ᴺˣ × `¬ˣ (Θ ᵒˣ) ᴺˣ) → S ˢ—↠ⱽ T → (S ⱽˢ) c ≡ (T ⱽˢ) c
S—↠ⱽT⇒Sⱽ≡Tⱽ S .S c (.S ∎ˢⱽ) = refl
S—↠ⱽT⇒Sⱽ≡Tⱽ S T c ( _ˢ⟶ⱽ⟨_⟩_ .S {S′} {T} S⟶S′ S′↠T) = trans (S⟶ⱽT⇒Sⱽ≡Tⱽ S S′ c S⟶S′) (S—↠ⱽT⇒Sⱽ≡Tⱽ S′ T c S′↠T)

-- ren-lemma-term : ∀ {Γ Γ′ Θ Θ′ A} (s : Γ ↝ Γ′) (t : Θ ↝ Θ′) (M : Γ ⟶ Θ ∣ A) (γ : Γ′ ⱽˣ) (θ : (`¬ˣ Θ′) ⱽˣ) (k : ((`¬ A) ⱽᵀ)) →
--   (rename-term s t M ⱽᴸ) ⟨ γ , θ ⟩ k ≡ (M ⱽᴸ) ⟨ ren-int Γ Γ′ s γ , ren-int {!  !} Θ′ {!   !} {!   !} ⟩ k

-- ren-lemma-term s t (` x) γ θ k = {!   !}
-- ren-lemma-term s t `⟨ M , M₁ ⟩ γ θ k = {!   !}
-- ren-lemma-term s t inl⟨ M ⟩ γ θ k = {!   !}
-- ren-lemma-term s t inr⟨ M ⟩ γ θ k = {!   !}
-- ren-lemma-term s t not[ x ] γ θ k = {!   !}
-- ren-lemma-term s t (μθ x) γ θ k = {!   !}


M⟶ⱽN⇒Mⱽ≡Nⱽ : ∀ {Γ Θ A} (M N : Γ ⟶ Θ ∣ A) (c : (Γ ᵒˣ) ᴺˣ × `¬ˣ (Θ ᵒˣ) ᴺˣ) (k : ((`¬ A) ⱽᵀ)) → M ᵗ⟶ⱽ N → (M ⱽᴸ) c k ≡ (N ⱽᴸ) c k
M⟶ⱽN⇒Mⱽ≡Nⱽ M .(μθ (rename-term id-var (rename-weaken id-var) M ● ` `Z)) ⟨ c₁ , c₂ ⟩ k ηR = {!   !}

M—↠ⱽN⇒Mⱽ≡Nⱽ : ∀ {Γ Θ A} (M N : Γ ⟶ Θ ∣ A) (c : (Γ ᵒˣ) ᴺˣ × `¬ˣ (Θ ᵒˣ) ᴺˣ) (k : ((`¬ A) ⱽᵀ)) → M ᵗ—↠ⱽ N → (M ⱽᴸ) c k ≡ (N ⱽᴸ) c k
M—↠ⱽN⇒Mⱽ≡Nⱽ M .M c k (.M ∎ᵗⱽ) = refl
M—↠ⱽN⇒Mⱽ≡Nⱽ M N c k ( _ᵗ⟶ⱽ⟨_⟩_ .M {M′} {N} M⟶M′ M′↠N) = trans (M⟶ⱽN⇒Mⱽ≡Nⱽ M M′ c k M⟶M′) (M—↠ⱽN⇒Mⱽ≡Nⱽ M′ N c k M′↠N)

-- lemma : ∀ {Γ Θ A} (K : A ∣ Γ ⟶ Θ) (c : (Γ ᵒˣ) ᴺˣ × `¬ˣ (Θ ᵒˣ) ᴺˣ) (k : (A) ⱽᵀ)
--   →   (K ⱽᴿ) c ≡
--       (rename-coterm (rename-weaken id-var) id-var K ⱽᴿ) ⟨ ⟨ proj₁ c , k ⟩ , proj₂ c ⟩
-- lemma (` α) c k = refl
-- lemma fst[ K ] c k = ext {!   !}
-- lemma snd[ K ] c k = {!   !}
-- lemma `[ K , L ] c k = {!   !}
-- lemma not⟨ M ⟩ c k = {!   !}
-- lemma (μγ S) c k = {!   !}

K⟶ⱽL⇒Kⱽ≡Lⱽ : ∀ {Γ Θ A} (K L : A ∣ Γ ⟶ Θ) (c : (Γ ᵒˣ) ᴺˣ × `¬ˣ (Θ ᵒˣ) ᴺˣ) (k : (A) ⱽᵀ) → K ᶜ⟶ⱽ L → (K ⱽᴿ) c k ≡ (L ⱽᴿ) c k
K⟶ⱽL⇒Kⱽ≡Lⱽ K .(μγ (` `Z ● rename-coterm (rename-weaken id-var) id-var K)) ⟨ c₁ , c₂ ⟩ k ηL = {!   !}

K—↠ⱽL⇒Kⱽ≡Lⱽ : ∀ {Γ Θ A} (K L : A ∣ Γ ⟶ Θ) (c : (Γ ᵒˣ) ᴺˣ × `¬ˣ (Θ ᵒˣ) ᴺˣ) (k : (A) ⱽᵀ) → K ᶜ—↠ⱽ L → (K ⱽᴿ) c k ≡ (L ⱽᴿ) c k
K—↠ⱽL⇒Kⱽ≡Lⱽ K .K c k (.K ∎ᶜⱽ) = refl
K—↠ⱽL⇒Kⱽ≡Lⱽ K L c k (_ᶜ⟶ⱽ⟨_⟩_ .K {K′} {L} K⟶K′ K′↠L) = trans (K⟶ⱽL⇒Kⱽ≡Lⱽ K K′ c k K⟶K′) (K—↠ⱽL⇒Kⱽ≡Lⱽ K′ L c k K′↠L)