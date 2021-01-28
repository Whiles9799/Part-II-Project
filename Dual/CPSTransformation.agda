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

_ⱽᴸ : ∀ {Γ Θ A} → (Γ ⟶ Θ ∣ A) → (Γ ⱽˣ × (`¬ˣ Θ) ⱽˣ) → ((`¬ `¬ A) ⱽᵀ)
_ⱽᴿ : ∀ {Γ Θ A} → (A ∣ Γ ⟶ Θ) → (Γ ⱽˣ × (`¬ˣ Θ) ⱽˣ) → ((`¬ A) ⱽᵀ)
_ⱽˢ : ∀ {Γ Θ}   → (Γ ↦ Θ)     → (Γ ⱽˣ × (`¬ˣ Θ) ⱽˣ) → R

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

_ⱽᵘ : ∀ {Γ Γ′ T} → Γ –[ T ]→ Γ′ → (Γ ⱽˣ → Γ′ ⱽˣ)
_ⱽᵘ {∅} {Γ′} σ c = ((σ ⱽᵘ) tt) 
_ⱽᵘ {Γ , A} {Γ′} σ c = (((λ ()) ⱽᵘ) tt) 


_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
  → (B → C) → (A → B) → A → C
(g ∘ f) x  =  g (f x)

-- sub-lemma-term : ∀ {T C Γ Γ′ Θ Θ′ A} (s : Γ –[ (λ - → T - Θ′) ]→ Γ′) (t : Θ –[ (C Γ′) ]→ Θ′) (M : Γ ⟶ Θ ∣ A) (c : Γ ⱽˣ × `¬ˣ Θ ⱽˣ) → ((sub-term TermKit CotermKit s t M) ⱽᴸ) c ≡ ((M ⱽᴸ) ∘ (s + t ⱽᵘ)) c  
-- sub-lemma-coterm : ∀ {T C Γ Γ′ Θ Θ′ A} (s : Γ –[ (λ - → T - Θ′) ]→ Γ′) (t : Θ –[ (C Γ′) ]→ Θ′) (K : A ∣ Γ ⟶ Θ) (c : Γ ⱽˣ × `¬ˣ Θ ⱽˣ) → ((sub-coterm TermKit CotermKit s t K) ⱽᴿ) c ≡ ((K ⱽᴿ) ∘ (s + t ⱽᵘ)) c


sub-lemma-statement : ∀ {T C Γ Γ′ Θ Θ′ A} (s : Γ –[ (λ - → T - Θ′) ]→ Γ′) (t : Θ –[ (C Γ′) ]→ Θ′) (S : Γ ↦ Θ) (c : Γ ⱽˣ × `¬ˣ Θ ⱽˣ) → ((sub-statement TermKit CotermKit s t S) ⱽˢ) c ≡ {!   !}

sub-lemma-statement s t (M ● K) c = {!   !}

S⟶ⱽT⇒Sⱽ≡Tⱽ : ∀ {Γ Θ} (S T : Γ ↦ Θ) (c : (Γ ᵒˣ) ᴺˣ × `¬ˣ (Θ ᵒˣ) ᴺˣ) → S ˢ⟶ⱽ T → (S ⱽˢ) c ≡ (T ⱽˢ) c
S⟶ⱽT⇒Sⱽ≡Tⱽ (`⟨ V , W ⟩ ● fst[ K ]) (V ● K) c (β×₁ x x₁) = cong ((V ⱽᴸ) c) (ext (λ - → Mⱽcλz→X≡X W c ((K ⱽᴿ) c -)))
S⟶ⱽT⇒Sⱽ≡Tⱽ (`⟨ V , W ⟩ ● snd[ L ]) (W ● L) c (β×₂ x x₁) = Mⱽcλz→X≡X V c ((W ⱽᴸ) c ((L ⱽᴿ) c))
S⟶ⱽT⇒Sⱽ≡Tⱽ (inl⟨ V ⟩ ● `[ K , L ]) (V ● K) c (β+₁ x) = cong ((V ⱽᴸ) c) refl
S⟶ⱽT⇒Sⱽ≡Tⱽ (inr⟨ W ⟩ ● `[ K , L ]) (W ● L) c (β+₂ x) = cong ((W ⱽᴸ) c) refl
S⟶ⱽT⇒Sⱽ≡Tⱽ (not[ K ] ● not⟨ M ⟩) (M ● K) c (β¬) = refl
S⟶ⱽT⇒Sⱽ≡Tⱽ (V ● μγ S) .(S ⟨ V /⟩ˢ) ⟨ c₁ , c₂ ⟩ (βL v) = {!  !}
S⟶ⱽT⇒Sⱽ≡Tⱽ (μθ S ● K) .(S [ K /]ˢ) ⟨ c₁ , c₂ ⟩ (βR) = sym (
  begin
    ((S [ K /]ˢ) ⱽˢ) ⟨ c₁ , c₂ ⟩
  ≡⟨⟩
    (sub-statement TermKit CotermKit id-term (λ{`Z → K ; (`S x) → ` x}) S ⱽˢ) ⟨ c₁ , c₂ ⟩
     {!   !})
S—↠ⱽT⇒Sⱽ≡Tⱽ : ∀ {Γ Θ} (S T : Γ ↦ Θ) (c : (Γ ᵒˣ) ᴺˣ × `¬ˣ (Θ ᵒˣ) ᴺˣ) → S ˢ—↠ⱽ T → (S ⱽˢ) c ≡ (T ⱽˢ) c
S—↠ⱽT⇒Sⱽ≡Tⱽ S .S c (.S ∎ˢⱽ) = refl
S—↠ⱽT⇒Sⱽ≡Tⱽ S T c ( _ˢ⟶ⱽ⟨_⟩_ .S {S′} {T} S⟶S′ S′↠T) = trans (S⟶ⱽT⇒Sⱽ≡Tⱽ S S′ c S⟶S′) (S—↠ⱽT⇒Sⱽ≡Tⱽ S′ T c S′↠T)

-- id-rename-term :  ∀ {Γ Θ A} (M : Γ ⟶ Θ ∣ A) (c : (Γ ᵒˣ) ᴺˣ × `¬ˣ (Θ ᵒˣ) ᴺˣ) (k : ((`¬ A) ⱽᵀ))
--   →   (M ⱽᴸ) c k ≡
--       (rename-term id-var (rename-weaken id-var) M ⱽᴸ) ⟨ proj₁ c , ⟨ proj₂ c , k ⟩ ⟩ k
-- id-rename-term (` x) c k = refl
-- id-rename-term `⟨ M , N ⟩ c k = trans (id-rename-term M c (λ x → (N ⱽᴸ) c (λ y → k ⟨ x , y ⟩))) (cong ((rename-term id-var (rename-weaken id-var) M ⱽᴸ) ⟨ proj₁ c , ⟨ proj₂ c , k ⟩ ⟩) (ext (λ x → id-rename-term N c (λ y → k ⟨ x , y ⟩))))
-- id-rename-term inl⟨ M ⟩ c k = id-rename-term M c (λ x → k (inj₁ x))
-- id-rename-term inr⟨ M ⟩ c k = id-rename-term M c (λ x → k (inj₂ x))
-- id-rename-term not[ x ] c k = {!   !}
-- id-rename-term (μθ x) c k = {!   !}

M⟶ⱽN⇒Mⱽ≡Nⱽ : ∀ {Γ Θ A} (M N : Γ ⟶ Θ ∣ A) (c : (Γ ᵒˣ) ᴺˣ × `¬ˣ (Θ ᵒˣ) ᴺˣ) (k : ((`¬ A) ⱽᵀ)) → M ᵗ⟶ⱽ N → (M ⱽᴸ) c k ≡ (N ⱽᴸ) c k
M⟶ⱽN⇒Mⱽ≡Nⱽ M .(μθ (rename-term id-var (rename-weaken id-var) M ● ` `Z)) c k ηR = {!   !}

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
K⟶ⱽL⇒Kⱽ≡Lⱽ K .(μγ (` `Z ● rename-coterm (rename-weaken id-var) id-var K)) c k ηL = {!   !}

K—↠ⱽL⇒Kⱽ≡Lⱽ : ∀ {Γ Θ A} (K L : A ∣ Γ ⟶ Θ) (c : (Γ ᵒˣ) ᴺˣ × `¬ˣ (Θ ᵒˣ) ᴺˣ) (k : (A) ⱽᵀ) → K ᶜ—↠ⱽ L → (K ⱽᴿ) c k ≡ (L ⱽᴿ) c k
K—↠ⱽL⇒Kⱽ≡Lⱽ K .K c k (.K ∎ᶜⱽ) = refl
K—↠ⱽL⇒Kⱽ≡Lⱽ K L c k (_ᶜ⟶ⱽ⟨_⟩_ .K {K′} {L} K⟶K′ K′↠L) = trans (K⟶ⱽL⇒Kⱽ≡Lⱽ K K′ c k K⟶K′) (K—↠ⱽL⇒Kⱽ≡Lⱽ K′ L c k K′↠L)