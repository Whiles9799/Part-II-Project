module Dual.DenotationalSemantics.CPSTransformation (R : Set) where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym; trans)
open import Data.Unit using (⊤; tt) public
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_ ; z≤n; s≤s) public
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩) public
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎) public
open import Relation.Nullary using (¬_) public
open import Dual.Syntax.Core
open import Dual.Syntax.Duality
open import Dual.Syntax.Substitution
open import Dual.Syntax.Values

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

X ⱽᵀ       = ℕ
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


--Sequents--
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

--Substitutions--

ren-int-cbv : ∀ Γ Γ′ → Γ ↝ Γ′ → (Γ′ ⱽˣ) → (Γ ⱽˣ)
ren-int-cbv ∅ Γ′ ρ γ = tt
ren-int-cbv (Γ , A) Γ′ ρ γ = ⟨ ren-int-cbv Γ Γ′ (λ x → ρ (`S x)) γ , ((ρ `Z) ⱽⱽ) γ ⟩

neg-ren-int-cbv : ∀ Θ Θ′ → Θ ↝ Θ′ → ((`¬ˣ Θ′) ⱽˣ) → ((`¬ˣ Θ) ⱽˣ)
neg-ren-int-cbv ∅ Θ′ ρ θ = tt
neg-ren-int-cbv (Θ , A) Θ′ ρ θ = ⟨ (neg-ren-int-cbv Θ Θ′ (λ x → ρ (`S x)) θ) , ((Γ∋A⇒¬Γ∋¬A (ρ `Z) ⱽⱽ) θ) ⟩
 
sub-TV-int : ∀ Γ Γ′ Θ → Γ –[ (Fix₂ TermValue Θ) ]→ Γ′ → ((`¬ˣ Θ) ⱽˣ) → (Γ′ ⱽˣ) → (Γ ⱽˣ)
sub-TV-int ∅ Γ′ Θ σ θ γ = tt
sub-TV-int (Γ , A) Γ′ Θ σ θ γ = ⟨ (sub-TV-int Γ Γ′ Θ (λ x → σ (`S x)) θ γ) , ((σ `Z ⱽᴸⱽ) ⟨ γ , θ ⟩) ⟩

sub-C-int : ∀ Γ Θ Θ′ → Θ –[ (Fix₁ Coterm Γ) ]→ Θ′ → Γ ⱽˣ → ((`¬ˣ Θ′) ⱽˣ) → ((`¬ˣ Θ) ⱽˣ)
sub-C-int Γ ∅ Θ′ σ γ _ = tt
sub-C-int Γ (Θ , A) Θ′ σ γ θ = ⟨ (sub-C-int Γ Θ Θ′ (λ z → σ (`S z)) γ θ)  , (((σ `Z) ⱽᴿ) ⟨ γ , θ ⟩) ⟩


--Call-by-Name CPS Transformation--


--Types and Contexts--
_ᴺᵀ : Type → Set
_ᴺˣ : Context → Set

X ᴺᵀ        = ℕ
(A `× B) ᴺᵀ  = (A ᴺᵀ) ⊎ (B ᴺᵀ)
(A `+ B) ᴺᵀ  = (A ᴺᵀ) × (B ᴺᵀ)
(`¬ A) ᴺᵀ    = (A ᴺᵀ) → R

∅ ᴺˣ       = ⊤
(Γ , A) ᴺˣ =  Γ ᴺˣ × A ᴺᵀ 


--Variables--
_ᴺⱽ : ∀ {Γ A} → (Γ ∋ A) → (Γ ᴺˣ) → (A ᴺᵀ)
_ᴺⱽ `Z     = λ x → proj₂ x 
_ᴺⱽ (`S x) = λ c → ((x ᴺⱽ) (proj₁ c))


--Sequents--
_ᴺᴿⱽ : ∀ {Γ Θ A} → (CotermValue Γ Θ A) → (Θ ᴺˣ × (`¬ˣ Γ) ᴺˣ) → (A) ᴺᵀ 
_ᴺᴸ : ∀ {Γ Θ A} → (Γ ⟶ Θ ∣ A) → (Θ ᴺˣ × (`¬ˣ Γ) ᴺˣ) → (`¬ A) ᴺᵀ
_ᴺᴿ : ∀ {Γ Θ A} → (A ∣ Γ ⟶ Θ) → (Θ ᴺˣ × (`¬ˣ Γ) ᴺˣ) → (`¬ `¬ A) ᴺᵀ
_ᴺˢ : ∀ {Γ Θ}   → (Γ ↦ Θ)     → (Θ ᴺˣ × (`¬ˣ Γ) ᴺˣ) → R

⟨ ` α , CV-covar ⟩ ᴺᴿⱽ = λ c → (α ᴺⱽ) (proj₁ c)
⟨ fst[ P ] , CV-fst p ⟩ ᴺᴿⱽ = λ c → inj₁ ((⟨ P , p ⟩ ᴺᴿⱽ) c)
⟨ snd[ P ] , CV-snd p ⟩ ᴺᴿⱽ = λ c → inj₂ ((⟨ P , p ⟩ ᴺᴿⱽ) c)
⟨ `[ P , Q ] , CV-sum p q ⟩ ᴺᴿⱽ = λ c → ⟨ ((⟨ P , p ⟩ ᴺᴿⱽ) c) , ((⟨ Q , q ⟩ ᴺᴿⱽ) c) ⟩
⟨ not⟨ M ⟩ , CV-not ⟩ ᴺᴿⱽ = λ c z → (M ᴺᴸ) c z

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

--Substitutions--

ren-int-cbn : ∀ Γ Γ′ → Γ ↝ Γ′ → (Γ′ ᴺˣ) → (Γ ᴺˣ)
ren-int-cbn ∅ Γ′ ρ γ = tt
ren-int-cbn (Γ , A) Γ′ ρ γ = ⟨ (ren-int-cbn Γ Γ′ (λ x → ρ (`S x)) γ) , (((ρ `Z) ᴺⱽ) γ) ⟩

neg-ren-int-cbn : ∀ Θ Θ′ → Θ ↝ Θ′ → ((`¬ˣ Θ′) ᴺˣ) → ((`¬ˣ Θ) ᴺˣ)
neg-ren-int-cbn ∅ Θ′ ρ θ = tt
neg-ren-int-cbn (Θ , A) Θ′ ρ θ = ⟨ (neg-ren-int-cbn Θ Θ′ (λ x → ρ (`S x)) θ) , (((Γ∋A⇒¬Γ∋¬A (ρ `Z)) ᴺⱽ) θ) ⟩
 
sub-T-int : ∀ Γ Γ′ Θ → Γ –[ (Fix₂ Term Θ) ]→ Γ′ → (Θ ᴺˣ) → ((`¬ˣ Γ′) ᴺˣ) → ((`¬ˣ Γ) ᴺˣ)
sub-T-int ∅ Γ′ Θ σ θ γ = tt
sub-T-int (Γ , A) Γ′ Θ σ θ γ = ⟨ (sub-T-int Γ Γ′ Θ (λ x → σ (`S x)) θ γ) , ((σ `Z) ᴺᴸ) ⟨ θ , γ ⟩ ⟩

sub-CV-int : ∀ Γ Θ Θ′ → Θ –[ (Fix₁ CotermValue Γ) ]→ Θ′ → ((`¬ˣ Γ) ᴺˣ) → (Θ′ ᴺˣ) → (Θ ᴺˣ)
sub-CV-int Γ ∅ Θ′ σ γ θ = tt
sub-CV-int Γ (Θ , A) Θ′ σ γ θ = ⟨ (sub-CV-int Γ Θ Θ′ (λ x → σ (`S x)) γ θ) , ((σ `Z) ᴺᴿⱽ) ⟨ θ , γ ⟩ ⟩

--CPS Transformation of Values--
cps-V : ∀ {Γ Θ A} (V : Γ ⟶ Θ ∣ A) (v : Value V) (c : Γ ⱽˣ × (`¬ˣ Θ) ⱽˣ) 
  → (V ⱽᴸ) c ≡ λ x → x ((⟨ V , v ⟩ ⱽᴸⱽ) c)
cps-V (` x) V-var c = refl
cps-V `⟨ V , W ⟩ (V-prod v w) c = ext (λ k → 
  cong₂ (λ -₁ -₂ → -₁ (λ x → -₂ (λ y → k ⟨ x , y ⟩))) (cps-V V v c) (cps-V W w c))
cps-V inl⟨ V ⟩ (V-inl v) c = ext (λ k → cong (λ - → - (λ x → k (inj₁ x))) (cps-V V v c))
cps-V inr⟨ V ⟩ (V-inr v) c = ext (λ k → cong (λ - → - (λ x → k (inj₂ x))) (cps-V V v c))
cps-V not[ K ] V-not c = refl

cps-CV : ∀ {Γ Θ A} (P : A ∣ Γ ⟶ Θ) (p : Covalue P) (c : Θ ᴺˣ × (`¬ˣ Γ) ᴺˣ) 
  → (P ᴺᴿ) c ≡ λ z → z ((⟨ P , p ⟩ ᴺᴿⱽ) c)
cps-CV (` α) CV-covar c = refl
cps-CV fst[ P ] (CV-fst p) c = ext (λ z → cong (λ - → - (λ α → z (inj₁ α))) (cps-CV P p c))
cps-CV snd[ P ] (CV-snd p) c = ext (λ z → cong (λ - → - (λ β → z (inj₂ β))) (cps-CV P p c))
cps-CV `[ P , Q ] (CV-sum p q) c = ext (λ z → 
  cong₂ (λ -₁ -₂ → -₁ (λ α → -₂ (λ β → z ⟨ α , β ⟩))) (cps-CV P p c) (cps-CV Q q c))
cps-CV not⟨ K ⟩ CV-not c = refl
