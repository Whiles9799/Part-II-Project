\begin{code}
{-# OPTIONS --rewriting #-}

module fragments.CPSTransformation (R : Set) where

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
\end{code}

%<*v-ty+ctx>
\begin{code}
_ⱽᵀ : Type → Set
_ⱽˣ : Context → Set
\end{code}  
%</v-ty+ctx>

\begin{code}
`ℕ ⱽᵀ       = ℕ
(A `× B) ⱽᵀ = (A ⱽᵀ) × (B ⱽᵀ)
(A `+ B) ⱽᵀ = (A ⱽᵀ) ⊎ (B ⱽᵀ)
(`¬ A) ⱽᵀ   = (A ⱽᵀ) → R

∅ ⱽˣ       = ⊤
(Γ , A) ⱽˣ = Γ ⱽˣ  × A ⱽᵀ
\end{code}

--Variables--
%<*v-var>
\begin{code}
_ⱽⱽ : ∀ {Γ A} → (Γ ∋ A) → ((Γ ⱽˣ) → (A ⱽᵀ))
_ⱽⱽ `Z     = λ c → proj₂ c
_ⱽⱽ (`S x) = λ c → ((x ⱽⱽ) (proj₁ c))
\end{code}
%</v-var>
\begin{code}
Γ∋A⇒¬Γ∋¬A : ∀ {Γ A} → (Γ ∋ A) → (`¬ˣ Γ) ∋ (`¬ A)
Γ∋A⇒¬Γ∋¬A `Z     = `Z
Γ∋A⇒¬Γ∋¬A (`S x) = `S (Γ∋A⇒¬Γ∋¬A x)
\end{code}

--Sequents--
%<*v-seqdef>
\begin{code}
_ⱽᴸⱽ : ∀ {Γ Θ A} → TermValue Γ Θ A → (Γ ⱽˣ × (`¬ˣ Θ) ⱽˣ) → (A ⱽᵀ)
_ⱽᴸ : ∀ {Γ Θ A} → (Γ ⟶ Θ ∣ A) → (Γ ⱽˣ × (`¬ˣ Θ) ⱽˣ) → ((`¬ `¬ A) ⱽᵀ)
_ⱽᴿ : ∀ {Γ Θ A} → (A ∣ Γ ⟶ Θ) → (Γ ⱽˣ × (`¬ˣ Θ) ⱽˣ) → ((`¬ A) ⱽᵀ)
_ⱽˢ : ∀ {Γ Θ}   → (Γ ↦ Θ)     → (Γ ⱽˣ × (`¬ˣ Θ) ⱽˣ) → R
\end{code}
%</v-seqdef>

%<*v-varval>
\begin{code}
⟨ ` x , V-var ⟩ ⱽᴸⱽ = λ c → (x ⱽⱽ) (proj₁ c)
\end{code}
%</v-varval>
\begin{code}
⟨ `⟨ M , N ⟩ , V-prod V W ⟩ ⱽᴸⱽ = λ c → ⟨ ((⟨ M , V ⟩ ⱽᴸⱽ) c) , (⟨ N , W ⟩ ⱽᴸⱽ) c ⟩
⟨ inl⟨ M ⟩ , V-inl V ⟩ ⱽᴸⱽ = λ c → inj₁ ((⟨ M , V ⟩ ⱽᴸⱽ) c)
⟨ inr⟨ M ⟩ , V-inr V ⟩ ⱽᴸⱽ = λ c → inj₂ ((⟨ M , V ⟩ ⱽᴸⱽ) c)
⟨ not[ K ] , V-not ⟩ ⱽᴸⱽ = λ c k → (K ⱽᴿ) c k
\end{code}

%<*v-vari>
\begin{code}
(` x) ⱽᴸ            = λ c k → k ((x ⱽⱽ) (proj₁ c))
\end{code}
%</v-vari>
\begin{code}
`⟨ M , N ⟩ ⱽᴸ         = λ c k → (M ⱽᴸ) c (λ x → (N ⱽᴸ) c (λ y → k ⟨ x , y ⟩))
inl⟨ M ⟩ ⱽᴸ           = λ c k → (M ⱽᴸ) c (λ x → k (inj₁ x))
inr⟨ M ⟩ ⱽᴸ           = λ c k → (M ⱽᴸ) c (λ x → k (inj₂ x))
not[ K ] ⱽᴸ          = λ c k → k (λ z → (K ⱽᴿ) c z)
\end{code}
%<*v-covarabs>
\begin{code}
(μθ S) ⱽᴸ = λ c α → (S ⱽˢ) ⟨ (proj₁ c) , ⟨ (proj₂ c) , α ⟩ ⟩
\end{code}
%</v-covarabs>

%<*v-covar>
\begin{code}
(` α) ⱽᴿ             = λ c z → ((Γ∋A⇒¬Γ∋¬A α) ⱽⱽ) (proj₂ c) z 
\end{code}
%</v-covar>
\begin{code}
`[ K , L ] ⱽᴿ        = λ c → λ{ (inj₁ x) → (K ⱽᴿ) c x ; (inj₂ y) → (L ⱽᴿ) c y}
fst[ K ] ⱽᴿ          = λ c → λ{ ⟨ x , _ ⟩ → (K ⱽᴿ) c x} 
snd[ L ] ⱽᴿ          = λ c → λ{ ⟨ _ , y ⟩ → (L ⱽᴿ) c y}
not⟨ M ⟩ ⱽᴿ           = λ c z → (λ k → (M ⱽᴸ) c k) z
\end{code}
%<*v-varabs>
\begin{code}
(μγ S) ⱽᴿ = λ c x →  (S ⱽˢ) ⟨ ⟨ proj₁ c , x ⟩ , (proj₂ c) ⟩
\end{code}
%</v-varabs>

\begin{code}
(M ● K) ⱽˢ           = λ c → ((M ⱽᴸ) c) ((K ⱽᴿ) c)
\end{code}

--Substitutions--
%<*v-ren+sub>
\begin{code}
ren-int-cbv : ∀ Γ Γ′ → Γ ↝ Γ′ → (Γ′ ⱽˣ) → (Γ ⱽˣ)
ren-int-cbv ∅ Γ′ ρ γ = tt
ren-int-cbv (Γ , A) Γ′ ρ γ = 
  ⟨ ren-int-cbv Γ Γ′ (λ x → ρ (`S x)) γ , ((ρ `Z) ⱽⱽ) γ ⟩

neg-ren-int-cbv : ∀ Θ Θ′ → Θ ↝ Θ′ → ((`¬ˣ Θ′) ⱽˣ) → ((`¬ˣ Θ) ⱽˣ)
neg-ren-int-cbv ∅ Θ′ ρ θ = tt
neg-ren-int-cbv (Θ , A) Θ′ ρ θ = 
  ⟨ (neg-ren-int-cbv Θ Θ′ (λ x → ρ (`S x)) θ) , ((Γ∋A⇒¬Γ∋¬A (ρ `Z) ⱽⱽ) θ) ⟩
 
termvalue-sub-int : ∀ Γ Γ′ Θ → Γ –[ (λ Γ A → TermValue Γ Θ A) ]→ Γ′ 
  → ((`¬ˣ Θ) ⱽˣ) → (Γ′ ⱽˣ) → (Γ ⱽˣ)
termvalue-sub-int ∅ Γ′ Θ σ θ γ = tt
termvalue-sub-int (Γ , A) Γ′ Θ σ θ γ = 
  ⟨ (termvalue-sub-int Γ Γ′ Θ (λ x → σ (`S x)) θ γ) , ((σ `Z ⱽᴸⱽ) ⟨ γ , θ ⟩) ⟩

coterm-sub-int : ∀ Γ Θ Θ′ → Θ –[ (λ Θ A → A ∣ Γ ⟶ Θ) ]→ Θ′ 
  → Γ ⱽˣ → ((`¬ˣ Θ′) ⱽˣ) → ((`¬ˣ Θ) ⱽˣ)
coterm-sub-int Γ ∅ Θ′ σ γ _ = tt
coterm-sub-int Γ (Θ , A) Θ′ σ γ θ = 
  ⟨ (coterm-sub-int Γ Θ Θ′ (λ z → σ (`S z)) γ θ) , (((σ `Z) ⱽᴿ) ⟨ γ , θ ⟩) ⟩
\end{code}
%</v-ren+sub>
--Call-by-Name CPS Transformation--


--Types and Contexts--
%<*n-ty+ctx>
\begin{code}
_ᴺᵀ : Type → Set
_ᴺˣ : Context → Set

`ℕ ᴺᵀ        = ℕ
(A `× B) ᴺᵀ  = (A ᴺᵀ) ⊎ (B ᴺᵀ)
(A `+ B) ᴺᵀ  = (A ᴺᵀ) × (B ᴺᵀ)
(`¬ A) ᴺᵀ    = (A ᴺᵀ) → R

∅ ᴺˣ       = ⊤
(Γ , A) ᴺˣ =  Γ ᴺˣ × A ᴺᵀ 
\end{code}
%</n-ty+ctx>

--Variables--
%<*n-var>
\begin{code}
_ᴺⱽ : ∀ {Γ A} → (Γ ∋ A) → (Γ ᴺˣ) → (A ᴺᵀ)
_ᴺⱽ `Z     = λ x → proj₂ x 
_ᴺⱽ (`S x) = λ c → ((x ᴺⱽ) (proj₁ c))
\end{code}
%</n-var>

--Sequents--
%<*n-seqdef>
\begin{code}
_ᴺᴿⱽ : ∀ {Γ Θ A} → (CotermValue Γ Θ A) → (Θ ᴺˣ × (`¬ˣ Γ) ᴺˣ) → (A) ᴺᵀ 
_ᴺᴸ : ∀ {Γ Θ A} → (Γ ⟶ Θ ∣ A) → (Θ ᴺˣ × (`¬ˣ Γ) ᴺˣ) → (`¬ A) ᴺᵀ
_ᴺᴿ : ∀ {Γ Θ A} → (A ∣ Γ ⟶ Θ) → (Θ ᴺˣ × (`¬ˣ Γ) ᴺˣ) → (`¬ `¬ A) ᴺᵀ
_ᴺˢ : ∀ {Γ Θ}   → (Γ ↦ Θ)     → (Θ ᴺˣ × (`¬ˣ Γ) ᴺˣ) → R
\end{code}
%</n-seqdef>

%<*n-seq>
\begin{code}
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
\end{code}
%</n-seq>

--Substitutions--
%<*n-ren+sub>
ren-int-cbn : ∀ Γ Γ′ → Γ ↝ Γ′ → (Γ′ ᴺˣ) → (Γ ᴺˣ)
ren-int-cbn ∅ Γ′ ρ γ = tt
ren-int-cbn (Γ , A) Γ′ ρ γ = 
  ⟨ (ren-int-cbn Γ Γ′ (λ x → ρ (`S x)) γ) , 
  (((ρ `Z) ᴺⱽ) γ) ⟩

neg-ren-int-cbn : ∀ Θ Θ′ → Θ ↝ Θ′ → ((`¬ˣ Θ′) ᴺˣ) → ((`¬ˣ Θ) ᴺˣ)
neg-ren-int-cbn ∅ Θ′ ρ θ = tt
neg-ren-int-cbn (Θ , A) Θ′ ρ θ = 
  ⟨ (neg-ren-int-cbn Θ Θ′ (λ x → ρ (`S x)) θ) , 
  (((Γ∋A⇒¬Γ∋¬A (ρ `Z)) ᴺⱽ) θ) ⟩
 
term-sub-int : ∀ Γ Γ′ Θ → Γ –[ (λ Γ A → Γ ⟶ Θ ∣ A) ]→ Γ′ 
  → (Θ ᴺˣ) → ((`¬ˣ Γ′) ᴺˣ) → ((`¬ˣ Γ) ᴺˣ)
term-sub-int ∅ Γ′ Θ σ θ γ = tt
term-sub-int (Γ , A) Γ′ Θ σ θ γ = 
  ⟨ (term-sub-int Γ Γ′ Θ (λ x → σ (`S x)) θ γ) , 
  ((σ `Z) ᴺᴸ) ⟨ θ , γ ⟩ ⟩

cotermvalue-sub-int : ∀ Γ Θ Θ′ → Θ –[ (λ Θ A → CotermValue Γ Θ A) ]→ Θ′ 
  → ((`¬ˣ Γ) ᴺˣ) → (Θ′ ᴺˣ) → (Θ ᴺˣ)
cotermvalue-sub-int Γ ∅ Θ′ σ γ θ = tt
cotermvalue-sub-int Γ (Θ , A) Θ′ σ γ θ = 
  ⟨ (cotermvalue-sub-int Γ Θ Θ′ (λ x → σ (`S x)) γ θ) ,
  ((σ `Z) ᴺᴿⱽ) ⟨ θ , γ ⟩ ⟩
%<‌/n-ren+sub>
--Proofs of Duality--

--Types and Contexts--
%<*dual-tyctx>
\begin{code}
Aⱽ≡Aᵒᴺ : ∀ {A} → A ⱽᵀ ≡ (A ᵒᵀ) ᴺᵀ
Aⱽ≡Aᵒᴺ {`ℕ}     = refl 
Aⱽ≡Aᵒᴺ {A `+ B} = cong₂ _⊎_ (Aⱽ≡Aᵒᴺ {A}) (Aⱽ≡Aᵒᴺ {B})
Aⱽ≡Aᵒᴺ {A `× B} = cong₂ _×_ (Aⱽ≡Aᵒᴺ {A}) (Aⱽ≡Aᵒᴺ {B})
Aⱽ≡Aᵒᴺ {`¬ A}   = cong (λ - → - → R) Aⱽ≡Aᵒᴺ

Γⱽ≡Γᵒᴺ : ∀ {Γ} → Γ ⱽˣ ≡ (Γ ᵒˣ) ᴺˣ
Γⱽ≡Γᵒᴺ {∅}       = refl
Γⱽ≡Γᵒᴺ {(Γ , A)} = cong₂ _×_ Γⱽ≡Γᵒᴺ Aⱽ≡Aᵒᴺ
\end{code}
%</dual-tyctx>
\begin{code}
{-# REWRITE Aⱽ≡Aᵒᴺ #-}
{-# REWRITE Γⱽ≡Γᵒᴺ #-}
\end{code}
--lemmas required for following proofs--
%<*dual-lemmas>
\begin{code}
[¬Γ]ᵒ≡¬[Γᵒ] : ∀ {Γ} → (`¬ˣ Γ) ᵒˣ ≡ `¬ˣ (Γ ᵒˣ)
[¬Γ]ᵒ≡¬[Γᵒ] {∅}       = refl
[¬Γ]ᵒ≡¬[Γᵒ] {(Γ , A)} = cong₂ _,_ ([¬Γ]ᵒ≡¬[Γᵒ] {Γ}) refl

{-# REWRITE [¬Γ]ᵒ≡¬[Γᵒ] #-}

[Γ∋A⇒¬Γ∋¬Ax]ᵒ≡Γ∋A⇒¬Γ∋¬A[xᵒ] : ∀ {Γ A} (x : Γ ∋ A) 
  → Γ∋A⇒¬Γ∋¬A x ᵒⱽ ≡ Γ∋A⇒¬Γ∋¬A (x ᵒⱽ)
[Γ∋A⇒¬Γ∋¬Ax]ᵒ≡Γ∋A⇒¬Γ∋¬A[xᵒ] `Z     = refl
[Γ∋A⇒¬Γ∋¬Ax]ᵒ≡Γ∋A⇒¬Γ∋¬A[xᵒ] (`S x) = cong `S ([Γ∋A⇒¬Γ∋¬Ax]ᵒ≡Γ∋A⇒¬Γ∋¬A[xᵒ] x)

{-# REWRITE [Γ∋A⇒¬Γ∋¬Ax]ᵒ≡Γ∋A⇒¬Γ∋¬A[xᵒ] #-}
\end{code}
%</dual-lemmas>
--Variables--
%<*dual-var>
\begin{code}
xⱽ≡xᵒᴺ : ∀ {Γ A} (x : Γ ∋ A) → x ⱽⱽ ≡ ((x ᵒⱽ) ᴺⱽ)
xⱽ≡xᵒᴺ `Z         = refl
xⱽ≡xᵒᴺ (`S x)     = ext (λ c → cong (λ - → - (proj₁ c)) (xⱽ≡xᵒᴺ x))
\end{code}
%</dual-var>
--Terms--

%<*dual-seq>
\begin{code}
Mⱽ≡Mᵒᴺ : ∀ {Γ Θ A} (M : Γ ⟶ Θ ∣ A) (c : Γ ⱽˣ × (`¬ˣ Θ) ⱽˣ) (k : ((`¬ A) ⱽᵀ)) 
  → (M ⱽᴸ) c k ≡ ((M ᵒᴸ) ᴺᴿ) c k
Kⱽ≡Kᵒᴺ : ∀ {Γ Θ A} (K : A ∣ Γ ⟶ Θ) (c : Γ ⱽˣ × (`¬ˣ Θ) ⱽˣ) (k : (A) ⱽᵀ)      
  → (K ⱽᴿ) c k ≡ ((K ᵒᴿ) ᴺᴸ) c k
Sⱽ≡Sᵒᴺ : ∀ {Γ Θ}   (S : Γ ↦ Θ)     (c : Γ ⱽˣ × (`¬ˣ Θ) ⱽˣ)                   
  → (S ⱽˢ) c   ≡ ((S ᵒˢ) ᴺˢ) c

Mⱽ≡Mᵒᴺ (` x) ⟨ c , _ ⟩ k       = cong  (λ - → k(-  c)) (xⱽ≡xᵒᴺ x)
Mⱽ≡Mᵒᴺ `⟨ M , N ⟩ c k          = trans 
  (Mⱽ≡Mᵒᴺ M c (λ x → (N ⱽᴸ) c ((λ y → k ⟨ x , y ⟩))))
  (cong (λ - → (((M ᵒᴸ) ᴺᴿ) c) - ) (ext (λ x → Mⱽ≡Mᵒᴺ N c (λ y → k ⟨ x , y ⟩))))
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

Sⱽ≡Sᵒᴺ (M ● K) c             = trans 
  (Mⱽ≡Mᵒᴺ M c ((K ⱽᴿ) c)) 
  (cong (λ - → ((M ᵒᴸ) ᴺᴿ) c -) (ext (λ x → Kⱽ≡Kᵒᴺ K c x)))
\end{code}
%</dual-seq>


--CPS Transformation of Values--
%<*val>
\begin{code}
cps-value : ∀ {Γ Θ A} (V : Γ ⟶ Θ ∣ A) (v : Value V) (c : Γ ⱽˣ × (`¬ˣ Θ) ⱽˣ) 
  → (V ⱽᴸ) c ≡ λ x → x ((⟨ V , v ⟩ ⱽᴸⱽ) c)
cps-value (` x) V-var c = refl
cps-value `⟨ V , W ⟩ (V-prod v w) c = ext (λ x → trans 
  ((cong (λ - → - (λ x₁ → (W ⱽᴸ) c (λ y → x ⟨ x₁ , y ⟩)))) (cps-value V v c)) 
  (cong (λ - → - (λ y → x ⟨ (⟨ V , v ⟩ ⱽᴸⱽ) c , y ⟩)) (cps-value W w c)))
cps-value inl⟨ V ⟩ (V-inl v) c = ext (λ x → cong (λ - → - (λ x₁ → x (inj₁ x₁))) (cps-value V v c))
cps-value inr⟨ V ⟩ (V-inr v) c = ext (λ x → cong (λ - → - (λ x₁ → x (inj₂ x₁))) (cps-value V v c))
cps-value not[ K ] V-not c = refl

cps-covalue : ∀ {Γ Θ A} (P : A ∣ Γ ⟶ Θ) (p : Covalue P) (c : Θ ᴺˣ × (`¬ˣ Γ) ᴺˣ) 
  → (P ᴺᴿ) c ≡ λ z → z ((⟨ P , p ⟩ ᴺᴿⱽ) c)
cps-covalue (` α) CV-covar c = refl
cps-covalue fst[ P ] (CV-fst p) c = ext (λ x → cong (λ - → - (λ α → x (inj₁ α))) (cps-covalue P p c))
cps-covalue snd[ P ] (CV-snd p) c = ext (λ x → cong (λ - → - (λ β → x (inj₂ β))) (cps-covalue P p c))
cps-covalue `[ P , Q ] (CV-sum p q) c = ext (λ x → 
  cong₂ (λ -₁ -₂ → -₁ (λ α → -₂ (λ β → x ⟨ α , β ⟩))) (cps-covalue P p c) (cps-covalue Q q c))
cps-covalue not⟨ K ⟩ CV-not c = refl
\end{code}
%</val>