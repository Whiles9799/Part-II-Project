\begin{code}
{-# OPTIONS --rewriting #-}

module fragments.CPSTransformation (R : Set) where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym; trans; subst)
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

infix 13 _ⱽᵀ
infix 13 _ⱽⱽ
infix 13 _ⱽˣ
infix 13 _ⱽᴸ
infix 13 _ⱽᴿ
infix 13 _ⱽˢ

infix 13 _ᴺᵀ
infix 13 _ᴺⱽ
infix 13 _ᴺˣ
infix 13 _ᴺᴸ
infix 13 _ᴺᴿ
infix 13 _ᴺˢ


--Call-by-Value CPS Transformation--

--Types and Contexts--
\end{code}

%<*v-ty+ctx>
\begin{code}
_ⱽᵀ : Type → Set
_ⱽˣ : Context → Set

`ℕ ⱽᵀ       = ℕ
(A `× B) ⱽᵀ = (A ⱽᵀ) × (B ⱽᵀ)
(A `+ B) ⱽᵀ = (A ⱽᵀ) ⊎ (B ⱽᵀ)
(`¬ A) ⱽᵀ   = (A ⱽᵀ) → R

∅ ⱽˣ       = ⊤
(Γ , A) ⱽˣ = Γ ⱽˣ  × A ⱽᵀ
\end{code}  
%</v-ty+ctx>

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
_ⱽᴸ : ∀ {Γ Θ A} → (Γ ⟶ Θ ∣ A) → (Γ ⱽˣ × (`¬ˣ Θ) ⱽˣ) → ((A ⱽᵀ → R) → R)
_ⱽᴿ : ∀ {Γ Θ A} → (A ∣ Γ ⟶ Θ) → (Γ ⱽˣ × (`¬ˣ Θ) ⱽˣ) → (A ⱽᵀ → R)
_ⱽˢ : ∀ {Γ Θ}   → (Γ ↦ Θ)     → (Γ ⱽˣ × (`¬ˣ Θ) ⱽˣ) → R
\end{code}
%</v-seqdef>

%<*v-varval>
\begin{code}
(⟨ ` x , V-var ⟩ ⱽᴸⱽ) ⟨ γ , θ ⟩ = (x ⱽⱽ) γ
\end{code}
%</v-varval>
\begin{code}
(⟨ `⟨ M , N ⟩ , V-prod V W ⟩ ⱽᴸⱽ) c = ⟨ ((⟨ M , V ⟩ ⱽᴸⱽ) c) , (⟨ N , W ⟩ ⱽᴸⱽ) c ⟩
(⟨ inl⟨ M ⟩ , V-inl V ⟩ ⱽᴸⱽ) c = inj₁ ((⟨ M , V ⟩ ⱽᴸⱽ) c)
(⟨ inr⟨ M ⟩ , V-inr V ⟩ ⱽᴸⱽ) c = inj₂ ((⟨ M , V ⟩ ⱽᴸⱽ) c)
(⟨ not[ K ] , V-not ⟩ ⱽᴸⱽ) c = λ k → (K ⱽᴿ) c k
\end{code}

%<*v-vari>
\begin{code}
((` x) ⱽᴸ) ⟨ γ , θ ⟩         = λ k → k ((x ⱽⱽ) γ)
\end{code}
%</v-vari>
\begin{code}
(`⟨ M , N ⟩ ⱽᴸ) c        = λ k → (M ⱽᴸ) c (λ x → (N ⱽᴸ) c (λ y → k ⟨ x , y ⟩))
(inl⟨ M ⟩ ⱽᴸ) c          = λ k → (M ⱽᴸ) c (λ x → k (inj₁ x))
(inr⟨ M ⟩ ⱽᴸ) c          = λ k → (M ⱽᴸ) c (λ x → k (inj₂ x))
(not[ K ] ⱽᴸ) c          = λ k → k (λ z → (K ⱽᴿ) c z)
\end{code}
%<*v-covarabs>
\begin{code}
((μθ S) ⱽᴸ) ⟨ γ , θ ⟩ = λ α → (S ⱽˢ) ⟨ γ , ⟨ θ , α ⟩ ⟩
\end{code}
%</v-covarabs>

%<*v-covar>
\begin{code}
((` α) ⱽᴿ) ⟨ γ , θ ⟩            = λ z → ((Γ∋A⇒¬Γ∋¬A α) ⱽⱽ) θ z 
\end{code}
%</v-covar>
\begin{code}
(`[ K , L ] ⱽᴿ) c       =  λ{ (inj₁ x) → (K ⱽᴿ) c x ; (inj₂ y) → (L ⱽᴿ) c y}
(fst[ K ] ⱽᴿ) c         = λ{ ⟨ x , _ ⟩ → (K ⱽᴿ) c x} 
(snd[ L ] ⱽᴿ) c         = λ{ ⟨ _ , y ⟩ → (L ⱽᴿ) c y}
(not⟨ M ⟩ ⱽᴿ) c         = λ z → (λ k → (M ⱽᴸ) c k) z
\end{code}
%<*v-varabs>
\begin{code}
((μγ S) ⱽᴿ) ⟨ γ , θ ⟩ = λ x →  (S ⱽˢ) ⟨ ⟨ γ , x ⟩ , θ ⟩
\end{code}
%</v-varabs>

\begin{code}
((M ● K) ⱽˢ) c          = ((M ⱽᴸ) c) ((K ⱽᴿ) c)
\end{code}

--Substitutions--
%<*v-renty>
\begin{code}
ren-int-cbv : ∀ Γ Γ′ → Γ ↝ Γ′ → (Γ′ ⱽˣ) → (Γ ⱽˣ)
\end{code}
%</v-renty>
%<*v-ren>
\begin{code}
ren-int-cbv ∅ Γ′ ρ γ = tt
ren-int-cbv (Γ , A) Γ′ ρ γ = 
  ⟨ (ren-int-cbv Γ Γ′ (λ z → ρ (`S z)) γ) , (((ρ `Z) ⱽⱽ) γ) ⟩
\end{code}
%</v-ren>
%<*v-negren>
\begin{code}
neg-ren-int-cbv : ∀ Θ Θ′ → Θ ↝ Θ′ → ((`¬ˣ Θ′) ⱽˣ) → ((`¬ˣ Θ) ⱽˣ)
\end{code}
%</v-negren>
\begin{code}
neg-ren-int-cbv ∅ Θ′ ρ θ = tt
neg-ren-int-cbv (Θ , A) Θ′ ρ θ = 
  ⟨ (neg-ren-int-cbv Θ Θ′ (λ x → ρ (`S x)) θ) , ((Γ∋A⇒¬Γ∋¬A (ρ `Z) ⱽⱽ) θ) ⟩
\end{code}

%<*v-tvsub>
\begin{code}
sub-TV-int : ∀ Γ Γ′ Θ → Γ –[ (Fix₂ TermValue Θ) ]→ Γ′ 
  → ((`¬ˣ Θ) ⱽˣ) → (Γ′ ⱽˣ) → (Γ ⱽˣ)
\end{code}
%</v-tvsub>
\begin{code}
sub-TV-int ∅ Γ′ Θ σ θ γ = tt
sub-TV-int (Γ , A) Γ′ Θ σ θ γ = 
  ⟨ (sub-TV-int Γ Γ′ Θ (λ x → σ (`S x)) θ γ) , ((σ `Z ⱽᴸⱽ) ⟨ γ , θ ⟩) ⟩
\end{code}

%<*v-csub>
\begin{code}
sub-C-int : ∀ Γ Θ Θ′ → Θ –[ (Fix₁ Coterm Γ) ]→ Θ′ 
  → Γ ⱽˣ → ((`¬ˣ Θ′) ⱽˣ) → ((`¬ˣ Θ) ⱽˣ)
\end{code}
%</v-csub>
\begin{code}
sub-C-int Γ ∅ Θ′ σ γ _ = tt
sub-C-int Γ (Θ , A) Θ′ σ γ θ = 
  ⟨ (sub-C-int Γ Θ Θ′ (λ z → σ (`S z)) γ θ) , (((σ `Z) ⱽᴿ) ⟨ γ , θ ⟩) ⟩
\end{code}

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
_ᴺᴸ : ∀ {Γ Θ A} → (Γ ⟶ Θ ∣ A) → (Θ ᴺˣ × (`¬ˣ Γ) ᴺˣ) → (A ᴺᵀ → R)
_ᴺᴿ : ∀ {Γ Θ A} → (A ∣ Γ ⟶ Θ) → (Θ ᴺˣ × (`¬ˣ Γ) ᴺˣ) → ((A ᴺᵀ → R) → R)
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
 
sub-T-int : ∀ Γ Γ′ Θ → Γ –[ (Fix₂ Term Θ) ]→ Γ′ 
  → (Θ ᴺˣ) → ((`¬ˣ Γ′) ᴺˣ) → ((`¬ˣ Γ) ᴺˣ)
sub-T-int ∅ Γ′ Θ σ θ γ = tt
sub-T-int (Γ , A) Γ′ Θ σ θ γ = 
  ⟨ (sub-T-int Γ Γ′ Θ (λ x → σ (`S x)) θ γ) , 
  ((σ `Z) ᴺᴸ) ⟨ θ , γ ⟩ ⟩

sub-CV-int : ∀ Γ Θ Θ′ → Θ –[ (Fix₁ CotermValue Γ) ]→ Θ′ 
  → ((`¬ˣ Γ) ᴺˣ) → (Θ′ ᴺˣ) → (Θ ᴺˣ)
sub-CV-int Γ ∅ Θ′ σ γ θ = tt
sub-CV-int Γ (Θ , A) Θ′ σ γ θ = 
  ⟨ (sub-CV-int Γ Θ Θ′ (λ x → σ (`S x)) γ θ) ,
  ((σ `Z) ᴺᴿⱽ) ⟨ θ , γ ⟩ ⟩
%<‌/n-ren+sub>
--Proofs of Duality--

--Types and Contexts--
%<*dual-ty>
\begin{code}
Aⱽ≡Aᵒᴺ : ∀ {A} → A ⱽᵀ ≡ (A ᵒᵀ) ᴺᵀ
\end{code}
%</dual-ty>
\begin{code}
Aⱽ≡Aᵒᴺ {`ℕ}     = refl 
Aⱽ≡Aᵒᴺ {A `+ B} = cong₂ _⊎_ (Aⱽ≡Aᵒᴺ {A}) (Aⱽ≡Aᵒᴺ {B})
Aⱽ≡Aᵒᴺ {A `× B} = cong₂ _×_ (Aⱽ≡Aᵒᴺ {A}) (Aⱽ≡Aᵒᴺ {B})
Aⱽ≡Aᵒᴺ {`¬ A}   = cong (λ - → - → R) Aⱽ≡Aᵒᴺ
\end{code}
%<*dual-ctx>
\begin{code}
Γⱽ≡Γᵒᴺ : ∀ {Γ} → Γ ⱽˣ ≡ (Γ ᵒˣ) ᴺˣ
\end{code}
%</dual-ctx>
\begin{code}
Γⱽ≡Γᵒᴺ {∅}       = refl
Γⱽ≡Γᵒᴺ {(Γ , A)} = cong₂ _×_ Γⱽ≡Γᵒᴺ Aⱽ≡Aᵒᴺ

{-# REWRITE Aⱽ≡Aᵒᴺ #-}
{-# REWRITE Γⱽ≡Γᵒᴺ #-}
\end{code}
--lemmas required for following proofs--
%<*dual-lemma1>
\begin{code}
[¬Γ]ᵒ≡¬[Γᵒ] : ∀ {Γ} → (`¬ˣ Γ) ᵒˣ ≡ `¬ˣ (Γ ᵒˣ)
\end{code}
%</dual-lemma1>
\begin{code}
[¬Γ]ᵒ≡¬[Γᵒ] {∅}       = refl
[¬Γ]ᵒ≡¬[Γᵒ] {(Γ , A)} = cong₂ _,_ ([¬Γ]ᵒ≡¬[Γᵒ] {Γ}) refl

{-# REWRITE [¬Γ]ᵒ≡¬[Γᵒ] #-}
\end{code}

%<*dual-lemma2>
\begin{code}
[Γ∋A⇒¬Γ∋¬Ax]ᵒ≡Γ∋A⇒¬Γ∋¬A[xᵒ] : ∀ {Γ A} (x : Γ ∋ A) 
  → Γ∋A⇒¬Γ∋¬A x ᵒⱽ ≡ Γ∋A⇒¬Γ∋¬A (x ᵒⱽ)
\end{code}
%</dual-lemma2>
\begin{code}
[Γ∋A⇒¬Γ∋¬Ax]ᵒ≡Γ∋A⇒¬Γ∋¬A[xᵒ] `Z     = refl
[Γ∋A⇒¬Γ∋¬Ax]ᵒ≡Γ∋A⇒¬Γ∋¬A[xᵒ] (`S x) = cong `S ([Γ∋A⇒¬Γ∋¬Ax]ᵒ≡Γ∋A⇒¬Γ∋¬A[xᵒ] x)

-- {-# REWRITE [Γ∋A⇒¬Γ∋¬Ax]ᵒ≡Γ∋A⇒¬Γ∋¬A[xᵒ] #-}
\end{code}
--Variables--
%<*dual-var>
\begin{code}
xⱽ≡xᵒᴺ : ∀ {Γ A} (x : Γ ∋ A) (c : Γ ⱽˣ) → (x ⱽⱽ) c ≡ ((x ᵒⱽ) ᴺⱽ) c
xⱽ≡xᵒᴺ `Z c     = refl
xⱽ≡xᵒᴺ (`S x) c = xⱽ≡xᵒᴺ x (proj₁ c)
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
\end{code}
%</dual-seq>
\begin{code}
Mⱽ≡Mᵒᴺ (` x) ⟨ c , _ ⟩ k       = cong k (xⱽ≡xᵒᴺ x c)
Mⱽ≡Mᵒᴺ `⟨ M , N ⟩ c k          = cong₂ (λ -₁ -₂ → -₁ (λ x → -₂ (λ y → k ⟨ x , y ⟩))) 
                                  (ext (λ k → Mⱽ≡Mᵒᴺ M c k)) (ext (λ  k → Mⱽ≡Mᵒᴺ N c k))
Mⱽ≡Mᵒᴺ inl⟨ M ⟩ c k            = Mⱽ≡Mᵒᴺ M c (λ x → k (inj₁ x)) 
Mⱽ≡Mᵒᴺ inr⟨ M ⟩ c k            = Mⱽ≡Mᵒᴺ M c (λ x → k (inj₂ x))
Mⱽ≡Mᵒᴺ not[ K ] c k           = cong k (ext (λ x → Kⱽ≡Kᵒᴺ K c x))
\end{code}
%<*dual-covarabs>
\begin{code}
Mⱽ≡Mᵒᴺ (μθ S) ⟨ c₁ , c₂ ⟩ k    = Sⱽ≡Sᵒᴺ S ⟨ c₁ , ⟨ c₂ , k ⟩ ⟩ 
\end{code}
%</dual-covarabs>
%<*dual-covari>
\begin{code}
Kⱽ≡Kᵒᴺ (` α) ⟨ _ , c ⟩ k      = trans 
                                 (cong (λ - → - k) (xⱽ≡xᵒᴺ (Γ∋A⇒¬Γ∋¬A α) c)) 
                                 (cong (λ - → (- ᴺⱽ) c k) ([Γ∋A⇒¬Γ∋¬Ax]ᵒ≡Γ∋A⇒¬Γ∋¬A[xᵒ] α))
\end{code}
%</dual-covari>
\begin{code}
Kⱽ≡Kᵒᴺ fst[ K ] c ⟨ k , _ ⟩   = Kⱽ≡Kᵒᴺ K c k
Kⱽ≡Kᵒᴺ snd[ K ] c ⟨ _ , k ⟩   = Kⱽ≡Kᵒᴺ K c k
Kⱽ≡Kᵒᴺ `[ K , L ] c (inj₁ k) = Kⱽ≡Kᵒᴺ K c k
Kⱽ≡Kᵒᴺ `[ K , L ] c (inj₂ k) = Kⱽ≡Kᵒᴺ L c k
Kⱽ≡Kᵒᴺ not⟨ M ⟩ c k           = Mⱽ≡Mᵒᴺ M c k
\end{code}
%<*dual-varabs>
\begin{code}
Kⱽ≡Kᵒᴺ (μγ S) ⟨ c₁ , c₂ ⟩ k   = Sⱽ≡Sᵒᴺ S ⟨ ⟨ c₁ , k ⟩ , c₂ ⟩
\end{code}
%</dual-varabs>
\begin{code}
Sⱽ≡Sᵒᴺ (M ● K) c             = (cong₂ (λ -₁ -₂ → -₁ -₂)) 
                                 (ext (λ k → Mⱽ≡Mᵒᴺ M c k)) (ext (λ k → Kⱽ≡Kᵒᴺ K c k))
\end{code}



--CPS Transformation of Values--
%<*valty>
\begin{code}
cps-V : ∀ {Γ Θ A} (V : Γ ⟶ Θ ∣ A) (v : Value V) (c : Γ ⱽˣ × (`¬ˣ Θ) ⱽˣ)
  → (V ⱽᴸ) c ≡ λ x → x ((⟨ V , v ⟩ ⱽᴸⱽ) c)
\end{code}
%</valty>
\begin{code}
cps-V (` x) V-var c = refl
cps-V `⟨ V , W ⟩ (V-prod v w) c = ext (λ k → 
  cong₂ (λ -₁ -₂ → -₁ (λ x → -₂ (λ y → k ⟨ x , y ⟩))) (cps-V V v c) (cps-V W w c))
\end{code}
%<*valeg>
\begin{code}
cps-V inl⟨ V ⟩ (V-inl v) c = ext (λ k → cong (λ - → - (λ x → k (inj₁ x))) (cps-V V v c))
\end{code}
%</valeg>
\begin{code}
cps-V inr⟨ V ⟩ (V-inr v) c = ext (λ k → cong (λ - → - (λ y → k (inj₂ y))) (cps-V V v c))
cps-V not[ K ] V-not c = refl
\end{code}

%<*covalty>
\begin{code}
cps-CV : ∀ {Γ Θ A} (P : A ∣ Γ ⟶ Θ) (p : Covalue P) (c : Θ ᴺˣ × (`¬ˣ Γ) ᴺˣ) 
  → (P ᴺᴿ) c ≡ λ z → z ((⟨ P , p ⟩ ᴺᴿⱽ) c)
\end{code}
%</covalty>
\begin{code}
cps-CV (` α) CV-covar c = refl
cps-CV fst[ P ] (CV-fst p) c = ext (λ z → cong (λ - → - (λ α → z (inj₁ α))) (cps-CV P p c))
cps-CV snd[ P ] (CV-snd p) c = ext (λ z → cong (λ - → - (λ β → z (inj₂ β))) (cps-CV P p c))
\end{code}
%<*covaleg>
\begin{code}
cps-CV `[ P , Q ] (CV-sum p q) c = ext (λ z → 
  cong₂ (λ -₁ -₂ → -₁ (λ α → -₂ (λ β → z ⟨ α , β ⟩))) (cps-CV P p c) (cps-CV Q q c))
\end{code}
%</covaleg>
\begin{code}
cps-CV not⟨ K ⟩ CV-not c = refl
\end{code}

\begin{code}
ex1 : ∀ {A B} → ∅ , A , B ⟶ ∅ ∣ A `× B
ex1 = `⟨ γ 1 , γ 0 ⟩

ex1ⱽ : ∀ {A B} x y → (((A `× B) ⱽᵀ → R) → R)
ex1ⱽ {A} {B} x y = (ex1 {A}{B} ⱽᴸ) ⟨ ⟨ ⟨ tt , x ⟩ , y ⟩ , tt ⟩
\end{code}

%<*ex2>
\begin{code}
ex2 : ∀ {A B} → ∅ , (A `× B) ⟶ ∅ ∣ A
ex2 = μθ (γ 0 ● fst[ θ 0 ])

ex2ⱽ : ∀ {A B} z → ((A ⱽᵀ → R) → R)
ex2ⱽ {A}{B} z = (ex2 {A}{B} ⱽᴸ) ⟨ ⟨ tt , z ⟩ , tt ⟩

_ : ∀ {A B} z → (ex2ⱽ {A}{B} z) ≡ λ α → α (proj₁ z)
_ = λ z → refl
\end{code}
%</ex2>

\begin{code}

ex3 : ∀ {A B} → (∅ , A `× B) ⟶ ∅ ∣ A `× B
ex3 = `⟨ μθ ( γ 0 ● fst[ θ 0 ] ) , μθ ( γ 0 ● snd[ θ 0 ] ) ⟩

ex3ⱽ : ∀ {A B} x → (((A `× B) ⱽᵀ → R) → R)
ex3ⱽ {A}{B} x = ((ex3 {A}{B}) ⱽᴸ) ⟨ ⟨ tt , x ⟩ , tt ⟩

ex4 : ∀ {A} → (∅ , A) ↦ (∅ , A)
ex4 = (γ 0) ● (θ 0)

ex4ⱽ : ∀ {A} x α → R
ex4ⱽ {A} x α = (ex4 {A} ⱽˢ) ⟨ ⟨ tt , x ⟩ , ⟨ tt , α ⟩ ⟩

ex5 : ∀ {A} → (∅ , A) ↦ (∅ , A)
ex5 = not[ (θ 0) ] ● not⟨ (γ 0) ⟩ 

ex5ⱽ : ∀ {A} x α → R
ex5ⱽ {A} x α = (ex5 {A} ⱽˢ) ⟨ ⟨ tt , x ⟩ , ⟨ tt , α ⟩ ⟩
\end{code}