\begin{code}
{-# OPTIONS --rewriting #-}

module fragments.CBVSoundness (R : Set) where

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
open import Dual.CPSTransformation R


--Lemmas for proving the Renaming Lemma--

--The interpretation of weakened renaming applied to an extended context is equivalent to 
--the interpretation of the unweakened renaming applied to the unextended context--
\end{code}

%<*ren-weaken-ty>
\begin{code}
weaken-ren-int-cbv-lemma : ∀ {Γ Γ′ A} (ρ : Γ ↝ Γ′) γ k 
  → ren-int-cbv Γ (Γ′ , A) (rename-weaken ρ) ⟨ γ , k ⟩ ≡ ren-int-cbv Γ Γ′ ρ γ
\end{code}
%</ren-weaken-ty>
%<*ren-weaken>
\begin{code}
weaken-ren-int-cbv-lemma {∅} ρ γ k = refl
weaken-ren-int-cbv-lemma {Γ , B}{Γ′}{A} ρ γ k = 
  cong (λ - → ⟨ - , (ρ `Z ⱽⱽ) γ ⟩) (weaken-ren-int-cbv-lemma {Γ}{Γ′}{A} (ren-skip ρ) γ k)
\end{code}
%</ren-weaken>

--The interpretation of the id renaming to an interpreted context has no effect--
%<*id-ren>
\begin{code}
id-ren : ∀ {Γ} (γ : Γ ⱽˣ) → ren-int-cbv Γ Γ id-var γ ≡ γ
\end{code}
%</id-ren>
\begin{code}
id-ren {∅} γ = refl
id-ren {Γ , A} ⟨ γ₁ , γ₂ ⟩ = 
  cong (λ - → ⟨ - , γ₂ ⟩) (trans (weaken-ren-int-cbv-lemma id-var γ₁ γ₂) (id-ren γ₁))
\end{code}
--Equivalent lemmas for negated context interpretations--
%<*neg-ren-weaken-ty>
\begin{code}
weaken-neg-ren-int-cbv-lemma : ∀ {Θ Θ′ A} (ρ : Θ ↝ Θ′) θ k 
  → neg-ren-int-cbv Θ (Θ′ , A) (rename-weaken ρ) ⟨ θ , k ⟩ ≡ neg-ren-int-cbv Θ Θ′ ρ θ
\end{code}
%</neg-ren-weaken-ty>
\begin{code}
weaken-neg-ren-int-cbv-lemma {∅} ρ θ k = refl
weaken-neg-ren-int-cbv-lemma {Θ , B}{Θ′}{A} ρ θ k = 
  cong (λ - → ⟨ - , (Γ∋A⇒¬Γ∋¬A (ρ `Z) ⱽⱽ) θ ⟩) (weaken-neg-ren-int-cbv-lemma (ren-skip ρ) θ k)
\end{code}

%<*id-neg-ren>
\begin{code}
id-neg-ren : ∀ {Θ} (θ : (`¬ˣ Θ) ⱽˣ) → neg-ren-int-cbv Θ Θ id-var θ ≡ θ
\end{code}
%</id-neg-ren>
\begin{code}
id-neg-ren {∅} θ = refl
id-neg-ren {Θ , A} ⟨ θ₁ , θ₂ ⟩ = 
  cong (λ - → ⟨ - , θ₂ ⟩) (trans (weaken-neg-ren-int-cbv-lemma id-var θ₁ θ₂) (id-neg-ren θ₁))
\end{code}
--The Renaming Lemma--
--The interpretation of the renaming of a sequent applied to some contexts is equivalent to the interpretation of the sequent applied 
--to the interpretation of the renamings applied to each of the contexts--

--Variables and Covariables--
%<*ren-lemma-var-ty*>
\begin{code}
ren-lemma-var : ∀ {Γ Γ′ A} (x : Γ ∋ A) (ρ : Γ ↝ Γ′) (γ : Γ′ ⱽˣ) 
  → ((ρ x ⱽⱽ) γ) ≡ ((x ⱽⱽ) (ren-int-cbv Γ Γ′ ρ γ))
\end{code}
%</ren-lemma-var-ty>
%<*ren-lemma-var>
\begin{code}
ren-lemma-var `Z ρ γ = refl
ren-lemma-var (`S x) ρ γ = ren-lemma-var x (ren-skip ρ) γ
\end{code}
%</ren-lemma-var>

%<*ren-lemma-covar-ty>
\begin{code}
ren-lemma-covar : ∀ {Θ Θ′ A} (α : Θ ∋ A) (ρ : Θ ↝ Θ′) (θ : `¬ˣ Θ′ ⱽˣ) (k : A ⱽᵀ)
  → (Γ∋A⇒¬Γ∋¬A (ρ α) ⱽⱽ) θ k ≡ (Γ∋A⇒¬Γ∋¬A α ⱽⱽ) (neg-ren-int-cbv Θ Θ′ ρ θ) k
\end{code}
%</ren-lemma-covar-ty>
\begin{code}
ren-lemma-covar `Z ρ θ k = refl
ren-lemma-covar (`S α) ρ θ k = ren-lemma-covar α (ren-skip ρ) θ k
\end{code}

--Sequents--
%<*ren-lemma-ty>
\begin{code}
ren-lemma-term : ∀ {Γ Γ′ Θ Θ′ A} 
  (M : Γ ⟶ Θ ∣ A) (s : Γ ↝ Γ′) (t : Θ ↝ Θ′) 
  (γ : Γ′ ⱽˣ) (θ : `¬ˣ Θ′ ⱽˣ) (k : ((`¬ A) ⱽᵀ))
  → (rename-term s t M ⱽᴸ) ⟨ γ , θ ⟩ k ≡ (M ⱽᴸ) ⟨ ren-int-cbv Γ Γ′ s γ , neg-ren-int-cbv Θ Θ′ t θ ⟩ k 

ren-lemma-termvalue : ∀ {Γ Γ′ Θ Θ′ A} 
  (V : TermValue Γ Θ A) (s : Γ ↝ Γ′) (t : Θ ↝ Θ′) (γ : Γ′ ⱽˣ) (θ : `¬ˣ Θ′ ⱽˣ)
  → (⟨ rename-term s t (proj₁ V) , value-rename s t (proj₂ V) ⟩ ⱽᴸⱽ) ⟨ γ , θ ⟩ 
    ≡ (V ⱽᴸⱽ) ⟨ ren-int-cbv Γ Γ′ s γ , neg-ren-int-cbv Θ Θ′ t θ ⟩

ren-lemma-coterm : ∀ {Γ Γ′ Θ Θ′ A} 
  (K : A ∣ Γ ⟶ Θ) (s : Γ ↝ Γ′) (t : Θ ↝ Θ′) (γ : Γ′ ⱽˣ) (θ : `¬ˣ Θ′ ⱽˣ) (k : A ⱽᵀ)
  → (rename-coterm s t K ⱽᴿ) ⟨ γ , θ ⟩ k ≡ (K ⱽᴿ) ⟨ ren-int-cbv Γ Γ′ s γ , neg-ren-int-cbv Θ Θ′ t θ ⟩ k 

ren-lemma-statement : ∀ {Γ Γ′ Θ Θ′} (S : Γ ↦ Θ) (s : Γ ↝ Γ′) (t : Θ ↝ Θ′) (γ : Γ′ ⱽˣ) (θ : `¬ˣ Θ′ ⱽˣ)
  → (rename-statement s t S ⱽˢ) ⟨ γ , θ ⟩ ≡ (S ⱽˢ) ⟨ ren-int-cbv Γ Γ′ s γ , neg-ren-int-cbv Θ Θ′ t θ ⟩
\end{code}
%</ren-lemma-ty>

%<*ren-lemma-vari>
\begin{code}
ren-lemma-term (` x) s t γ θ k = cong k (ren-lemma-var x s γ)
\end{code}
%</ren-lemma-vari>
\begin{code}
ren-lemma-term {Γ}{Γ′}{Θ}{Θ′} `⟨ M , N ⟩ s t γ θ k = 
  cong₂ (λ -₁ -₂ → -₁ (λ x → -₂ (λ y → k ⟨ x , y ⟩))) 
  (ext λ x → ren-lemma-term M s t γ θ x) 
  (ext (λ x → ren-lemma-term N s t γ θ x))
ren-lemma-term inl⟨ M ⟩ s t γ θ k = ren-lemma-term M s t γ θ λ x → k (inj₁ x)
ren-lemma-term inr⟨ M ⟩ s t γ θ k = ren-lemma-term M s t γ θ λ x → k (inj₂ x)
ren-lemma-term not[ K ] s t γ θ k = cong k (ext (λ x → ren-lemma-coterm K s t γ θ x))
\end{code}
%<*ren-lemma-covarabs>
\begin{code}
ren-lemma-term {Γ}{Γ′}{Θ}{Θ′}{A} (μθ S) s t γ θ k =
  begin
    (rename-statement s (rename-lift t) S ⱽˢ) ⟨ γ , ⟨ θ , k ⟩ ⟩
  ≡⟨ ren-lemma-statement S s (rename-lift t) γ ⟨ θ , k ⟩ ⟩
    (S ⱽˢ) ⟨ ren-int-cbv Γ Γ′ s γ , ⟨ neg-ren-int-cbv Θ (Θ′ , A) (rename-weaken t) ⟨ θ , k ⟩ , k ⟩ ⟩
  ≡⟨ cong (λ - → (S ⱽˢ) ⟨ ren-int-cbv Γ Γ′ s γ , ⟨ - , k ⟩ ⟩) (weaken-neg-ren-int-cbv-lemma t θ k) ⟩
    (S ⱽˢ) ⟨ ren-int-cbv Γ Γ′ s γ , ⟨ neg-ren-int-cbv Θ Θ′ t θ , k ⟩ ⟩ 
  ∎
\end{code}
%</ren-lemma-covarabs>

%<*ren-lemma-varval>
\begin{code}
ren-lemma-termvalue ⟨ ` x , V-var ⟩ s t γ θ = ren-lemma-var x s γ
\end{code}
%</ren-lemma-varval>
\begin{code}
ren-lemma-termvalue ⟨ `⟨ V , W ⟩ , V-prod v w ⟩ s t γ θ = 
  cong₂ ⟨_,_⟩ 
    (ren-lemma-termvalue ⟨ V , v ⟩ s t γ θ) 
    (ren-lemma-termvalue ⟨ W , w ⟩ s t γ θ)
ren-lemma-termvalue ⟨ inl⟨ V ⟩ , V-inl v ⟩ s t γ θ = cong inj₁ (ren-lemma-termvalue ⟨ V , v ⟩ s t γ θ)
ren-lemma-termvalue ⟨ inr⟨ V ⟩ , V-inr v ⟩ s t γ θ = cong inj₂ (ren-lemma-termvalue ⟨ V , v ⟩ s t γ θ)
ren-lemma-termvalue ⟨ not[ K ] , V-not ⟩ s t γ θ = ext (λ x → ren-lemma-coterm K s t γ θ x)
\end{code}
%<*ren-lemma-covari>
\begin{code}
ren-lemma-coterm (` α) s t γ θ k = ren-lemma-covar α t θ k
\end{code}
%</ren-lemma-covari>
\begin{code}
ren-lemma-coterm fst[ K ] s t γ θ k = 
  cong (λ - → - k) (ext (λ x → ren-lemma-coterm K s t γ θ (proj₁ x)))
ren-lemma-coterm snd[ K ] s t γ θ k = 
  cong (λ - → - k) (ext (λ x → ren-lemma-coterm K s t γ θ (proj₂ x)))
ren-lemma-coterm {Γ}{Γ′}{Θ}{Θ′}{A} `[ K , L ] s t γ θ k = 
  cong (λ - → - k) 
    {(rename-coterm s t `[ K , L ] ⱽᴿ) ⟨ γ , θ ⟩ }
    {(`[ K , L ] ⱽᴿ) ⟨ ren-int-cbv Γ Γ′ s γ , neg-ren-int-cbv Θ Θ′ t θ ⟩} 
    (ext (λ{(inj₁ x) → ren-lemma-coterm K s t γ θ x ; (inj₂ y) → ren-lemma-coterm L s t γ θ y}))
ren-lemma-coterm not⟨ M ⟩ s t γ θ k = ren-lemma-term M s t γ θ k
\end{code}
%<*ren-lemma-varabs>
\begin{code}
ren-lemma-coterm {Γ}{Γ′}{Θ}{Θ′}{A} (μγ S) s t γ θ k = 
  begin
    (rename-coterm s t (μγ S) ⱽᴿ) ⟨ γ , θ ⟩ k
  ≡⟨⟩ 
    (rename-statement (rename-lift s) t S ⱽˢ) ⟨ ⟨ γ , k ⟩ , θ ⟩
  ≡⟨ ren-lemma-statement S (rename-lift s) t ⟨ γ , k ⟩ θ ⟩
    (S ⱽˢ) ⟨ ⟨ ren-int-cbv Γ (Γ′ , A) (rename-weaken s) ⟨ γ , k ⟩ , k ⟩ , neg-ren-int-cbv Θ Θ′ t θ ⟩
  ≡⟨ cong (λ - → (S ⱽˢ) ⟨ ⟨ - , k ⟩ , neg-ren-int-cbv Θ Θ′ t θ ⟩) (weaken-ren-int-cbv-lemma s γ k) ⟩
    (S ⱽˢ) ⟨ ⟨ ren-int-cbv Γ Γ′ s γ , k ⟩ , neg-ren-int-cbv Θ Θ′ t θ ⟩
  ∎ 
\end{code}
%</ren-lemma-varabs>
\begin{code}
ren-lemma-statement {Γ} {Γ′} {Θ} {Θ′} (M ● K) s t γ θ = 
  cong₂ (λ -₁ -₂ → -₁ -₂) 
  (ext (λ x → ren-lemma-term M s t γ θ x)) 
  (ext (λ x → ren-lemma-coterm K s t γ θ x))
\end{code}

--Lemmas for proving the Substitution Lemma--

--TermValues--
%<*weaken-termval-ty>
\begin{code}
weaken-termvalue-sub-int-lemma : ∀ {Γ Γ′ Θ A} (σ : Γ –[ (λ Γ A → TermValue Γ Θ A) ]→ Γ′) γ θ k 
  → termvalue-sub-int Γ (Γ′ , A) Θ (sub-weaken (TermSubstKit.kit TVK) σ) θ ⟨ γ , k ⟩ 
    ≡ termvalue-sub-int Γ Γ′ Θ σ θ γ
\end{code}
%</weaken-termval-ty>
%<*weaken-termval>
\begin{code}
weaken-termvalue-sub-int-lemma {∅} σ γ θ k = refl
weaken-termvalue-sub-int-lemma {Γ , A} {Γ′} {Θ} σ γ θ k = cong₂ ⟨_,_⟩ 
  (weaken-termvalue-sub-int-lemma (sub-skip (λ Γ A → TermValue Γ Θ A) σ) γ θ k) 
  (trans (ren-lemma-termvalue (σ `Z) (rename-weaken id-var) id-var ⟨ γ , k ⟩ θ) 
         (cong₂ (λ -₁ -₂ → (σ `Z ⱽᴸⱽ) ⟨ -₁ , -₂ ⟩) 
           (trans (weaken-ren-int-cbv-lemma id-var γ k) (id-ren γ)) (id-neg-ren θ)))
\end{code}
%</weaken-termval>

%<*fmap-termval>
\begin{code}
fmap-termvalue-sub-int-lemma : ∀ {Γ Γ′ Θ A} (σ : Γ –[(λ Γ A → TermValue Γ Θ A)]→ Γ′) γ θ k
  → termvalue-sub-int Γ Γ′ (Θ , A) 
    (fmap {λ Γ B → TermValue Γ Θ B} {λ Γ B → TermValue Γ (Θ , A) B} wkΘⱽ σ) 
    ⟨ θ , k ⟩ γ 
    ≡ termvalue-sub-int Γ Γ′ Θ σ θ γ
\end{code}
%</fmap-termval>
\begin{code}
fmap-termvalue-sub-int-lemma {∅} σ γ θ k = refl
fmap-termvalue-sub-int-lemma {Γ , x}{Γ′}{Θ} σ γ θ k = cong₂ ⟨_,_⟩ 
  (fmap-termvalue-sub-int-lemma (sub-skip (λ Γ A → TermValue Γ Θ A) σ) γ θ k) 
  (trans (ren-lemma-termvalue (σ `Z) id-var (rename-weaken id-var) γ ⟨ θ , k ⟩) 
         (cong₂ (λ -₁ -₂ → (σ `Z ⱽᴸⱽ) ⟨ -₁ , -₂ ⟩) 
           (id-ren γ) (trans (weaken-neg-ren-int-cbv-lemma id-var θ k) (id-neg-ren θ))))
\end{code}
%<*id-termval>
\begin{code}
id-termvalue-sub : ∀ Γ Θ γ θ → termvalue-sub-int Γ Γ Θ id-termvalue θ γ ≡ γ
\end{code}
%</id-termval>
\begin{code}
id-termvalue-sub ∅ Θ γ θ = refl
id-termvalue-sub (Γ , A) Θ ⟨ γ , k ⟩ θ = cong (λ - → ⟨ - , k ⟩) 
  (trans (weaken-termvalue-sub-int-lemma id-termvalue γ θ k) (id-termvalue-sub Γ Θ γ θ))
\end{code}
--Coterms--
%<*weaken-coterm>
\begin{code}
weaken-coterm-sub-int-lemma : ∀ {Γ Θ Θ′ A} (σ : Θ –[ (λ Θ A → A ∣ Γ ⟶ Θ) ]→ Θ′) γ θ k
  → coterm-sub-int Γ Θ (Θ′ , A) (sub-weaken (CotermSubstKit.kit CK) σ) γ ⟨ θ , k ⟩ 
    ≡ coterm-sub-int Γ Θ Θ′ σ γ θ
\end{code}
%</weaken-coterm>
\begin{code}
weaken-coterm-sub-int-lemma {Γ}{∅} σ γ θ k = refl
weaken-coterm-sub-int-lemma {Γ}{Θ , A}{Θ′} σ γ θ k = cong₂ ⟨_,_⟩ 
  (weaken-coterm-sub-int-lemma (sub-skip (λ Θ A → A ∣ Γ ⟶ Θ) σ) γ θ k) 
  (ext (λ x → 
    trans (ren-lemma-coterm (σ `Z) id-var (rename-weaken id-var) γ ⟨ θ , k ⟩ x) 
          (cong₂ (λ -₁ -₂ → (σ `Z ⱽᴿ) ⟨ -₁ , -₂ ⟩ x) 
            (id-ren γ) (trans (weaken-neg-ren-int-cbv-lemma id-var θ k) (id-neg-ren θ))))) 
\end{code}

%<*fmap-coterm>
\begin{code}
fmap-coterm-sub-int-lemma : ∀ {Γ Θ Θ′ A} (σ : Θ –[ (λ Θ A → A ∣ Γ ⟶ Θ) ]→ Θ′) γ θ k
  → coterm-sub-int (Γ , A) Θ Θ′ 
    (fmap {λ Θ B → B ∣ Γ ⟶ Θ} {λ Θ B → B ∣ (Γ , A) ⟶ Θ} wkΓᶜ σ) 
    ⟨ γ , k ⟩ θ 
    ≡ coterm-sub-int Γ Θ Θ′ σ γ θ
\end{code}
%</fmap-coterm>
\begin{code}
fmap-coterm-sub-int-lemma {Γ}{∅}{Θ′} σ γ θ k = refl 
fmap-coterm-sub-int-lemma {Γ}{Θ , A}{Θ′} σ γ θ k = cong₂ ⟨_,_⟩ 
  (fmap-coterm-sub-int-lemma (sub-skip (λ Θ A → A ∣ Γ ⟶ Θ) σ) γ θ k) 
  (ext (λ x → 
    trans (ren-lemma-coterm (σ `Z) (rename-weaken id-var) id-var ⟨ γ , k ⟩ θ x) 
          (cong₂ (λ -₁ -₂ → (σ `Z ⱽᴿ) ⟨ -₁ , -₂ ⟩ x) 
            (trans (weaken-ren-int-cbv-lemma id-var γ k) (id-ren γ)) (id-neg-ren θ))))
\end{code}
%<*id-coterm>
\begin{code}
id-coterm-sub : ∀ Γ Θ γ θ → coterm-sub-int Γ Θ Θ id-coterm γ θ ≡ θ
\end{code}
%</id-coterm>
\begin{code}
id-coterm-sub Γ ∅ γ θ = refl
id-coterm-sub Γ (Θ , A) γ ⟨ θ , k ⟩ = cong (λ - → ⟨ - , k ⟩) 
  (trans (weaken-coterm-sub-int-lemma id-coterm γ θ k) (id-coterm-sub Γ Θ γ θ))
\end{code}
--The Substitution Lemma--
--The interpretation of substituted sequent applied to some contexts is equivalent to the interpretation of the sequent applied 
--to the interpretation of the substitutions applied to each of the contexts--

--Variables and Covariables--
%<*sub-lemma-var>
\begin{code}
sub-lemma-var : ∀ {Γ Γ′ Θ′ A} (s : Γ –[ (λ Γ A → TermValue Γ Θ′ A) ]→ Γ′) 
  (x : Γ ∋ A) (γ : Γ′ ⱽˣ) (θ : (`¬ˣ Θ′) ⱽˣ ) 
  → (proj₁ (s x) ⱽᴸ) ⟨ γ , θ ⟩ ≡ (λ k → k ((x ⱽⱽ) (termvalue-sub-int Γ Γ′ Θ′ s θ γ)))
sub-lemma-var s `Z γ θ = cps-value (proj₁ (s `Z)) (proj₂ (s `Z)) ⟨ γ , θ ⟩
sub-lemma-var {Γ}{Γ′}{Θ′} s (`S x) γ θ = 
  sub-lemma-var (sub-skip (λ Γ A → TermValue Γ Θ′ A) s) x γ θ
\end{code}
%</sub-lemma-var>

%<*sub-lemma-covar>
\begin{code}
sub-lemma-covar : ∀ {Γ′ Θ Θ′ A} (t : Θ –[ (λ Θ A → A ∣ Γ′ ⟶ Θ) ]→ Θ′) 
  (α : Θ ∋ A) (γ : Γ′ ⱽˣ) (θ : (`¬ˣ Θ′) ⱽˣ ) 
  → (t α ⱽᴿ) ⟨ γ , θ ⟩ ≡ (Γ∋A⇒¬Γ∋¬A α ⱽⱽ) (coterm-sub-int Γ′ Θ Θ′ t γ θ)
\end{code}
%</sub-lemma-covar>
\begin{code}
sub-lemma-covar t `Z γ θ = refl
sub-lemma-covar {Γ′} t (`S α) γ θ = sub-lemma-covar (sub-skip (λ Θ A → A ∣ Γ′ ⟶ Θ) t) α γ θ
\end{code}
--Sequents--

%<*sub-lemma-ty>
\begin{code}
sub-lemma-term : ∀ {Γ Γ′ Θ Θ′ A} 
  (s : Γ –[ (λ Γ A → TermValue Γ Θ′ A) ]→ Γ′) (t : Θ –[ (λ Θ A → A ∣ Γ′ ⟶ Θ) ]→ Θ′) 
  (M : Γ ⟶ Θ ∣ A) (γ : Γ′ ⱽˣ) (θ : (`¬ˣ Θ′) ⱽˣ ) 
  → ((sub-term TVK CK s t M) ⱽᴸ) ⟨ γ , θ ⟩ 
    ≡ (M ⱽᴸ) ⟨ termvalue-sub-int Γ Γ′ Θ′ s θ γ , coterm-sub-int Γ′ Θ Θ′ t γ θ ⟩

sub-lemma-coterm : ∀ {Γ Γ′ Θ Θ′ A} 
  (s : Γ –[ (λ Γ A → TermValue Γ Θ′ A) ]→ Γ′) (t : Θ –[ (λ Θ A → A ∣ Γ′ ⟶ Θ) ]→ Θ′) 
  (K : A ∣ Γ ⟶ Θ) (γ : Γ′ ⱽˣ) (θ : (`¬ˣ Θ′) ⱽˣ ) 
  → ((sub-coterm TVK CK s t K) ⱽᴿ) ⟨ γ , θ ⟩ 
    ≡ (K ⱽᴿ) ⟨ termvalue-sub-int Γ Γ′ Θ′ s θ γ , coterm-sub-int Γ′ Θ Θ′ t γ θ ⟩

sub-lemma-statement : ∀ {Γ Γ′ Θ Θ′} 
  (s : Γ –[ (λ Γ A → TermValue Γ Θ′ A) ]→ Γ′) (t : Θ –[ (λ Θ A → A ∣ Γ′ ⟶ Θ) ]→ Θ′) 
  (S : Γ ↦ Θ) (γ : Γ′ ⱽˣ) (θ : (`¬ˣ Θ′) ⱽˣ ) 
  → ((sub-statement TVK CK s t S) ⱽˢ) ⟨ γ , θ ⟩ 
    ≡ (S ⱽˢ) ⟨ termvalue-sub-int Γ Γ′ Θ′ s θ γ , coterm-sub-int Γ′ Θ Θ′ t γ θ ⟩
\end{code}
%</sub-lemma-ty>
\begin{code}
sub-lemma-term s t (` x) γ θ = sub-lemma-var s x γ θ
sub-lemma-term {Γ}{Γ′}{Θ}{Θ′} s t `⟨ M , N ⟩ γ θ = ext (λ k → 
  cong₂ (λ -₁ -₂ → -₁ (λ x → -₂ (λ y → k ⟨ x , y ⟩))) 
    (sub-lemma-term s t M γ θ) (sub-lemma-term s t N γ θ))
sub-lemma-term s t inl⟨ M ⟩ γ θ = ext (λ k → 
  cong (λ - → - (λ x → k (inj₁ x))) (sub-lemma-term s t M γ θ))
sub-lemma-term s t inr⟨ M ⟩ γ θ = ext (λ k → 
  cong (λ - → - (λ x → k (inj₂ x))) (sub-lemma-term s t M γ θ))
sub-lemma-term s t not[ K ] γ θ = ext (λ k → cong k (sub-lemma-coterm s t K γ θ))
sub-lemma-term {Γ}{Γ′}{Θ}{Θ′}{A} s t (μθ S) γ θ = ext (λ k → 
  begin
    (sub-statement TVK CK 
      (fmap {λ Γ B → TermValue Γ Θ′ B} {λ Γ B → TermValue Γ (Θ′ , A) B} wkΘⱽ s)
      (sub-lift (CotermSubstKit.kit CK) t)
      S ⱽˢ) ⟨ γ , ⟨ θ , k ⟩ ⟩
  ≡⟨ 
    sub-lemma-statement 
      (fmap {λ Γ B → TermValue Γ Θ′ B} {λ Γ B → TermValue Γ (Θ′ , A) B} wkΘⱽ s) 
      (sub-lift (CotermSubstKit.kit CK) t) 
      S γ ⟨ θ , k ⟩ 
    ⟩
    (S ⱽˢ) 
      ⟨ termvalue-sub-int Γ Γ′ (Θ′ , A) 
      (fmap {λ Γ B → TermValue Γ Θ′ B} {λ Γ B → TermValue Γ (Θ′ , A) B} wkΘⱽ s) 
      ⟨ θ , k ⟩ γ , 
      ⟨ coterm-sub-int Γ′ Θ (Θ′ , A) (sub-weaken (CotermSubstKit.kit CK) t) γ ⟨ θ , k ⟩ , k ⟩ ⟩
  ≡⟨ 
    cong (λ - → (S ⱽˢ) 
    ⟨ termvalue-sub-int Γ Γ′ (Θ′ , A) 
    (fmap {λ Γ B → TermValue Γ Θ′ B} {λ Γ B → TermValue Γ (Θ′ , A) B} wkΘⱽ s) 
    ⟨ θ , k ⟩ γ , ⟨ - , k ⟩ ⟩) 
      (weaken-coterm-sub-int-lemma t γ θ k) 
    ⟩
    (S ⱽˢ) 
    ⟨ termvalue-sub-int Γ Γ′ (Θ′ , A) 
      (fmap {λ Γ B → TermValue Γ Θ′ B} {λ Γ B → TermValue Γ (Θ′ , A) B} wkΘⱽ s)
      ⟨ θ , k ⟩ γ 
    , ⟨ coterm-sub-int Γ′ Θ Θ′ t γ θ , k ⟩ ⟩ 
  ≡⟨ 
    cong (λ - → (S ⱽˢ) ⟨ - , ⟨ coterm-sub-int Γ′ Θ Θ′ t γ θ , k ⟩ ⟩) 
      (fmap-termvalue-sub-int-lemma s γ θ k) 
    ⟩
    (S ⱽˢ) ⟨ termvalue-sub-int Γ Γ′ Θ′ s θ γ , ⟨ coterm-sub-int Γ′ Θ Θ′ t γ θ , k ⟩ ⟩
  ∎)


sub-lemma-coterm s t (` α) γ θ = sub-lemma-covar t α γ θ
sub-lemma-coterm s t fst[ K ] γ θ = cong (λ - → λ { ⟨ x , _ ⟩ → - x }) (sub-lemma-coterm s t K γ θ)
sub-lemma-coterm s t snd[ K ] γ θ = cong (λ - → λ { ⟨ _ , y ⟩ → - y }) (sub-lemma-coterm s t K γ θ)
sub-lemma-coterm {Γ} {Γ′} {Θ} {Θ′} {A `+ B} s t `[ K , L ] γ θ = 
  ext (λ{ (inj₁ x) → cong (λ - → - x) (sub-lemma-coterm s t K γ θ) 
        ; (inj₂ y) → cong (λ - → - y) (sub-lemma-coterm s t L γ θ)})
sub-lemma-coterm s t not⟨ M ⟩ γ θ = sub-lemma-term s t M γ θ
\end{code}
%<*sub-lemma-varabs>
\begin{code}
sub-lemma-coterm {Γ}{Γ′}{Θ}{Θ′}{A} s t (μγ S) γ θ = ext (λ x → 
  begin 
    (sub-statement TVK CK
      (sub-lift (TermSubstKit.kit TVK) s)
      (fmap {λ Θ B → B ∣ Γ′ ⟶ Θ} {λ Θ B → B ∣ Γ′ , A ⟶ Θ} wkΓᶜ t)
      S ⱽˢ) ⟨ ⟨ γ , x ⟩ , θ ⟩
  ≡⟨ 
    sub-lemma-statement 
      (sub-lift (TermSubstKit.kit TVK) s) 
      (fmap {λ Θ B → B ∣ Γ′ ⟶ Θ} {λ Θ B → B ∣ Γ′ , A ⟶ Θ} wkΓᶜ t) 
      S ⟨ γ , x ⟩ θ 
    ⟩
    (S ⱽˢ)
      ⟨ ⟨ termvalue-sub-int Γ (Γ′ , A) Θ′ (sub-weaken (TermSubstKit.kit TVK) s) θ ⟨ γ , x ⟩ , x ⟩ 
      , coterm-sub-int (Γ′ , A) Θ Θ′ 
        (fmap {λ Θ B → B ∣ Γ′ ⟶ Θ} {λ Θ B → B ∣ Γ′ , A ⟶ Θ} wkΓᶜ t) ⟨ γ , x ⟩ θ ⟩
  ≡⟨ 
    cong (λ - → (S ⱽˢ) ⟨ ⟨ - , x ⟩ , coterm-sub-int (Γ′ , A) Θ Θ′
    (fmap {λ Θ B → B ∣ Γ′ ⟶ Θ} {λ Θ B → B ∣ Γ′ , A ⟶ Θ} wkΓᶜ t) ⟨ γ , x ⟩ θ ⟩) 
      (weaken-termvalue-sub-int-lemma s γ θ x) 
    ⟩
    (S ⱽˢ)
      ⟨ ⟨ termvalue-sub-int Γ Γ′ Θ′ s θ γ , x ⟩ 
      , coterm-sub-int (Γ′ , A) Θ Θ′ 
        (fmap {λ Θ B → B ∣ Γ′ ⟶ Θ} {λ Θ B → B ∣ Γ′ , A ⟶ Θ} wkΓᶜ t) 
        ⟨ γ , x ⟩ θ ⟩
  ≡⟨ 
    cong (λ - → (S ⱽˢ) ⟨ ⟨ termvalue-sub-int Γ Γ′ Θ′ s θ γ , x ⟩ , - ⟩) 
      (fmap-coterm-sub-int-lemma t γ θ x) 
    ⟩
   (S ⱽˢ) ⟨ ⟨ termvalue-sub-int Γ Γ′ Θ′ s θ γ , x ⟩ , coterm-sub-int Γ′ Θ Θ′ t γ θ ⟩
  ∎)
\end{code}
%</sub-lemma-varabs>

\begin{code}
sub-lemma-statement {Γ} {Γ′} {Θ} {Θ′} s t (M ● K) γ θ = 
  begin
    (sub-term TVK CK s t M ⱽᴸ) ⟨ γ , θ ⟩ 
    ((sub-coterm TVK CK s t K ⱽᴿ) ⟨ γ , θ ⟩)
  ≡⟨ 
    cong (λ - → - ((sub-coterm TVK CK s t K ⱽᴿ) ⟨ γ , θ ⟩)) 
      (sub-lemma-term s t M γ θ) 
    ⟩
    (M ⱽᴸ) ⟨ termvalue-sub-int Γ Γ′ Θ′ s θ γ , coterm-sub-int Γ′ Θ Θ′ t γ θ ⟩ 
    ((sub-coterm TVK CK s t K ⱽᴿ) ⟨ γ , θ ⟩)
  ≡⟨ 
    cong (λ - → (M ⱽᴸ) ⟨ termvalue-sub-int Γ Γ′ Θ′ s θ γ , coterm-sub-int Γ′ Θ Θ′ t γ θ ⟩ -) 
      (sub-lemma-coterm s t K γ θ)
    ⟩
    (M ⱽᴸ) ⟨ termvalue-sub-int Γ Γ′ Θ′ s θ γ , coterm-sub-int Γ′ Θ Θ′ t γ θ ⟩ 
    ((K ⱽᴿ) ⟨ termvalue-sub-int Γ Γ′ Θ′ s θ γ , coterm-sub-int Γ′ Θ Θ′ t γ θ ⟩)
  ∎
\end{code}


--Lemma for Soundness of the CPS Transformation--
--If a given Sequent steps to another different Sequent then the CPS Transformation of those two Sequents are equivalent

--Statements
%<*sound-lemma-ty>
\begin{code}
S⟶ⱽT⇒Sⱽ≡Tⱽ : ∀ {Γ Θ} (S T : Γ ↦ Θ) (c : (Γ ᵒˣ) ᴺˣ × `¬ˣ (Θ ᵒˣ) ᴺˣ) 
  → S ˢ⟶ⱽ T → (S ⱽˢ) c ≡ (T ⱽˢ) c
\end{code}
%</sound-lemma-ty>
\begin{code}
S⟶ⱽT⇒Sⱽ≡Tⱽ (`⟨ V , W ⟩ ● fst[ K ]) (V ● K) c (β×₁ v w) = 
  cong ((V ⱽᴸ) c) (ext (λ x → cong (λ - → - (λ y → (K ⱽᴿ) c x)) (cps-value W w c)))
S⟶ⱽT⇒Sⱽ≡Tⱽ (`⟨ V , W ⟩ ● snd[ L ]) (W ● L) c (β×₂ v w) = 
  cong (λ - → - (λ x → (W ⱽᴸ) c (λ y → (L ⱽᴿ) c y))) (cps-value V v c)
S⟶ⱽT⇒Sⱽ≡Tⱽ (inl⟨ V ⟩ ● `[ K , L ]) (V ● K) c (β+₁ v) = refl
S⟶ⱽT⇒Sⱽ≡Tⱽ (inr⟨ W ⟩ ● `[ K , L ]) (W ● L) c (β+₂ w) = refl
S⟶ⱽT⇒Sⱽ≡Tⱽ (not[ K ] ● not⟨ M ⟩) (M ● K) c (β¬) = refl
\end{code}
%<*sound-lemma-termval>
\begin{code}
S⟶ⱽT⇒Sⱽ≡Tⱽ {Γ} {Θ} (V ● μγ {Γ}{Θ}{A} S) .(S ⱽ⟨ ⟨ V , v ⟩ /⟩ˢ) ⟨ γ , θ ⟩ (βL v) = sym (
  begin
    ((S ⱽ⟨ ⟨ V , v ⟩ /⟩ˢ) ⱽˢ) ⟨ γ , θ ⟩
  ≡⟨⟩
    (sub-statement TVK CK 
      (add (λ Γ A → TermValue Γ Θ A) ⟨ V , v ⟩ id-termvalue) id-coterm S ⱽˢ) 
      ⟨ γ , θ ⟩
  ≡⟨ sub-lemma-statement (add (λ Γ A → TermValue Γ Θ A) ⟨ V , v ⟩ id-termvalue) id-coterm S γ θ ⟩
    (S ⱽˢ) 
      ⟨ termvalue-sub-int (Γ , A) Γ Θ (add (λ Γ A → TermValue Γ Θ A) ⟨ V , v ⟩ id-termvalue) θ γ 
      , coterm-sub-int Γ Θ Θ id-coterm γ θ ⟩
  ≡⟨⟩
    (S ⱽˢ)
      ⟨ ⟨ termvalue-sub-int Γ Γ Θ id-termvalue θ γ , (⟨ V , v ⟩ ⱽᴸⱽ) ⟨ γ , θ ⟩ ⟩
      , coterm-sub-int Γ Θ Θ id-coterm γ θ ⟩
  ≡⟨ 
    cong (λ - → (S ⱽˢ) 
    ⟨ ⟨ termvalue-sub-int Γ Γ Θ id-termvalue θ γ , (⟨ V , v ⟩ ⱽᴸⱽ) ⟨ γ , θ ⟩ ⟩ , - ⟩) 
    (id-coterm-sub Γ Θ γ θ) 
    ⟩
    (S ⱽˢ) ⟨ ⟨ termvalue-sub-int Γ Γ Θ id-termvalue θ γ , (⟨ V , v ⟩ ⱽᴸⱽ) ⟨ γ , θ ⟩ ⟩ , θ ⟩
  ≡⟨ cong (λ - → (S ⱽˢ) ⟨ ⟨ - , (⟨ V , v ⟩ ⱽᴸⱽ) ⟨ γ , θ ⟩ ⟩ , θ ⟩) (id-termvalue-sub Γ Θ γ θ) ⟩
    (S ⱽˢ) ⟨ ⟨ γ , (⟨ V , v ⟩ ⱽᴸⱽ) ⟨ γ , θ ⟩ ⟩ , θ ⟩
  ≡⟨ sym (cong (λ - → - (λ x → (S ⱽˢ) ⟨ ⟨ γ , x ⟩ , θ ⟩)) (cps-value V v ⟨ γ , θ ⟩)) ⟩
    (V ⱽᴸ) ⟨ γ , θ ⟩ (λ x → (S ⱽˢ) ⟨ ⟨ γ , x ⟩ , θ ⟩)
  ∎)
\end{code}
%</sound-lemma-termval>
\begin{code}
S⟶ⱽT⇒Sⱽ≡Tⱽ {Γ}{Θ}(μθ {Γ}{Θ}{A} S ● K) .(S [ K /]ˢ) ⟨ γ , θ ⟩ (βR) = sym (
  begin
    ((S [ K /]ˢ) ⱽˢ) ⟨ γ , θ ⟩
  ≡⟨⟩
    (sub-statement TVK CK id-termvalue 
      (add (λ Θ A → A ∣ Γ ⟶ Θ) K id-coterm) S ⱽˢ) 
      ⟨ γ , θ ⟩
  ≡⟨ sub-lemma-statement id-termvalue ((add (λ Θ A → A ∣ Γ ⟶ Θ) K id-coterm)) S γ θ ⟩
    (S ⱽˢ) 
      ⟨ (termvalue-sub-int Γ Γ Θ id-termvalue θ γ) 
      , (coterm-sub-int Γ (Θ , A) Θ (add (λ Θ A → A ∣ Γ ⟶ Θ) K id-coterm) γ θ) ⟩
  ≡⟨ 
    cong (λ - → (S ⱽˢ) 
    ⟨ - , coterm-sub-int Γ (Θ , A) Θ (add (λ Θ A → A ∣ Γ ⟶ Θ) K id-coterm) γ θ ⟩) 
      (id-termvalue-sub Γ Θ γ θ) 
    ⟩
    (S ⱽˢ) ⟨ γ , (coterm-sub-int Γ (Θ , A) Θ (add (λ Θ A → A ∣ Γ ⟶ Θ) K id-coterm) γ θ) ⟩
  ≡⟨ cong (λ - → (S ⱽˢ) ⟨ γ , ⟨ - , (K ⱽᴿ) ⟨ γ , θ ⟩ ⟩ ⟩) (id-coterm-sub Γ Θ γ θ) ⟩
    (S ⱽˢ) ⟨ γ , ⟨ θ , (K ⱽᴿ) ⟨ γ , θ ⟩ ⟩ ⟩
  ∎)
\end{code}

--Soundness of the CPS Transformation--
--If a given sequent eventually reduces to another sequent then the CPS Transformations of those two sequents are equivalent

%<*soundty>
\begin{code}
S—↠ⱽT⇒Sⱽ≡Tⱽ : ∀ {Γ Θ} (S T : Γ ↦ Θ) (c : (Γ ᵒˣ) ᴺˣ × `¬ˣ (Θ ᵒˣ) ᴺˣ) 
  → S ˢ—↠ⱽ T → (S ⱽˢ) c ≡ (T ⱽˢ) c
\end{code}
%</soundty>
%<*sound>
\begin{code}
S—↠ⱽT⇒Sⱽ≡Tⱽ S .S c (.S ∎ˢⱽ) = refl
S—↠ⱽT⇒Sⱽ≡Tⱽ S T c ( _ˢ⟶ⱽ⟨_⟩_ .S {S′} .{T} S⟶S′ S′↠T) = 
  trans (S⟶ⱽT⇒Sⱽ≡Tⱽ S S′ c S⟶S′) (S—↠ⱽT⇒Sⱽ≡Tⱽ S′ T c S′↠T)
\end{code}
%</sound>\end{code}
