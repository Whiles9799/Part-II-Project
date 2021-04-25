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
  → ren-int-cbv Γ (Γ′ , A) (ren-weaken ρ) ⟨ γ , k ⟩ ≡ ren-int-cbv Γ Γ′ ρ γ
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
  → neg-ren-int-cbv Θ (Θ′ , A) (ren-weaken ρ) ⟨ θ , k ⟩ ≡ neg-ren-int-cbv Θ Θ′ ρ θ
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
ren-lemma-T : ∀ {Γ Γ′ Θ Θ′ A} 
  (M : Γ ⟶ Θ ∣ A) (s : Γ ↝ Γ′) (t : Θ ↝ Θ′) 
  (γ : Γ′ ⱽˣ) (θ : `¬ˣ Θ′ ⱽˣ) (k : ((`¬ A) ⱽᵀ))
  → (ren-T s t M ⱽᴸ) ⟨ γ , θ ⟩ k ≡ (M ⱽᴸ) ⟨ ren-int-cbv Γ Γ′ s γ , neg-ren-int-cbv Θ Θ′ t θ ⟩ k 

ren-lemma-TV : ∀ {Γ Γ′ Θ Θ′ A} 
  (V : TermValue Γ Θ A) (s : Γ ↝ Γ′) (t : Θ ↝ Θ′) (γ : Γ′ ⱽˣ) (θ : `¬ˣ Θ′ ⱽˣ)
  → (⟨ ren-T s t (proj₁ V) , V-ren s t (proj₂ V) ⟩ ⱽᴸⱽ) ⟨ γ , θ ⟩ 
    ≡ (V ⱽᴸⱽ) ⟨ ren-int-cbv Γ Γ′ s γ , neg-ren-int-cbv Θ Θ′ t θ ⟩

ren-lemma-C : ∀ {Γ Γ′ Θ Θ′ A} 
  (K : A ∣ Γ ⟶ Θ) (s : Γ ↝ Γ′) (t : Θ ↝ Θ′) (γ : Γ′ ⱽˣ) (θ : `¬ˣ Θ′ ⱽˣ) (k : A ⱽᵀ)
  → (ren-C s t K ⱽᴿ) ⟨ γ , θ ⟩ k ≡ (K ⱽᴿ) ⟨ ren-int-cbv Γ Γ′ s γ , neg-ren-int-cbv Θ Θ′ t θ ⟩ k 

ren-lemma-S : ∀ {Γ Γ′ Θ Θ′} (S : Γ ↦ Θ) (s : Γ ↝ Γ′) (t : Θ ↝ Θ′) (γ : Γ′ ⱽˣ) (θ : `¬ˣ Θ′ ⱽˣ)
  → (ren-S s t S ⱽˢ) ⟨ γ , θ ⟩ ≡ (S ⱽˢ) ⟨ ren-int-cbv Γ Γ′ s γ , neg-ren-int-cbv Θ Θ′ t θ ⟩
\end{code}
%</ren-lemma-ty>

%<*ren-lemma-vari>
\begin{code}
ren-lemma-T (` x) s t γ θ k = cong k (ren-lemma-var x s γ)
\end{code}
%</ren-lemma-vari>
\begin{code}
ren-lemma-T {Γ}{Γ′}{Θ}{Θ′} `⟨ M , N ⟩ s t γ θ k = 
  cong₂ (λ -₁ -₂ → -₁ (λ x → -₂ (λ y → k ⟨ x , y ⟩))) 
  (ext λ x → ren-lemma-T M s t γ θ x) 
  (ext (λ x → ren-lemma-T N s t γ θ x))
ren-lemma-T inl⟨ M ⟩ s t γ θ k = ren-lemma-T M s t γ θ λ x → k (inj₁ x)
ren-lemma-T inr⟨ M ⟩ s t γ θ k = ren-lemma-T M s t γ θ λ x → k (inj₂ x)
ren-lemma-T not[ K ] s t γ θ k = cong k (ext (λ x → ren-lemma-C K s t γ θ x))
\end{code}
%<*ren-lemma-covarabs>
\begin{code}
ren-lemma-T {Γ}{Γ′}{Θ}{Θ′}{A} (μθ S) s t γ θ k =
  begin
    (ren-S s (ren-lift t) S ⱽˢ) ⟨ γ , ⟨ θ , k ⟩ ⟩
  ≡⟨ ren-lemma-S S s (ren-lift t) γ ⟨ θ , k ⟩ ⟩
    (S ⱽˢ) ⟨ ren-int-cbv Γ Γ′ s γ , ⟨ neg-ren-int-cbv Θ (Θ′ , A) (ren-weaken t) ⟨ θ , k ⟩ , k ⟩ ⟩
  ≡⟨ cong (λ - → (S ⱽˢ) ⟨ ren-int-cbv Γ Γ′ s γ , ⟨ - , k ⟩ ⟩) (weaken-neg-ren-int-cbv-lemma t θ k) ⟩
    (S ⱽˢ) ⟨ ren-int-cbv Γ Γ′ s γ , ⟨ neg-ren-int-cbv Θ Θ′ t θ , k ⟩ ⟩ 
  ∎
\end{code}
%</ren-lemma-covarabs>

%<*ren-lemma-varval>
\begin{code}
ren-lemma-TV ⟨ ` x , V-var ⟩ s t γ θ = ren-lemma-var x s γ
\end{code}
%</ren-lemma-varval>
\begin{code}
ren-lemma-TV ⟨ `⟨ V , W ⟩ , V-prod v w ⟩ s t γ θ = 
  cong₂ ⟨_,_⟩ 
    (ren-lemma-TV ⟨ V , v ⟩ s t γ θ) 
    (ren-lemma-TV ⟨ W , w ⟩ s t γ θ)
ren-lemma-TV ⟨ inl⟨ V ⟩ , V-inl v ⟩ s t γ θ = cong inj₁ (ren-lemma-TV ⟨ V , v ⟩ s t γ θ)
ren-lemma-TV ⟨ inr⟨ V ⟩ , V-inr v ⟩ s t γ θ = cong inj₂ (ren-lemma-TV ⟨ V , v ⟩ s t γ θ)
ren-lemma-TV ⟨ not[ K ] , V-not ⟩ s t γ θ = ext (λ x → ren-lemma-C K s t γ θ x)
\end{code}
%<*ren-lemma-covari>
\begin{code}
ren-lemma-C (` α) s t γ θ k = ren-lemma-covar α t θ k
\end{code}
%</ren-lemma-covari>
\begin{code}
ren-lemma-C fst[ K ] s t γ θ k = 
  cong (λ - → - k) (ext (λ x → ren-lemma-C K s t γ θ (proj₁ x)))
ren-lemma-C snd[ K ] s t γ θ k = 
  cong (λ - → - k) (ext (λ x → ren-lemma-C K s t γ θ (proj₂ x)))
ren-lemma-C {Γ}{Γ′}{Θ}{Θ′}{A} `[ K , L ] s t γ θ k = 
  cong (λ - → - k) 
    {(ren-C s t `[ K , L ] ⱽᴿ) ⟨ γ , θ ⟩ }
    {(`[ K , L ] ⱽᴿ) ⟨ ren-int-cbv Γ Γ′ s γ , neg-ren-int-cbv Θ Θ′ t θ ⟩} 
    (ext (λ{(inj₁ x) → ren-lemma-C K s t γ θ x ; (inj₂ y) → ren-lemma-C L s t γ θ y}))
ren-lemma-C not⟨ M ⟩ s t γ θ k = ren-lemma-T M s t γ θ k
\end{code}
%<*ren-lemma-varabs>
\begin{code}
ren-lemma-C {Γ}{Γ′}{Θ}{Θ′}{A} (μγ S) s t γ θ k = 
  begin
    (ren-C s t (μγ S) ⱽᴿ) ⟨ γ , θ ⟩ k
  ≡⟨⟩ 
    (ren-S (ren-lift s) t S ⱽˢ) ⟨ ⟨ γ , k ⟩ , θ ⟩
  ≡⟨ ren-lemma-S S (ren-lift s) t ⟨ γ , k ⟩ θ ⟩
    (S ⱽˢ) ⟨ ⟨ ren-int-cbv Γ (Γ′ , A) (ren-weaken s) ⟨ γ , k ⟩ , k ⟩ , neg-ren-int-cbv Θ Θ′ t θ ⟩
  ≡⟨ cong (λ - → (S ⱽˢ) ⟨ ⟨ - , k ⟩ , neg-ren-int-cbv Θ Θ′ t θ ⟩) (weaken-ren-int-cbv-lemma s γ k) ⟩
    (S ⱽˢ) ⟨ ⟨ ren-int-cbv Γ Γ′ s γ , k ⟩ , neg-ren-int-cbv Θ Θ′ t θ ⟩
  ∎ 
\end{code}
%</ren-lemma-varabs>
\begin{code}
ren-lemma-S {Γ} {Γ′} {Θ} {Θ′} (M ● K) s t γ θ = 
  cong₂ (λ -₁ -₂ → -₁ -₂) 
  (ext (λ x → ren-lemma-T M s t γ θ x)) 
  (ext (λ x → ren-lemma-C K s t γ θ x))
\end{code}

--Lemmas for proving the Substitution Lemma--

--TermValues--
%<*weaken-TV-ty>
\begin{code}
weaken-sub-TV-int-lemma : ∀ {Γ Γ′ Θ A} (σ : Γ –[ (Fix₂ TermValue Θ) ]→ Γ′) γ θ k 
  → sub-TV-int Γ (Γ′ , A) Θ (sub-weaken (TermKit.kit TVK) σ) θ ⟨ γ , k ⟩ 
    ≡ sub-TV-int Γ Γ′ Θ σ θ γ
\end{code}
%</weaken-TV-ty>
%<*weaken-TV>
\begin{code}
weaken-sub-TV-int-lemma {∅} σ γ θ k = refl
weaken-sub-TV-int-lemma {Γ , A} {Γ′} {Θ} σ γ θ k = cong₂ ⟨_,_⟩ 
  (weaken-sub-TV-int-lemma (sub-skip (Fix₂ TermValue Θ) σ) γ θ k) 
  (trans (ren-lemma-TV (σ `Z) (ren-weaken id-var) id-var ⟨ γ , k ⟩ θ) 
         (cong₂ (λ -₁ -₂ → (σ `Z ⱽᴸⱽ) ⟨ -₁ , -₂ ⟩) 
           (trans (weaken-ren-int-cbv-lemma id-var γ k) (id-ren γ)) (id-neg-ren θ)))
\end{code}
%</weaken-TV>

%<*fmap-TV>
\begin{code}
fmap-sub-TV-int-lemma : ∀ {Γ Γ′ Θ A} (σ : Γ –[(Fix₂ TermValue Θ)]→ Γ′) γ θ k
  → sub-TV-int Γ Γ′ (Θ , A) 
    (fmap-wkΘᵗⱽ Θ A σ) 
    ⟨ θ , k ⟩ γ 
    ≡ sub-TV-int Γ Γ′ Θ σ θ γ
\end{code}
%</fmap-TV>
\begin{code}
fmap-sub-TV-int-lemma {∅} σ γ θ k = refl
fmap-sub-TV-int-lemma {Γ , x}{Γ′}{Θ} σ γ θ k = cong₂ ⟨_,_⟩ 
  (fmap-sub-TV-int-lemma (sub-skip (Fix₂ TermValue Θ) σ) γ θ k) 
  (trans (ren-lemma-TV (σ `Z) id-var (ren-weaken id-var) γ ⟨ θ , k ⟩) 
         (cong₂ (λ -₁ -₂ → (σ `Z ⱽᴸⱽ) ⟨ -₁ , -₂ ⟩) 
           (id-ren γ) (trans (weaken-neg-ren-int-cbv-lemma id-var θ k) (id-neg-ren θ))))
\end{code}
%<*id-TV>
\begin{code}
id-sub-TV : ∀ Γ Θ γ θ → sub-TV-int Γ Γ Θ id-TV θ γ ≡ γ
\end{code}
%</id-TV>
\begin{code}
id-sub-TV ∅ Θ γ θ = refl
id-sub-TV (Γ , A) Θ ⟨ γ , k ⟩ θ = cong (λ - → ⟨ - , k ⟩) 
  (trans (weaken-sub-TV-int-lemma id-TV γ θ k) (id-sub-TV Γ Θ γ θ))
\end{code}
--Coterms--
%<*weaken-C>
\begin{code}
weaken-sub-C-int-lemma : ∀ {Γ Θ Θ′ A} (σ : Θ –[ (Fix₁ Coterm Γ) ]→ Θ′) γ θ k
  → sub-C-int Γ Θ (Θ′ , A) (sub-weaken (CotermKit.kit CK) σ) γ ⟨ θ , k ⟩ 
    ≡ sub-C-int Γ Θ Θ′ σ γ θ
\end{code}
%</weaken-C>
\begin{code}
weaken-sub-C-int-lemma {Γ}{∅} σ γ θ k = refl
weaken-sub-C-int-lemma {Γ}{Θ , A}{Θ′} σ γ θ k = cong₂ ⟨_,_⟩ 
  (weaken-sub-C-int-lemma (sub-skip (Fix₁ Coterm Γ) σ) γ θ k) 
  (ext (λ x → 
    trans (ren-lemma-C (σ `Z) id-var (ren-weaken id-var) γ ⟨ θ , k ⟩ x) 
          (cong₂ (λ -₁ -₂ → (σ `Z ⱽᴿ) ⟨ -₁ , -₂ ⟩ x) 
            (id-ren γ) (trans (weaken-neg-ren-int-cbv-lemma id-var θ k) (id-neg-ren θ))))) 
\end{code}

%<*fmap-C>
\begin{code}
fmap-sub-C-int-lemma : ∀ {Γ Θ Θ′ A} (σ : Θ –[ (Fix₁ Coterm Γ) ]→ Θ′) γ θ k
  → sub-C-int (Γ , A) Θ Θ′ 
    (fmap-wkΓᶜ Γ A σ) 
    ⟨ γ , k ⟩ θ 
    ≡ sub-C-int Γ Θ Θ′ σ γ θ
\end{code}
%</fmap-C>
\begin{code}
fmap-sub-C-int-lemma {Γ}{∅}{Θ′} σ γ θ k = refl 
fmap-sub-C-int-lemma {Γ}{Θ , A}{Θ′} σ γ θ k = cong₂ ⟨_,_⟩ 
  (fmap-sub-C-int-lemma (sub-skip (Fix₁ Coterm Γ) σ) γ θ k) 
  (ext (λ x → 
    trans (ren-lemma-C (σ `Z) (ren-weaken id-var) id-var ⟨ γ , k ⟩ θ x) 
          (cong₂ (λ -₁ -₂ → (σ `Z ⱽᴿ) ⟨ -₁ , -₂ ⟩ x) 
            (trans (weaken-ren-int-cbv-lemma id-var γ k) (id-ren γ)) (id-neg-ren θ))))
\end{code}
%<*id-C>
\begin{code}
id-sub-C : ∀ Γ Θ γ θ → sub-C-int Γ Θ Θ id-C γ θ ≡ θ
\end{code}
%</id-C>
\begin{code}
id-sub-C Γ ∅ γ θ = refl
id-sub-C Γ (Θ , A) γ ⟨ θ , k ⟩ = cong (λ - → ⟨ - , k ⟩) 
  (trans (weaken-sub-C-int-lemma id-C γ θ k) (id-sub-C Γ Θ γ θ))
\end{code}
--The Substitution Lemma--
--The interpretation of substituted sequent applied to some contexts is equivalent to the interpretation of the sequent applied 
--to the interpretation of the substitutions applied to each of the contexts--

--Variables and Covariables--
%<*sub-lemma-var>
\begin{code}
sub-lemma-var : ∀ {Γ Γ′ Θ′ A} (s : Γ –[ (Fix₂ TermValue Θ′) ]→ Γ′) 
  (x : Γ ∋ A) (γ : Γ′ ⱽˣ) (θ : (`¬ˣ Θ′) ⱽˣ ) 
  → (proj₁ (s x) ⱽᴸ) ⟨ γ , θ ⟩ ≡ (λ k → k ((x ⱽⱽ) (sub-TV-int Γ Γ′ Θ′ s θ γ)))
sub-lemma-var s `Z γ θ = cps-V (proj₁ (s `Z)) (proj₂ (s `Z)) ⟨ γ , θ ⟩
sub-lemma-var {Γ}{Γ′}{Θ′} s (`S x) γ θ = 
  sub-lemma-var (sub-skip (Fix₂ TermValue Θ′) s) x γ θ
\end{code}
%</sub-lemma-var>

%<*sub-lemma-covar>
\begin{code}
sub-lemma-covar : ∀ {Γ′ Θ Θ′ A} (t : Θ –[ (Fix₁ Coterm Γ′) ]→ Θ′) 
  (α : Θ ∋ A) (γ : Γ′ ⱽˣ) (θ : (`¬ˣ Θ′) ⱽˣ ) 
  → (t α ⱽᴿ) ⟨ γ , θ ⟩ ≡ (Γ∋A⇒¬Γ∋¬A α ⱽⱽ) (sub-C-int Γ′ Θ Θ′ t γ θ)
\end{code}
%</sub-lemma-covar>
\begin{code}
sub-lemma-covar t `Z γ θ = refl
sub-lemma-covar {Γ′} t (`S α) γ θ = sub-lemma-covar (sub-skip (Fix₁ Coterm Γ′) t) α γ θ
\end{code}
--Sequents--

%<*sub-lemma-ty>
\begin{code}
sub-lemma-T : ∀ {Γ Γ′ Θ Θ′ A} 
  (s : Γ –[ (Fix₂ TermValue Θ′) ]→ Γ′) (t : Θ –[ (Fix₁ Coterm Γ′) ]→ Θ′) 
  (M : Γ ⟶ Θ ∣ A) (γ : Γ′ ⱽˣ) (θ : (`¬ˣ Θ′) ⱽˣ ) 
  → ((sub-T TVK CK s t M) ⱽᴸ) ⟨ γ , θ ⟩ 
    ≡ (M ⱽᴸ) ⟨ sub-TV-int Γ Γ′ Θ′ s θ γ , sub-C-int Γ′ Θ Θ′ t γ θ ⟩

sub-lemma-C : ∀ {Γ Γ′ Θ Θ′ A} 
  (s : Γ –[ (Fix₂ TermValue Θ′) ]→ Γ′) (t : Θ –[ (Fix₁ Coterm Γ′) ]→ Θ′) 
  (K : A ∣ Γ ⟶ Θ) (γ : Γ′ ⱽˣ) (θ : (`¬ˣ Θ′) ⱽˣ ) 
  → ((sub-C TVK CK s t K) ⱽᴿ) ⟨ γ , θ ⟩ 
    ≡ (K ⱽᴿ) ⟨ sub-TV-int Γ Γ′ Θ′ s θ γ , sub-C-int Γ′ Θ Θ′ t γ θ ⟩

sub-lemma-S : ∀ {Γ Γ′ Θ Θ′} 
  (s : Γ –[ (Fix₂ TermValue Θ′) ]→ Γ′) (t : Θ –[ (Fix₁ Coterm Γ′) ]→ Θ′) 
  (S : Γ ↦ Θ) (γ : Γ′ ⱽˣ) (θ : (`¬ˣ Θ′) ⱽˣ ) 
  → ((sub-S TVK CK s t S) ⱽˢ) ⟨ γ , θ ⟩ 
    ≡ (S ⱽˢ) ⟨ sub-TV-int Γ Γ′ Θ′ s θ γ , sub-C-int Γ′ Θ Θ′ t γ θ ⟩
\end{code}
%</sub-lemma-ty>
\begin{code}
sub-lemma-T s t (` x) γ θ = sub-lemma-var s x γ θ
sub-lemma-T {Γ}{Γ′}{Θ}{Θ′} s t `⟨ M , N ⟩ γ θ = ext (λ k → 
  cong₂ (λ -₁ -₂ → -₁ (λ x → -₂ (λ y → k ⟨ x , y ⟩))) 
    (sub-lemma-T s t M γ θ) (sub-lemma-T s t N γ θ))
sub-lemma-T s t inl⟨ M ⟩ γ θ = ext (λ k → 
  cong (λ - → - (λ x → k (inj₁ x))) (sub-lemma-T s t M γ θ))
sub-lemma-T s t inr⟨ M ⟩ γ θ = ext (λ k → 
  cong (λ - → - (λ x → k (inj₂ x))) (sub-lemma-T s t M γ θ))
sub-lemma-T s t not[ K ] γ θ = ext (λ k → cong k (sub-lemma-C s t K γ θ))
sub-lemma-T {Γ}{Γ′}{Θ}{Θ′}{A} s t (μθ S) γ θ = ext (λ k → 
  begin
    (sub-S TVK CK 
      (fmap-wkΘᵗⱽ Θ′ A s)
      (sub-lift (CK.kit) t)
      S ⱽˢ) ⟨ γ , ⟨ θ , k ⟩ ⟩
  ≡⟨ 
    sub-lemma-S 
      (fmap-wkΘᵗⱽ Θ′ A s) 
      (sub-lift (CotermKit.kit CK) t) 
      S γ ⟨ θ , k ⟩ 
    ⟩
    (S ⱽˢ) 
      ⟨ sub-TV-int Γ Γ′ (Θ′ , A) 
      (fmap-wkΘᵗⱽ Θ′ A s) 
      ⟨ θ , k ⟩ γ , 
      ⟨ sub-C-int Γ′ Θ (Θ′ , A) (sub-weaken (CotermKit.kit CK) t) γ ⟨ θ , k ⟩ , k ⟩ ⟩
  ≡⟨ 
    cong (λ - → (S ⱽˢ) 
    ⟨ sub-TV-int Γ Γ′ (Θ′ , A) 
    (fmap-wkΘᵗⱽ Θ′ A s) 
    ⟨ θ , k ⟩ γ , ⟨ - , k ⟩ ⟩) 
      (weaken-sub-C-int-lemma t γ θ k) 
    ⟩
    (S ⱽˢ) 
    ⟨ sub-TV-int Γ Γ′ (Θ′ , A) 
      (fmap-wkΘᵗⱽ Θ′ A s)
      ⟨ θ , k ⟩ γ 
    , ⟨ sub-C-int Γ′ Θ Θ′ t γ θ , k ⟩ ⟩ 
  ≡⟨ 
    cong (λ - → (S ⱽˢ) ⟨ - , ⟨ sub-C-int Γ′ Θ Θ′ t γ θ , k ⟩ ⟩) 
      (fmap-sub-TV-int-lemma s γ θ k) 
    ⟩
    (S ⱽˢ) ⟨ sub-TV-int Γ Γ′ Θ′ s θ γ , ⟨ sub-C-int Γ′ Θ Θ′ t γ θ , k ⟩ ⟩
  ∎)


sub-lemma-C s t (` α) γ θ = sub-lemma-covar t α γ θ
sub-lemma-C s t fst[ K ] γ θ = cong (λ - → λ { ⟨ x , _ ⟩ → - x }) (sub-lemma-C s t K γ θ)
sub-lemma-C s t snd[ K ] γ θ = cong (λ - → λ { ⟨ _ , y ⟩ → - y }) (sub-lemma-C s t K γ θ)
sub-lemma-C {Γ} {Γ′} {Θ} {Θ′} {A `+ B} s t `[ K , L ] γ θ = 
  ext (λ{ (inj₁ x) → cong (λ - → - x) (sub-lemma-C s t K γ θ) 
        ; (inj₂ y) → cong (λ - → - y) (sub-lemma-C s t L γ θ)})
sub-lemma-C s t not⟨ M ⟩ γ θ = sub-lemma-T s t M γ θ
\end{code}
%<*sub-lemma-varabs>
\begin{code}
sub-lemma-C {Γ}{Γ′}{Θ}{Θ′}{A} s t (μγ S) γ θ = ext (λ x → 
  begin 
    (sub-S TVK CK (sub-lift (TVK.kit) s) (fmap-wkΓᶜ Γ′ A t) S ⱽˢ)
      ⟨ ⟨ γ , x ⟩ , θ ⟩
  ≡⟨ sub-lemma-S (sub-lift (TVK.kit) s) (fmap-wkΓᶜ Γ′ A t) S ⟨ γ , x ⟩ θ ⟩
    (S ⱽˢ)
      ⟨ ⟨ sub-TV-int Γ (Γ′ , A) Θ′ (sub-weaken (TVK.kit) s) θ ⟨ γ , x ⟩ , x ⟩ 
      , sub-C-int (Γ′ , A) Θ Θ′ (fmap-wkΓᶜ Γ′ A t) ⟨ γ , x ⟩ θ ⟩
  ≡⟨ cong (λ - → (S ⱽˢ) ⟨ ⟨ - , x ⟩ , sub-C-int (Γ′ , A) Θ Θ′ (fmap-wkΓᶜ Γ′ A t) ⟨ γ , x ⟩ θ ⟩) 
      (weaken-sub-TV-int-lemma s γ θ x) ⟩
    (S ⱽˢ)
      ⟨ ⟨ sub-TV-int Γ Γ′ Θ′ s θ γ , x ⟩ 
      , sub-C-int (Γ′ , A) Θ Θ′ (fmap-wkΓᶜ Γ′ A t) ⟨ γ , x ⟩ θ ⟩
  ≡⟨ cong (λ - → (S ⱽˢ) ⟨ ⟨ sub-TV-int Γ Γ′ Θ′ s θ γ , x ⟩ , - ⟩) 
      (fmap-sub-C-int-lemma t γ θ x) ⟩
    (S ⱽˢ) ⟨ ⟨ sub-TV-int Γ Γ′ Θ′ s θ γ , x ⟩ , sub-C-int Γ′ Θ Θ′ t γ θ ⟩
  ∎)
\end{code}
%</sub-lemma-varabs>

\begin{code}
sub-lemma-S {Γ} {Γ′} {Θ} {Θ′} s t (M ● K) γ θ = 
  begin
    (sub-T TVK CK s t M ⱽᴸ) ⟨ γ , θ ⟩ 
    ((sub-C TVK CK s t K ⱽᴿ) ⟨ γ , θ ⟩)
  ≡⟨ cong (λ - → - ((sub-C TVK CK s t K ⱽᴿ) ⟨ γ , θ ⟩)) 
      (sub-lemma-T s t M γ θ) ⟩
    (M ⱽᴸ) ⟨ sub-TV-int Γ Γ′ Θ′ s θ γ , sub-C-int Γ′ Θ Θ′ t γ θ ⟩ 
    ((sub-C TVK CK s t K ⱽᴿ) ⟨ γ , θ ⟩)
  ≡⟨ cong (λ - → (M ⱽᴸ) ⟨ sub-TV-int Γ Γ′ Θ′ s θ γ , sub-C-int Γ′ Θ Θ′ t γ θ ⟩ -) 
      (sub-lemma-C s t K γ θ) ⟩
    (M ⱽᴸ) ⟨ sub-TV-int Γ Γ′ Θ′ s θ γ , sub-C-int Γ′ Θ Θ′ t γ θ ⟩ 
    ((K ⱽᴿ) ⟨ sub-TV-int Γ Γ′ Θ′ s θ γ , sub-C-int Γ′ Θ Θ′ t γ θ ⟩)
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
  cong ((V ⱽᴸ) c) (ext (λ x → cong (λ - → - (λ y → (K ⱽᴿ) c x)) (cps-V W w c)))
S⟶ⱽT⇒Sⱽ≡Tⱽ (`⟨ V , W ⟩ ● snd[ L ]) (W ● L) c (β×₂ v w) = 
  cong (λ - → - (λ x → (W ⱽᴸ) c (λ y → (L ⱽᴿ) c y))) (cps-V V v c)
S⟶ⱽT⇒Sⱽ≡Tⱽ (inl⟨ V ⟩ ● `[ K , L ]) (V ● K) c (β+₁ v) = refl
S⟶ⱽT⇒Sⱽ≡Tⱽ (inr⟨ W ⟩ ● `[ K , L ]) (W ● L) c (β+₂ w) = refl
S⟶ⱽT⇒Sⱽ≡Tⱽ (not[ K ] ● not⟨ M ⟩) (M ● K) c (β¬) = refl
\end{code}
%<*sound-lemma-TV>
\begin{code}
S⟶ⱽT⇒Sⱽ≡Tⱽ {Γ} {Θ} (V ● μγ {Γ}{Θ}{A} S) .(S ⱽ⟨ ⟨ V , v ⟩ /⟩ˢ) ⟨ γ , θ ⟩ (βL v) = sym (
  begin
    ((S ⱽ⟨ ⟨ V , v ⟩ /⟩ˢ) ⱽˢ) ⟨ γ , θ ⟩
  ≡⟨⟩
    (sub-S TVK CK 
      (add (Fix₂ TermValue Θ) ⟨ V , v ⟩ id-TV) id-C S ⱽˢ) 
      ⟨ γ , θ ⟩
  ≡⟨ sub-lemma-S (add (Fix₂ TermValue Θ) ⟨ V , v ⟩ id-TV) id-C S γ θ ⟩
    (S ⱽˢ) 
      ⟨ sub-TV-int (Γ , A) Γ Θ (add (Fix₂ TermValue Θ) ⟨ V , v ⟩ id-TV) θ γ 
      , sub-C-int Γ Θ Θ id-C γ θ ⟩
  ≡⟨⟩
    (S ⱽˢ)
      ⟨ ⟨ sub-TV-int Γ Γ Θ id-TV θ γ , (⟨ V , v ⟩ ⱽᴸⱽ) ⟨ γ , θ ⟩ ⟩
      , sub-C-int Γ Θ Θ id-C γ θ ⟩
  ≡⟨ cong (λ - → (S ⱽˢ) ⟨ ⟨ sub-TV-int Γ Γ Θ id-TV θ γ , (⟨ V , v ⟩ ⱽᴸⱽ) ⟨ γ , θ ⟩ ⟩ , - ⟩) 
    (id-sub-C Γ Θ γ θ) ⟩
    (S ⱽˢ) ⟨ ⟨ sub-TV-int Γ Γ Θ id-TV θ γ , (⟨ V , v ⟩ ⱽᴸⱽ) ⟨ γ , θ ⟩ ⟩ , θ ⟩
  ≡⟨ cong (λ - → (S ⱽˢ) ⟨ ⟨ - , (⟨ V , v ⟩ ⱽᴸⱽ) ⟨ γ , θ ⟩ ⟩ , θ ⟩) (id-sub-TV Γ Θ γ θ) ⟩
    (S ⱽˢ) ⟨ ⟨ γ , (⟨ V , v ⟩ ⱽᴸⱽ) ⟨ γ , θ ⟩ ⟩ , θ ⟩
  ≡⟨ sym (cong (λ - → - (λ x → (S ⱽˢ) ⟨ ⟨ γ , x ⟩ , θ ⟩)) (cps-V V v ⟨ γ , θ ⟩)) ⟩
    (V ⱽᴸ) ⟨ γ , θ ⟩ (λ x → (S ⱽˢ) ⟨ ⟨ γ , x ⟩ , θ ⟩)
  ∎)
\end{code}
%</sound-lemma-TV>
\begin{code}
S⟶ⱽT⇒Sⱽ≡Tⱽ {Γ}{Θ}(μθ {Γ}{Θ}{A} S ● K) .(S [ K /]ˢ) ⟨ γ , θ ⟩ (βR) = sym (
  begin
    ((S [ K /]ˢ) ⱽˢ) ⟨ γ , θ ⟩
  ≡⟨⟩
    (sub-S TVK CK id-TV 
      (add (Fix₁ Coterm Γ) K id-C) S ⱽˢ) 
      ⟨ γ , θ ⟩
  ≡⟨ sub-lemma-S id-TV ((add (Fix₁ Coterm Γ) K id-C)) S γ θ ⟩
    (S ⱽˢ) 
      ⟨ (sub-TV-int Γ Γ Θ id-TV θ γ) 
      , (sub-C-int Γ (Θ , A) Θ (add (Fix₁ Coterm Γ) K id-C) γ θ) ⟩
  ≡⟨ 
    cong (λ - → (S ⱽˢ) ⟨ - , sub-C-int Γ (Θ , A) Θ (add (Fix₁ Coterm Γ) K id-C) γ θ ⟩) 
      (id-sub-TV Γ Θ γ θ) 
    ⟩
    (S ⱽˢ) ⟨ γ , (sub-C-int Γ (Θ , A) Θ (add (Fix₁ Coterm Γ) K id-C) γ θ) ⟩
  ≡⟨ cong (λ - → (S ⱽˢ) ⟨ γ , ⟨ - , (K ⱽᴿ) ⟨ γ , θ ⟩ ⟩ ⟩) (id-sub-C Γ Θ γ θ) ⟩
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
