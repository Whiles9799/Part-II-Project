{-# OPTIONS --rewriting #-}

module Dual.Soundness (R : Set) where

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
weaken-ren-int-cbv-lemma : ∀ {Γ Γ′ A} (ρ : Γ ↝ Γ′) γ k → ren-int-cbv Γ (Γ′ , A) (rename-weaken ρ) ⟨ γ , k ⟩ ≡ ren-int-cbv Γ Γ′ ρ γ
weaken-ren-int-cbv-lemma {∅} ρ γ k = refl
weaken-ren-int-cbv-lemma {Γ , B}{Γ′}{A} ρ γ k = cong (λ - → ⟨ - , (ρ `Z ⱽⱽ) γ ⟩) (weaken-ren-int-cbv-lemma {Γ}{Γ′}{A} (ren-skip ρ) γ k)


lift-ren-int-cbv-lemma : ∀ {Γ Γ′ A} (ρ : Γ ↝ Γ′) γ k → ren-int-cbv (Γ , A) (Γ′ , A) (rename-lift ρ) ⟨ γ , k ⟩ ≡ ⟨ (ren-int-cbv Γ Γ′ ρ γ) , k ⟩
lift-ren-int-cbv-lemma {∅} ρ γ k = refl
lift-ren-int-cbv-lemma {Γ , x} ρ γ k = cong (λ - → ⟨ ⟨ - , (ρ `Z ⱽⱽ) γ ⟩ , k ⟩) (weaken-ren-int-cbv-lemma (ren-skip ρ) γ k)

--The interpretation of the id renaming to an interpreted context has no effect--
id-ren : ∀ {Γ} (γ : Γ ⱽˣ) → ren-int-cbv Γ Γ id-var γ ≡ γ
id-ren {∅} γ = refl
id-ren {Γ , A} ⟨ γ₁ , γ₂ ⟩ = cong (λ - → ⟨ - , γ₂ ⟩) (trans (weaken-ren-int-cbv-lemma id-var γ₁ γ₂) (id-ren γ₁))

--Equivalent lemmas for negated context interpretations--
weaken-neg-ren-int-cbv-lemma : ∀ {Θ Θ′ A} (ρ : Θ ↝ Θ′) θ k → neg-ren-int-cbv Θ (Θ′ , A) (rename-weaken ρ) ⟨ θ , k ⟩ ≡ neg-ren-int-cbv Θ Θ′ ρ θ
weaken-neg-ren-int-cbv-lemma {∅} ρ θ k = refl
weaken-neg-ren-int-cbv-lemma {Θ , B}{Θ′}{A} ρ θ k = cong (λ - → ⟨ - , (Γ∋A⇒¬Γ∋¬A (ρ `Z) ⱽⱽ) θ ⟩) (weaken-neg-ren-int-cbv-lemma (ren-skip ρ) θ k)

lift-neg-ren-int-cbv-lemma : ∀ {Θ Θ′ A} (ρ : Θ ↝ Θ′) θ k → neg-ren-int-cbv (Θ , A) (Θ′ , A) (rename-lift ρ) ⟨ θ , k ⟩ ≡ ⟨ (neg-ren-int-cbv Θ Θ′ ρ θ) , k ⟩
lift-neg-ren-int-cbv-lemma {∅} ρ θ k = refl
lift-neg-ren-int-cbv-lemma {Θ , x} ρ θ k = cong (λ - → ⟨ ⟨ - , (Γ∋A⇒¬Γ∋¬A (ρ `Z) ⱽⱽ) θ ⟩ , k ⟩) (weaken-neg-ren-int-cbv-lemma (ren-skip ρ) θ k)

id-neg-ren : ∀ {Θ} (θ : (`¬ˣ Θ) ⱽˣ) → neg-ren-int-cbv Θ Θ id-var θ ≡ θ
id-neg-ren {∅} θ = refl
id-neg-ren {Θ , A} ⟨ θ₁ , θ₂ ⟩ = cong (λ - → ⟨ - , θ₂ ⟩) (trans (weaken-neg-ren-int-cbv-lemma id-var θ₁ θ₂) (id-neg-ren θ₁))

--The Renaming Lemma--
--The interpretation of the renaming of a sequent applied to some contexts is equivalent to the interpretation of the sequent applied 
--to the interpretation of the renamings applied to each of the contexts--

--Variables and Covariables--
ren-lemma-var : ∀ {Γ Γ′ A} (x : Γ ∋ A) (ρ : Γ ↝ Γ′) (γ : Γ′ ⱽˣ) 
  → ((ρ x ⱽⱽ) γ) ≡ ((x ⱽⱽ) (ren-int-cbv Γ Γ′ ρ γ))
ren-lemma-var `Z ρ γ = refl
ren-lemma-var (`S x) ρ γ = ren-lemma-var x (ren-skip ρ) γ

ren-lemma-covar : ∀ {Θ Θ′ A} (α : Θ ∋ A) (ρ : Θ ↝ Θ′) (θ : `¬ˣ Θ′ ⱽˣ) (k : A ⱽᵀ)
  → (Γ∋A⇒¬Γ∋¬A (ρ α) ⱽⱽ) θ k ≡ (Γ∋A⇒¬Γ∋¬A α ⱽⱽ) (neg-ren-int-cbv Θ Θ′ ρ θ) k
ren-lemma-covar `Z ρ θ k = refl
ren-lemma-covar (`S α) ρ θ k = ren-lemma-covar α (ren-skip ρ) θ k

--Sequents--
ren-lemma-term : ∀ {Γ Γ′ Θ Θ′ A} (M : Γ ⟶ Θ ∣ A) (s : Γ ↝ Γ′) (t : Θ ↝ Θ′) (c₁ : Γ′ ⱽˣ) (c₂ : `¬ˣ Θ′ ⱽˣ) (k : ((`¬ A) ⱽᵀ))
  → (rename-term s t M ⱽᴸ) ⟨ c₁ , c₂ ⟩ k ≡ (M ⱽᴸ) ⟨ ren-int-cbv Γ Γ′ s c₁ , neg-ren-int-cbv Θ Θ′ t c₂ ⟩ k 
ren-lemma-termvalue : ∀ {Γ Γ′ Θ Θ′ A} (V : TermValue Γ Θ A) (s : Γ ↝ Γ′) (t : Θ ↝ Θ′) (c₁ : Γ′ ⱽˣ) (c₂ : `¬ˣ Θ′ ⱽˣ)
  → (⟨ rename-term s t (proj₁ V) , value-invariant-under-renaming s t (proj₂ V) ⟩ ⱽᴸⱽ) ⟨ c₁ , c₂ ⟩ ≡ (V ⱽᴸⱽ) ⟨ ren-int-cbv Γ Γ′ s c₁ , neg-ren-int-cbv Θ Θ′ t c₂ ⟩
ren-lemma-coterm : ∀ {Γ Γ′ Θ Θ′ A} (K : A ∣ Γ ⟶ Θ) (s : Γ ↝ Γ′) (t : Θ ↝ Θ′) (c₁ : Γ′ ⱽˣ) (c₂ : `¬ˣ Θ′ ⱽˣ) (k : A ⱽᵀ)
  → (rename-coterm s t K ⱽᴿ) ⟨ c₁ , c₂ ⟩ k ≡ (K ⱽᴿ) ⟨ ren-int-cbv Γ Γ′ s c₁ , neg-ren-int-cbv Θ Θ′ t c₂ ⟩ k    
ren-lemma-statement : ∀ {Γ Γ′ Θ Θ′} (S : Γ ↦ Θ) (s : Γ ↝ Γ′) (t : Θ ↝ Θ′) (c₁ : Γ′ ⱽˣ) (c₂ : `¬ˣ Θ′ ⱽˣ)
  → (rename-statement s t S ⱽˢ) ⟨ c₁ , c₂ ⟩ ≡ (S ⱽˢ) ⟨ ren-int-cbv Γ Γ′ s c₁ , neg-ren-int-cbv Θ Θ′ t c₂ ⟩
    

ren-lemma-term (` x) s t c₁ c₂ k = cong k (ren-lemma-var x s c₁)
ren-lemma-term {Γ}{Γ′}{Θ}{Θ′} `⟨ M , N ⟩ s t c₁ c₂ k = cong₂ (λ -₁ -₂ → -₁ (λ x → -₂ (λ y → k ⟨ x , y ⟩))) (ext λ x → ren-lemma-term M s t c₁ c₂ x) (ext (λ x → ren-lemma-term N s t c₁ c₂ x))
ren-lemma-term inl⟨ M ⟩ s t c₁ c₂ k = ren-lemma-term M s t c₁ c₂ λ x → k (inj₁ x)
ren-lemma-term inr⟨ M ⟩ s t c₁ c₂ k = ren-lemma-term M s t c₁ c₂ λ x → k (inj₂ x)
ren-lemma-term not[ K ] s t c₁ c₂ k = cong k (ext (λ x → ren-lemma-coterm K s t c₁ c₂ x))
ren-lemma-term {Γ}{Γ′}{Θ}{Θ′}{A} (μθ S) s t c₁ c₂ k =
  begin
    (rename-statement s (rename-lift t) S ⱽˢ) ⟨ c₁ , ⟨ c₂ , k ⟩ ⟩
  ≡⟨ ren-lemma-statement S s (rename-lift t) c₁ ⟨ c₂ , k ⟩ ⟩
    (S ⱽˢ) ⟨ ren-int-cbv Γ Γ′ s c₁ , ⟨ neg-ren-int-cbv Θ (Θ′ , A) (λ x → `S (t x)) ⟨ c₂ , k ⟩ , k ⟩ ⟩
  ≡⟨ cong (λ - → (S ⱽˢ) ⟨ ren-int-cbv Γ Γ′ s c₁ , - ⟩) (lift-neg-ren-int-cbv-lemma t c₂ k) ⟩
    (S ⱽˢ) ⟨ ren-int-cbv Γ Γ′ s c₁ , ⟨ neg-ren-int-cbv Θ Θ′ t c₂ , k ⟩ ⟩ 
  ∎

ren-lemma-termvalue ⟨ ` x , V-var ⟩ s t c₁ c₂ = ren-lemma-var x s c₁
ren-lemma-termvalue ⟨ `⟨ V , W ⟩ , V-prod v w ⟩ s t c₁ c₂ = cong₂ ⟨_,_⟩ (ren-lemma-termvalue ⟨ V , v ⟩ s t c₁ c₂) (ren-lemma-termvalue ⟨ W , w ⟩ s t c₁ c₂)
ren-lemma-termvalue ⟨ inl⟨ V ⟩ , V-inl v ⟩ s t c₁ c₂ = cong inj₁ (ren-lemma-termvalue ⟨ V , v ⟩ s t c₁ c₂)
ren-lemma-termvalue ⟨ inr⟨ V ⟩ , V-inr v ⟩ s t c₁ c₂ = cong inj₂ (ren-lemma-termvalue ⟨ V , v ⟩ s t c₁ c₂)
ren-lemma-termvalue ⟨ not[ K ] , V-not ⟩ s t c₁ c₂ = ext (λ x → ren-lemma-coterm K s t c₁ c₂ x)


ren-lemma-coterm (` α) s t c₁ c₂ k = ren-lemma-covar α t c₂ k
ren-lemma-coterm fst[ K ] s t c₁ c₂ k = cong (λ - → - k) (ext (λ x → ren-lemma-coterm K s t c₁ c₂ (proj₁ x)))
ren-lemma-coterm snd[ K ] s t c₁ c₂ k = cong (λ - → - k) (ext (λ x → ren-lemma-coterm K s t c₁ c₂ (proj₂ x)))
ren-lemma-coterm {Γ}{Γ′}{Θ}{Θ′}{A} `[ K , L ] s t c₁ c₂ k = cong (λ - → - k) {(rename-coterm s t `[ K , L ] ⱽᴿ) ⟨ c₁ , c₂ ⟩ }{(`[ K , L ] ⱽᴿ) ⟨ ren-int-cbv Γ Γ′ s c₁ , neg-ren-int-cbv Θ Θ′ t c₂ ⟩} (ext (λ{(inj₁ x) → ren-lemma-coterm K s t c₁ c₂ x ; (inj₂ y) → ren-lemma-coterm L s t c₁ c₂ y}))
ren-lemma-coterm not⟨ M ⟩ s t c₁ c₂ k = ren-lemma-term M s t c₁ c₂ k
ren-lemma-coterm {Γ}{Γ′}{Θ}{Θ′}{A} (μγ S) s t c₁ c₂ k = 
  begin 
    (rename-statement (rename-lift s) t S ⱽˢ) ⟨ ⟨ c₁ , k ⟩ , c₂ ⟩
  ≡⟨ ren-lemma-statement S (rename-lift s) t ⟨ c₁ , k ⟩ c₂ ⟩
    (S ⱽˢ) ⟨ ⟨ ren-int-cbv Γ (Γ′ , A) (λ x → `S (s x)) ⟨ c₁ , k ⟩ , k ⟩ , neg-ren-int-cbv Θ Θ′ t c₂ ⟩
  ≡⟨ cong (λ - → (S ⱽˢ) ⟨ - , neg-ren-int-cbv Θ Θ′ t c₂ ⟩) (lift-ren-int-cbv-lemma s c₁ k) ⟩
    (S ⱽˢ) ⟨ ⟨ ren-int-cbv Γ Γ′ s c₁ , k ⟩ , neg-ren-int-cbv Θ Θ′ t c₂ ⟩
  ∎ 

ren-lemma-statement {Γ} {Γ′} {Θ} {Θ′} (M ● K) s t c₁ c₂ = cong₂ (λ -₁ -₂ → -₁ -₂) (ext (λ x → ren-lemma-term M s t c₁ c₂ x)) (ext (λ x → ren-lemma-coterm K s t c₁ c₂ x))


--Lemmas for proving the Substitution Lemma--

--TermValues--
termvalue-sub-weaken-lemma : ∀ {Γ Γ′ Θ A B} (σ : Γ –[(λ Γ A → TermValue Γ Θ A)]→ Γ′) (x : Γ ∋ A) γ θ k
  → (sub-weaken {Γ}{Γ′}{B} (TermSubstKit.kit TVK) σ x ⱽᴸⱽ) ⟨ ⟨ γ , k ⟩ , θ ⟩ ≡ (σ x ⱽᴸⱽ) ⟨ γ , θ ⟩ 
termvalue-sub-weaken-lemma {Γ}{Γ′}{Θ}{A}{B} σ `Z γ θ k = 
  begin 
    (⟨ rename-term (λ x → `S x) (λ x → x) (proj₁ (σ `Z)) , value-invariant-under-renaming (λ x → `S x) (λ x → x) (proj₂ (σ `Z)) ⟩ ⱽᴸⱽ) ⟨ ⟨ γ , k ⟩ , θ ⟩
  ≡⟨ ren-lemma-termvalue (σ `Z) (λ x → `S x) (λ x → x) ⟨ γ , k ⟩ θ ⟩
    ((σ `Z) ⱽᴸⱽ) ⟨ ren-int-cbv Γ′ (Γ′ , B) (λ x → `S x) ⟨ γ , k ⟩ , neg-ren-int-cbv Θ Θ (λ x → x) θ ⟩
  ≡⟨ cong₂ (λ -₁ -₂ → (σ `Z ⱽᴸⱽ) ⟨ -₁ , -₂ ⟩) (trans (weaken-ren-int-cbv-lemma (λ x → x) γ k) (id-ren γ)) (id-neg-ren θ) ⟩
    (σ `Z ⱽᴸⱽ) ⟨ γ , θ ⟩
  ∎
termvalue-sub-weaken-lemma {Γ}{Γ′}{Θ} σ (`S x) γ θ k = termvalue-sub-weaken-lemma (sub-skip (λ Γ A → TermValue Γ Θ A) σ) x γ θ k

termvalue-sub-fmap-lemma : ∀ {Γ Γ′ Θ A B} (σ : Γ –[(λ Γ A → TermValue Γ Θ A)]→ Γ′) (x : Γ ∋ A) γ θ k
  → (fmap {λ Γ A → TermValue Γ Θ A}{λ Γ A → TermValue Γ (Θ , B) A} (TermSubstKit.wkΘ TVK) σ x ⱽᴸⱽ) ⟨ γ , ⟨ θ , k ⟩ ⟩ ≡ ((σ x) ⱽᴸⱽ) ⟨ γ , θ ⟩
termvalue-sub-fmap-lemma {Γ}{Γ′}{Θ}{A}{B} σ `Z γ θ k = 
  begin 
    (⟨ rename-term (λ x → x) (λ x → `S x) (proj₁ (σ `Z)) , value-invariant-under-renaming (λ x → x) (λ x → `S x) (proj₂ (σ `Z)) ⟩ ⱽᴸⱽ) ⟨ γ , ⟨ θ , k ⟩ ⟩
  ≡⟨ ren-lemma-termvalue (σ `Z) (λ x → x) (λ x → `S x) γ ⟨ θ , k ⟩ ⟩
    (σ `Z ⱽᴸⱽ) ⟨ ren-int-cbv Γ′ Γ′ (λ x → x) γ , neg-ren-int-cbv Θ (Θ , B) (λ x → `S x) ⟨ θ , k ⟩ ⟩
  ≡⟨ cong₂ (λ -₁ -₂ → (σ `Z ⱽᴸⱽ) ⟨ -₁ , -₂ ⟩) (id-ren γ) (trans (weaken-neg-ren-int-cbv-lemma (λ x → x) θ k) (id-neg-ren θ)) ⟩
    (σ `Z ⱽᴸⱽ) ⟨ γ , θ ⟩ 
  ∎
  
termvalue-sub-fmap-lemma {Γ}{Γ′}{Θ} σ (`S x) γ θ k = termvalue-sub-fmap-lemma (sub-skip (λ Γ A → TermValue Γ Θ A) σ) x γ θ k

weaken-termvalue-sub-int-lemma : ∀ {Γ Γ′ Θ A} (σ : Γ –[ (λ Γ A → TermValue Γ Θ A) ]→ Γ′) γ θ k 
  → termvalue-sub-int Γ (Γ′ , A) Θ (sub-weaken (TermSubstKit.kit TVK) σ) θ ⟨ γ , k ⟩ ≡ termvalue-sub-int Γ Γ′ Θ σ θ γ
weaken-termvalue-sub-int-lemma {∅} σ γ θ k = refl
weaken-termvalue-sub-int-lemma {Γ , A} {Γ′} {Θ} σ γ θ k = cong₂ (λ -₁ -₂ → ⟨ -₁ , -₂ ⟩) (weaken-termvalue-sub-int-lemma (sub-skip (λ Γ A → TermValue Γ Θ A) σ) γ θ k) (termvalue-sub-weaken-lemma σ `Z γ θ k)

lift-termvalue-sub-int-lemma : ∀ {Γ Γ′ Θ A} (σ : Γ –[(λ Γ A → TermValue Γ Θ A)]→ Γ′) γ θ k
  → termvalue-sub-int (Γ , A) (Γ′ , A) Θ (sub-lift (TermSubstKit.kit TVK) σ) θ ⟨ γ , k ⟩ ≡ ⟨ (termvalue-sub-int Γ Γ′ Θ σ θ γ) , k ⟩
lift-termvalue-sub-int-lemma {∅} σ γ θ k = refl
lift-termvalue-sub-int-lemma {Γ , x} {_} {Θ} σ γ θ k = cong₂ (λ -₁ -₂ → ⟨ ⟨ -₁ , -₂ ⟩ , k ⟩ ) (weaken-termvalue-sub-int-lemma (sub-skip (λ Γ A → TermValue Γ Θ A) σ) γ θ k) (termvalue-sub-weaken-lemma σ `Z γ θ k)

fmap-termvalue-sub-int-lemma : ∀ {Γ Γ′ Θ A} (σ : Γ –[(λ Γ A → TermValue Γ Θ A)]→ Γ′) γ θ k
  → termvalue-sub-int Γ Γ′ (Θ , A) (fmap {λ Γ B → TermValue Γ Θ B} {λ Γ B → TermValue Γ (Θ , A) B} (TermSubstKit.wkΘ TVK) σ) ⟨ θ , k ⟩ γ ≡ termvalue-sub-int Γ Γ′ Θ σ θ γ
fmap-termvalue-sub-int-lemma {∅} σ γ θ k = refl
fmap-termvalue-sub-int-lemma {Γ , x}{Γ′}{Θ} σ γ θ k = cong₂ (λ -₁ -₂ → ⟨ -₁ , -₂ ⟩) (fmap-termvalue-sub-int-lemma (sub-skip (λ Γ A → TermValue Γ Θ A) σ) γ θ k) (termvalue-sub-fmap-lemma σ `Z γ θ k)

id-termvalue-sub-int : ∀ Γ Θ γ θ → termvalue-sub-int Γ Γ Θ id-termvalue θ γ ≡ γ
id-termvalue-sub-int ∅ Θ γ θ = refl
id-termvalue-sub-int (Γ , A) Θ ⟨ γ , k ⟩ θ = cong (λ - → ⟨ - , k ⟩)
  (begin 
    termvalue-sub-int Γ (Γ , A) Θ (λ x → id-termvalue (`S x)) θ ⟨ γ , k ⟩
  ≡⟨ weaken-termvalue-sub-int-lemma id-termvalue γ θ k ⟩
    termvalue-sub-int Γ Γ Θ (λ x → id-termvalue x) θ γ
  ≡⟨ id-termvalue-sub-int Γ Θ γ θ ⟩
    γ
  ∎)

--Coterms--
coterm-sub-weaken-lemma : ∀ {Γ Θ Θ′ A B} (σ : Θ –[ (λ Θ A → A ∣ Γ ⟶ Θ) ]→ Θ′) (α : Θ ∋ A) γ θ k
  → (sub-weaken {Θ}{Θ′}{B} (CotermSubstKit.kit CK) σ α ⱽᴿ) ⟨ γ , ⟨ θ , k ⟩ ⟩ ≡ (σ α ⱽᴿ) ⟨ γ , θ ⟩
coterm-sub-weaken-lemma {Γ}{Θ}{Θ′}{A}{B} σ `Z γ θ k = ext (λ z → 
  begin 
    (rename-coterm (λ x → x) (λ x → `S x) (σ `Z) ⱽᴿ) ⟨ γ , ⟨ θ , k ⟩ ⟩ z
  ≡⟨ ren-lemma-coterm (σ `Z) (λ x → x) (λ x → `S x) γ ⟨ θ , k ⟩ z ⟩
    (σ `Z ⱽᴿ) ⟨ ren-int-cbv Γ Γ (λ x → x) γ , neg-ren-int-cbv Θ′ (Θ′ , B) (λ x → `S x) ⟨ θ , k ⟩ ⟩ z
  ≡⟨ cong₂ (λ -₁ -₂ → (σ `Z ⱽᴿ) ⟨ -₁ , -₂ ⟩ z) (id-ren γ) (trans (weaken-neg-ren-int-cbv-lemma (λ x → x) θ k) (id-neg-ren θ)) ⟩
    ((σ `Z ⱽᴿ) ⟨ γ , θ ⟩ z) 
  ∎)
coterm-sub-weaken-lemma {Γ} σ (`S α) γ θ k = coterm-sub-weaken-lemma (sub-skip (λ Θ A → A ∣ Γ ⟶ Θ) σ) α γ θ k

coterm-sub-fmap-lemma : ∀ {Γ Θ Θ′ A B} (σ : Θ –[ (λ Θ A → A ∣ Γ ⟶ Θ) ]→ Θ′) (α : Θ ∋ A) γ θ k
  → (fmap {λ Θ A → A ∣ Γ ⟶ Θ} {λ Θ A → A ∣ Γ , B ⟶ Θ} (CotermSubstKit.wkΓ CK) σ α ⱽᴿ) ⟨ ⟨ γ , k ⟩ , θ ⟩ ≡ (σ α ⱽᴿ) ⟨ γ , θ ⟩
coterm-sub-fmap-lemma {Γ}{Θ}{Θ′}{A}{B} σ `Z γ θ k = ext (λ z → 
  begin
    (rename-coterm (λ x → `S x) (λ x → x) (σ `Z) ⱽᴿ) ⟨ ⟨ γ , k ⟩ , θ ⟩ z
  ≡⟨ ren-lemma-coterm (σ `Z) (λ x → `S x) (λ x → x) ⟨ γ , k ⟩ θ z ⟩
    (σ `Z ⱽᴿ) ⟨ ren-int-cbv Γ (Γ , B) (λ x → `S x) ⟨ γ , k ⟩ , neg-ren-int-cbv Θ′ Θ′ (λ x → x) θ ⟩ z
  ≡⟨ cong₂ (λ -₁ -₂ → (σ `Z ⱽᴿ) ⟨ -₁ , -₂ ⟩ z) (trans (weaken-ren-int-cbv-lemma (λ x → x) γ k) (id-ren γ)) (id-neg-ren θ) ⟩
    (σ `Z ⱽᴿ) ⟨ γ , θ ⟩ z
  ∎)
coterm-sub-fmap-lemma {Γ} σ (`S α) γ θ k = coterm-sub-fmap-lemma (sub-skip (λ Θ A → A ∣ Γ ⟶ Θ) σ) α γ θ k

weaken-coterm-sub-int-lemma : ∀ {Γ Θ Θ′ A} (σ : Θ –[ (λ Θ A → A ∣ Γ ⟶ Θ) ]→ Θ′) γ θ k
  → coterm-sub-int Γ Θ (Θ′ , A) (sub-weaken (CotermSubstKit.kit CK) σ) γ ⟨ θ , k ⟩ ≡ coterm-sub-int Γ Θ Θ′ σ γ θ
weaken-coterm-sub-int-lemma {Γ}{∅} σ γ θ k = refl
weaken-coterm-sub-int-lemma {Γ}{Θ , A}{Θ′} σ γ θ k = cong₂ (λ -₁ -₂ → ⟨ -₁ , -₂ ⟩) (weaken-coterm-sub-int-lemma (sub-skip (λ Θ A → A ∣ Γ ⟶ Θ) σ) γ θ k) (coterm-sub-weaken-lemma σ `Z γ θ k) 
   
lift-coterm-sub-int-lemma : ∀ {Γ Θ Θ′ A} (σ : Θ –[ (λ Θ A → A ∣ Γ ⟶ Θ) ]→ Θ′) γ θ k
  → coterm-sub-int Γ (Θ , A) (Θ′ , A) (sub-lift (CotermSubstKit.kit CK) σ) γ ⟨ θ , k ⟩ ≡ ⟨ coterm-sub-int Γ Θ Θ′ σ γ θ , k ⟩
lift-coterm-sub-int-lemma {Γ} {∅} {Θ′} σ γ θ k = refl
lift-coterm-sub-int-lemma {Γ} {Θ , x} {Θ′} σ γ θ k = cong₂ (λ -₁ -₂ → ⟨ ⟨ -₁ , -₂ ⟩ , k ⟩) (weaken-coterm-sub-int-lemma (sub-skip (λ Θ A → A ∣ Γ ⟶ Θ) σ) γ θ k) (coterm-sub-weaken-lemma σ `Z γ θ k)

fmap-coterm-sub-int-lemma : ∀ {Γ Θ Θ′ A} (σ : Θ –[ (λ Θ A → A ∣ Γ ⟶ Θ) ]→ Θ′) γ θ k
  → coterm-sub-int (Γ , A) Θ Θ′ (fmap {λ Θ B → B ∣ Γ ⟶ Θ} {λ Θ B → B ∣ (Γ , A) ⟶ Θ} (CotermSubstKit.wkΓ CK) σ) ⟨ γ , k ⟩ θ ≡ coterm-sub-int Γ Θ Θ′ σ γ θ
fmap-coterm-sub-int-lemma {Γ}{∅}{Θ′} σ γ θ k = refl 
fmap-coterm-sub-int-lemma {Γ}{Θ , A}{Θ′} σ γ θ k = cong₂ (λ -₁ -₂ → ⟨ -₁ , -₂ ⟩) (fmap-coterm-sub-int-lemma (sub-skip (λ Θ A → A ∣ Γ ⟶ Θ) σ) γ θ k) (coterm-sub-fmap-lemma σ `Z γ θ k) 

id-coterm-sub-int : ∀ Γ Θ γ θ → coterm-sub-int Γ Θ Θ id-coterm γ θ ≡ θ
id-coterm-sub-int Γ ∅ γ θ = refl
id-coterm-sub-int Γ (Θ , A) γ ⟨ θ , k ⟩ = cong (λ - → ⟨ - , k ⟩) 
  (begin 
    coterm-sub-int Γ Θ (Θ , A) (λ z → id-coterm (`S z)) γ ⟨ θ , k ⟩
  ≡⟨ weaken-coterm-sub-int-lemma id-coterm γ θ k ⟩ 
    coterm-sub-int Γ Θ Θ (λ z → id-coterm z) γ θ
  ≡⟨ id-coterm-sub-int Γ Θ γ θ ⟩
    θ
  ∎)


--The Substitution Lemma--
--The interpretation of substituted sequent applied to some contexts is equivalent to the interpretation of the sequent applied 
--to the interpretation of the substitutions applied to each of the contexts--

--Variables and Covariables--
sub-lemma-var : ∀ {Γ Γ′ Θ′ A} (s : Γ –[ (λ Γ A → TermValue Γ Θ′ A) ]→ Γ′) (x : Γ ∋ A) (γ : Γ′ ⱽˣ) (θ : (`¬ˣ Θ′) ⱽˣ ) →
  (proj₁ (s x) ⱽᴸ) ⟨ γ , θ ⟩ ≡ (λ k → k ((x ⱽⱽ) (termvalue-sub-int Γ Γ′ Θ′ s θ γ)))

sub-lemma-var s `Z γ θ = cps-value (proj₁ (s `Z)) (proj₂ (s `Z)) ⟨ γ , θ ⟩
sub-lemma-var {Γ}{Γ′}{Θ′} s (`S x) γ θ = sub-lemma-var (sub-skip (λ Γ A → TermValue Γ Θ′ A) s) x γ θ

sub-lemma-covar : ∀ {Γ′ Θ Θ′ A} (t : Θ –[ (λ Θ A → A ∣ Γ′ ⟶ Θ) ]→ Θ′) (α : Θ ∋ A) (γ : Γ′ ⱽˣ) (θ : (`¬ˣ Θ′) ⱽˣ ) → 
  (t α ⱽᴿ) ⟨ γ , θ ⟩ ≡ (Γ∋A⇒¬Γ∋¬A α ⱽⱽ) (coterm-sub-int Γ′ Θ Θ′ t γ θ)
sub-lemma-covar t `Z γ θ = refl
sub-lemma-covar {Γ′} t (`S α) γ θ = sub-lemma-covar (sub-skip (λ Θ A → A ∣ Γ′ ⟶ Θ) t) α γ θ

--Sequents--
sub-lemma-term : ∀ {Γ Γ′ Θ Θ′ A} (s : Γ –[ (λ Γ A → TermValue Γ Θ′ A) ]→ Γ′) (t : Θ –[ (λ Θ A → A ∣ Γ′ ⟶ Θ) ]→ Θ′) (M : Γ ⟶ Θ ∣ A) (γ : Γ′ ⱽˣ) (θ : (`¬ˣ Θ′) ⱽˣ ) →
  ((sub-term TVK CK s t M) ⱽᴸ) ⟨ γ , θ ⟩ ≡ (M ⱽᴸ) ⟨ termvalue-sub-int Γ Γ′ Θ′ s θ γ , coterm-sub-int Γ′ Θ Θ′ t γ θ ⟩

sub-lemma-coterm : ∀ {Γ Γ′ Θ Θ′ A} (s : Γ –[ (λ Γ A → TermValue Γ Θ′ A) ]→ Γ′) (t : Θ –[ (λ Θ A → A ∣ Γ′ ⟶ Θ) ]→ Θ′) (K : A ∣ Γ ⟶ Θ) (γ : Γ′ ⱽˣ) (θ : (`¬ˣ Θ′) ⱽˣ ) →
  ((sub-coterm TVK CK s t K) ⱽᴿ) ⟨ γ , θ ⟩ ≡ (K ⱽᴿ) ⟨ termvalue-sub-int Γ Γ′ Θ′ s θ γ , coterm-sub-int Γ′ Θ Θ′ t γ θ ⟩

sub-lemma-statement : ∀ {Γ Γ′ Θ Θ′} (s : Γ –[ (λ Γ A → TermValue Γ Θ′ A) ]→ Γ′) (t : Θ –[ (λ Θ A → A ∣ Γ′ ⟶ Θ) ]→ Θ′) (S : Γ ↦ Θ) (γ : Γ′ ⱽˣ) (θ : (`¬ˣ Θ′) ⱽˣ ) →
  ((sub-statement TVK CK s t S) ⱽˢ) ⟨ γ , θ ⟩ ≡ (S ⱽˢ) ⟨ termvalue-sub-int Γ Γ′ Θ′ s θ γ , coterm-sub-int Γ′ Θ Θ′ t γ θ ⟩

sub-lemma-term s t (` x) γ θ = sub-lemma-var s x γ θ
sub-lemma-term {Γ}{Γ′}{Θ}{Θ′} s t `⟨ M , N ⟩ γ θ = ext (λ k → trans 
  (cong (λ - → - (λ x → (sub-term TVK CK s t N ⱽᴸ) ⟨ γ , θ ⟩ (λ y → k ⟨ x , y ⟩))) (sub-lemma-term s t M γ θ)) 
  (cong (λ - → (M ⱽᴸ) ⟨ termvalue-sub-int Γ Γ′ Θ′ s θ γ , coterm-sub-int Γ′ Θ Θ′ t γ θ ⟩ (λ x → - (λ y → k ⟨ x , y ⟩))) (sub-lemma-term s t N γ θ)))
sub-lemma-term s t inl⟨ M ⟩ γ θ = ext (λ k → cong (λ - → - (λ x → k (inj₁ x))) (sub-lemma-term s t M γ θ))
sub-lemma-term s t inr⟨ M ⟩ γ θ = ext (λ k → cong (λ - → - (λ x → k (inj₂ x))) (sub-lemma-term s t M γ θ))
sub-lemma-term s t not[ K ] γ θ = ext (λ k → cong k (sub-lemma-coterm s t K γ θ))
sub-lemma-term {Γ}{Γ′}{Θ}{Θ′}{A} s t (μθ S) γ θ = ext (λ k → 
  begin
    (sub-statement TVK CK 
    (fmap {λ Γ B → TermValue Γ Θ′ B} {λ Γ B → TermValue Γ (Θ′ , A) B} (TermSubstKit.wkΘ TVK) s)
    (sub-lift (CotermSubstKit.kit CK) t)
    S ⱽˢ) ⟨ γ , ⟨ θ , k ⟩ ⟩
  ≡⟨ sub-lemma-statement (fmap {λ Γ B → TermValue Γ Θ′ B} {λ Γ B → TermValue Γ (Θ′ , A) B} (TermSubstKit.wkΘ TVK) s) (sub-lift (CotermSubstKit.kit CK) t) S γ ⟨ θ , k ⟩ ⟩
    (S ⱽˢ) 
    ⟨ termvalue-sub-int Γ Γ′ (Θ′ , A) (fmap {λ Γ B → TermValue Γ Θ′ B} {λ Γ B → TermValue Γ (Θ′ , A) B} (TermSubstKit.wkΘ TVK) s) ⟨ θ , k ⟩ γ , 
    ⟨ coterm-sub-int Γ′ Θ (Θ′ , A) (sub-weaken (CotermSubstKit.kit CK) t) γ ⟨ θ , k ⟩ , k ⟩ ⟩
  ≡⟨ cong (λ - → (S ⱽˢ) ⟨ termvalue-sub-int Γ Γ′ (Θ′ , A) (fmap {λ Γ B → TermValue Γ Θ′ B} {λ Γ B → TermValue Γ (Θ′ , A) B} (TermSubstKit.wkΘ TVK) s) ⟨ θ , k ⟩ γ , ⟨ - , k ⟩ ⟩) (weaken-coterm-sub-int-lemma t γ θ k) ⟩
    (S ⱽˢ) 
    ⟨ termvalue-sub-int Γ Γ′ (Θ′ , A) (fmap {λ Γ B → TermValue Γ Θ′ B} {λ Γ B → TermValue Γ (Θ′ , A) B} (TermSubstKit.wkΘ TVK) s) ⟨ θ , k ⟩ γ ,     
    ⟨ coterm-sub-int Γ′ Θ Θ′ t γ θ , k ⟩ ⟩ 
  ≡⟨ cong (λ - → (S ⱽˢ) ⟨ - , ⟨ coterm-sub-int Γ′ Θ Θ′ t γ θ , k ⟩ ⟩) (fmap-termvalue-sub-int-lemma s γ θ k) ⟩
    (S ⱽˢ) ⟨ termvalue-sub-int Γ Γ′ Θ′ s θ γ , ⟨ coterm-sub-int Γ′ Θ Θ′ t γ θ , k ⟩ ⟩
  ∎)

sub-lemma-coterm s t (` α) γ θ = sub-lemma-covar t α γ θ
sub-lemma-coterm s t fst[ K ] γ θ = cong (λ - → λ { ⟨ x , _ ⟩ → - x }) (sub-lemma-coterm s t K γ θ)
sub-lemma-coterm s t snd[ K ] γ θ = cong (λ - → λ { ⟨ _ , y ⟩ → - y }) (sub-lemma-coterm s t K γ θ)
sub-lemma-coterm {Γ} {Γ′} {Θ} {Θ′} {A `+ B} s t `[ K , L ] γ θ = ext (λ{(inj₁ x) → cong (λ - → - x) (sub-lemma-coterm s t K γ θ) ; (inj₂ y) → cong (λ - → - y) (sub-lemma-coterm s t L γ θ)})
sub-lemma-coterm s t not⟨ M ⟩ γ θ = sub-lemma-term s t M γ θ
sub-lemma-coterm {Γ}{Γ′}{Θ}{Θ′}{A} s t (μγ S) γ θ = ext (λ x → 
  begin 
    (sub-statement TVK CK
    (sub-lift (TermSubstKit.kit TVK) s)
    (fmap {λ Θ B → B ∣ Γ′ ⟶ Θ} {λ Θ B → B ∣ Γ′ , A ⟶ Θ} (CotermSubstKit.wkΓ CK) t)
    S ⱽˢ) ⟨ ⟨ γ , x ⟩ , θ ⟩
  ≡⟨ sub-lemma-statement (sub-lift (TermSubstKit.kit TVK) s) (fmap {λ Θ B → B ∣ Γ′ ⟶ Θ} {λ Θ B → B ∣ Γ′ , A ⟶ Θ} (CotermSubstKit.wkΓ CK) t) S ⟨ γ , x ⟩ θ ⟩
    (S ⱽˢ)
    ⟨ ⟨ termvalue-sub-int Γ (Γ′ , A) Θ′ (sub-weaken (TermSubstKit.kit TVK) s) θ ⟨ γ , x ⟩ , x ⟩ ,
    coterm-sub-int (Γ′ , A) Θ Θ′ (fmap {λ Θ B → B ∣ Γ′ ⟶ Θ} {λ Θ B → B ∣ Γ′ , A ⟶ Θ} (CotermSubstKit.wkΓ CK) t) ⟨ γ , x ⟩ θ ⟩
  ≡⟨ cong (λ - → (S ⱽˢ) ⟨ ⟨ - , x ⟩ , coterm-sub-int (Γ′ , A) Θ Θ′ (fmap {λ Θ B → B ∣ Γ′ ⟶ Θ} {λ Θ B → B ∣ Γ′ , A ⟶ Θ} (CotermSubstKit.wkΓ CK) t) ⟨ γ , x ⟩ θ ⟩) (weaken-termvalue-sub-int-lemma s γ θ x) ⟩
    (S ⱽˢ)
    ⟨ ⟨ termvalue-sub-int Γ Γ′ Θ′ s θ γ , x ⟩ , 
    coterm-sub-int (Γ′ , A) Θ Θ′ (fmap {λ Θ B → B ∣ Γ′ ⟶ Θ} {λ Θ B → B ∣ Γ′ , A ⟶ Θ} (CotermSubstKit.wkΓ CK) t) ⟨ γ , x ⟩ θ ⟩
  ≡⟨ cong (λ - → (S ⱽˢ) ⟨ ⟨ termvalue-sub-int Γ Γ′ Θ′ s θ γ , x ⟩ , - ⟩) (fmap-coterm-sub-int-lemma t γ θ x) ⟩
   (S ⱽˢ) ⟨ ⟨ termvalue-sub-int Γ Γ′ Θ′ s θ γ , x ⟩ , coterm-sub-int Γ′ Θ Θ′ t γ θ ⟩
  ∎)

sub-lemma-statement {Γ} {Γ′} {Θ} {Θ′} s t (M ● K) γ θ = 
  begin
    (sub-term TVK CK s t M ⱽᴸ) ⟨ γ , θ ⟩ ((sub-coterm TVK CK s t K ⱽᴿ) ⟨ γ , θ ⟩)
  ≡⟨ cong (λ - → - ((sub-coterm TVK CK s t K ⱽᴿ) ⟨ γ , θ ⟩)) (sub-lemma-term s t M γ θ) ⟩
    (M ⱽᴸ) ⟨ termvalue-sub-int Γ Γ′ Θ′ s θ γ , coterm-sub-int Γ′ Θ Θ′ t γ θ ⟩ ((sub-coterm TVK CK s t K ⱽᴿ) ⟨ γ , θ ⟩)
  ≡⟨ cong (λ - → (M ⱽᴸ) ⟨ termvalue-sub-int Γ Γ′ Θ′ s θ γ , coterm-sub-int Γ′ Θ Θ′ t γ θ ⟩ -) (sub-lemma-coterm s t K γ θ) ⟩
    (M ⱽᴸ) ⟨ termvalue-sub-int Γ Γ′ Θ′ s θ γ , coterm-sub-int Γ′ Θ Θ′ t γ θ ⟩ ((K ⱽᴿ) ⟨ termvalue-sub-int Γ Γ′ Θ′ s θ γ , coterm-sub-int Γ′ Θ Θ′ t γ θ ⟩)
  ∎
  

--Lemma for Soundness of the CPS Transformation--
--If a given Sequent steps to another different Sequent then the CPS Transformation of those two Sequents are equivalent

--Statements
S⟶ⱽT⇒Sⱽ≡Tⱽ : ∀ {Γ Θ} (S T : Γ ↦ Θ) (c : (Γ ᵒˣ) ᴺˣ × `¬ˣ (Θ ᵒˣ) ᴺˣ) → S ˢ⟶ⱽ T → (S ⱽˢ) c ≡ (T ⱽˢ) c
S⟶ⱽT⇒Sⱽ≡Tⱽ (`⟨ V , W ⟩ ● fst[ K ]) (V ● K) c (β×₁ v w) = cong ((V ⱽᴸ) c) (ext (λ x → cong (λ - → - (λ y → (K ⱽᴿ) c x)) (cps-value W w c)))
S⟶ⱽT⇒Sⱽ≡Tⱽ (`⟨ V , W ⟩ ● snd[ L ]) (W ● L) c (β×₂ v w) = cong (λ - → - (λ x → (W ⱽᴸ) c (λ y → (L ⱽᴿ) c y))) (cps-value V v c)
S⟶ⱽT⇒Sⱽ≡Tⱽ (inl⟨ V ⟩ ● `[ K , L ]) (V ● K) c (β+₁ v) = cong ((V ⱽᴸ) c) refl
S⟶ⱽT⇒Sⱽ≡Tⱽ (inr⟨ W ⟩ ● `[ K , L ]) (W ● L) c (β+₂ w) = cong ((W ⱽᴸ) c) refl
S⟶ⱽT⇒Sⱽ≡Tⱽ (not[ K ] ● not⟨ M ⟩) (M ● K) c (β¬) = refl
S⟶ⱽT⇒Sⱽ≡Tⱽ {Γ} {Θ} (V ● μγ {Γ}{Θ}{A} S) .(S ⱽ⟨ ⟨ V , v ⟩ /⟩ˢ) ⟨ c₁ , c₂ ⟩ (βL v) = sym (
  begin
    ((S ⱽ⟨ ⟨ V , v ⟩ /⟩ˢ) ⱽˢ) ⟨ c₁ , c₂ ⟩
  ≡⟨⟩
    (sub-statement TVK CK (add (λ Γ A → TermValue Γ Θ A) ⟨ V , v ⟩ id-termvalue) id-coterm S ⱽˢ) ⟨ c₁ , c₂ ⟩
  ≡⟨ sub-lemma-statement (add (λ Γ A → TermValue Γ Θ A) ⟨ V , v ⟩ id-termvalue) id-coterm S c₁ c₂ ⟩
    (S ⱽˢ) ⟨ termvalue-sub-int (Γ , A) Γ Θ (add (λ Γ A → TermValue Γ Θ A) ⟨ V , v ⟩ id-termvalue) c₂ c₁ , coterm-sub-int Γ Θ Θ id-coterm c₁ c₂ ⟩
  ≡⟨ cong (λ - → (S ⱽˢ) ⟨ ⟨ termvalue-sub-int Γ Γ Θ (λ x → id-termvalue x) c₂ c₁ , (⟨ V , v ⟩ ⱽᴸⱽ) ⟨ c₁ , c₂ ⟩ ⟩ , - ⟩) (id-coterm-sub-int Γ Θ c₁ c₂) ⟩
    (S ⱽˢ) ⟨ ⟨ termvalue-sub-int Γ Γ Θ (λ x → id-termvalue x) c₂ c₁ , (⟨ V , v ⟩ ⱽᴸⱽ) ⟨ c₁ , c₂ ⟩ ⟩ , c₂ ⟩
  ≡⟨ cong (λ - → (S ⱽˢ) ⟨ ⟨ - , (⟨ V , v ⟩ ⱽᴸⱽ) ⟨ c₁ , c₂ ⟩ ⟩ , c₂ ⟩) (id-termvalue-sub-int Γ Θ c₁ c₂) ⟩
    (S ⱽˢ) ⟨ ⟨ c₁ , (⟨ V , v ⟩ ⱽᴸⱽ) ⟨ c₁ , c₂ ⟩ ⟩ , c₂ ⟩
  ≡⟨ sym (cong (λ - → - (λ x → (S ⱽˢ) ⟨ ⟨ c₁ , x ⟩ , c₂ ⟩)) (cps-value V v ⟨ c₁ , c₂ ⟩)) ⟩
    (V ⱽᴸ) ⟨ c₁ , c₂ ⟩ (λ x → (S ⱽˢ) ⟨ ⟨ c₁ , x ⟩ , c₂ ⟩)
  ∎)
S⟶ⱽT⇒Sⱽ≡Tⱽ {Γ}{Θ}(μθ {Γ}{Θ}{A} S ● K) .(S [ K /]ˢ) ⟨ c₁ , c₂ ⟩ (βR) = sym (
  begin
    ((S [ K /]ˢ) ⱽˢ) ⟨ c₁ , c₂ ⟩
  ≡⟨⟩
    (sub-statement TVK CK id-termvalue (add (λ Θ A → A ∣ Γ ⟶ Θ) K id-coterm) S ⱽˢ) ⟨ c₁ , c₂ ⟩
  ≡⟨ sub-lemma-statement id-termvalue ((add (λ Θ A → A ∣ Γ ⟶ Θ) K id-coterm)) S c₁ c₂ ⟩
    (S ⱽˢ) ⟨ (termvalue-sub-int Γ Γ Θ id-termvalue c₂ c₁) , (coterm-sub-int Γ (Θ , A) Θ (add (λ Θ A → A ∣ Γ ⟶ Θ) K id-coterm) c₁ c₂) ⟩
  ≡⟨ cong (λ - → (S ⱽˢ) ⟨ - , coterm-sub-int Γ (Θ , A) Θ (add (λ Θ A → A ∣ Γ ⟶ Θ) K id-coterm) c₁ c₂ ⟩) (id-termvalue-sub-int Γ Θ c₁ c₂) ⟩
    (S ⱽˢ) ⟨ c₁ , (coterm-sub-int Γ (Θ , A) Θ (add (λ Θ A → A ∣ Γ ⟶ Θ) K id-coterm) c₁ c₂) ⟩
  ≡⟨ cong (λ - → (S ⱽˢ) ⟨ c₁ , ⟨ - , (K ⱽᴿ) ⟨ c₁ , c₂ ⟩ ⟩ ⟩) (id-coterm-sub-int Γ Θ c₁ c₂) ⟩
    (S ⱽˢ) ⟨ c₁ , ⟨ c₂ , (K ⱽᴿ) ⟨ c₁ , c₂ ⟩ ⟩ ⟩
  ∎)

--Terms--
M⟶ⱽN⇒Mⱽ≡Nⱽ : ∀ {Γ Θ A} (M N : Γ ⟶ Θ ∣ A) (c : (Γ ᵒˣ) ᴺˣ × `¬ˣ (Θ ᵒˣ) ᴺˣ) (k : ((`¬ A) ⱽᵀ)) → M ᵗ⟶ⱽ N → (M ⱽᴸ) c k ≡ (N ⱽᴸ) c k
M⟶ⱽN⇒Mⱽ≡Nⱽ {Γ} {Θ} {A} M .(μθ (rename-term id-var (rename-weaken id-var) M ● ` `Z)) ⟨ c₁ , c₂ ⟩ k ηR = 
  begin
    (M ⱽᴸ) ⟨ c₁ , c₂ ⟩ k
  ≡⟨ cong (λ - → (M ⱽᴸ) ⟨ c₁ , - ⟩ k) (sym (trans (weaken-neg-ren-int-cbv-lemma id-var c₂ k) (id-neg-ren c₂))) ⟩
    (M ⱽᴸ) ⟨ c₁ , neg-ren-int-cbv Θ (Θ , A) (rename-weaken id-var) ⟨ c₂ , k ⟩ ⟩ k
  ≡⟨ cong (λ - → (M ⱽᴸ) ⟨ - , neg-ren-int-cbv Θ (Θ , A) (rename-weaken id-var) ⟨ c₂ , k ⟩ ⟩ k) (sym (id-ren c₁)) ⟩
    (M ⱽᴸ) ⟨ ren-int-cbv Γ Γ id-var c₁ , neg-ren-int-cbv Θ (Θ , A) (rename-weaken id-var) ⟨ c₂ , k ⟩ ⟩ k
  ≡⟨ sym (ren-lemma-term M id-var (rename-weaken id-var) c₁ ⟨ c₂ , k ⟩ k) ⟩
    (rename-term id-var (rename-weaken id-var) M ⱽᴸ) ⟨ c₁ , ⟨ c₂ , k ⟩ ⟩ k
  ∎

--Coterms--
K⟶ⱽL⇒Kⱽ≡Lⱽ : ∀ {Γ Θ A} (K L : A ∣ Γ ⟶ Θ) (c : (Γ ᵒˣ) ᴺˣ × `¬ˣ (Θ ᵒˣ) ᴺˣ) (k : (A) ⱽᵀ) → K ᶜ⟶ⱽ L → (K ⱽᴿ) c k ≡ (L ⱽᴿ) c k
K⟶ⱽL⇒Kⱽ≡Lⱽ {Γ}{Θ}{A} K .(μγ (` `Z ● rename-coterm (rename-weaken id-var) id-var K)) ⟨ c₁ , c₂ ⟩ k ηL =
  begin
    (K ⱽᴿ) ⟨ c₁ , c₂ ⟩ k
  ≡⟨ cong (λ - → (K ⱽᴿ) ⟨ - , c₂ ⟩ k) (sym (trans (weaken-ren-int-cbv-lemma id-var c₁ k) (id-ren c₁))) ⟩
    (K ⱽᴿ) ⟨ ren-int-cbv Γ (Γ , A) ((rename-weaken id-var)) ⟨ c₁ , k ⟩ , c₂ ⟩ k
  ≡⟨ cong (λ - → (K ⱽᴿ) ⟨ ren-int-cbv Γ (Γ , A) (rename-weaken id-var) ⟨ c₁ , k ⟩ , - ⟩ k) (sym (id-neg-ren c₂)) ⟩
    (K ⱽᴿ) ⟨ ren-int-cbv Γ (Γ , A) ((rename-weaken id-var)) ⟨ c₁ , k ⟩ , neg-ren-int-cbv Θ Θ id-var c₂ ⟩ k
  ≡⟨ sym(ren-lemma-coterm K (rename-weaken id-var) id-var ⟨ c₁ , k ⟩ c₂ k) ⟩
    (rename-coterm (rename-weaken id-var) id-var K ⱽᴿ) ⟨ ⟨ c₁ , k ⟩ , c₂ ⟩ k
  ∎ 
 
--Soundness of the CPS Transformation--
--If a given sequent eventually reduces to another sequent then the CPS Transformations of those two sequents are equivalent

S—↠ⱽT⇒Sⱽ≡Tⱽ : ∀ {Γ Θ} (S T : Γ ↦ Θ) (c : (Γ ᵒˣ) ᴺˣ × `¬ˣ (Θ ᵒˣ) ᴺˣ) → S ˢ—↠ⱽ T → (S ⱽˢ) c ≡ (T ⱽˢ) c
S—↠ⱽT⇒Sⱽ≡Tⱽ S .S c (.S ∎ˢⱽ) = refl
S—↠ⱽT⇒Sⱽ≡Tⱽ S T c ( _ˢ⟶ⱽ⟨_⟩_ .S {S′} {T} S⟶S′ S′↠T) = trans (S⟶ⱽT⇒Sⱽ≡Tⱽ S S′ c S⟶S′) (S—↠ⱽT⇒Sⱽ≡Tⱽ S′ T c S′↠T)

M—↠ⱽN⇒Mⱽ≡Nⱽ : ∀ {Γ Θ A} (M N : Γ ⟶ Θ ∣ A) (c : (Γ ᵒˣ) ᴺˣ × `¬ˣ (Θ ᵒˣ) ᴺˣ) (k : ((`¬ A) ⱽᵀ)) → M ᵗ—↠ⱽ N → (M ⱽᴸ) c k ≡ (N ⱽᴸ) c k
M—↠ⱽN⇒Mⱽ≡Nⱽ M .M c k (.M ∎ᵗⱽ) = refl
M—↠ⱽN⇒Mⱽ≡Nⱽ M N c k ( _ᵗ⟶ⱽ⟨_⟩_ .M {M′} {N} M⟶M′ M′↠N) = trans (M⟶ⱽN⇒Mⱽ≡Nⱽ M M′ c k M⟶M′) (M—↠ⱽN⇒Mⱽ≡Nⱽ M′ N c k M′↠N)

K—↠ⱽL⇒Kⱽ≡Lⱽ : ∀ {Γ Θ A} (K L : A ∣ Γ ⟶ Θ) (c : (Γ ᵒˣ) ᴺˣ × `¬ˣ (Θ ᵒˣ) ᴺˣ) (k : (A) ⱽᵀ) → K ᶜ—↠ⱽ L → (K ⱽᴿ) c k ≡ (L ⱽᴿ) c k
K—↠ⱽL⇒Kⱽ≡Lⱽ K .K c k (.K ∎ᶜⱽ) = refl
K—↠ⱽL⇒Kⱽ≡Lⱽ K L c k (_ᶜ⟶ⱽ⟨_⟩_ .K {K′} {L} K⟶K′ K′↠L) = trans (K⟶ⱽL⇒Kⱽ≡Lⱽ K K′ c k K⟶K′) (K—↠ⱽL⇒Kⱽ≡Lⱽ K′ L c k K′↠L)