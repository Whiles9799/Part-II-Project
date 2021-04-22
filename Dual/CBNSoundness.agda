{-# OPTIONS --rewriting #-}

module Dual.CBNSoundness (R : Set) where

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

weaken-ren-int-cbn-lemma : ∀ {Θ Θ′ A} (ρ : Θ ↝ Θ′) θ k → ren-int-cbn Θ (Θ′ , A) (ren-weaken ρ) ⟨ θ , k ⟩ ≡ ren-int-cbn Θ Θ′ ρ θ
weaken-ren-int-cbn-lemma {∅} ρ θ k = refl
weaken-ren-int-cbn-lemma {Θ , B}{Θ′}{A} ρ θ k = cong (λ - → ⟨ - , (ρ `Z ᴺⱽ) θ ⟩) (weaken-ren-int-cbn-lemma (λ z → ρ (`S z)) θ k)

lift-ren-int-cbn-lemma : ∀ {Θ Θ′ A} (ρ : Θ ↝ Θ′) θ k → ren-int-cbn (Θ , A) (Θ′ , A) (ren-lift ρ) ⟨ θ , k ⟩ ≡ ⟨ (ren-int-cbn Θ Θ′ ρ θ) , k ⟩
lift-ren-int-cbn-lemma {∅} ρ θ k = refl
lift-ren-int-cbn-lemma {Θ , B}{Θ′}{A} ρ θ k = cong (λ - → ⟨ ⟨ - , (ρ `Z ᴺⱽ) θ ⟩ , k ⟩) (weaken-ren-int-cbn-lemma (λ z → ρ (`S z)) θ k)

id-ren : ∀ Θ θ → ren-int-cbn Θ Θ (id-var) θ ≡ θ
id-ren ∅ θ = refl
id-ren (Θ , A) ⟨ θ , α ⟩ = cong (λ - → ⟨ - , α ⟩) (trans (weaken-ren-int-cbn-lemma (id-var) θ α) (id-ren Θ θ))

weaken-neg-ren-int-cbn-lemma : ∀ {Γ Γ′ A} (ρ : Γ ↝ Γ′) γ k → neg-ren-int-cbn Γ (Γ′ , A) (ren-weaken ρ) ⟨ γ , k ⟩ ≡ neg-ren-int-cbn Γ Γ′ ρ γ
weaken-neg-ren-int-cbn-lemma {∅} ρ γ k = refl
weaken-neg-ren-int-cbn-lemma {Γ , B}{Γ′}{A} ρ γ k = cong (λ - → ⟨ - , (Γ∋A⇒¬Γ∋¬A (ρ `Z) ᴺⱽ) γ ⟩) (weaken-neg-ren-int-cbn-lemma (λ z → ρ (`S z)) γ k)

lift-neg-ren-int-cbn-lemma : ∀ {Γ Γ′ A} (ρ : Γ ↝ Γ′) γ k → neg-ren-int-cbn (Γ , A) (Γ′ , A) (ren-lift ρ) ⟨ γ , k ⟩ ≡ ⟨ (neg-ren-int-cbn Γ Γ′ ρ γ) , k ⟩
lift-neg-ren-int-cbn-lemma {∅} ρ γ k = refl
lift-neg-ren-int-cbn-lemma {Γ , B}{Γ′}{A} ρ γ k = cong (λ - → ⟨ ⟨ - , (Γ∋A⇒¬Γ∋¬A (ρ `Z) ᴺⱽ) γ ⟩ , k ⟩) (weaken-neg-ren-int-cbn-lemma (λ z → ρ (`S z)) γ k)

id-neg-ren : ∀ Γ γ → neg-ren-int-cbn Γ Γ (id-var) γ ≡ γ
id-neg-ren ∅ γ = refl
id-neg-ren (Γ , A) ⟨ γ , α ⟩ = cong (λ - → ⟨ - , α ⟩) (trans (weaken-neg-ren-int-cbn-lemma (id-var) γ α) (id-neg-ren Γ γ))

ren-lemma-var : ∀ {Γ Γ′ A} (x : Γ ∋ A) (s : Γ ↝ Γ′) (γ : `¬ˣ Γ′ ᴺˣ)
  → (Γ∋A⇒¬Γ∋¬A (s x) ᴺⱽ) γ ≡ (Γ∋A⇒¬Γ∋¬A x ᴺⱽ) (neg-ren-int-cbn Γ Γ′ s γ)
ren-lemma-var `Z s γ = refl
ren-lemma-var (`S x) s γ = ren-lemma-var x (λ z → s (`S z)) γ

ren-lemma-covar : ∀ {Θ Θ′ A} (α : Θ ∋ A) (t : Θ ↝ Θ′) (θ : Θ′ ᴺˣ)
  → (t α ᴺⱽ) θ ≡ (α ᴺⱽ) (ren-int-cbn Θ Θ′ t θ)
ren-lemma-covar `Z s γ = refl
ren-lemma-covar (`S α) s γ = ren-lemma-covar α (λ z → s (`S z)) γ

ren-lemma-T : ∀ {Γ Γ′ Θ Θ′ A} (M : Γ ⟶ Θ ∣ A) (s : Γ ↝ Γ′) (t : Θ ↝ Θ′) (γ : `¬ˣ Γ′ ᴺˣ) (θ : Θ′ ᴺˣ) (k : (A ᴺᵀ))
  → (ren-T s t M ᴺᴸ) ⟨ θ , γ ⟩ k ≡ (M ᴺᴸ) ⟨ ren-int-cbn Θ Θ′ t θ , neg-ren-int-cbn Γ Γ′ s γ ⟩ k 
ren-lemma-C : ∀ {Γ Γ′ Θ Θ′ A} (K : A ∣ Γ ⟶ Θ) (s : Γ ↝ Γ′) (t : Θ ↝ Θ′) (γ : `¬ˣ Γ′ ᴺˣ) (θ : Θ′ ᴺˣ) (k : (`¬ A) ᴺᵀ)
  → (ren-C s t K ᴺᴿ) ⟨ θ , γ ⟩ k ≡ (K ᴺᴿ) ⟨ ren-int-cbn Θ Θ′ t θ , neg-ren-int-cbn Γ Γ′ s γ ⟩ k
ren-lemma-CV : ∀ {Γ Γ′ Θ Θ′ A} (P : CotermValue Γ Θ A) (s : Γ ↝ Γ′) (t : Θ ↝ Θ′) (γ : `¬ˣ Γ′ ᴺˣ) (θ : Θ′ ᴺˣ)
  → (⟨ ren-C s t (proj₁ P) , CV-ren s t (proj₂ P) ⟩ ᴺᴿⱽ) ⟨ θ , γ ⟩ ≡ (P ᴺᴿⱽ) ⟨ ren-int-cbn Θ Θ′ t θ , neg-ren-int-cbn Γ Γ′ s γ ⟩
ren-lemma-S : ∀ {Γ Γ′ Θ Θ′} (S : Γ ↦ Θ) (s : Γ ↝ Γ′) (t : Θ ↝ Θ′) (γ : `¬ˣ Γ′ ᴺˣ) (θ : Θ′ ᴺˣ)
  → (ren-S s t S ᴺˢ) ⟨ θ , γ ⟩ ≡ (S ᴺˢ) ⟨ ren-int-cbn Θ Θ′ t θ , neg-ren-int-cbn Γ Γ′ s γ ⟩

ren-lemma-T (` x) s t γ θ k = cong (λ - → - k) (ren-lemma-var x s γ)
ren-lemma-T {Γ}{Γ′}{Θ}{Θ′} `⟨ M , N ⟩ s t γ θ k = cong (λ - → - k) {(`⟨ ren-T s t M , ren-T s t N ⟩ ᴺᴸ) ⟨ θ , γ ⟩}{(`⟨ M , N ⟩ ᴺᴸ) ⟨ ren-int-cbn Θ Θ′ t θ , neg-ren-int-cbn Γ Γ′ s γ ⟩}
  (ext ((λ{(inj₁ x) → ren-lemma-T M s t γ θ x ; (inj₂ y) → ren-lemma-T N s t γ θ y })))
ren-lemma-T inl⟨ M ⟩ s t γ θ k = ren-lemma-T M s t γ θ (proj₁ k)
ren-lemma-T inr⟨ M ⟩ s t γ θ k = ren-lemma-T M s t γ θ (proj₂ k)
ren-lemma-T not[ K ] s t γ θ k = ren-lemma-C K s t γ θ k
ren-lemma-T {Γ}{Γ′}{Θ}{Θ′}{A} (μθ S) s t γ θ k = 
  begin
    (ren-S s (ren-lift t) S ᴺˢ) ⟨ ⟨ θ , k ⟩ , γ ⟩
  ≡⟨ ren-lemma-S S s (ren-lift t) γ ⟨ θ , k ⟩ ⟩
    (S ᴺˢ) ⟨ ⟨ ren-int-cbn Θ (Θ′ , A) (λ x → `S (t x)) ⟨ θ , k ⟩ , k ⟩ , neg-ren-int-cbn Γ Γ′ s γ ⟩
  ≡⟨ cong (λ - → (S ᴺˢ) ⟨ - , neg-ren-int-cbn Γ Γ′ s γ ⟩) (lift-ren-int-cbn-lemma t θ k) ⟩
    (S ᴺˢ) ⟨ ⟨ ren-int-cbn Θ Θ′ t θ , k ⟩ , neg-ren-int-cbn Γ Γ′ s γ ⟩
  ∎

ren-lemma-C (` α) s t γ θ k = cong k (ren-lemma-covar α t θ)
ren-lemma-C fst[ K ] s t γ θ k = ren-lemma-C K s t γ θ (λ x → k (inj₁ x))
ren-lemma-C snd[ K ] s t γ θ k = ren-lemma-C K s t γ θ (λ x → k (inj₂ x))
ren-lemma-C `[ K , L ] s t γ θ k = cong₂ (λ -₁ -₂ → -₁ (λ α → -₂ λ β → k ⟨ α , β ⟩)) (ext (λ x → ren-lemma-C K s t γ θ x)) (ext (λ x → ren-lemma-C L s t γ θ x))
ren-lemma-C not⟨ M ⟩ s t γ θ k = cong k (ext (λ x → ren-lemma-T M s t γ θ x))
ren-lemma-C {Γ}{Γ′}{Θ}{Θ′}{A} (μγ S) s t γ θ k = 
  begin
    (ren-S (ren-lift s) t S ᴺˢ) ⟨ θ , ⟨ γ , k ⟩ ⟩
  ≡⟨ ren-lemma-S S (ren-lift s) t ⟨ γ , k ⟩ θ ⟩
    (S ᴺˢ) ⟨ ren-int-cbn Θ Θ′ t θ , ⟨ neg-ren-int-cbn Γ (Γ′ , A) (λ x → `S (s x)) ⟨ γ , k ⟩ , k ⟩ ⟩ 
  ≡⟨ cong (λ - → (S ᴺˢ) ⟨ ren-int-cbn Θ Θ′ t θ , - ⟩ ) (lift-neg-ren-int-cbn-lemma s γ k) ⟩
    (S ᴺˢ) ⟨ ren-int-cbn Θ Θ′ t θ , ⟨ neg-ren-int-cbn Γ Γ′ s γ , k ⟩ ⟩
  ∎

ren-lemma-CV ⟨ ` α , CV-covar ⟩ s t γ θ = ren-lemma-covar α t θ
ren-lemma-CV ⟨ `[ P , Q ] , CV-sum p q ⟩ s t γ θ = cong₂ ⟨_,_⟩ (ren-lemma-CV ⟨ P , p ⟩ s t γ θ) (ren-lemma-CV ⟨ Q , q ⟩ s t γ θ)
ren-lemma-CV ⟨ fst[ P ] , CV-fst p ⟩ s t γ θ = cong inj₁ (ren-lemma-CV ⟨ P , p ⟩ s t γ θ)
ren-lemma-CV ⟨ snd[ P ] , CV-snd p ⟩ s t γ θ = cong inj₂ (ren-lemma-CV ⟨ P , p ⟩ s t γ θ)
ren-lemma-CV ⟨ not⟨ K ⟩ , CV-not ⟩ s t γ θ = ext (λ x → ren-lemma-T K s t γ θ x)

ren-lemma-S (M ● K) s t γ θ = cong₂ (λ -₁ -₂ → -₁ -₂) (ext (λ x → ren-lemma-C K s t γ θ x)) (ext (λ x → ren-lemma-T M s t γ θ x))


fmap-sub-T-int-lemma : ∀ {Γ Γ′ Θ A} (σ : Γ –[ (Fix₂ Term Θ) ]→ Γ′) θ γ α →
  sub-T-int Γ Γ′ (Θ , A) (fmap-wkΘᵗ Θ A σ) ⟨ θ , α ⟩ γ ≡ sub-T-int Γ Γ′ Θ σ θ γ
fmap-sub-T-int-lemma {∅} σ θ γ α = refl
fmap-sub-T-int-lemma {Γ , B}{Γ′}{Θ} σ θ γ α = cong₂ ⟨_,_⟩ 
  (fmap-sub-T-int-lemma (sub-skip (Fix₂ Term Θ) σ) θ γ α) 
  (ext (λ x → trans (ren-lemma-T (σ `Z) (id-var) (ren-weaken id-var) γ ⟨ θ , α ⟩ x) 
  (cong₂ (λ -₁ -₂ → (σ `Z ᴺᴸ) ⟨ -₁ , -₂ ⟩ x) (trans (weaken-ren-int-cbn-lemma (id-var) θ α) (id-ren Θ θ)) (id-neg-ren Γ′ γ))))

fmap-sub-CV-int-lemma : ∀ {Γ′ Θ Θ′ A} (σ : Θ –[ (Fix₁ CotermValue Γ′) ]→ Θ′) θ γ α →
  sub-CV-int (Γ′ , A) Θ Θ′ (fmap-wkΓᶜⱽ Γ′ A σ) ⟨ γ , α ⟩ θ ≡ sub-CV-int Γ′ Θ Θ′ σ γ θ
fmap-sub-CV-int-lemma {Γ′}{∅} σ θ γ α = refl
fmap-sub-CV-int-lemma {Γ′}{Θ , B}{Θ′} σ θ γ α = cong₂ ⟨_,_⟩ 
  (fmap-sub-CV-int-lemma (sub-skip (Fix₁ CotermValue Γ′) σ) θ γ α) 
  (trans (ren-lemma-CV (σ `Z) (ren-weaken id-var) id-var ⟨ γ , α ⟩ θ) 
  (cong₂ (λ -₁ -₂ → (σ `Z ᴺᴿⱽ) ⟨ -₁ , -₂ ⟩) (id-ren Θ′ θ) (trans (weaken-neg-ren-int-cbn-lemma (id-var) γ α) (id-neg-ren Γ′ γ))))

weaken-sub-T-int-lemma : ∀ {Γ Γ′ Θ A} (σ : Γ –[ (Fix₂ Term Θ) ]→ Γ′) θ γ α → 
  sub-T-int Γ (Γ′ , A) Θ (sub-weaken (TK.kit) σ) θ ⟨ γ , α ⟩ ≡ sub-T-int Γ Γ′ Θ σ θ γ
weaken-sub-T-int-lemma {∅} σ θ γ α = refl
weaken-sub-T-int-lemma {Γ , B}{Γ′}{Θ} σ θ γ α = cong₂ ⟨_,_⟩ 
  (weaken-sub-T-int-lemma (sub-skip (Fix₂ Term Θ) σ) θ γ α) 
  (ext (λ x → trans (ren-lemma-T (σ `Z) (ren-weaken id-var) id-var ⟨ γ , α ⟩ θ x) 
  (cong₂ (λ -₁ -₂ → (σ `Z ᴺᴸ) ⟨ -₁ , -₂ ⟩ x) (id-ren Θ θ) (trans (weaken-neg-ren-int-cbn-lemma id-var γ α) (id-neg-ren Γ′ γ)))))

weaken-sub-CV-int-lemma : ∀ {Γ′ Θ Θ′ A} (σ : Θ –[ (Fix₁ CotermValue Γ′) ]→ Θ′) θ γ α →
  sub-CV-int Γ′ Θ (Θ′ , A) (sub-weaken (CVK.kit) σ) γ ⟨ θ , α ⟩ ≡ sub-CV-int Γ′ Θ Θ′ σ γ θ
weaken-sub-CV-int-lemma {Γ′}{∅} σ θ γ α = refl
weaken-sub-CV-int-lemma {Γ′}{Θ , B}{Θ′} σ θ γ α = cong₂ ⟨_,_⟩ 
  (weaken-sub-CV-int-lemma (sub-skip (Fix₁ CotermValue Γ′) σ) θ γ α) 
  (trans (ren-lemma-CV (σ `Z) (id-var) (ren-weaken id-var) γ ⟨ θ , α ⟩) 
  (cong₂ (λ -₁ -₂ → (σ `Z ᴺᴿⱽ) ⟨ -₁ , -₂ ⟩) (trans (weaken-ren-int-cbn-lemma (id-var) θ α) (id-ren Θ′ θ)) (id-neg-ren Γ′ γ)))

id-sub-T : ∀ Γ Θ γ θ → sub-T-int Γ Γ Θ id-T θ γ ≡ γ
id-sub-T ∅ Θ tt θ = refl
id-sub-T (Γ , A) Θ ⟨ γ , x ⟩ θ = cong (λ - → ⟨ - , x ⟩) (trans (weaken-sub-T-int-lemma id-T θ γ x) (id-sub-T Γ Θ γ θ))

id-sub-CV : ∀ Γ Θ γ θ → sub-CV-int Γ Θ Θ id-CV γ θ ≡ θ
id-sub-CV Γ ∅ γ tt = refl
id-sub-CV Γ (Θ , A) γ ⟨ θ , α ⟩ = cong (λ - → ⟨ - , α ⟩) (trans (weaken-sub-CV-int-lemma id-CV θ γ α) (id-sub-CV Γ Θ γ θ))

sub-lemma-var : ∀ {Γ Γ′ Θ′ A} (x : Γ ∋ A) (s : Γ –[ (Fix₂ Term Θ′) ]→ Γ′) (γ : (`¬ˣ Γ′) ᴺˣ) (θ : Θ′ ᴺˣ) →
  (s x ᴺᴸ) ⟨ θ , γ ⟩ ≡ (Γ∋A⇒¬Γ∋¬A x ᴺⱽ) (sub-T-int Γ Γ′ Θ′ s θ γ)
sub-lemma-var `Z s γ θ = refl
sub-lemma-var {Γ}{Γ′}{Θ′} (`S x) s γ θ = sub-lemma-var x (sub-skip (Fix₂ Term Θ′) s) γ θ

sub-lemma-covar : ∀ {Γ′ Θ Θ′ A} (α : Θ ∋ A) (t : Θ –[ (Fix₁ CotermValue Γ′) ]→ Θ′) (γ : (`¬ˣ Γ′) ᴺˣ) (θ : Θ′ ᴺˣ) →
  (proj₁ (t α) ᴺᴿ) ⟨ θ , γ ⟩ ≡ (λ z → z ((α ᴺⱽ) (sub-CV-int Γ′ Θ Θ′ t γ θ)))
sub-lemma-covar `Z t γ θ = cps-CV (proj₁ (t `Z)) (proj₂ (t `Z)) ⟨ θ , γ ⟩
sub-lemma-covar {Γ′}(`S α) t γ θ = sub-lemma-covar α (sub-skip (Fix₁ CotermValue Γ′) t) γ θ

sub-lemma-T : ∀ {Γ Γ′ Θ Θ′ A} (M : Γ ⟶ Θ ∣ A) (s : Γ –[ (Fix₂ Term Θ′) ]→ Γ′) (t : Θ –[ (Fix₁ CotermValue Γ′) ]→ Θ′) (γ : (`¬ˣ Γ′) ᴺˣ) (θ : Θ′ ᴺˣ) → 
  (sub-T TK CVK s t M ᴺᴸ) ⟨ θ , γ ⟩ ≡ (M ᴺᴸ) ⟨ sub-CV-int Γ′ Θ Θ′ t γ θ , sub-T-int Γ Γ′ Θ′ s θ γ ⟩
sub-lemma-C : ∀ {Γ Γ′ Θ Θ′ A} (K : A ∣ Γ ⟶ Θ) (s : Γ –[ (Fix₂ Term Θ′) ]→ Γ′) (t : Θ –[ (Fix₁ CotermValue Γ′) ]→ Θ′) (γ : (`¬ˣ Γ′) ᴺˣ) (θ : Θ′ ᴺˣ) →
  (sub-C TK CVK s t K ᴺᴿ) ⟨ θ , γ ⟩ ≡ (K ᴺᴿ) ⟨ sub-CV-int Γ′ Θ Θ′ t γ θ , sub-T-int Γ Γ′ Θ′ s θ γ ⟩
sub-lemma-S : ∀ {Γ Γ′ Θ Θ′} (S : Γ ↦ Θ) (s : Γ –[ (Fix₂ Term Θ′) ]→ Γ′) (t : Θ –[ (Fix₁ CotermValue Γ′) ]→ Θ′) (γ : (`¬ˣ Γ′) ᴺˣ) (θ : Θ′ ᴺˣ) →
  (sub-S TK CVK s t S ᴺˢ) ⟨ θ , γ ⟩ ≡ (S ᴺˢ) ⟨ sub-CV-int Γ′ Θ Θ′ t γ θ , sub-T-int Γ Γ′ Θ′ s θ γ ⟩

sub-lemma-T (` x) s t γ θ = sub-lemma-var x s γ θ
sub-lemma-T `⟨ M , N ⟩ s t γ θ = ext (λ{(inj₁ α) → cong (λ - → - α) (sub-lemma-T M s t γ θ) ; (inj₂ β) → cong (λ - → - β) (sub-lemma-T N s t γ θ)})
sub-lemma-T inl⟨ M ⟩ s t γ θ = cong (λ - → λ { ⟨ α , _ ⟩ → - α }) (sub-lemma-T M s t γ θ)
sub-lemma-T inr⟨ M ⟩ s t γ θ = cong (λ - → λ { ⟨ _ , β ⟩ → - β }) (sub-lemma-T M s t γ θ)
sub-lemma-T not[ K ] s t γ θ = sub-lemma-C K s t γ θ
sub-lemma-T {Γ}{Γ′}{Θ}{Θ′}{A} (μθ S) s t γ θ = ext (λ α → 
  begin
    (sub-S TK CVK
    ((fmap-wkΘᵗ Θ′ A) s)
    (sub-lift (CVK.kit) t)
    S ᴺˢ) ⟨ ⟨ θ , α ⟩ , γ ⟩
  ≡⟨ sub-lemma-S S ((fmap-wkΘᵗ Θ′ A) s) (sub-lift (CVK.kit) t) γ ⟨ θ , α ⟩ ⟩ 
    (S ᴺˢ)
    ⟨ ⟨ (sub-CV-int Γ′ Θ (Θ′ , A) (sub-weaken (CVK.kit) t) γ ⟨ θ , α ⟩) , α ⟩ ,
    sub-T-int Γ Γ′ (Θ′ , A) ((fmap-wkΘᵗ Θ′ A) s) ⟨ θ , α ⟩ γ ⟩
  ≡⟨ cong (λ - → (S ᴺˢ) ⟨ ⟨ - , α ⟩ , sub-T-int Γ Γ′ (Θ′ , A) ((fmap-wkΘᵗ Θ′ A) s) ⟨ θ , α ⟩ γ ⟩) (weaken-sub-CV-int-lemma t θ γ α) ⟩
    (S ᴺˢ)
    ⟨ ⟨ sub-CV-int Γ′ Θ Θ′ t γ θ , α ⟩ ,
    sub-T-int Γ Γ′ (Θ′ , A) ((fmap-wkΘᵗ Θ′ A) s) ⟨ θ , α ⟩ γ ⟩
  ≡⟨ cong (λ - → (S ᴺˢ) ⟨ ⟨ sub-CV-int Γ′ Θ Θ′ t γ θ , α ⟩ , - ⟩) (fmap-sub-T-int-lemma s θ γ α) ⟩ 
    (S ᴺˢ) 
    ⟨ ⟨ sub-CV-int Γ′ Θ Θ′ t γ θ , α ⟩ ,
    sub-T-int Γ Γ′ Θ′ s θ γ ⟩
  ∎)

sub-lemma-C (` α) s t γ θ = sub-lemma-covar α t γ θ
sub-lemma-C fst[ K ] s t γ θ = cong (λ - → λ z → - (λ α → z (inj₁ α))) (sub-lemma-C K s t γ θ)
sub-lemma-C snd[ K ] s t γ θ = cong (λ - → λ z → - (λ β → z (inj₂ β))) (sub-lemma-C K s t γ θ)
sub-lemma-C `[ K , L ] s t γ θ = cong₂ (λ -₁ -₂ → λ z → -₁ (λ α → -₂ (λ β → z ⟨ α , β ⟩))) (sub-lemma-C K s t γ θ) (sub-lemma-C L s t γ θ)
sub-lemma-C not⟨ M ⟩ s t γ θ = cong (λ - → λ z → z -) (sub-lemma-T M s t γ θ)
sub-lemma-C {Γ}{Γ′}{Θ}{Θ′}{A} (μγ S) s t γ θ = ext (λ x → 
  begin
    (sub-S TK CVK
    (sub-lift (TK.kit) s)
    (fmap-wkΓᶜⱽ Γ′ A t)
    S ᴺˢ) ⟨ θ , ⟨ γ , x ⟩ ⟩
  ≡⟨ sub-lemma-S S (sub-lift (TK.kit) s) (fmap-wkΓᶜⱽ Γ′ A t) ⟨ γ , x ⟩ θ ⟩
    (S ᴺˢ)
    ⟨ sub-CV-int (Γ′ , A) Θ Θ′ (fmap-wkΓᶜⱽ Γ′ A t) ⟨ γ , x ⟩ θ ,
    ⟨ sub-T-int Γ (Γ′ , A) Θ′ (sub-weaken (TK.kit) s) θ ⟨ γ , x ⟩ , x ⟩ ⟩
  ≡⟨ cong (λ - → (S ᴺˢ) ⟨ - , ⟨ sub-T-int Γ (Γ′ , A) Θ′ (sub-weaken (TK.kit) s) θ ⟨ γ , x ⟩ , x ⟩ ⟩) (fmap-sub-CV-int-lemma t θ γ x) ⟩
    (S ᴺˢ)
    ⟨ sub-CV-int Γ′ Θ Θ′ t γ θ , 
    ⟨ sub-T-int Γ (Γ′ , A) Θ′ (sub-weaken (TK.kit) s) θ ⟨ γ , x ⟩ , x ⟩ ⟩
  ≡⟨ cong (λ - → (S ᴺˢ) ⟨ sub-CV-int Γ′ Θ Θ′ t γ θ , ⟨ - , x ⟩ ⟩) (weaken-sub-T-int-lemma s θ γ x) ⟩
    (S ᴺˢ)
    ⟨ sub-CV-int Γ′ Θ Θ′ t γ θ ,
    ⟨ sub-T-int Γ Γ′ Θ′ s θ γ , x ⟩ ⟩
  ∎)

sub-lemma-S (M ● K) s t γ θ = cong₂ (λ -₁ -₂ → -₁ -₂) (sub-lemma-C K s t γ θ) (sub-lemma-T M s t γ θ) 

S⟶ᴺT⇒Sᴺ≡Tᴺ : ∀ {Γ Θ} (S T : Γ ↦ Θ) (γ : (`¬ˣ Γ) ᴺˣ) (θ : Θ ᴺˣ) → S ˢ⟶ᴺ T → (S ᴺˢ) ⟨ θ , γ ⟩ ≡ (T ᴺˢ) ⟨ θ , γ ⟩
S⟶ᴺT⇒Sᴺ≡Tᴺ (`⟨ M , N ⟩ ● fst[ P ]) (M ● P) γ θ (β×₁ p) = refl
S⟶ᴺT⇒Sᴺ≡Tᴺ (`⟨ M , N ⟩ ● snd[ Q ]) (N ● Q) γ θ (β×₂ q) = refl
S⟶ᴺT⇒Sᴺ≡Tᴺ (inl⟨ M ⟩ ● `[ P , Q ]) (M ● P) γ θ (β+₁ p q) = cong ((P ᴺᴿ) ⟨ θ , γ ⟩) (ext (λ α → cong (λ - → - (λ β → (M ᴺᴸ) ⟨ θ , γ ⟩ α)) (cps-CV Q q ⟨ θ , γ ⟩)))
S⟶ᴺT⇒Sᴺ≡Tᴺ (inr⟨ N ⟩ ● `[ P , Q ]) (N ● Q) γ θ (β+₂ p q) = cong (λ - → - (λ α → (Q ᴺᴿ) ⟨ θ , γ ⟩ (λ β → (N ᴺᴸ) ⟨ θ , γ ⟩ β))) (cps-CV P p ⟨ θ , γ ⟩)
S⟶ᴺT⇒Sᴺ≡Tᴺ (not[ K ] ● not⟨ M ⟩) (M ● K) γ θ β¬ = refl
S⟶ᴺT⇒Sᴺ≡Tᴺ {Γ}{Θ} (M ● μγ {Γ}{Θ}{A} S) .(S ⟨ M /⟩ˢ) γ θ βL = sym(
  begin
    (sub-S TK CVK (add (Fix₂ Term Θ) M id-T) id-CV S ᴺˢ) ⟨ θ , γ ⟩
  ≡⟨ sub-lemma-S S (add (Fix₂ Term Θ) M id-T) id-CV γ θ ⟩
    (S ᴺˢ) ⟨ sub-CV-int Γ Θ Θ id-CV γ θ , ⟨ sub-T-int Γ Γ Θ id-T θ γ , (M ᴺᴸ) ⟨ θ , γ ⟩ ⟩ ⟩
  ≡⟨ cong₂ (λ -₁ -₂ → (S ᴺˢ) ⟨ -₁ , ⟨ -₂ , (M ᴺᴸ) ⟨ θ , γ ⟩ ⟩ ⟩) (id-sub-CV Γ Θ γ θ) (id-sub-T Γ Θ γ θ) ⟩
    (S ᴺˢ) ⟨ θ , ⟨ γ , (M ᴺᴸ) ⟨ θ , γ ⟩ ⟩ ⟩
  ∎)
S⟶ᴺT⇒Sᴺ≡Tᴺ {Γ}{Θ} (μθ {Γ}{Θ}{A} S ● P) .(S ⱽ[ ⟨ P , p ⟩ /]ˢ) γ θ (βR p) = sym (
  begin 
    (sub-S TK CVK id-T (add (Fix₁ CotermValue Γ) ⟨ P , p ⟩ id-CV) S ᴺˢ) ⟨ θ , γ ⟩
  ≡⟨ sub-lemma-S S id-T (add (Fix₁ CotermValue Γ) ⟨ P , p ⟩ id-CV) γ θ ⟩
    (S ᴺˢ) ⟨ ⟨ sub-CV-int Γ Θ Θ id-CV γ θ , (⟨ P , p ⟩ ᴺᴿⱽ) ⟨ θ , γ ⟩ ⟩ , sub-T-int Γ Γ Θ id-T θ γ ⟩ 
  ≡⟨ cong₂ (λ -₁ -₂ → (S ᴺˢ) ⟨ ⟨ -₁ , (⟨ P , p ⟩ ᴺᴿⱽ) ⟨ θ , γ ⟩ ⟩ , -₂ ⟩) (id-sub-CV Γ Θ γ θ) (id-sub-T Γ Θ γ θ) ⟩
    (S ᴺˢ) ⟨ ⟨ θ , (⟨ P , p ⟩ ᴺᴿⱽ) ⟨ θ , γ ⟩ ⟩ , γ ⟩
  ≡⟨ sym (cong (λ - → - (λ α → (S ᴺˢ) ⟨ ⟨ θ , α ⟩ , γ ⟩)) (cps-CV P p ⟨ θ , γ ⟩)) ⟩ 
    (P ᴺᴿ) ⟨ θ , γ ⟩ (λ α → (S ᴺˢ) ⟨ ⟨ θ , α ⟩ , γ ⟩)
  ∎)

M⟶ᴺN⇒Mᴺ≡Nᴺ : ∀ {Γ Θ A} (M N : Γ ⟶ Θ ∣ A) (γ : (`¬ˣ Γ) ᴺˣ) (θ : Θ ᴺˣ) → M ᵗ⟶ᴺ N → (M ᴺᴸ) ⟨ θ , γ ⟩ ≡ (N ᴺᴸ) ⟨ θ , γ ⟩
M⟶ᴺN⇒Mᴺ≡Nᴺ {Γ}{Θ}{A} M .(μθ (wkΘᵗ M ● (θ_ 0))) γ θ ηR = ext (λ α →  sym (trans 
  (ren-lemma-T M id-var (ren-weaken id-var) γ ⟨ θ , α ⟩ α) 
  (cong₂ (λ -₁ -₂ → (M ᴺᴸ) ⟨ -₁ , -₂ ⟩ α) (trans (weaken-ren-int-cbn-lemma id-var θ α) (id-ren Θ θ)) (id-neg-ren Γ γ))))

K⟶ᴺL⇒Kᴺ≡Lᴺ : ∀ {Γ Θ A} (K L : A ∣ Γ ⟶ Θ) (γ : (`¬ˣ Γ) ᴺˣ) (θ : Θ ᴺˣ) → K ᶜ⟶ᴺ L → (K ᴺᴿ) ⟨ θ , γ ⟩ ≡ (L ᴺᴿ) ⟨ θ , γ ⟩
K⟶ᴺL⇒Kᴺ≡Lᴺ {Γ}{Θ}{A} K .(μγ (γ_ 0 ● wkΓᶜ K)) γ θ ηL = ext (λ x → sym (trans 
  (ren-lemma-C K (ren-weaken (id-var)) id-var ⟨ γ , x ⟩ θ x) 
  (cong₂ (λ -₁ -₂ → (K ᴺᴿ) ⟨ -₁ , -₂ ⟩ x) (id-ren Θ θ) (trans (weaken-neg-ren-int-cbn-lemma id-var γ x) (id-neg-ren Γ γ)))))

S—↠ᴺT⇒Sᴺ≡Tᴺ : ∀ {Γ Θ} (S T : Γ ↦ Θ) (γ : (`¬ˣ Γ) ᴺˣ) (θ : Θ ᴺˣ) → S ˢ—↠ᴺ T → (S ᴺˢ) ⟨ θ , γ ⟩ ≡ (T ᴺˢ) ⟨ θ , γ ⟩
S—↠ᴺT⇒Sᴺ≡Tᴺ S .S γ θ (.S ∎ˢᴺ) = refl
S—↠ᴺT⇒Sᴺ≡Tᴺ S T γ θ (_ˢ⟶ᴺ⟨_⟩_ .S {S′} {T} S⟶S′ S′↠T) = trans (S⟶ᴺT⇒Sᴺ≡Tᴺ S S′ γ θ S⟶S′) (S—↠ᴺT⇒Sᴺ≡Tᴺ S′ T γ θ S′↠T)

M—↠ᴺN⇒Mᴺ≡Nᴺ : ∀ {Γ Θ A} (M N : Γ ⟶ Θ ∣ A) (γ : (`¬ˣ Γ) ᴺˣ) (θ : Θ ᴺˣ) → M ᵗ—↠ᴺ N → (M ᴺᴸ) ⟨ θ , γ ⟩ ≡ (N ᴺᴸ) ⟨ θ , γ ⟩
M—↠ᴺN⇒Mᴺ≡Nᴺ M .M γ θ (.M ∎ᵗᴺ) = refl
M—↠ᴺN⇒Mᴺ≡Nᴺ M N γ θ (_ᵗ⟶ᴺ⟨_⟩_ .M {M′} {N} M⟶M′ M′↠N) = trans (M⟶ᴺN⇒Mᴺ≡Nᴺ M M′ γ θ M⟶M′) (M—↠ᴺN⇒Mᴺ≡Nᴺ M′ N γ θ M′↠N)

K—↠ᴺL⇒Kᴹ≡Lᴺ : ∀ {Γ Θ A} (K L : A ∣ Γ ⟶ Θ) (γ : (`¬ˣ Γ) ᴺˣ) (θ : Θ ᴺˣ) → K ᶜ—↠ᴺ L → (K ᴺᴿ) ⟨ θ , γ ⟩ ≡ (L ᴺᴿ) ⟨ θ , γ ⟩
K—↠ᴺL⇒Kᴹ≡Lᴺ K .K γ θ (.K ∎ᶜᴺ) = refl
K—↠ᴺL⇒Kᴹ≡Lᴺ K L γ θ (_ᶜ⟶ᴺ⟨_⟩_ .K {K′} {L} K⟶K′ K′↠L) = trans (K⟶ᴺL⇒Kᴺ≡Lᴺ K K′ γ θ K⟶K′) (K—↠ᴺL⇒Kᴹ≡Lᴺ K′ L γ θ K′↠L)