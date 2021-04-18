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

weaken-ren-int-cbn-lemma : ∀ {Θ Θ′ A} (ρ : Θ ↝ Θ′) θ k → ren-int-cbn Θ (Θ′ , A) (rename-weaken ρ) ⟨ θ , k ⟩ ≡ ren-int-cbn Θ Θ′ ρ θ
weaken-ren-int-cbn-lemma {∅} ρ θ k = refl
weaken-ren-int-cbn-lemma {Θ , B}{Θ′}{A} ρ θ k = cong (λ - → ⟨ - , (ρ `Z ᴺⱽ) θ ⟩) (weaken-ren-int-cbn-lemma (λ z → ρ (`S z)) θ k)

lift-ren-int-cbn-lemma : ∀ {Θ Θ′ A} (ρ : Θ ↝ Θ′) θ k → ren-int-cbn (Θ , A) (Θ′ , A) (rename-lift ρ) ⟨ θ , k ⟩ ≡ ⟨ (ren-int-cbn Θ Θ′ ρ θ) , k ⟩
lift-ren-int-cbn-lemma {∅} ρ θ k = refl
lift-ren-int-cbn-lemma {Θ , B}{Θ′}{A} ρ θ k = cong (λ - → ⟨ ⟨ - , (ρ `Z ᴺⱽ) θ ⟩ , k ⟩) (weaken-ren-int-cbn-lemma (λ z → ρ (`S z)) θ k)

id-ren : ∀ Θ θ → ren-int-cbn Θ Θ (id-var) θ ≡ θ
id-ren ∅ θ = refl
id-ren (Θ , A) ⟨ θ , α ⟩ = cong (λ - → ⟨ - , α ⟩) (trans (weaken-ren-int-cbn-lemma (id-var) θ α) (id-ren Θ θ))

weaken-neg-ren-int-cbn-lemma : ∀ {Γ Γ′ A} (ρ : Γ ↝ Γ′) γ k → neg-ren-int-cbn Γ (Γ′ , A) (rename-weaken ρ) ⟨ γ , k ⟩ ≡ neg-ren-int-cbn Γ Γ′ ρ γ
weaken-neg-ren-int-cbn-lemma {∅} ρ γ k = refl
weaken-neg-ren-int-cbn-lemma {Γ , B}{Γ′}{A} ρ γ k = cong (λ - → ⟨ - , (Γ∋A⇒¬Γ∋¬A (ρ `Z) ᴺⱽ) γ ⟩) (weaken-neg-ren-int-cbn-lemma (λ z → ρ (`S z)) γ k)

lift-neg-ren-int-cbn-lemma : ∀ {Γ Γ′ A} (ρ : Γ ↝ Γ′) γ k → neg-ren-int-cbn (Γ , A) (Γ′ , A) (rename-lift ρ) ⟨ γ , k ⟩ ≡ ⟨ (neg-ren-int-cbn Γ Γ′ ρ γ) , k ⟩
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

ren-lemma-term : ∀ {Γ Γ′ Θ Θ′ A} (M : Γ ⟶ Θ ∣ A) (s : Γ ↝ Γ′) (t : Θ ↝ Θ′) (γ : `¬ˣ Γ′ ᴺˣ) (θ : Θ′ ᴺˣ) (k : (A ᴺᵀ))
  → (rename-term s t M ᴺᴸ) ⟨ θ , γ ⟩ k ≡ (M ᴺᴸ) ⟨ ren-int-cbn Θ Θ′ t θ , neg-ren-int-cbn Γ Γ′ s γ ⟩ k 
ren-lemma-coterm : ∀ {Γ Γ′ Θ Θ′ A} (K : A ∣ Γ ⟶ Θ) (s : Γ ↝ Γ′) (t : Θ ↝ Θ′) (γ : `¬ˣ Γ′ ᴺˣ) (θ : Θ′ ᴺˣ) (k : (`¬ A) ᴺᵀ)
  → (rename-coterm s t K ᴺᴿ) ⟨ θ , γ ⟩ k ≡ (K ᴺᴿ) ⟨ ren-int-cbn Θ Θ′ t θ , neg-ren-int-cbn Γ Γ′ s γ ⟩ k
ren-lemma-cotermvalue : ∀ {Γ Γ′ Θ Θ′ A} (P : CotermValue Γ Θ A) (s : Γ ↝ Γ′) (t : Θ ↝ Θ′) (γ : `¬ˣ Γ′ ᴺˣ) (θ : Θ′ ᴺˣ)
  → (⟨ rename-coterm s t (proj₁ P) , covalue-rename s t (proj₂ P) ⟩ ᴺᴿⱽ) ⟨ θ , γ ⟩ ≡ (P ᴺᴿⱽ) ⟨ ren-int-cbn Θ Θ′ t θ , neg-ren-int-cbn Γ Γ′ s γ ⟩
ren-lemma-statement : ∀ {Γ Γ′ Θ Θ′} (S : Γ ↦ Θ) (s : Γ ↝ Γ′) (t : Θ ↝ Θ′) (γ : `¬ˣ Γ′ ᴺˣ) (θ : Θ′ ᴺˣ)
  → (rename-statement s t S ᴺˢ) ⟨ θ , γ ⟩ ≡ (S ᴺˢ) ⟨ ren-int-cbn Θ Θ′ t θ , neg-ren-int-cbn Γ Γ′ s γ ⟩

ren-lemma-term (` x) s t γ θ k = cong (λ - → - k) (ren-lemma-var x s γ)
ren-lemma-term {Γ}{Γ′}{Θ}{Θ′} `⟨ M , N ⟩ s t γ θ k = cong (λ - → - k) {(`⟨ rename-term s t M , rename-term s t N ⟩ ᴺᴸ) ⟨ θ , γ ⟩}{(`⟨ M , N ⟩ ᴺᴸ) ⟨ ren-int-cbn Θ Θ′ t θ , neg-ren-int-cbn Γ Γ′ s γ ⟩}
  (ext ((λ{(inj₁ x) → ren-lemma-term M s t γ θ x ; (inj₂ y) → ren-lemma-term N s t γ θ y })))
ren-lemma-term inl⟨ M ⟩ s t γ θ k = ren-lemma-term M s t γ θ (proj₁ k)
ren-lemma-term inr⟨ M ⟩ s t γ θ k = ren-lemma-term M s t γ θ (proj₂ k)
ren-lemma-term not[ K ] s t γ θ k = ren-lemma-coterm K s t γ θ k
ren-lemma-term {Γ}{Γ′}{Θ}{Θ′}{A} (μθ S) s t γ θ k = 
  begin
    (rename-statement s (rename-lift t) S ᴺˢ) ⟨ ⟨ θ , k ⟩ , γ ⟩
  ≡⟨ ren-lemma-statement S s (rename-lift t) γ ⟨ θ , k ⟩ ⟩
    (S ᴺˢ) ⟨ ⟨ ren-int-cbn Θ (Θ′ , A) (λ x → `S (t x)) ⟨ θ , k ⟩ , k ⟩ , neg-ren-int-cbn Γ Γ′ s γ ⟩
  ≡⟨ cong (λ - → (S ᴺˢ) ⟨ - , neg-ren-int-cbn Γ Γ′ s γ ⟩) (lift-ren-int-cbn-lemma t θ k) ⟩
    (S ᴺˢ) ⟨ ⟨ ren-int-cbn Θ Θ′ t θ , k ⟩ , neg-ren-int-cbn Γ Γ′ s γ ⟩
  ∎

ren-lemma-coterm (` α) s t γ θ k = cong k (ren-lemma-covar α t θ)
ren-lemma-coterm fst[ K ] s t γ θ k = ren-lemma-coterm K s t γ θ (λ x → k (inj₁ x))
ren-lemma-coterm snd[ K ] s t γ θ k = ren-lemma-coterm K s t γ θ (λ x → k (inj₂ x))
ren-lemma-coterm `[ K , L ] s t γ θ k = cong₂ (λ -₁ -₂ → -₁ (λ α → -₂ λ β → k ⟨ α , β ⟩)) (ext (λ x → ren-lemma-coterm K s t γ θ x)) (ext (λ x → ren-lemma-coterm L s t γ θ x))
ren-lemma-coterm not⟨ M ⟩ s t γ θ k = cong k (ext (λ x → ren-lemma-term M s t γ θ x))
ren-lemma-coterm {Γ}{Γ′}{Θ}{Θ′}{A} (μγ S) s t γ θ k = 
  begin
    (rename-statement (rename-lift s) t S ᴺˢ) ⟨ θ , ⟨ γ , k ⟩ ⟩
  ≡⟨ ren-lemma-statement S (rename-lift s) t ⟨ γ , k ⟩ θ ⟩
    (S ᴺˢ) ⟨ ren-int-cbn Θ Θ′ t θ , ⟨ neg-ren-int-cbn Γ (Γ′ , A) (λ x → `S (s x)) ⟨ γ , k ⟩ , k ⟩ ⟩ 
  ≡⟨ cong (λ - → (S ᴺˢ) ⟨ ren-int-cbn Θ Θ′ t θ , - ⟩ ) (lift-neg-ren-int-cbn-lemma s γ k) ⟩
    (S ᴺˢ) ⟨ ren-int-cbn Θ Θ′ t θ , ⟨ neg-ren-int-cbn Γ Γ′ s γ , k ⟩ ⟩
  ∎

ren-lemma-cotermvalue ⟨ ` α , CV-covar ⟩ s t γ θ = ren-lemma-covar α t θ
ren-lemma-cotermvalue ⟨ `[ P , Q ] , CV-sum p q ⟩ s t γ θ = cong₂ ⟨_,_⟩ (ren-lemma-cotermvalue ⟨ P , p ⟩ s t γ θ) (ren-lemma-cotermvalue ⟨ Q , q ⟩ s t γ θ)
ren-lemma-cotermvalue ⟨ fst[ P ] , CV-fst p ⟩ s t γ θ = cong inj₁ (ren-lemma-cotermvalue ⟨ P , p ⟩ s t γ θ)
ren-lemma-cotermvalue ⟨ snd[ P ] , CV-snd p ⟩ s t γ θ = cong inj₂ (ren-lemma-cotermvalue ⟨ P , p ⟩ s t γ θ)
ren-lemma-cotermvalue ⟨ not⟨ K ⟩ , CV-not ⟩ s t γ θ = ext (λ x → ren-lemma-term K s t γ θ x)

ren-lemma-statement (M ● K) s t γ θ = cong₂ (λ -₁ -₂ → -₁ -₂) (ext (λ x → ren-lemma-coterm K s t γ θ x)) (ext (λ x → ren-lemma-term M s t γ θ x))


fmap-term-sub-int-lemma : ∀ {Γ Γ′ Θ A} (σ : Γ –[ (λ Γ A → Γ ⟶ Θ ∣ A) ]→ Γ′) θ γ α →
  term-sub-int Γ Γ′ (Θ , A) (fmap {λ Γ B → Γ ⟶ Θ ∣ B} {λ Γ B → Γ ⟶ (Θ , A) ∣ B} (TermSubstKit.wkΘ TK) σ) ⟨ θ , α ⟩ γ ≡ term-sub-int Γ Γ′ Θ σ θ γ
fmap-term-sub-int-lemma {∅} σ θ γ α = refl
fmap-term-sub-int-lemma {Γ , B}{Γ′}{Θ} σ θ γ α = cong₂ ⟨_,_⟩ 
  (fmap-term-sub-int-lemma (sub-skip (λ Γ A → Γ ⟶ Θ ∣ A) σ) θ γ α) 
  (ext (λ x → trans (ren-lemma-term (σ `Z) (id-var) (rename-weaken id-var) γ ⟨ θ , α ⟩ x) 
  (cong₂ (λ -₁ -₂ → (σ `Z ᴺᴸ) ⟨ -₁ , -₂ ⟩ x) (trans (weaken-ren-int-cbn-lemma (id-var) θ α) (id-ren Θ θ)) (id-neg-ren Γ′ γ))))

fmap-cotermvalue-sub-int-lemma : ∀ {Γ′ Θ Θ′ A} (σ : Θ –[ (λ Θ A → CotermValue Γ′ Θ A) ]→ Θ′) θ γ α →
  cotermvalue-sub-int (Γ′ , A) Θ Θ′ (fmap {λ Θ B → CotermValue Γ′ Θ B}{λ Θ B → CotermValue (Γ′ , A ) Θ B} (CotermSubstKit.wkΓ CVK) σ) ⟨ γ , α ⟩ θ ≡ cotermvalue-sub-int Γ′ Θ Θ′ σ γ θ
fmap-cotermvalue-sub-int-lemma {Γ′}{∅} σ θ γ α = refl
fmap-cotermvalue-sub-int-lemma {Γ′}{Θ , B}{Θ′} σ θ γ α = cong₂ ⟨_,_⟩ 
  (fmap-cotermvalue-sub-int-lemma (sub-skip (λ Θ A → CotermValue Γ′ Θ A) σ) θ γ α) 
  (trans (ren-lemma-cotermvalue (σ `Z) (rename-weaken id-var) id-var ⟨ γ , α ⟩ θ) 
  (cong₂ (λ -₁ -₂ → (σ `Z ᴺᴿⱽ) ⟨ -₁ , -₂ ⟩) (id-ren Θ′ θ) (trans (weaken-neg-ren-int-cbn-lemma (id-var) γ α) (id-neg-ren Γ′ γ))))

weaken-term-sub-int-lemma : ∀ {Γ Γ′ Θ A} (σ : Γ –[ (λ Γ A → Γ ⟶ Θ ∣ A) ]→ Γ′) θ γ α → 
  term-sub-int Γ (Γ′ , A) Θ (sub-weaken (TermSubstKit.kit TK) σ) θ ⟨ γ , α ⟩ ≡ term-sub-int Γ Γ′ Θ σ θ γ
weaken-term-sub-int-lemma {∅} σ θ γ α = refl
weaken-term-sub-int-lemma {Γ , B}{Γ′}{Θ} σ θ γ α = cong₂ ⟨_,_⟩ 
  (weaken-term-sub-int-lemma (sub-skip (λ Γ A → Γ ⟶ Θ ∣ A) σ) θ γ α) 
  (ext (λ x → trans (ren-lemma-term (σ `Z) (rename-weaken id-var) id-var ⟨ γ , α ⟩ θ x) 
  (cong₂ (λ -₁ -₂ → (σ `Z ᴺᴸ) ⟨ -₁ , -₂ ⟩ x) (id-ren Θ θ) (trans (weaken-neg-ren-int-cbn-lemma id-var γ α) (id-neg-ren Γ′ γ)))))

weaken-cotermvalue-sub-int-lemma : ∀ {Γ′ Θ Θ′ A} (σ : Θ –[ (λ Θ A → CotermValue Γ′ Θ A) ]→ Θ′) θ γ α →
  cotermvalue-sub-int Γ′ Θ (Θ′ , A) (sub-weaken (CotermSubstKit.kit CVK) σ) γ ⟨ θ , α ⟩ ≡ cotermvalue-sub-int Γ′ Θ Θ′ σ γ θ
weaken-cotermvalue-sub-int-lemma {Γ′}{∅} σ θ γ α = refl
weaken-cotermvalue-sub-int-lemma {Γ′}{Θ , B}{Θ′} σ θ γ α = cong₂ ⟨_,_⟩ 
  (weaken-cotermvalue-sub-int-lemma (sub-skip (λ Θ A → CotermValue Γ′ Θ A) σ) θ γ α) 
  (trans (ren-lemma-cotermvalue (σ `Z) (id-var) (rename-weaken id-var) γ ⟨ θ , α ⟩) 
  (cong₂ (λ -₁ -₂ → (σ `Z ᴺᴿⱽ) ⟨ -₁ , -₂ ⟩) (trans (weaken-ren-int-cbn-lemma (id-var) θ α) (id-ren Θ′ θ)) (id-neg-ren Γ′ γ)))

id-term-sub : ∀ Γ Θ γ θ → term-sub-int Γ Γ Θ id-term θ γ ≡ γ
id-term-sub ∅ Θ tt θ = refl
id-term-sub (Γ , A) Θ ⟨ γ , x ⟩ θ = cong (λ - → ⟨ - , x ⟩) (trans (weaken-term-sub-int-lemma id-term θ γ x) (id-term-sub Γ Θ γ θ))

id-cotermvalue-sub : ∀ Γ Θ γ θ → cotermvalue-sub-int Γ Θ Θ id-cotermvalue γ θ ≡ θ
id-cotermvalue-sub Γ ∅ γ tt = refl
id-cotermvalue-sub Γ (Θ , A) γ ⟨ θ , α ⟩ = cong (λ - → ⟨ - , α ⟩) (trans (weaken-cotermvalue-sub-int-lemma id-cotermvalue θ γ α) (id-cotermvalue-sub Γ Θ γ θ))

sub-lemma-var : ∀ {Γ Γ′ Θ′ A} (x : Γ ∋ A) (s : Γ –[ (λ Γ A → Γ ⟶ Θ′ ∣ A) ]→ Γ′) (γ : (`¬ˣ Γ′) ᴺˣ) (θ : Θ′ ᴺˣ) →
  (s x ᴺᴸ) ⟨ θ , γ ⟩ ≡ (Γ∋A⇒¬Γ∋¬A x ᴺⱽ) (term-sub-int Γ Γ′ Θ′ s θ γ)
sub-lemma-var `Z s γ θ = refl
sub-lemma-var {Γ}{Γ′}{Θ′} (`S x) s γ θ = sub-lemma-var x (sub-skip (λ Γ A → Γ ⟶ Θ′ ∣ A) s) γ θ

sub-lemma-covar : ∀ {Γ′ Θ Θ′ A} (α : Θ ∋ A) (t : Θ –[ (λ Θ A → CotermValue Γ′ Θ A) ]→ Θ′) (γ : (`¬ˣ Γ′) ᴺˣ) (θ : Θ′ ᴺˣ) →
  (proj₁ (t α) ᴺᴿ) ⟨ θ , γ ⟩ ≡ (λ z → z ((α ᴺⱽ) (cotermvalue-sub-int Γ′ Θ Θ′ t γ θ)))
sub-lemma-covar `Z t γ θ = cps-covalue (proj₁ (t `Z)) (proj₂ (t `Z)) ⟨ θ , γ ⟩
sub-lemma-covar {Γ′}(`S α) t γ θ = sub-lemma-covar α (sub-skip (λ Θ A → CotermValue Γ′ Θ A) t) γ θ

sub-lemma-term : ∀ {Γ Γ′ Θ Θ′ A} (M : Γ ⟶ Θ ∣ A) (s : Γ –[ (λ Γ A → Γ ⟶ Θ′ ∣ A) ]→ Γ′) (t : Θ –[ (λ Θ A → CotermValue Γ′ Θ A) ]→ Θ′) (γ : (`¬ˣ Γ′) ᴺˣ) (θ : Θ′ ᴺˣ) → 
  (sub-term TK CVK s t M ᴺᴸ) ⟨ θ , γ ⟩ ≡ (M ᴺᴸ) ⟨ cotermvalue-sub-int Γ′ Θ Θ′ t γ θ , term-sub-int Γ Γ′ Θ′ s θ γ ⟩
sub-lemma-coterm : ∀ {Γ Γ′ Θ Θ′ A} (K : A ∣ Γ ⟶ Θ) (s : Γ –[ (λ Γ A → Γ ⟶ Θ′ ∣ A) ]→ Γ′) (t : Θ –[ (λ Θ A → CotermValue Γ′ Θ A) ]→ Θ′) (γ : (`¬ˣ Γ′) ᴺˣ) (θ : Θ′ ᴺˣ) →
  (sub-coterm TK CVK s t K ᴺᴿ) ⟨ θ , γ ⟩ ≡ (K ᴺᴿ) ⟨ cotermvalue-sub-int Γ′ Θ Θ′ t γ θ , term-sub-int Γ Γ′ Θ′ s θ γ ⟩
sub-lemma-statement : ∀ {Γ Γ′ Θ Θ′} (S : Γ ↦ Θ) (s : Γ –[ (λ Γ A → Γ ⟶ Θ′ ∣ A) ]→ Γ′) (t : Θ –[ (λ Θ A → CotermValue Γ′ Θ A) ]→ Θ′) (γ : (`¬ˣ Γ′) ᴺˣ) (θ : Θ′ ᴺˣ) →
  (sub-statement TK CVK s t S ᴺˢ) ⟨ θ , γ ⟩ ≡ (S ᴺˢ) ⟨ cotermvalue-sub-int Γ′ Θ Θ′ t γ θ , term-sub-int Γ Γ′ Θ′ s θ γ ⟩

sub-lemma-term (` x) s t γ θ = sub-lemma-var x s γ θ
sub-lemma-term `⟨ M , N ⟩ s t γ θ = ext (λ{(inj₁ α) → cong (λ - → - α) (sub-lemma-term M s t γ θ) ; (inj₂ β) → cong (λ - → - β) (sub-lemma-term N s t γ θ)})
sub-lemma-term inl⟨ M ⟩ s t γ θ = cong (λ - → λ { ⟨ α , _ ⟩ → - α }) (sub-lemma-term M s t γ θ)
sub-lemma-term inr⟨ M ⟩ s t γ θ = cong (λ - → λ { ⟨ _ , β ⟩ → - β }) (sub-lemma-term M s t γ θ)
sub-lemma-term not[ K ] s t γ θ = sub-lemma-coterm K s t γ θ
sub-lemma-term {Γ}{Γ′}{Θ}{Θ′}{A} (μθ S) s t γ θ = ext (λ α → 
  begin
    (sub-statement TK CVK
    (fmap {λ Γ B → Γ ⟶ Θ′ ∣ B} {λ Γ B → Γ ⟶ (Θ′ , A) ∣ B} (TermSubstKit.wkΘ TK) s)
    (sub-lift (CotermSubstKit.kit CVK) t)
    S ᴺˢ) ⟨ ⟨ θ , α ⟩ , γ ⟩
  ≡⟨ sub-lemma-statement S (fmap {λ Γ B → Γ ⟶ Θ′ ∣ B} {λ Γ B → Γ ⟶ (Θ′ , A) ∣ B} (TermSubstKit.wkΘ TK) s) (sub-lift (CotermSubstKit.kit CVK) t) γ ⟨ θ , α ⟩ ⟩ 
    (S ᴺˢ)
    ⟨ ⟨ (cotermvalue-sub-int Γ′ Θ (Θ′ , A) (sub-weaken (CotermSubstKit.kit CVK) t) γ ⟨ θ , α ⟩) , α ⟩ ,
    term-sub-int Γ Γ′ (Θ′ , A) (fmap {λ Γ B → Γ ⟶ Θ′ ∣ B} {λ Γ B → Γ ⟶ (Θ′ , A) ∣ B} (TermSubstKit.wkΘ TK) s) ⟨ θ , α ⟩ γ ⟩
  ≡⟨ cong (λ - → (S ᴺˢ) ⟨ ⟨ - , α ⟩ , term-sub-int Γ Γ′ (Θ′ , A) (fmap {λ Γ B → Γ ⟶ Θ′ ∣ B} {λ Γ B → Γ ⟶ Θ′ , A ∣ B} (TermSubstKit.wkΘ TK) s) ⟨ θ , α ⟩ γ ⟩) (weaken-cotermvalue-sub-int-lemma t θ γ α) ⟩
    (S ᴺˢ)
    ⟨ ⟨ cotermvalue-sub-int Γ′ Θ Θ′ t γ θ , α ⟩ ,
    term-sub-int Γ Γ′ (Θ′ , A) (fmap {λ Γ B → Γ ⟶ Θ′ ∣ B} {λ Γ B → Γ ⟶ (Θ′ , A) ∣ B} (TermSubstKit.wkΘ TK) s) ⟨ θ , α ⟩ γ ⟩
  ≡⟨ cong (λ - → (S ᴺˢ) ⟨ ⟨ cotermvalue-sub-int Γ′ Θ Θ′ t γ θ , α ⟩ , - ⟩) (fmap-term-sub-int-lemma s θ γ α) ⟩ 
    (S ᴺˢ) 
    ⟨ ⟨ cotermvalue-sub-int Γ′ Θ Θ′ t γ θ , α ⟩ ,
    term-sub-int Γ Γ′ Θ′ s θ γ ⟩
  ∎)

sub-lemma-coterm (` α) s t γ θ = sub-lemma-covar α t γ θ
sub-lemma-coterm fst[ K ] s t γ θ = cong (λ - → λ z → - (λ α → z (inj₁ α))) (sub-lemma-coterm K s t γ θ)
sub-lemma-coterm snd[ K ] s t γ θ = cong (λ - → λ z → - (λ β → z (inj₂ β))) (sub-lemma-coterm K s t γ θ)
sub-lemma-coterm `[ K , L ] s t γ θ = cong₂ (λ -₁ -₂ → λ z → -₁ (λ α → -₂ (λ β → z ⟨ α , β ⟩))) (sub-lemma-coterm K s t γ θ) (sub-lemma-coterm L s t γ θ)
sub-lemma-coterm not⟨ M ⟩ s t γ θ = cong (λ - → λ z → z -) (sub-lemma-term M s t γ θ)
sub-lemma-coterm {Γ}{Γ′}{Θ}{Θ′}{A} (μγ S) s t γ θ = ext (λ x → 
  begin
    (sub-statement TK CVK
    (sub-lift (TermSubstKit.kit TK) s)
    (fmap {λ Θ B → CotermValue Γ′ Θ B}{λ Θ B → CotermValue (Γ′ , A ) Θ B} (CotermSubstKit.wkΓ CVK) t)
    S ᴺˢ) ⟨ θ , ⟨ γ , x ⟩ ⟩
  ≡⟨ sub-lemma-statement S (sub-lift (TermSubstKit.kit TK) s) (fmap {λ Θ B → CotermValue Γ′ Θ B}{λ Θ B → CotermValue (Γ′ , A ) Θ B} (CotermSubstKit.wkΓ CVK) t) ⟨ γ , x ⟩ θ ⟩
    (S ᴺˢ)
    ⟨ cotermvalue-sub-int (Γ′ , A) Θ Θ′ (fmap {λ Θ B → CotermValue Γ′ Θ B}{λ Θ B → CotermValue (Γ′ , A ) Θ B} (CotermSubstKit.wkΓ CVK) t) ⟨ γ , x ⟩ θ ,
    ⟨ term-sub-int Γ (Γ′ , A) Θ′ (sub-weaken (TermSubstKit.kit TK) s) θ ⟨ γ , x ⟩ , x ⟩ ⟩
  ≡⟨ cong (λ - → (S ᴺˢ) ⟨ - , ⟨ term-sub-int Γ (Γ′ , A) Θ′ (sub-weaken (TermSubstKit.kit TK) s) θ ⟨ γ , x ⟩ , x ⟩ ⟩) (fmap-cotermvalue-sub-int-lemma t θ γ x) ⟩
    (S ᴺˢ)
    ⟨ cotermvalue-sub-int Γ′ Θ Θ′ t γ θ , 
    ⟨ term-sub-int Γ (Γ′ , A) Θ′ (sub-weaken (TermSubstKit.kit TK) s) θ ⟨ γ , x ⟩ , x ⟩ ⟩
  ≡⟨ cong (λ - → (S ᴺˢ) ⟨ cotermvalue-sub-int Γ′ Θ Θ′ t γ θ , ⟨ - , x ⟩ ⟩) (weaken-term-sub-int-lemma s θ γ x) ⟩
    (S ᴺˢ)
    ⟨ cotermvalue-sub-int Γ′ Θ Θ′ t γ θ ,
    ⟨ term-sub-int Γ Γ′ Θ′ s θ γ , x ⟩ ⟩
  ∎)

sub-lemma-statement (M ● K) s t γ θ = cong₂ (λ -₁ -₂ → -₁ -₂) (sub-lemma-coterm K s t γ θ) (sub-lemma-term M s t γ θ) 

S⟶ᴺT⇒Sᴺ≡Tᴺ : ∀ {Γ Θ} (S T : Γ ↦ Θ) (γ : (`¬ˣ Γ) ᴺˣ) (θ : Θ ᴺˣ) → S ˢ⟶ᴺ T → (S ᴺˢ) ⟨ θ , γ ⟩ ≡ (T ᴺˢ) ⟨ θ , γ ⟩
S⟶ᴺT⇒Sᴺ≡Tᴺ (`⟨ M , N ⟩ ● fst[ P ]) (M ● P) γ θ (β×₁ p) = refl
S⟶ᴺT⇒Sᴺ≡Tᴺ (`⟨ M , N ⟩ ● snd[ Q ]) (N ● Q) γ θ (β×₂ q) = refl
S⟶ᴺT⇒Sᴺ≡Tᴺ (inl⟨ M ⟩ ● `[ P , Q ]) (M ● P) γ θ (β+₁ p q) = cong ((P ᴺᴿ) ⟨ θ , γ ⟩) (ext (λ α → cong (λ - → - (λ β → (M ᴺᴸ) ⟨ θ , γ ⟩ α)) (cps-covalue Q q ⟨ θ , γ ⟩)))
S⟶ᴺT⇒Sᴺ≡Tᴺ (inr⟨ N ⟩ ● `[ P , Q ]) (N ● Q) γ θ (β+₂ p q) = cong (λ - → - (λ α → (Q ᴺᴿ) ⟨ θ , γ ⟩ (λ β → (N ᴺᴸ) ⟨ θ , γ ⟩ β))) (cps-covalue P p ⟨ θ , γ ⟩)
S⟶ᴺT⇒Sᴺ≡Tᴺ (not[ K ] ● not⟨ M ⟩) (M ● K) γ θ β¬ = refl
S⟶ᴺT⇒Sᴺ≡Tᴺ {Γ}{Θ} (M ● μγ {Γ}{Θ}{A} S) .(S ⟨ M /⟩ˢ) γ θ βL = sym(
  begin
    (sub-statement TK CVK (add (λ Γ A → Γ ⟶ Θ ∣ A) M id-term) id-cotermvalue S ᴺˢ) ⟨ θ , γ ⟩
  ≡⟨ sub-lemma-statement S (add (λ Γ A → Γ ⟶ Θ ∣ A) M id-term) id-cotermvalue γ θ ⟩
    (S ᴺˢ) ⟨ cotermvalue-sub-int Γ Θ Θ id-cotermvalue γ θ , ⟨ term-sub-int Γ Γ Θ id-term θ γ , (M ᴺᴸ) ⟨ θ , γ ⟩ ⟩ ⟩
  ≡⟨ cong₂ (λ -₁ -₂ → (S ᴺˢ) ⟨ -₁ , ⟨ -₂ , (M ᴺᴸ) ⟨ θ , γ ⟩ ⟩ ⟩) (id-cotermvalue-sub Γ Θ γ θ) (id-term-sub Γ Θ γ θ) ⟩
    (S ᴺˢ) ⟨ θ , ⟨ γ , (M ᴺᴸ) ⟨ θ , γ ⟩ ⟩ ⟩
  ∎)
S⟶ᴺT⇒Sᴺ≡Tᴺ {Γ}{Θ} (μθ {Γ}{Θ}{A} S ● P) .(S ⱽ[ ⟨ P , p ⟩ /]ˢ) γ θ (βR p) = sym (
  begin 
    (sub-statement TK CVK id-term (add (λ Θ A → CotermValue Γ Θ A) ⟨ P , p ⟩ id-cotermvalue) S ᴺˢ) ⟨ θ , γ ⟩
  ≡⟨ sub-lemma-statement S id-term (add (λ Θ A → CotermValue Γ Θ A) ⟨ P , p ⟩ id-cotermvalue) γ θ ⟩
    (S ᴺˢ) ⟨ ⟨ cotermvalue-sub-int Γ Θ Θ id-cotermvalue γ θ , (⟨ P , p ⟩ ᴺᴿⱽ) ⟨ θ , γ ⟩ ⟩ , term-sub-int Γ Γ Θ id-term θ γ ⟩ 
  ≡⟨ cong₂ (λ -₁ -₂ → (S ᴺˢ) ⟨ ⟨ -₁ , (⟨ P , p ⟩ ᴺᴿⱽ) ⟨ θ , γ ⟩ ⟩ , -₂ ⟩) (id-cotermvalue-sub Γ Θ γ θ) (id-term-sub Γ Θ γ θ) ⟩
    (S ᴺˢ) ⟨ ⟨ θ , (⟨ P , p ⟩ ᴺᴿⱽ) ⟨ θ , γ ⟩ ⟩ , γ ⟩
  ≡⟨ sym (cong (λ - → - (λ α → (S ᴺˢ) ⟨ ⟨ θ , α ⟩ , γ ⟩)) (cps-covalue P p ⟨ θ , γ ⟩)) ⟩ 
    (P ᴺᴿ) ⟨ θ , γ ⟩ (λ α → (S ᴺˢ) ⟨ ⟨ θ , α ⟩ , γ ⟩)
  ∎)

M⟶ᴺN⇒Mᴺ≡Nᴺ : ∀ {Γ Θ A} (M N : Γ ⟶ Θ ∣ A) (γ : (`¬ˣ Γ) ᴺˣ) (θ : Θ ᴺˣ) → M ᵗ⟶ᴺ N → (M ᴺᴸ) ⟨ θ , γ ⟩ ≡ (N ᴺᴸ) ⟨ θ , γ ⟩
M⟶ᴺN⇒Mᴺ≡Nᴺ {Γ}{Θ}{A} M .(μθ (wkΘᵗ M ● (θ_ 0))) γ θ ηR = ext (λ α →  sym (trans 
  (ren-lemma-term M id-var (rename-weaken id-var) γ ⟨ θ , α ⟩ α) 
  (cong₂ (λ -₁ -₂ → (M ᴺᴸ) ⟨ -₁ , -₂ ⟩ α) (trans (weaken-ren-int-cbn-lemma id-var θ α) (id-ren Θ θ)) (id-neg-ren Γ γ))))

K⟶ᴺL⇒Kᴺ≡Lᴺ : ∀ {Γ Θ A} (K L : A ∣ Γ ⟶ Θ) (γ : (`¬ˣ Γ) ᴺˣ) (θ : Θ ᴺˣ) → K ᶜ⟶ᴺ L → (K ᴺᴿ) ⟨ θ , γ ⟩ ≡ (L ᴺᴿ) ⟨ θ , γ ⟩
K⟶ᴺL⇒Kᴺ≡Lᴺ {Γ}{Θ}{A} K .(μγ (γ_ 0 ● wkΓᶜ K)) γ θ ηL = ext (λ x → sym (trans 
  (ren-lemma-coterm K (rename-weaken (id-var)) id-var ⟨ γ , x ⟩ θ x) 
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