{-# OPTIONS --rewriting #-}

module Dual.Duality where

open import Dual.Syntax
open import Dual.Substitution
open import Dual.DualTranslation
open import Dual.Semantics
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym; trans; subst; subst₂)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎) 
open import Data.Product using (Σ; _×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Product.Properties using (Σ-≡,≡↔≡)
open import Dual.Values
open import Axiom.Extensionality.Propositional using (Extensionality; ExtensionalityImplicit)
open import Level as L hiding (lift) public
open import Function.Bundles using (Inverse)

dual-ren-weaken-lemma : ∀ {A B} Γ Γ′ (ρ : Γ ↝ Γ′) (x : Γ ᵒˣ ∋ A) →  dual-ren Γ (Γ′ , B) (rename-weaken ρ) x ≡ (rename-weaken (dual-ren Γ Γ′ ρ)) x
dual-ren-weaken-lemma (Γ , C) Γ′ ρ `Z = refl
dual-ren-weaken-lemma (Γ , C) Γ′ ρ (`S x) = dual-ren-weaken-lemma Γ Γ′ (λ z → ρ (`S z)) x

dual-ren-id-lemma : ∀ Γ A (x : Γ ᵒˣ ∋ A) → (dual-ren Γ Γ id-var) x ≡ id-var x
dual-ren-id-lemma (Γ , B) A `Z = refl
dual-ren-id-lemma (Γ , B) A (`S x) =  trans (dual-ren-weaken-lemma Γ Γ id-var x) (cong `S (dual-ren-id-lemma Γ A x))

dual-ren-lift-lemma : ∀ {A B} Γ Γ′ (ρ : Γ ↝ Γ′) (x : Γ ᵒˣ , B ᵒᵀ ∋ A) → dual-ren (Γ , B) (Γ′ , B) (rename-lift ρ) x ≡ (rename-lift (dual-ren Γ Γ′ ρ)) x
dual-ren-lift-lemma Γ Γ′ ρ `Z = refl
dual-ren-lift-lemma {A}{B} Γ Γ′ ρ (`S x) = dual-ren-weaken-lemma Γ Γ′ ρ x
  

dual-ren-lemma-var : ∀ {Γ Γ′ A} (x : Γ ∋ A) (ρ : Γ ↝ Γ′) → ρ x ᵒⱽ ≡ dual-ren Γ Γ′ ρ (x ᵒⱽ)
dual-ren-lemma-var `Z ρ = refl
dual-ren-lemma-var (`S x) ρ = dual-ren-lemma-var x (λ z → ρ (`S z))

dual-ren-lemma-term : ∀ {Γ Γ′ Θ Θ′ A} (M : Γ ⟶ Θ ∣ A) (s : Γ ↝ Γ′) (t : Θ ↝ Θ′) → (rename-term s t M ᵒᴸ) ≡ rename-coterm (dual-ren Θ Θ′ t) (dual-ren Γ Γ′ s) (M ᵒᴸ)
dual-ren-lemma-coterm : ∀ {Γ Γ′ Θ Θ′ A} (K : A ∣ Γ ⟶ Θ) (s : Γ ↝ Γ′) (t : Θ ↝ Θ′) → (rename-coterm s t K ᵒᴿ) ≡ rename-term (dual-ren Θ Θ′ t) (dual-ren Γ Γ′ s) (K ᵒᴿ)
dual-ren-lemma-statement : ∀ {Γ Γ′ Θ Θ′} (S : Γ ↦ Θ) (s : Γ ↝ Γ′) (t : Θ ↝ Θ′) → (rename-statement s t S ᵒˢ) ≡ rename-statement (dual-ren Θ Θ′ t) (dual-ren Γ Γ′ s) (S ᵒˢ)

dual-ren-lemma-term (` x) s t = cong `_ (dual-ren-lemma-var x s)
dual-ren-lemma-term `⟨ M , N ⟩ s t = cong₂ `[_,_] (dual-ren-lemma-term M s t) (dual-ren-lemma-term N s t)
dual-ren-lemma-term inl⟨ M ⟩ s t = cong fst[_] (dual-ren-lemma-term M s t)
dual-ren-lemma-term inr⟨ M ⟩ s t = cong snd[_] (dual-ren-lemma-term M s t)
dual-ren-lemma-term not[ K ] s t = cong not⟨_⟩ (dual-ren-lemma-coterm K s t)
dual-ren-lemma-term {Γ}{Γ′}{Θ}{Θ′}{A} (μθ S) s t = cong μγ 
  (trans (dual-ren-lemma-statement S s (rename-lift t)) (cong (λ - → - (dual-ren Γ Γ′ s) (S ᵒˢ)) (cong rename-statement (iext (ext λ x → dual-ren-lift-lemma Θ Θ′ t x)))))

dual-ren-lemma-coterm (` α) s t = cong `_ (dual-ren-lemma-var α t)
dual-ren-lemma-coterm fst[ K ] s t = cong inl⟨_⟩ (dual-ren-lemma-coterm K s t)
dual-ren-lemma-coterm snd[ K ] s t = cong inr⟨_⟩ (dual-ren-lemma-coterm K s t)
dual-ren-lemma-coterm `[ K , L ] s t = cong₂ `⟨_,_⟩ (dual-ren-lemma-coterm K s t) (dual-ren-lemma-coterm L s t)
dual-ren-lemma-coterm not⟨ M ⟩ s t = cong not[_] (dual-ren-lemma-term M s t)
dual-ren-lemma-coterm {Γ}{Γ′}{Θ}{Θ′}{A} (μγ S) s t = cong μθ 
  (trans (dual-ren-lemma-statement S (rename-lift s) t) (cong (λ - → - (S ᵒˢ)) (cong (rename-statement (dual-ren Θ Θ′ t)) (iext (ext (λ x → dual-ren-lift-lemma Γ Γ′ s x))))))

dual-ren-lemma-statement (M ● K) s t = cong₂ _●_ (dual-ren-lemma-coterm K s t) (dual-ren-lemma-term M s t)

-- {-# REWRITE dual-ren-lemma-term #-}
-- {-# REWRITE dual-ren-lemma-coterm #-}
-- {-# REWRITE dual-ren-lemma-statement #-}
-- {-# REWRITE dual-ren-weaken-lemma #-}
-- {-# REWRITE dual-ren-id-lemma #-}

dual-termval-sub-weaken-lemma : ∀ Γ Γ′ Θ′ A {B} (σ : Γ –[ (λ Γ A → TermValue Γ Θ′ A) ]→ Γ′) (x : Γ ᵒˣ ∋ B) 
  → dual-termval-sub Γ (Γ′ , A) Θ′ (sub-weaken (TermSubstKit.kit TVK) σ) x
    ≡ sub-weaken (CotermSubstKit.kit CVK) (dual-termval-sub Γ Γ′ Θ′ σ) x
dual-termval-sub-weaken-lemma (Γ , C) Γ′ Θ′ A σ `Z = Inverse.f Σ-≡,≡↔≡ 
  ⟨ (trans 
      (dual-ren-lemma-term (proj₁ (σ `Z)) (rename-weaken (λ z → z)) (λ x → x)) 
      (cong₂ (λ -₁ -₂ → rename-coterm (λ {A} → -₁ {A}) (λ {A} → -₂ {A}) (proj₁ (σ `Z) ᵒᴸ)) 
        (iext (λ {A} → ext (λ x → dual-ren-id-lemma Θ′ A x)))
        (iext (λ {A} → ext (λ x → trans (dual-ren-weaken-lemma Γ′ Γ′ (λ z → z) x) (cong `S (dual-ren-id-lemma Γ′ A x))))))) 
  , {!   !} ⟩
dual-termval-sub-weaken-lemma (Γ , C) Γ′ Θ′ A σ (`S x) = dual-termval-sub-weaken-lemma Γ Γ′ Θ′ A (sub-skip (λ Γ A → TermValue Γ Θ′ A) σ) x

dual-termval-sub-lift-lemma : ∀ Γ Γ′ Θ′ A {B} (σ : Γ –[ (λ Γ A → TermValue Γ Θ′ A) ]→ Γ′) (x : (Γ , A) ᵒˣ ∋ B)
  → dual-termval-sub (Γ , A) (Γ′ , A) Θ′ (sub-lift (TermSubstKit.kit TVK) σ) x
    ≡ sub-lift (CotermSubstKit.kit CVK) (dual-termval-sub Γ Γ′ Θ′ σ) x
dual-termval-sub-lift-lemma Γ Γ′ Θ′ A σ `Z = refl
dual-termval-sub-lift-lemma Γ Γ′ Θ′ A σ (`S x) = dual-termval-sub-weaken-lemma Γ Γ′ Θ′ A σ x

dual-termval-sub-fmap-lemma : ∀ Γ Γ′ Θ′ A {B} (σ : Γ –[ (λ Γ A → TermValue Γ Θ′ A) ]→ Γ′) (x : Γ ᵒˣ ∋ B)
  → dual-termval-sub Γ Γ′ (Θ′ , A) (fmap {λ Γ B → TermValue Γ Θ′ B}{λ Γ B → TermValue Γ (Θ′ , A) B} wkΘⱽ σ) x 
    ≡ fmap {λ Γ B → CotermValue (Θ′ ᵒˣ) Γ B}{λ Γ B → CotermValue ((Θ′ , A) ᵒˣ) Γ B} wkΓᶜⱽ (dual-termval-sub Γ Γ′ Θ′ σ) x
dual-termval-sub-fmap-lemma (Γ , C) Γ′ Θ′ A σ `Z = Inverse.f Σ-≡,≡↔≡ 
  ⟨ (trans 
      (dual-ren-lemma-term (proj₁ (σ `Z)) (λ z → z) (rename-weaken (λ z → z))) 
      (cong₂ (λ -₁ -₂ → rename-coterm (λ {A} → -₁ {A}) (λ {A} → -₂ {A}) (proj₁ (σ `Z) ᵒᴸ))
        (iext (λ {A} → ext (λ x → trans (dual-ren-weaken-lemma Θ′ Θ′ (λ z → z) x) (cong `S (dual-ren-id-lemma Θ′ A x))))) 
        (iext (λ {A} → ext (λ x → dual-ren-id-lemma Γ′ A x))))) 
  , {!   !} ⟩
dual-termval-sub-fmap-lemma (Γ , C) Γ′ Θ′ A σ (`S x) = dual-termval-sub-fmap-lemma Γ Γ′ Θ′ A (sub-skip (λ Γ A → TermValue Γ Θ′ A) σ) x

dual-termval-sub-id-lemma : ∀ Γ Θ A (x : Γ ᵒˣ ∋ A)
  → dual-termval-sub Γ Γ Θ id-termvalue x ≡ id-cotermvalue x
dual-termval-sub-id-lemma (Γ , B) Θ A `Z = refl 
dual-termval-sub-id-lemma (Γ , B) Θ A (`S x) = 
  trans 
    (dual-termval-sub-weaken-lemma Γ Γ Θ B id-termvalue x) 
    (Inverse.f Σ-≡,≡↔≡ 
      ⟨ cong (rename-coterm (λ x → x) (rename-weaken (λ x → x))) (cong proj₁ (dual-termval-sub-id-lemma Γ Θ A x)) 
      , {!   !} ⟩) 

dual-coterm-sub-weaken-lemma : ∀ Γ′ Θ Θ′ A {B} (σ : Θ –[ (λ Θ A → A ∣ Γ′ ⟶ Θ) ]→ Θ′) (x : Θ ᵒˣ ∋ B) 
  → dual-coterm-sub Γ′ Θ (Θ′ , A) (sub-weaken (CotermSubstKit.kit CK) σ) x
    ≡ sub-weaken (TermSubstKit.kit TK) (dual-coterm-sub Γ′ Θ Θ′ σ) x
dual-coterm-sub-weaken-lemma Γ′ (Θ , C) Θ′ A σ `Z = 
  trans 
    (dual-ren-lemma-coterm (σ `Z) (λ z → z) (rename-weaken (λ z → z))) 
    (cong₂ (λ -₁ -₂ → rename-term (λ {A} → -₁ {A}) (λ {A} → -₂ {A}) (σ `Z ᵒᴿ))
      (iext λ {C} → ext (λ x → trans (dual-ren-weaken-lemma Θ′ Θ′ id-var x) (cong `S (dual-ren-id-lemma Θ′ C x)))) 
      (iext (λ {C} → ext (λ x → dual-ren-id-lemma Γ′ C x))))
dual-coterm-sub-weaken-lemma Γ′ (Θ , C) Θ′ A σ (`S x) = dual-coterm-sub-weaken-lemma Γ′ Θ Θ′ A (sub-skip (λ Θ A → A ∣ Γ′ ⟶ Θ) σ) x

dual-coterm-sub-lift-lemma : ∀ Γ′ Θ Θ′ A {B} (σ : Θ –[ (λ Θ A → A ∣ Γ′ ⟶ Θ) ]→ Θ′) (x : (Θ , A) ᵒˣ ∋ B)
  → dual-coterm-sub Γ′ (Θ , A) (Θ′ , A) (sub-lift (CotermSubstKit.kit CK) σ) x
      ≡ sub-lift (TermSubstKit.kit TK) (dual-coterm-sub Γ′ Θ Θ′ σ) x
dual-coterm-sub-lift-lemma Γ′ Θ Θ′ A σ `Z = refl
dual-coterm-sub-lift-lemma Γ′ Θ Θ′ A σ (`S x) = dual-coterm-sub-weaken-lemma Γ′ Θ Θ′ A σ x

dual-coterm-sub-fmap-lemma : ∀ Γ′ Θ Θ′ A {B} (σ : Θ –[ (λ Θ A → A ∣ Γ′ ⟶ Θ) ]→ Θ′) (x : Θ ᵒˣ ∋ B)
  → dual-coterm-sub (Γ′ , A) Θ Θ′ (fmap {λ Θ B → B ∣ Γ′ ⟶ Θ}{λ Θ B → B ∣ Γ′ , A ⟶ Θ} wkΓᶜ σ) x
    ≡ fmap {λ Θ B → Θ ⟶ Γ′ ᵒˣ ∣ B}{λ Θ B → Θ ⟶ (Γ′ , A) ᵒˣ ∣ B} wkΘᵗ (dual-coterm-sub Γ′ Θ Θ′ σ) x
dual-coterm-sub-fmap-lemma Γ′ (Θ , C) Θ′ A {B} σ `Z = 
  trans 
    (dual-ren-lemma-coterm (σ `Z) (rename-weaken (λ z → z)) (λ z → z))
    (cong₂ (λ -₁ -₂ → rename-term (λ { {A} → -₁ {A} }) (λ { {A} → -₂ {A} }) (σ `Z ᵒᴿ))
      (iext λ {C} → ext (λ x → dual-ren-id-lemma Θ′ C x)) 
      (iext (λ {C} → ext (λ x → trans (dual-ren-weaken-lemma Γ′ Γ′ id-var x) (cong `S (dual-ren-id-lemma Γ′ C x))))))
dual-coterm-sub-fmap-lemma Γ′ (Θ , C) Θ′ A σ (`S x) = dual-coterm-sub-fmap-lemma Γ′ Θ Θ′ A (sub-skip (λ Θ A → A ∣ Γ′ ⟶ Θ) σ) x

dual-coterm-sub-id-lemma : ∀ Γ Θ A (x : Θ ᵒˣ ∋ A)
  → dual-coterm-sub Γ Θ Θ id-coterm x ≡ id-term x 
dual-coterm-sub-id-lemma Γ (Θ , B) .(B ᵒᵀ) `Z = refl
dual-coterm-sub-id-lemma Γ (Θ , B) A (`S x) = trans (dual-coterm-sub-weaken-lemma Γ Θ Θ B `_ x) (cong (rename-term (λ x₁ → `S x₁) (λ x₁ → x₁)) (dual-coterm-sub-id-lemma Γ Θ A x))


dual-sub-lemma-var : ∀ {Γ Γ′ Θ′ A} (x : Γ ∋ A) (s : Γ –[ (λ Γ A → TermValue Γ Θ′ A) ]→ Γ′) →
  proj₁ (s x) ᵒᴸ ≡ proj₁ (dual-termval-sub Γ Γ′ Θ′ s (x ᵒⱽ))
dual-sub-lemma-var `Z s = refl
dual-sub-lemma-var {Γ}{Γ′}{Θ′} (`S x) s = dual-sub-lemma-var x (sub-skip (λ Γ A → TermValue Γ Θ′ A) s)

dual-sub-lemma-covar : ∀ {Γ′ Θ Θ′ A} (α : Θ ∋ A) (t : Θ –[ (λ Θ A → A ∣ Γ′ ⟶ Θ) ]→ Θ′) →
  t α ᵒᴿ ≡ dual-coterm-sub Γ′ Θ Θ′ t (α ᵒⱽ)
dual-sub-lemma-covar `Z t = refl
dual-sub-lemma-covar {Γ′} (`S α) t = dual-sub-lemma-covar α (sub-skip (λ Θ A → A ∣ Γ′ ⟶ Θ) t)


dual-sub-lemma-term : ∀ {Γ Γ′ Θ Θ′ A} (M : Γ ⟶ Θ ∣ A) (s : Γ –[ (λ Γ A → TermValue Γ Θ′ A) ]→ Γ′) (t : Θ –[ (λ Θ A → A ∣ Γ′ ⟶ Θ) ]→ Θ′) →
  sub-term TVK CK s t M ᵒᴸ ≡ sub-coterm TK CVK (dual-coterm-sub Γ′ Θ Θ′ t) (dual-termval-sub Γ Γ′ Θ′ s) (M ᵒᴸ)
dual-sub-lemma-coterm : ∀ {Γ Γ′ Θ Θ′ A} (K : A ∣ Γ ⟶ Θ) (s : Γ –[ (λ Γ A → TermValue Γ Θ′ A) ]→ Γ′) (t : Θ –[ (λ Θ A → A ∣ Γ′ ⟶ Θ) ]→ Θ′) →
  sub-coterm TVK CK s t K ᵒᴿ ≡ sub-term TK CVK (dual-coterm-sub Γ′ Θ Θ′ t) (dual-termval-sub Γ Γ′ Θ′ s) (K ᵒᴿ)
dual-sub-lemma-statement : ∀ {Γ Γ′ Θ Θ′} (S : Γ ↦ Θ) (s : Γ –[ (λ Γ A → TermValue Γ Θ′ A) ]→ Γ′) (t : Θ –[ (λ Θ A → A ∣ Γ′ ⟶ Θ) ]→ Θ′) →
  (sub-statement TVK CK s t S ᵒˢ) ≡ sub-statement TK CVK (dual-coterm-sub Γ′ Θ Θ′ t) (dual-termval-sub Γ Γ′ Θ′ s) (S ᵒˢ)

dual-sub-lemma-term (` x) s t = dual-sub-lemma-var x s
dual-sub-lemma-term `⟨ M , N ⟩ s t = cong₂ `[_,_] (dual-sub-lemma-term M s t) (dual-sub-lemma-term N s t)
dual-sub-lemma-term inl⟨ M ⟩ s t = cong fst[_] (dual-sub-lemma-term M s t)
dual-sub-lemma-term inr⟨ M ⟩ s t = cong snd[_] (dual-sub-lemma-term M s t)
dual-sub-lemma-term not[ K ] s t = cong not⟨_⟩ (dual-sub-lemma-coterm K s t)
dual-sub-lemma-term {Γ}{Γ′}{Θ}{Θ′}{A} (μθ S) s t = cong μγ (
  begin 
    sub-statement TVK CK 
      (fmap {λ Γ B → TermValue Γ Θ′ B}{λ Γ B → TermValue Γ (Θ′ , A) B} wkΘⱽ s) 
      (sub-lift (CotermSubstKit.kit CK) t) 
      S ᵒˢ
  ≡⟨ dual-sub-lemma-statement S (fmap {λ Γ B → TermValue Γ Θ′ B}{λ Γ B → TermValue Γ (Θ′ , A) B} wkΘⱽ s) (sub-lift (CotermSubstKit.kit CK) t) ⟩
    sub-statement TK CVK
      (dual-coterm-sub Γ′ (Θ , A) (Θ′ , A) (sub-lift (CotermSubstKit.kit CK) t))
      (dual-termval-sub Γ Γ′ (Θ′ , A) (fmap {λ Γ B → TermValue Γ Θ′ B}{λ Γ B → TermValue Γ (Θ′ , A) B} wkΘⱽ s))
      (S ᵒˢ)
  ≡⟨ cong₂(λ -₁ -₂ → sub-statement TK CVK (λ {A} → -₁ {A}) (λ {A} → -₂ {A}) (S ᵒˢ))
      (iext (ext (λ x → dual-coterm-sub-lift-lemma Γ′ Θ Θ′ A t x))) 
      (iext (ext (λ x → dual-termval-sub-fmap-lemma Γ Γ′ Θ′ A s x))) ⟩
    (sub-statement TK CVK 
      (sub-lift (TermSubstKit.kit TK) (dual-coterm-sub Γ′ Θ Θ′ t)) 
      (fmap {λ Γ B → CotermValue (Θ′ ᵒˣ) Γ B}{λ Γ B → CotermValue ((Θ′ , A) ᵒˣ) Γ B} wkΓᶜⱽ (dual-termval-sub Γ Γ′ Θ′ s)) 
      (S ᵒˢ)) 
  ∎)

dual-sub-lemma-coterm (` α) s t = dual-sub-lemma-covar α t
dual-sub-lemma-coterm fst[ K ] s t = cong inl⟨_⟩ (dual-sub-lemma-coterm K s t)
dual-sub-lemma-coterm snd[ K ] s t = cong inr⟨_⟩ (dual-sub-lemma-coterm K s t)
dual-sub-lemma-coterm `[ K , L ] s t = cong₂ `⟨_,_⟩ (dual-sub-lemma-coterm K s t) (dual-sub-lemma-coterm L s t)
dual-sub-lemma-coterm not⟨ M ⟩ s t = cong not[_] (dual-sub-lemma-term M s t)
dual-sub-lemma-coterm {Γ}{Γ′}{Θ}{Θ′}{A} (μγ S) s t = cong μθ (
  begin 
    sub-statement TVK CK (sub-lift (TermSubstKit.kit TVK) s) (fmap {λ Θ B → B ∣ Γ′ ⟶ Θ}{λ Θ B → B ∣ Γ′ , A ⟶ Θ} wkΓᶜ t) S ᵒˢ
  ≡⟨ dual-sub-lemma-statement S (sub-lift (TermSubstKit.kit TVK) s) (fmap {λ Θ B → B ∣ Γ′ ⟶ Θ}{λ Θ B → B ∣ Γ′ , A ⟶ Θ} wkΓᶜ t) ⟩ 
    sub-statement TK CVK 
      (dual-coterm-sub (Γ′ , A) Θ Θ′ (fmap {λ Θ B → B ∣ Γ′ ⟶ Θ}{λ Θ B → B ∣ Γ′ , A ⟶ Θ} wkΓᶜ t)) 
      (dual-termval-sub (Γ , A) (Γ′ , A) Θ′ (sub-lift (TermSubstKit.kit TVK) s))
      (S ᵒˢ)
  ≡⟨ cong₂ (λ -₁ -₂ → sub-statement TK CVK (λ{ {A} → -₁ {A} }) (λ{ {A} → -₂ {A} }) (S ᵒˢ) )
      (iext (ext (λ x → dual-coterm-sub-fmap-lemma Γ′ Θ Θ′ A t x))) 
      (iext (ext (λ x → dual-termval-sub-lift-lemma Γ Γ′ Θ′ A s x))) ⟩ 
    sub-statement TK CVK
      (fmap {λ Θ B → Θ ⟶ Γ′ ᵒˣ ∣ B}{λ Θ B → Θ ⟶ (Γ′ , A) ᵒˣ ∣ B} wkΘᵗ (dual-coterm-sub Γ′ Θ Θ′ t))
      (sub-lift (CotermSubstKit.kit CVK) (dual-termval-sub Γ Γ′ Θ′ s))
      (S ᵒˢ)
  ∎)

dual-sub-lemma-statement (M ● K) s t = cong₂ _●_ (dual-sub-lemma-coterm K s t) (dual-sub-lemma-term M s t)


-- M⟶ⱽN⇒Mᵒ⟶ᴺNᵒ : ∀ {Γ Θ A} (M N : Γ ⟶ Θ ∣ A) → M ᵗ⟶ⱽ N → (M ᵒᴸ) ᶜ⟶ᴺ (N ᵒᴸ)
-- M⟶ⱽN⇒Mᵒ⟶ᴺNᵒ {Γ}{Θ}{A} M .(μθ (rename-term (λ x → x) (λ x → `S x) M ● ` `Z)) ηR = subst (λ - → M ᵒᴸ ᶜ⟶ᴺ μγ (` `Z ● -))
--   (sym (trans (dual-ren-lemma-term M (λ x → x) (rename-weaken (λ z → z))) {!  !})) ηL

-- K⟶ⱽL⇒Kᵒ⟶ᴺLᵒ : ∀ {Γ Θ A} (K L : A ∣ Γ ⟶ Θ) → K ᶜ⟶ⱽ L → (K ᵒᴿ) ᵗ⟶ᴺ (L ᵒᴿ)
-- K⟶ⱽL⇒Kᵒ⟶ᴺLᵒ K .(μγ (` `Z ● rename-coterm (λ x → `S x) (λ x → x) K)) ηL = subst (λ - → K ᵒᴿ ᵗ⟶ᴺ μθ (- ● ` `Z)) 
--   (sym (trans (dual-ren-lemma-coterm K (rename-weaken (λ z → z)) (λ z → z)) {!   !})) ηR

S⟶ⱽT⇒Sᵒ⟶ᴺTᵒ : ∀ {Γ Θ} (S T : Γ ↦ Θ) → S ˢ⟶ⱽ T → (S ᵒˢ) ˢ⟶ᴺ (T ᵒˢ)
S⟶ⱽT⇒Sᵒ⟶ᴺTᵒ (`⟨ V , W ⟩ ● fst[ K ]) (V ● K) (β×₁ v w) = β+₁ (Vᵒ≡P V v) (Vᵒ≡P W w)
S⟶ⱽT⇒Sᵒ⟶ᴺTᵒ (`⟨ V , W ⟩ ● snd[ L ]) (W ● L) (β×₂ v w) = β+₂ (Vᵒ≡P V v) (Vᵒ≡P W w)
S⟶ⱽT⇒Sᵒ⟶ᴺTᵒ (inl⟨ V ⟩ ● `[ K , L ]) (V ● K) (β+₁ v) = β×₁ (Vᵒ≡P V v)
S⟶ⱽT⇒Sᵒ⟶ᴺTᵒ (inr⟨ W ⟩ ● `[ K , L ]) (W ● L) (β+₂ w) = β×₂ (Vᵒ≡P W w)
S⟶ⱽT⇒Sᵒ⟶ᴺTᵒ (not[ K ] ● not⟨ M ⟩) (M ● K) β¬ = β¬
S⟶ⱽT⇒Sᵒ⟶ᴺTᵒ {Γ}{Θ} (V ● μγ S) .(sub-statement TVK CK (add (λ Γ A → Σ (Γ ⟶ _ ∣ A) Value) ⟨ V , v ⟩ (λ x → ⟨ ` x , V-var ⟩)) (λ x → ` x) S) (βL v) = 
  subst (λ - → μθ (S ᵒˢ) ● V ᵒᴸ ˢ⟶ᴺ -) 
    (sym (trans 
      (dual-sub-lemma-statement S (add (λ Γ A → Σ (Γ ⟶ Θ ∣ A) Value) ⟨ V , v ⟩ id-termvalue) id-coterm) 
      (cong₂ (λ -₁ -₂ → sub-statement TK CVK (λ {A} → -₁ {A}) (λ {A} → -₂ {A}) (S ᵒˢ))
        (iext (λ {C} → ext (λ x → dual-coterm-sub-id-lemma Γ Θ C x))) 
        (iext λ {C} → ext (λ x → {!   !}))))) 
    (βR (Vᵒ≡P V v))
S⟶ⱽT⇒Sᵒ⟶ᴺTᵒ {Γ}{Θ} (μθ S ● K) .(sub-statement TVK CK (λ x → ⟨ ` x , V-var ⟩) (add (λ Θ A → A ∣ _ ⟶ Θ) K (λ x → ` x)) S) βR = 
  subst (λ - → K ᵒᴿ ● μγ (S ᵒˢ) ˢ⟶ᴺ -) 
    (sym (trans 
      (dual-sub-lemma-statement S id-termvalue (add (λ Θ A → A ∣ Γ ⟶ Θ) K id-coterm)) 
      (cong₂ (λ -₁ -₂ → sub-statement TK CVK (λ {A} → -₁ {A}) (λ {A} → -₂ {A}) (S ᵒˢ))
        (iext (λ {C} → ext (λ x → {!    !}))) 
        (iext λ {C} → ext (λ x → dual-termval-sub-id-lemma Γ Θ C x))))) 
    βL

-- M⟶ᴺN⇒Mᵒ⟶ⱽNᵒ : ∀ {Γ Θ A} (M N : Γ ⟶ Θ ∣ A) → M ᵗ⟶ᴺ N → (M ᵒᴸ) ᶜ⟶ⱽ (N ᵒᴸ)
-- M⟶ᴺN⇒Mᵒ⟶ⱽNᵒ M .(μθ (rename-term (λ x → x) (λ x → `S x) M ● ` `Z)) ηR = 
--   {! subst (λ - → M ᵒᴸ ᶜ⟶)  !}

-- K⟶ᴺL⇒Kᵒ⟶ⱽLᵒ : ∀ {Γ Θ A} (K L : A ∣ Γ ⟶ Θ) → K ᶜ⟶ᴺ L → (K ᵒᴿ) ᵗ⟶ᴺ (L ᵒᴿ)
-- K⟶ᴺL⇒Kᵒ⟶ⱽLᵒ K .(μγ (` `Z ● rename-coterm (λ x → `S x) (λ x → x) K)) ηL = {!   !}

-- S⟶ᴺT⇒Sᵒ⟶ⱽTᵒ : ∀ {Γ Θ} (S T : Γ ↦ Θ) → S ˢ⟶ᴺ T → (S ᵒˢ) ˢ⟶ⱽ (T ᵒˢ)
-- S⟶ᴺT⇒Sᵒ⟶ⱽTᵒ (`⟨ M , N ⟩ ● fst[ P ]) (M ● P) (β×₁ p) = β+₁ (Pᵒ≡V P p)
-- S⟶ᴺT⇒Sᵒ⟶ⱽTᵒ (`⟨ M , N ⟩ ● snd[ Q ]) (N ● Q) (β×₂ q) = β+₂ (Pᵒ≡V Q q)
-- S⟶ᴺT⇒Sᵒ⟶ⱽTᵒ (inl⟨ M ⟩ ● `[ P , Q ]) (M ● P) (β+₁ p q) = β×₁ (Pᵒ≡V P p) (Pᵒ≡V Q q)
-- S⟶ᴺT⇒Sᵒ⟶ⱽTᵒ (inr⟨ N ⟩ ● `[ P , Q ]) (N ● Q) (β+₂ p q) = β×₂ (Pᵒ≡V P p) (Pᵒ≡V Q q)
-- S⟶ᴺT⇒Sᵒ⟶ⱽTᵒ (not[ K ] ● not⟨ M ⟩) (M ● K) β¬ = β¬
-- S⟶ᴺT⇒Sᵒ⟶ⱽTᵒ {Γ}{Θ} (M ● μγ S) .(sub-statement TK CVK (add (λ Γ A → Γ ⟶ Θ ∣ A) M id-term) id-cotermvalue S) βL = 
--   subst (λ - → μθ (S ᵒˢ) ● M ᵒᴸ ˢ⟶ⱽ -) 
--     (sym (trans {!   !} {!   !}))
--     βR
-- S⟶ᴺT⇒Sᵒ⟶ⱽTᵒ {Γ}{Θ} (μθ S ● P) .(sub-statement TK CVK id-term (add (λ Θ A → CotermValue Γ Θ A) ⟨ P , p ⟩ id-cotermvalue) S) (βR p) = 
--   {!   !}

