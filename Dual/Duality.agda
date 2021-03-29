{-# OPTIONS --rewriting #-}

module Dual.Duality where

open import Dual.Syntax
open import Dual.Substitution
open import Dual.DualTranslation
open import Dual.Semantics
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Product using (Σ; _×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Dual.Values
open import Axiom.Extensionality.Propositional using (Extensionality; ExtensionalityImplicit)
open import Level as L hiding (lift) public

dual-ren-weaken-lemma : ∀ {A B} Γ Γ′ (ρ : Γ ↝ Γ′) (x : Γ ᵒˣ ∋ A) →  dual-ren Γ (Γ′ , B) (rename-weaken ρ) x ≡ (rename-weaken (dual-ren Γ Γ′ ρ)) x
dual-ren-weaken-lemma (Γ , C) Γ′ ρ `Z = refl
dual-ren-weaken-lemma (Γ , C) Γ′ ρ (`S x) = dual-ren-weaken-lemma Γ Γ′ (λ z → ρ (`S z)) x

dual-ren-id-lemma : ∀ Γ A (x : Γ ᵒˣ ∋ A) → (dual-ren Γ Γ id-var) x ≡ id-var x
dual-ren-id-lemma (Γ , B) A `Z = refl
dual-ren-id-lemma (Γ , B) A (`S x) =  trans (dual-ren-weaken-lemma Γ Γ id-var x) (cong `S (dual-ren-id-lemma Γ A x))

dual-ren-lift-lemma : ∀ {A B} Γ Γ′ (ρ : Γ ↝ Γ′) (x : Γ ᵒˣ , B ᵒᵀ ∋ A) → dual-ren (Γ , B) (Γ′ , B) (rename-lift ρ) x ≡ (rename-lift (dual-ren Γ Γ′ ρ)) x
dual-ren-lift-lemma Γ Γ′ ρ `Z = refl
dual-ren-lift-lemma {A}{B} Γ Γ′ ρ (`S x) = {!   !}
  

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

{-# REWRITE dual-ren-lemma-term #-}
{-# REWRITE dual-ren-lemma-coterm #-}
{-# REWRITE dual-ren-lemma-statement #-}
{-# REWRITE dual-ren-weaken-lemma #-}
{-# REWRITE dual-ren-id-lemma #-}

dual-sub-lemma-var : ∀ {Γ Γ′ Θ′ A} (x : Γ ∋ A) (s : Γ –[ (λ Γ A → TermValue Γ Θ′ A) ]→ Γ′) →
  proj₁ (s x) ᵒᴸ ≡ proj₁ (dual-termval-sub Γ Γ′ Θ′ s (x ᵒⱽ))
dual-sub-lemma-var `Z s = refl
dual-sub-lemma-var {Γ}{Γ′}{Θ′} (`S x) s = dual-sub-lemma-var x (sub-skip (λ Γ A → TermValue Γ Θ′ A) s)

dual-sub-lemma-covar : ∀ {Γ′ Θ Θ′ A} (α : Θ ∋ A) (t : Θ –[ (λ Θ A → A ∣ Γ′ ⟶ Θ) ]→ Θ′) →
  t α ᵒᴿ ≡ dual-coterm-sub Γ′ Θ Θ′ t (α ᵒⱽ)
dual-sub-lemma-covar `Z t = refl
dual-sub-lemma-covar {Γ′} (`S α) t = dual-sub-lemma-covar α (sub-skip (λ Θ A → A ∣ Γ′ ⟶ Θ) t)


dual-sub-lemma-term : ∀ {Γ Γ′ Θ Θ′ A} (M : Γ ⟶ Θ ∣ A) (s : Γ –[ (λ Γ A → TermValue Γ Θ′ A) ]→ Γ′) (t : Θ –[ (λ Θ A → A ∣ Γ′ ⟶ Θ) ]→ Θ′) →
  sub-term TermValueKit CotermKit s t M ᵒᴸ ≡ sub-coterm TermKit CotermValueKit (dual-coterm-sub Γ′ Θ Θ′ t) (dual-termval-sub Γ Γ′ Θ′ s) (M ᵒᴸ)
dual-sub-lemma-coterm : ∀ {Γ Γ′ Θ Θ′ A} (K : A ∣ Γ ⟶ Θ) (s : Γ –[ (λ Γ A → TermValue Γ Θ′ A) ]→ Γ′) (t : Θ –[ (λ Θ A → A ∣ Γ′ ⟶ Θ) ]→ Θ′) →
  sub-coterm TermValueKit CotermKit s t K ᵒᴿ ≡ sub-term TermKit CotermValueKit (dual-coterm-sub Γ′ Θ Θ′ t) (dual-termval-sub Γ Γ′ Θ′ s) (K ᵒᴿ)
dual-sub-lemma-statement : ∀ {Γ Γ′ Θ Θ′} (S : Γ ↦ Θ) (s : Γ –[ (λ Γ A → TermValue Γ Θ′ A) ]→ Γ′) (t : Θ –[ (λ Θ A → A ∣ Γ′ ⟶ Θ) ]→ Θ′) →
  (sub-statement TermValueKit CotermKit s t S ᵒˢ) ≡ sub-statement TermKit CotermValueKit (dual-coterm-sub Γ′ Θ Θ′ t) (dual-termval-sub Γ Γ′ Θ′ s) (S ᵒˢ)

dual-sub-lemma-term (` x) s t = dual-sub-lemma-var x s
dual-sub-lemma-term `⟨ M , N ⟩ s t = cong₂ `[_,_] (dual-sub-lemma-term M s t) (dual-sub-lemma-term N s t)
dual-sub-lemma-term inl⟨ M ⟩ s t = cong fst[_] (dual-sub-lemma-term M s t)
dual-sub-lemma-term inr⟨ M ⟩ s t = cong snd[_] (dual-sub-lemma-term M s t)
dual-sub-lemma-term not[ K ] s t = cong not⟨_⟩ (dual-sub-lemma-coterm K s t)
dual-sub-lemma-term (μθ S) s t = {!   !}

dual-sub-lemma-coterm (` α) s t = dual-sub-lemma-covar α t
dual-sub-lemma-coterm fst[ K ] s t = cong inl⟨_⟩ (dual-sub-lemma-coterm K s t)
dual-sub-lemma-coterm snd[ K ] s t = cong inr⟨_⟩ (dual-sub-lemma-coterm K s t)
dual-sub-lemma-coterm `[ K , L ] s t = cong₂ `⟨_,_⟩ (dual-sub-lemma-coterm K s t) (dual-sub-lemma-coterm L s t)
dual-sub-lemma-coterm not⟨ M ⟩ s t = cong not[_] (dual-sub-lemma-term M s t)
dual-sub-lemma-coterm (μγ S) s t = {!   !}

dual-sub-lemma-statement (M ● K) s t = cong₂ _●_ {!   !} {!   !}


M⟶ⱽN⇒Mᵒ⟶ᴺNᵒ : ∀ {Γ Θ A} (M N : Γ ⟶ Θ ∣ A) → M ᵗ⟶ⱽ N → (M ᵒᴸ) ᶜ⟶ᴺ (N ᵒᴸ)
M⟶ⱽN⇒Mᵒ⟶ᴺNᵒ M .(μθ (rename-term (λ x → x) (λ x → `S x) M ● ` `Z)) ηR = ηL

K⟶ⱽL⇒Kᵒ⟶ᴺLᵒ : ∀ {Γ Θ A} (K L : A ∣ Γ ⟶ Θ) → K ᶜ⟶ⱽ L → (K ᵒᴿ) ᵗ⟶ᴺ (L ᵒᴿ)
K⟶ⱽL⇒Kᵒ⟶ᴺLᵒ K .(μγ (` `Z ● rename-coterm (λ x → `S x) (λ x → x) K)) ηL = ηR

S⟶ⱽT⇒Sᵒ⟶ᴺTᵒ : ∀ {Γ Θ} (S T : Γ ↦ Θ) → S ˢ⟶ⱽ T → (S ᵒˢ) ˢ⟶ᴺ (T ᵒˢ)
S⟶ⱽT⇒Sᵒ⟶ᴺTᵒ (`⟨ V , W ⟩ ● fst[ K ]) (V ● K) (β×₁ v w) = β+₁ (Vᵒ≡P V v) (Vᵒ≡P W w)
S⟶ⱽT⇒Sᵒ⟶ᴺTᵒ (`⟨ V , W ⟩ ● snd[ L ]) (W ● L) (β×₂ v w) = β+₂ (Vᵒ≡P V v) (Vᵒ≡P W w)
S⟶ⱽT⇒Sᵒ⟶ᴺTᵒ (inl⟨ V ⟩ ● `[ K , L ]) (V ● K) (β+₁ v) = β×₁ (Vᵒ≡P V v)
S⟶ⱽT⇒Sᵒ⟶ᴺTᵒ (inr⟨ W ⟩ ● `[ K , L ]) (W ● L) (β+₂ w) = β×₂ (Vᵒ≡P W w)
S⟶ⱽT⇒Sᵒ⟶ᴺTᵒ (not[ K ] ● not⟨ M ⟩) (M ● K) β¬ = β¬
S⟶ⱽT⇒Sᵒ⟶ᴺTᵒ (V ● μγ S) .(sub-statement TermValueKit CotermKit (add (λ Γ A → Σ (Γ ⟶ _ ∣ A) Value) ⟨ V , v ⟩ (λ x → ⟨ ` x , V-var ⟩)) (λ x → ` x) S) (βL v) = {!   !}
S⟶ⱽT⇒Sᵒ⟶ᴺTᵒ (μθ S ● K) .(sub-statement TermValueKit CotermKit (λ x → ⟨ ` x , V-var ⟩) (add (λ Θ A → A ∣ _ ⟶ Θ) K (λ x → ` x)) S) βR = {!   !}

M⟶ᴺN⇒Mᵒ⟶ⱽNᵒ : ∀ {Γ Θ A} (M N : Γ ⟶ Θ ∣ A) → M ᵗ⟶ᴺ N → (M ᵒᴸ) ᶜ⟶ⱽ (N ᵒᴸ)
M⟶ᴺN⇒Mᵒ⟶ⱽNᵒ M .(μθ (rename-term (λ x → x) (λ x → `S x) M ● ` `Z)) ηR = ηL

K⟶ᴺL⇒Kᵒ⟶ⱽLᵒ : ∀ {Γ Θ A} (K L : A ∣ Γ ⟶ Θ) → K ᶜ⟶ᴺ L → (K ᵒᴿ) ᵗ⟶ᴺ (L ᵒᴿ)
K⟶ᴺL⇒Kᵒ⟶ⱽLᵒ K .(μγ (` `Z ● rename-coterm (λ x → `S x) (λ x → x) K)) ηL = ηR

S⟶ᴺT⇒Sᵒ⟶ⱽTᵒ : ∀ {Γ Θ} (S T : Γ ↦ Θ) → S ˢ⟶ᴺ T → (S ᵒˢ) ˢ⟶ⱽ (T ᵒˢ)
S⟶ᴺT⇒Sᵒ⟶ⱽTᵒ (`⟨ M , N ⟩ ● fst[ P ]) (M ● P) (β×₁ p) = β+₁ (Pᵒ≡V P p)
S⟶ᴺT⇒Sᵒ⟶ⱽTᵒ (`⟨ M , N ⟩ ● snd[ Q ]) (N ● Q) (β×₂ q) = β+₂ (Pᵒ≡V Q q)
S⟶ᴺT⇒Sᵒ⟶ⱽTᵒ (inl⟨ M ⟩ ● `[ P , Q ]) (M ● P) (β+₁ p q) = β×₁ (Pᵒ≡V P p) (Pᵒ≡V Q q)
S⟶ᴺT⇒Sᵒ⟶ⱽTᵒ (inr⟨ N ⟩ ● `[ P , Q ]) (N ● Q) (β+₂ p q) = β×₂ (Pᵒ≡V P p) (Pᵒ≡V Q q)
S⟶ᴺT⇒Sᵒ⟶ⱽTᵒ (not[ K ] ● not⟨ M ⟩) (M ● K) β¬ = β¬
S⟶ᴺT⇒Sᵒ⟶ⱽTᵒ {Γ}{Θ} (M ● μγ S) .(sub-statement TermKit CotermValueKit (add (λ Γ A → Γ ⟶ Θ ∣ A) M id-term) id-cotermvalue S) βL = {!   !}
S⟶ᴺT⇒Sᵒ⟶ⱽTᵒ {Γ}{Θ} (μθ S ● P) .(sub-statement TermKit CotermValueKit id-term (add (λ Θ A → CotermValue Γ Θ A) ⟨ P , p ⟩ id-cotermvalue) S) (βR p) = {!   !}

