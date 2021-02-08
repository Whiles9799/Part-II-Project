{-# OPTIONS --rewriting #-}

module Dual.Soundness (R : Set) where

import Relation.Binary.PropositionalEquality  as Eq
open Eq using (_≡_; refl; cong; cong₂; sym; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary using (¬_)
open import Agda.Builtin.Equality.Rewrite
open import Axiom.Extensionality.Propositional using (Extensionality; ExtensionalityImplicit)
open import Dual.Syntax
open import Dual.Semantics
open import Dual.Substitution
open import Dual.Values
open import Dual.CPSTransformation
open import Dual.DualTranslation


Mⱽcλz→X≡X : ∀ {Γ Θ A} (M : Γ ⟶ Θ ∣ A) (c : Γ ⱽˣ × (`¬ˣ Θ) ⱽˣ) (X : R) → ?

Mⱽcλz→X≡X (` x) c X = refl
Mⱽcλz→X≡X `⟨ M , N ⟩ c X = trans (Mⱽcλz→X≡X M c ((N ⱽᴸ) c (λ z → X))) (Mⱽcλz→X≡X N c X)
Mⱽcλz→X≡X inl⟨ M ⟩ c X = Mⱽcλz→X≡X M c X
Mⱽcλz→X≡X inr⟨ M ⟩ c X = Mⱽcλz→X≡X M c X
Mⱽcλz→X≡X not[ K ] c X = refl
Mⱽcλz→X≡X (μθ S) c X = {!   !} --⟨ proj₁ c , ⟨ proj₂ c , (λ z → X) ⟩ ⟩ X


ren-int : ∀ Γ Γ′ → Γ ↝ Γ′ → (Γ′ ⱽˣ) → (Γ ⱽˣ)
ren-int ∅ Γ′ ρ γ = tt
ren-int (Γ , x) Γ′ ρ γ = ⟨ (ren-int Γ Γ′ (λ z → ρ (`S z)) γ) , ((ρ `Z ⱽⱽ) γ) ⟩

neg-ren-int : ∀ Γ Γ′ → Γ ↝ Γ′ → ((`¬ˣ Γ′) ⱽˣ) → ((`¬ˣ Γ) ⱽˣ)
neg-ren-int ∅ Γ′ ρ γ = tt
neg-ren-int (Γ , x) Γ′ ρ γ = ⟨ (neg-ren-int Γ Γ′ (λ z → ρ (`S z)) γ) , (ρ (`S {!   !}) ⱽⱽ) {!   !} ⟩
 
termvalue-sub-int : ∀ Γ Γ′ Θ → Γ –[ (λ Γ A → TermValue Γ Θ A) ]→ Γ′ → ((`¬ˣ Θ) ⱽˣ) → (Γ′ ⱽˣ) → (Γ ⱽˣ)
termvalue-sub-int ∅ Γ′ Θ σ θ γ = tt
termvalue-sub-int (Γ , A) Γ′ Θ σ θ γ = ⟨ (termvalue-sub-int Γ Γ′ Θ (λ x → σ (`S x)) θ γ) , ((σ `Z ⱽᴸⱽ) ⟨ γ , θ ⟩) ⟩

coterm-sub-int : ∀ Γ Θ Θ′ → Θ –[ (λ Θ A → A ∣ Γ ⟶ Θ) ]→ Θ′ → Γ ⱽˣ → ((`¬ˣ Θ′) ⱽˣ) → ((`¬ˣ Θ) ⱽˣ)
coterm-sub-int Γ ∅ Θ′ σ γ _ = tt
coterm-sub-int Γ (Θ , A) Θ′ σ γ θ = ⟨ (coterm-sub-int Γ Θ Θ′ (λ z → σ (`S z)) γ θ)  , (((σ `Z) ⱽᴿ) ⟨ γ , θ ⟩) ⟩

_∘_ : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
  → (B → C) → (A → B) → A → C
(g ∘ f) x  =  g (f x)

sub-lemma-var : ∀ {Γ Γ′ Θ Θ′ A} (s : Γ –[ (λ Γ A → TermValue Γ Θ′ A) ]→ Γ′) (t : Θ –[ (λ Θ A → A ∣ Γ′ ⟶ Θ) ]→ Θ′) (x : Γ ∋ A) (γ : Γ′ ⱽˣ) (θ : (`¬ˣ Θ′) ⱽˣ ) →
  (proj₁ (s x) ⱽᴸ) ⟨ γ , θ ⟩ ≡ (λ k → k ((x ⱽⱽ) (termvalue-sub-int Γ Γ′ Θ′ s θ γ)))

sub-lemma-var s t `Z γ θ = ext (λ x → {! !})
sub-lemma-var s t (`S x) γ θ = {!   !}

sub-lemma-term : ∀ {Γ Γ′ Θ Θ′ A} (s : Γ –[ (λ Γ A → TermValue Γ Θ′ A) ]→ Γ′) (t : Θ –[ (λ Θ A → A ∣ Γ′ ⟶ Θ) ]→ Θ′) (M : Γ ⟶ Θ ∣ A) (γ : Γ′ ⱽˣ) (θ : (`¬ˣ Θ′) ⱽˣ ) →
  ((sub-term TermValueKit CotermKit s t M) ⱽᴸ) ⟨ γ , θ ⟩ ≡ (M ⱽᴸ) ⟨ termvalue-sub-int Γ Γ′ Θ′ s θ γ , coterm-sub-int Γ′ Θ Θ′ t γ θ ⟩

sub-lemma-coterm : ∀ {Γ Γ′ Θ Θ′ A} (s : Γ –[ (λ Γ A → TermValue Γ Θ′ A) ]→ Γ′) (t : Θ –[ (λ Θ A → A ∣ Γ′ ⟶ Θ) ]→ Θ′) (K : A ∣ Γ ⟶ Θ) (γ : Γ′ ⱽˣ) (θ : (`¬ˣ Θ′) ⱽˣ ) →
  ((sub-coterm TermValueKit CotermKit s t K) ⱽᴿ) ⟨ γ , θ ⟩ ≡ (K ⱽᴿ) ⟨ termvalue-sub-int Γ Γ′ Θ′ s θ γ , coterm-sub-int Γ′ Θ Θ′ t γ θ ⟩

sub-lemma-statement : ∀ {Γ Γ′ Θ Θ′} (s : Γ –[ (λ Γ A → TermValue Γ Θ′ A) ]→ Γ′) (t : Θ –[ (λ Θ A → A ∣ Γ′ ⟶ Θ) ]→ Θ′) (S : Γ ↦ Θ) (γ : Γ′ ⱽˣ) (θ : (`¬ˣ Θ′) ⱽˣ ) →
  ((sub-statement TermValueKit CotermKit s t S) ⱽˢ) ⟨ γ , θ ⟩ ≡ (S ⱽˢ) ⟨ termvalue-sub-int Γ Γ′ Θ′ s θ γ , coterm-sub-int Γ′ Θ Θ′ t γ θ ⟩

sub-lemma-term s t (` x) γ θ = {!   !} 
sub-lemma-term {Γ}{Γ′}{Θ}{Θ′} s t `⟨ M , N ⟩ γ θ = ext (λ k → trans 
  (cong (λ - → - (λ x → (sub-term TermValueKit CotermKit s t N ⱽᴸ) ⟨ γ , θ ⟩ (λ y → k ⟨ x , y ⟩))) (sub-lemma-term s t M γ θ)) 
  (cong (λ - → (M ⱽᴸ) ⟨ termvalue-sub-int Γ Γ′ Θ′ s θ γ , coterm-sub-int Γ′ Θ Θ′ t γ θ ⟩ (λ x → - (λ y → k ⟨ x , y ⟩))) (sub-lemma-term s t N γ θ)))
sub-lemma-term s t inl⟨ M ⟩ γ θ = ext (λ k → cong (λ - → - (λ x → k (inj₁ x))) (sub-lemma-term s t M γ θ))
sub-lemma-term s t inr⟨ M ⟩ γ θ = ext (λ k → cong (λ - → - (λ x → k (inj₂ x))) (sub-lemma-term s t M γ θ))
sub-lemma-term s t not[ K ] γ θ = ext (λ k → cong k (sub-lemma-coterm s t K γ θ))
sub-lemma-term {Γ}{Γ′}{Θ}{Θ′} s t (μθ S) γ θ = ext (λ k → 
  begin 
    (sub-statement TermValueKit CotermKit 
    (fmap (λ x → ⟨ rename-term id-var (rename-weaken id-var) (proj₁ x) , 
    value-invariant-under-renaming id-var (rename-weaken id-var) (proj₂ x) ⟩) s)
    (sub-lift (CotermSubstKit.kit CotermKit) t) S ⱽˢ) ⟨ γ , ⟨ θ , k ⟩ ⟩
  ≡⟨ {!   !} ⟩
    {!   !}
  ≡⟨ {!   !} ⟩
    (sub-statement TermValueKit CotermKit s ( {!   !}) S ⱽˢ) ⟨ γ , θ ⟩
  ≡⟨ sub-lemma-statement {!   !} ({!   !}) S γ θ ⟩
    (S ⱽˢ)
    ⟨ termvalue-sub-int Γ Γ′ Θ′ s θ γ ,
    ⟨ coterm-sub-int Γ′ Θ Θ′ t γ θ , k ⟩ ⟩ 
  ∎
  )

sub-lemma-coterm s t (` α) γ θ = {!   !}
sub-lemma-coterm s t fst[ K ] γ θ = cong (λ - → λ { ⟨ x , _ ⟩ → - x }) (sub-lemma-coterm s t K γ θ)
sub-lemma-coterm s t snd[ K ] γ θ = cong (λ - → λ { ⟨ _ , y ⟩ → - y }) (sub-lemma-coterm s t K γ θ) --ext (λ{⟨ _ , y ⟩ → cong ((λ - → λ { ⟨ _ , y ⟩ → - y }) ⟨ _ , y ⟩) (sub-lemma-coterm s t K γ θ)})
sub-lemma-coterm {Γ} {Γ′} {Θ} {Θ′} {A `+ B} s t `[ K , L ] γ θ = ext (λ{(inj₁ x) → cong (λ - → - x) (sub-lemma-coterm s t K γ θ) ; (inj₂ y) → cong (λ - → - y) (sub-lemma-coterm s t L γ θ)})
sub-lemma-coterm s t not⟨ M ⟩ γ θ = sub-lemma-term s t M γ θ
sub-lemma-coterm s t (μγ S) γ θ = ext (λ x → {!   !})

sub-lemma-statement {Γ} {Γ′} {Θ} {Θ′} s t (M ● K) γ θ = 
  begin
    (sub-term TermValueKit CotermKit s t M ⱽᴸ) ⟨ γ , θ ⟩ ((sub-coterm TermValueKit CotermKit s t K ⱽᴿ) ⟨ γ , θ ⟩)
  ≡⟨ cong (λ - → - ((sub-coterm TermValueKit CotermKit s t K ⱽᴿ) ⟨ γ , θ ⟩)) (sub-lemma-term s t M γ θ) ⟩
    (M ⱽᴸ) ⟨ termvalue-sub-int Γ Γ′ Θ′ s θ γ , coterm-sub-int Γ′ Θ Θ′ t γ θ ⟩ ((sub-coterm TermValueKit CotermKit s t K ⱽᴿ) ⟨ γ , θ ⟩)
  ≡⟨ cong (λ - → (M ⱽᴸ) ⟨ termvalue-sub-int Γ Γ′ Θ′ s θ γ , coterm-sub-int Γ′ Θ Θ′ t γ θ ⟩ -) (sub-lemma-coterm s t K γ θ) ⟩
    (M ⱽᴸ) ⟨ termvalue-sub-int Γ Γ′ Θ′ s θ γ , coterm-sub-int Γ′ Θ Θ′ t γ θ ⟩ ((K ⱽᴿ) ⟨ termvalue-sub-int Γ Γ′ Θ′ s θ γ , coterm-sub-int Γ′ Θ Θ′ t γ θ ⟩)
  ∎

id-termvalue-sub-int : ∀ Γ Θ γ θ → termvalue-sub-int Γ Γ Θ id-termvalue θ γ ≡ γ
id-termvalue-sub-int ∅ Θ γ θ = refl
id-termvalue-sub-int (Γ , A) Θ ⟨ γ₁ , γ₂ ⟩ θ = cong (λ - → ⟨ - , γ₂ ⟩) {!   !}

id-coterm-sub-int : ∀ Γ Θ γ θ → coterm-sub-int Γ Θ Θ id-coterm γ θ ≡ θ
id-coterm-sub-int Γ ∅ γ θ = refl
id-coterm-sub-int Γ (Θ , A) γ ⟨ θ₁ , θ₂ ⟩ = cong (λ - → ⟨ - , θ₂ ⟩) {!   !}



S⟶ⱽT⇒Sⱽ≡Tⱽ : ∀ {Γ Θ} (S T : Γ ↦ Θ) (c : (Γ ᵒˣ) ᴺˣ × `¬ˣ (Θ ᵒˣ) ᴺˣ) → S ˢ⟶ⱽ T → (S ⱽˢ) c ≡ (T ⱽˢ) c
S⟶ⱽT⇒Sⱽ≡Tⱽ (`⟨ V , W ⟩ ● fst[ K ]) (V ● K) c (β×₁ x x₁) = cong ((V ⱽᴸ) c) (ext (λ - → Mⱽcλz→X≡X W c ((K ⱽᴿ) c -)))
S⟶ⱽT⇒Sⱽ≡Tⱽ (`⟨ V , W ⟩ ● snd[ L ]) (W ● L) c (β×₂ x x₁) = Mⱽcλz→X≡X V c ((W ⱽᴸ) c ((L ⱽᴿ) c))
S⟶ⱽT⇒Sⱽ≡Tⱽ (inl⟨ V ⟩ ● `[ K , L ]) (V ● K) c (β+₁ x) = cong ((V ⱽᴸ) c) refl
S⟶ⱽT⇒Sⱽ≡Tⱽ (inr⟨ W ⟩ ● `[ K , L ]) (W ● L) c (β+₂ x) = cong ((W ⱽᴸ) c) refl
S⟶ⱽT⇒Sⱽ≡Tⱽ (not[ K ] ● not⟨ M ⟩) (M ● K) c (β¬) = refl
S⟶ⱽT⇒Sⱽ≡Tⱽ {Γ} {Θ} (V ● μγ {Γ}{Θ}{A} S) .(S ⱽ⟨ ⟨ V , v ⟩ /⟩ˢ) ⟨ c₁ , c₂ ⟩ (βL v) = sym (
  begin
    ((S ⱽ⟨ ⟨ V , v ⟩ /⟩ˢ) ⱽˢ) ⟨ c₁ , c₂ ⟩
  ≡⟨⟩
    (sub-statement TermValueKit CotermKit (add (λ Γ A → TermValue Γ Θ A) ⟨ V , v ⟩ id-termvalue) id-coterm S ⱽˢ) ⟨ c₁ , c₂ ⟩
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
    (sub-statement TermValueKit CotermKit id-termvalue (add (λ Θ A → A ∣ Γ ⟶ Θ) K id-coterm) S ⱽˢ) ⟨ c₁ , c₂ ⟩
  ≡⟨ sub-lemma-statement id-termvalue ((add (λ Θ A → A ∣ Γ ⟶ Θ) K id-coterm)) S c₁ c₂ ⟩
    (S ⱽˢ) ⟨ (termvalue-sub-int Γ Γ Θ id-termvalue c₂ c₁) , (coterm-sub-int Γ (Θ , A) Θ (add (λ Θ A → A ∣ Γ ⟶ Θ) K id-coterm) c₁ c₂) ⟩
  ≡⟨ cong (λ - → (S ⱽˢ) ⟨ - , coterm-sub-int Γ (Θ , A) Θ (add (λ Θ A → A ∣ Γ ⟶ Θ) K id-coterm) c₁ c₂ ⟩) (id-termvalue-sub-int Γ Θ c₁ c₂) ⟩
    (S ⱽˢ) ⟨ c₁ , (coterm-sub-int Γ (Θ , A) Θ (add (λ Θ A → A ∣ Γ ⟶ Θ) K id-coterm) c₁ c₂) ⟩
  ≡⟨ cong (λ - → (S ⱽˢ) ⟨ c₁ , ⟨ - , (K ⱽᴿ) ⟨ c₁ , c₂ ⟩ ⟩ ⟩) (id-coterm-sub-int Γ Θ c₁ c₂) ⟩
    (S ⱽˢ) ⟨ c₁ , ⟨ c₂ , (K ⱽᴿ) ⟨ c₁ , c₂ ⟩ ⟩ ⟩
  ∎)
S—↠ⱽT⇒Sⱽ≡Tⱽ : ∀ {Γ Θ} (S T : Γ ↦ Θ) (c : (Γ ᵒˣ) ᴺˣ × `¬ˣ (Θ ᵒˣ) ᴺˣ) → S ˢ—↠ⱽ T → (S ⱽˢ) c ≡ (T ⱽˢ) c
S—↠ⱽT⇒Sⱽ≡Tⱽ S .S c (.S ∎ˢⱽ) = refl
S—↠ⱽT⇒Sⱽ≡Tⱽ S T c ( _ˢ⟶ⱽ⟨_⟩_ .S {S′} {T} S⟶S′ S′↠T) = trans (S⟶ⱽT⇒Sⱽ≡Tⱽ S S′ c S⟶S′) (S—↠ⱽT⇒Sⱽ≡Tⱽ S′ T c S′↠T)

-- ren-lemma-term : ∀ {Γ Γ′ Θ Θ′ A} (s : Γ ↝ Γ′) (t : Θ ↝ Θ′) (M : Γ ⟶ Θ ∣ A) (γ : Γ′ ⱽˣ) (θ : (`¬ˣ Θ′) ⱽˣ) (k : ((`¬ A) ⱽᵀ)) →
--   (rename-term s t M ⱽᴸ) ⟨ γ , θ ⟩ k ≡ (M ⱽᴸ) ⟨ ren-int Γ Γ′ s γ , ren-int {!  !} Θ′ {!   !} {!   !} ⟩ k

-- ren-lemma-term s t (` x) γ θ k = {!   !}
-- ren-lemma-term s t `⟨ M , M₁ ⟩ γ θ k = {!   !}
-- ren-lemma-term s t inl⟨ M ⟩ γ θ k = {!   !}
-- ren-lemma-term s t inr⟨ M ⟩ γ θ k = {!   !}
-- ren-lemma-term s t not[ x ] γ θ k = {!   !}
-- ren-lemma-term s t (μθ x) γ θ k = {!   !}


M⟶ⱽN⇒Mⱽ≡Nⱽ : ∀ {Γ Θ A} (M N : Γ ⟶ Θ ∣ A) (c : (Γ ᵒˣ) ᴺˣ × `¬ˣ (Θ ᵒˣ) ᴺˣ) (k : ((`¬ A) ⱽᵀ)) → M ᵗ⟶ⱽ N → (M ⱽᴸ) c k ≡ (N ⱽᴸ) c k
M⟶ⱽN⇒Mⱽ≡Nⱽ M .(μθ (rename-term id-var (rename-weaken id-var) M ● ` `Z)) ⟨ c₁ , c₂ ⟩ k ηR = {!   !}

M—↠ⱽN⇒Mⱽ≡Nⱽ : ∀ {Γ Θ A} (M N : Γ ⟶ Θ ∣ A) (c : (Γ ᵒˣ) ᴺˣ × `¬ˣ (Θ ᵒˣ) ᴺˣ) (k : ((`¬ A) ⱽᵀ)) → M ᵗ—↠ⱽ N → (M ⱽᴸ) c k ≡ (N ⱽᴸ) c k
M—↠ⱽN⇒Mⱽ≡Nⱽ M .M c k (.M ∎ᵗⱽ) = refl
M—↠ⱽN⇒Mⱽ≡Nⱽ M N c k ( _ᵗ⟶ⱽ⟨_⟩_ .M {M′} {N} M⟶M′ M′↠N) = trans (M⟶ⱽN⇒Mⱽ≡Nⱽ M M′ c k M⟶M′) (M—↠ⱽN⇒Mⱽ≡Nⱽ M′ N c k M′↠N)

-- lemma : ∀ {Γ Θ A} (K : A ∣ Γ ⟶ Θ) (c : (Γ ᵒˣ) ᴺˣ × `¬ˣ (Θ ᵒˣ) ᴺˣ) (k : (A) ⱽᵀ)
--   →   (K ⱽᴿ) c ≡
--       (rename-coterm (rename-weaken id-var) id-var K ⱽᴿ) ⟨ ⟨ proj₁ c , k ⟩ , proj₂ c ⟩
-- lemma (` α) c k = refl
-- lemma fst[ K ] c k = ext {!   !}
-- lemma snd[ K ] c k = {!   !}
-- lemma `[ K , L ] c k = {!   !}
-- lemma not⟨ M ⟩ c k = {!   !}
-- lemma (μγ S) c k = {!   !}

K⟶ⱽL⇒Kⱽ≡Lⱽ : ∀ {Γ Θ A} (K L : A ∣ Γ ⟶ Θ) (c : (Γ ᵒˣ) ᴺˣ × `¬ˣ (Θ ᵒˣ) ᴺˣ) (k : (A) ⱽᵀ) → K ᶜ⟶ⱽ L → (K ⱽᴿ) c k ≡ (L ⱽᴿ) c k
K⟶ⱽL⇒Kⱽ≡Lⱽ K .(μγ (` `Z ● rename-coterm (rename-weaken id-var) id-var K)) ⟨ c₁ , c₂ ⟩ k ηL = {!   !}

K—↠ⱽL⇒Kⱽ≡Lⱽ : ∀ {Γ Θ A} (K L : A ∣ Γ ⟶ Θ) (c : (Γ ᵒˣ) ᴺˣ × `¬ˣ (Θ ᵒˣ) ᴺˣ) (k : (A) ⱽᵀ) → K ᶜ—↠ⱽ L → (K ⱽᴿ) c k ≡ (L ⱽᴿ) c k
K—↠ⱽL⇒Kⱽ≡Lⱽ K .K c k (.K ∎ᶜⱽ) = refl
K—↠ⱽL⇒Kⱽ≡Lⱽ K L c k (_ᶜ⟶ⱽ⟨_⟩_ .K {K′} {L} K⟶K′ K′↠L) = trans (K⟶ⱽL⇒Kⱽ≡Lⱽ K K′ c k K⟶K′) (K—↠ⱽL⇒Kⱽ≡Lⱽ K′ L c k K′↠L)