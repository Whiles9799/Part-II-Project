module Dual.ExampleTerms (R : Set) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Relation.Nullary using (¬_)
open import Dual.Syntax
open import Dual.DualTranslation
open import Dual.CPSTransformation R
--open import IO using (run; putStrLn)

lem : ∀ {A} → ∅ ⟶ ∅ ∣ A `+ `¬ A
lem = μθ (inr⟨ not[ μγ (inl⟨ γ 0 ⟩ ● (θ 0) ) ] ⟩ ● (θ 0))

lemⱽ : ∀ {A} → ((A ⱽᵀ ⊎ (A ⱽᵀ → R)) → R) → R
lemⱽ {A} = (lem {A} ⱽᴸ) ⟨ tt , tt ⟩ 

lemⱽ-norm : ∀ {A} → ((A ⊎ (A → R)) → R) → R
lemⱽ-norm {A} = λ α → α (inj₂ (λ x → α (inj₁ x)))

lemᴺ : ∀ {A} → ((A ᴺᵀ × (A ᴺᵀ → R)) → R)
lemᴺ = (lem ᴺᴸ) ⟨ tt , tt ⟩ 

lemᴺ-norm : ∀ {A} → (A × (A → R)) → R
lemᴺ-norm = λ α → proj₂ α (proj₁ α)

dnl : ∀ {A} → ∅ ⟶ ∅ ∣ (`¬ (`¬ A)) ⇒ⱽ A
dnl = ƛⱽ (μθ (ƛⱽ γ 0 ● ( γ 0 ·ⱽ μγ (γ 0 ● not⟨ not[ θ 0 ] ⟩))))

lnc : ∀ {A} → ∅ ⟶ ∅ ∣ `¬(A `× (`¬ A))
lnc = not[ μγ ( γ 0 ● fst[ (μγ ((γ 1) ● snd[ not⟨ γ 0 ⟩ ])) ]) ]

coc : ∀ {P Q} → ∅ ⟶ ∅ ∣ ((P `× Q) ⇒ⱽ (Q `× P)) `× ((Q `× P) ⇒ⱽ (P `× Q))
coc = `⟨ ƛⱽ `⟨ (μθ ((γ 0) ● snd[ (θ 0) ])) , (μθ ((γ 0) ● fst[ (θ 0) ])) ⟩ , ƛⱽ `⟨ (μθ ((γ 0) ● snd[ (θ 0) ])) , μθ ((γ 0) ● fst[ (θ 0) ]) ⟩ ⟩ 

pierce : ∀ {A B} → ∅ ⟶ ∅ ∣ (((A ⇒ⱽ B) ⇒ⱽ A) ⇒ⱽ A)
pierce = ƛⱽ (μθ (γ 0 ● ((ƛⱽ (μθ (γ 0 ● (θ 1)))) ·ⱽ θ 0)))

demorgan : ∀ {P Q} → (∅ , (`¬ P) `+ (`¬ Q)) ⟶ ∅ ∣ `¬ (P `× Q)
demorgan = {!   !}

--main = (run (putStrLn "Hello World"))
