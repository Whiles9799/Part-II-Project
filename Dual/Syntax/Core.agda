module Dual.Syntax.Core where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Axiom.Extensionality.Propositional using (Extensionality; ExtensionalityImplicit)
open import Level as L hiding (lift) public

infix  4 _⟶_∣_
infix  4 _↦_ 
infix  4 _∣_⟶_

infix 8 _`+_
infix 9 _`×_
infix 10 `¬_
infix 10 `¬ˣ

infix 4 _●_

infix  5 μθ
infix  5 μγ

infix  9 `_
infix  10 θ_
infix  10 γ_

postulate
  ext  : Extensionality 0ℓ 0ℓ
  iext : ExtensionalityImplicit 0ℓ 0ℓ

--Types--

data Type : Set where
  `ℕ : Type
  _`×_ : Type → Type → Type
  _`+_ : Type → Type → Type
  `¬_ : Type → Type

open import Dual.Syntax.ContextandVars Type public


`¬ˣ : Context → Context
`¬ˣ ∅ = ∅
`¬ˣ (Γ , A) = (`¬ˣ Γ) , (`¬ A)

--Sequents--

data _⟶_∣_ : Context → Context → Type → Set 

data _∣_⟶_ : Type → Context → Context → Set

data _↦_ : Context → Context → Set

--lambdas and function application are syntactic sugar

data _⟶_∣_ where
  
  `_ : ∀ {Γ Θ A}
    → Γ ∋ A
      ----------
    → Γ ⟶ Θ ∣ A 

  `⟨_,_⟩ : ∀ {Γ Θ A B}
    → Γ ⟶ Θ ∣ A
    → Γ ⟶ Θ ∣ B
      ---------------
    → Γ ⟶ Θ ∣ A `× B

  inl⟨_⟩ : ∀ {Γ Θ A B}
    → Γ ⟶ Θ ∣ A
      ---------------
    → Γ ⟶ Θ ∣ A `+ B 

  inr⟨_⟩ : ∀ {Γ Θ A B}
    → Γ ⟶ Θ ∣ B
      ---------------
    → Γ ⟶ Θ ∣ A `+ B

  not[_] : ∀ {Γ Θ A}
    → A ∣ Γ ⟶ Θ
      -------------
    → Γ ⟶ Θ ∣ `¬ A

  μθ : ∀ {Γ Θ A}
    → Γ ↦ Θ , A
      ----------
    → Γ ⟶ Θ ∣ A

data _∣_⟶_ where
  
  `_ : ∀ {Γ Θ A}
    → Θ ∋ A
      ----------
    → A ∣ Γ ⟶ Θ

  fst[_] : ∀ {Γ Θ A B}
    → A ∣ Γ ⟶ Θ
      ---------------
    → A `× B ∣ Γ ⟶ Θ

  snd[_] : ∀ {Γ Θ A B}
    → B ∣ Γ ⟶ Θ
      ---------------
    → A `× B ∣ Γ ⟶ Θ

  `[_,_] : ∀ {Γ Θ A B}
    → A ∣ Γ ⟶ Θ
    → B ∣ Γ ⟶ Θ
      ---------------
    → A `+ B ∣ Γ ⟶ Θ

  not⟨_⟩ : ∀ {Γ Θ A}
    → Γ ⟶ Θ ∣ A
      -------------
    → `¬ A ∣ Γ ⟶ Θ
    
  μγ : ∀ {Γ Θ A}
    → Γ , A ↦ Θ
      ----------
    → A ∣ Γ ⟶ Θ

data _↦_ where

  _●_ : ∀ {Γ Θ A}
    → Γ ⟶ Θ ∣ A
    → A ∣ Γ ⟶ Θ
      ----------
    → Γ ↦ Θ

Term : Context → Context → Type → Set 
Term Γ Θ A = Γ ⟶ Θ ∣ A

Coterm : Context → Context → Type → Set 
Coterm Γ Θ A = A ∣ Γ ⟶ Θ

Statement : Context → Context → Set 
Statement Γ Θ = Γ ↦ Θ

Fix₁ : (T : Context → Context → Type → Set) (Γ : Context) → (Context → Type → Set)
Fix₁ T Γ = λ Θ A → T Γ Θ A

Fix₂ : (T : Context → Context → Type → Set) (Θ : Context) → (Context → Type → Set)
Fix₂ T Θ = λ Γ A → T Γ Θ A

lookup : Context → ℕ → Type
lookup (Γ , A) zero    = A
lookup (Γ , _) (suc n) = lookup Γ n
lookup ∅       _       = ⊥-elim impossible
  where postulate impossible : ⊥ 

count : ∀ {Γ} → (n : ℕ) → Γ ∋ lookup Γ n
count {Γ , _} zero    = `Z
count {Γ , _} (suc n) = `S (count n)
count {∅}     _       = ⊥-elim impossible
  where postulate impossible : ⊥

--We define a separate way to refer to variables and covariables

γ_ : ∀ {Γ Θ} → (n : ℕ) → Γ ⟶ Θ ∣ lookup Γ n
γ n = ` count n

θ_ : ∀ {Γ Θ} → (n : ℕ) → lookup Θ n ∣ Γ ⟶ Θ
θ n = ` count n


--Lambda Abstraction and Function Application--

