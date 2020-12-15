module Dual.Syntax where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)

infix  4 _⟶_∣_
infix  4 _↦_ 
infix  4 _∣_⟶_
infix  4 _∋_
infixl 5 _,_

infixr 7 _⇒ⱽ_
infixr 7 _⇒ᴺ_
infix 8 _`+_
infix 9 _`×_
infix 10 `¬_
infix 10 `¬ˣ

infix 4 _●_
infix  5 ƛⱽ_
infix  5 ƛᴺ_
infix  5 μθ
infix  5 μγ
infixl 7 _·ⱽ_
infixl 7 _·ᴺ_
infix  9 `_
infix  9 `S
infix  10 θ_
infix  10 γ_

--Types--

data Type : Set where
  `ℕ : Type
  _`×_ : Type → Type → Type
  _`+_ : Type → Type → Type
  `¬_ : Type → Type
  
--implication is defined in terms of other connectives
--it is defined differently for CBN and CBV

_⇒ⱽ_ : Type → Type → Type
A ⇒ⱽ B = `¬ (A `× `¬ B)

_⇒ᴺ_ : Type → Type → Type
A ⇒ᴺ B = `¬ A `+ B

--Contexts--

data Context : Set where
  ∅ : Context
  _,_ : Context → Type → Context

`¬ˣ : Context → Context
`¬ˣ ∅ = ∅
`¬ˣ (Γ , A) = (`¬ˣ Γ) , (`¬ A)

data _∋_ : Context → Type → Set where

  `Z : ∀ {Γ A}
      ---------
    → Γ , A ∋ A

  `S : ∀ {Γ A B}
    → Γ ∋ A
      ---------
    → Γ , B ∋ A

--Sequents--

data _⟶_∣_ : Context → Context → Type → Set 

data _∣_⟶_ : Type → Context → Context → Set

data _↦_ : Context → Context → Set

--lambdas and function application are syntactic sugar

ƛⱽ_ : ∀ {Γ Θ A B}
  → Γ , A `× `¬ B , A ⟶ Θ ∣ B
    --------------------------
  → Γ ⟶ Θ ∣ A ⇒ⱽ B 

ƛᴺ_ : ∀ {Γ Θ A B}
  → Γ , A ⟶ Θ , `¬ A `+ B ∣ B
    --------------------------
  → Γ ⟶ Θ ∣ A ⇒ᴺ B

_·ⱽ_ : ∀ {Γ Θ A B}
    → Γ ⟶ Θ ∣ A
    → B ∣ Γ ⟶ Θ
      ---------------
    → A ⇒ⱽ B ∣ Γ ⟶ Θ 

_·ᴺ_ : ∀ {Γ Θ A B}
    → Γ ⟶ Θ ∣ A
    → B ∣ Γ ⟶ Θ
      ---------------
    → A ⇒ᴺ B ∣ Γ ⟶ Θ 

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

ƛⱽ N = not[ μγ(γ 0 ● fst[ μγ (γ 1 ● snd[ not⟨ N ⟩ ]) ]) ]

ƛᴺ N = μθ (inl⟨ not[ μγ(inr⟨ N ⟩ ● θ 0) ] ⟩ ● θ 0) 

M ·ⱽ N = not⟨ `⟨ M , not[ N ] ⟩ ⟩

M ·ᴺ N = `[ not⟨ M ⟩ , N ]

-- data Value : ∀ {Γ Θ A} → Γ ⟶ Θ ∣ A → Set 
-- data Covalue : ∀ {Γ Θ A} → A ∣ Γ ⟶ Θ → Set

-- data Value where

--   V-var : ∀ {Γ A} {x : Γ ∋ A}
--       ---------
--     → Value (` x)

--   V-prod : ∀ {Γ Θ A B} {M : Γ ⟶ Θ ∣ A} {N : Γ ⟶ Θ ∣ B}
--     → Value M
--     → Value N
--       ---------------
--     → Value `⟨ M , N ⟩

--   V-inl : ∀ {Γ Θ A B} {M ∶ Γ ⟶ Θ ∣ A `× B}
--     → Value M
--       -------------
--     → Value inl⟨ M ⟩

--   V-inr : ∀ {Γ Θ A B} {M ∶ Γ ⟶ Θ ∣ A `× B}
--     → Value M
--       -------------
--     → Value inr⟨ M ⟩

--   V-not : ∀ {Γ Θ A} {K : A ∣ Γ ⟶ Θ}
--       --------------
--     → Value not[ K ]


-- data Covalue where
  
--   CV-covar : ∀ {Θ A} {α : Θ ∋ A}
--       -------
--     → Covalue(` α)

--   CV-sum : ∀ {Γ Θ A B} {K : A ∣ Γ ⟶ Θ} {L : B ∣ Γ ⟶ Θ}
--     → Covalue K
--     → Covalue L
--       ------------------
--     → Covalue `[ K , L ]

--   CV-fst : ∀ {Γ Θ A B} {K ∶ A `+ B ∣ Γ ⟶ Θ}
--     → Covalue K
--       ----------------
--     → Covalue fst[ K ]

--   CV-snd : ∀ {Γ Θ A B} {K ∶ A `+ B ∣ Γ ⟶ Θ}
--     → Covalue K
--       ----------------
--     → Covalue snd[ K ]

--   CV-not : ∀ {Γ Θ A} {M : Γ ⟶ Θ ∣ A}
--       --------------
--     → Covalue not⟨ M ⟩

