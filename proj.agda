{-# OPTIONS --rewriting #-}

module proj where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Agda.Builtin.Equality.Rewrite
open import Axiom.Extensionality.Propositional using (Extensionality; ExtensionalityImplicit)
open import Level as L hiding (lift) public

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

infix 4 _●_
infix  5 ƛⱽ_
infix  5 ƛᴺ_
infix  5 μθ
infix  5 μγ
infixl 7 _·ⱽ_
infixl 7 _·ᴺ_
infix  9 `_
infix  9 `S
infix  9 θ_
infix  9 γ_

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




--Dual Translation--

_ᵒᵀ : Type → Type
_ᵒˣ : Context → Context
_ᵒⱽ : ∀ {Γ A} → (Γ ∋ A) → (Γ ᵒˣ ∋ A ᵒᵀ)  
_ᵒᶜ : ∀ {Γ Θ} → (Γ ↦ Θ) → (Θ ᵒˣ ↦ Γ ᵒˣ)
_ᵒᴸ : ∀ {Γ Θ A} → (Γ ⟶ Θ ∣ A) → (A ᵒᵀ ∣ Θ ᵒˣ ⟶ Γ ᵒˣ)
_ᵒᴿ : ∀ {Γ Θ A} → (A ∣ Γ ⟶ Θ) → (Θ ᵒˣ ⟶ Γ ᵒˣ ∣ A ᵒᵀ)


(A `+ B)ᵒᵀ  = (A ᵒᵀ `× B ᵒᵀ)
(A `× B)ᵒᵀ  = (A ᵒᵀ `+ B ᵒᵀ)
(`¬ A)ᵒᵀ    = (`¬ (A)ᵒᵀ) 
(`ℕ)ᵒᵀ      = `ℕ

(∅ ᵒˣ)     = ∅
(Γ , A) ᵒˣ = ((Γ ᵒˣ) , (A ᵒᵀ))

`Z ᵒⱽ     = `Z
(`S x) ᵒⱽ = `S (x ᵒⱽ)

(` x)ᵒᴸ                 = `(x ᵒⱽ)
(`⟨ M , N ⟩) ᵒᴸ           = `[ M ᵒᴸ , N ᵒᴸ ]
(inl⟨ M ⟩) ᵒᴸ            = fst[ M ᵒᴸ ] 
(inr⟨ M ⟩) ᵒᴸ            = snd[ M ᵒᴸ ]
(not[ K ]) ᵒᴸ           = not⟨ K ᵒᴿ ⟩
(μθ {Γ} {Θ} {A} (S)) ᵒᴸ = μγ( _ᵒᶜ {Γ} {(Θ , A)} S )

(` α) ᵒᴿ                = ` (α ᵒⱽ)
(`[ K , L ]) ᵒᴿ          = `⟨ K ᵒᴿ , L ᵒᴿ ⟩
(fst[ K ]) ᵒᴿ           = inl⟨ K ᵒᴿ ⟩
(snd[ K ]) ᵒᴿ           = inr⟨ K ᵒᴿ ⟩
(not⟨ M ⟩) ᵒᴿ            = not[ M ᵒᴸ ]
(μγ {Γ} {Θ} {A} (S)) ᵒᴿ = μθ( _ᵒᶜ {(Γ , A)} {Θ} (S) )

(M ● K) ᵒᶜ = K ᵒᴿ ● M ᵒᴸ


--Properties of the Dual Translation--

--The Dual Translation is an Involution--

[Aᵒᵀ]ᵒᵀ≡A : ∀ {A} → (A ᵒᵀ) ᵒᵀ ≡ A
[Aᵒᵀ]ᵒᵀ≡A {`ℕ}     = refl
[Aᵒᵀ]ᵒᵀ≡A {`¬ A}   = cong `¬_   [Aᵒᵀ]ᵒᵀ≡A 
[Aᵒᵀ]ᵒᵀ≡A {A `+ B} = cong₂ _`+_ ([Aᵒᵀ]ᵒᵀ≡A {A}) ([Aᵒᵀ]ᵒᵀ≡A {B})
[Aᵒᵀ]ᵒᵀ≡A {A `× B} = cong₂ _`×_ ([Aᵒᵀ]ᵒᵀ≡A {A}) ([Aᵒᵀ]ᵒᵀ≡A {B})

[Γᵒˣ]ᵒˣ≡Γ : ∀ {Γ} → (Γ ᵒˣ) ᵒˣ ≡ Γ
[Γᵒˣ]ᵒˣ≡Γ {∅}       = refl
[Γᵒˣ]ᵒˣ≡Γ {(Γ , A)} = cong₂ _,_ [Γᵒˣ]ᵒˣ≡Γ [Aᵒᵀ]ᵒᵀ≡A

--we use these rewrite rules to handle equality between a term and a dual translated term
--as those two terms will be indexed by different contexts and type
{-# REWRITE [Aᵒᵀ]ᵒᵀ≡A #-}
{-# REWRITE [Γᵒˣ]ᵒˣ≡Γ #-}

[xᵒⱽ]ᵒⱽ≡x : ∀ {Γ A} (x : Γ ∋ A) → ((x ᵒⱽ) ᵒⱽ) ≡ x
[xᵒⱽ]ᵒⱽ≡x (`Z)   = refl
[xᵒⱽ]ᵒⱽ≡x (`S x) = cong `S ([xᵒⱽ]ᵒⱽ≡x x)

[Kᵒᴿ]ᵒᴸ≡K : ∀ {Γ Θ A} (K : A ∣ Γ ⟶ Θ) → (K ᵒᴿ) ᵒᴸ ≡ K
[Mᵒᴸ]ᵒᴿ≡M : ∀ {Γ Θ A} (M : Γ ⟶ Θ ∣ A) → (M ᵒᴸ) ᵒᴿ ≡ M 
[Sᵒᶜ]ᵒᶜ≡S : ∀ {Γ Θ}   (S : Γ ↦ Θ)     → (S ᵒᶜ) ᵒᶜ ≡ S

[Mᵒᴸ]ᵒᴿ≡M (` x)        = cong `_     ([xᵒⱽ]ᵒⱽ≡x x)
[Mᵒᴸ]ᵒᴿ≡M (`⟨ M , N ⟩)  = cong₂ `⟨_,_⟩ ([Mᵒᴸ]ᵒᴿ≡M M) ([Mᵒᴸ]ᵒᴿ≡M N)
[Mᵒᴸ]ᵒᴿ≡M (inl⟨ M ⟩)    = cong inl⟨_⟩ ([Mᵒᴸ]ᵒᴿ≡M M)
[Mᵒᴸ]ᵒᴿ≡M (inr⟨ M ⟩)    = cong inr⟨_⟩ ([Mᵒᴸ]ᵒᴿ≡M M)
[Mᵒᴸ]ᵒᴿ≡M (not[ K ])   = cong not[_] ([Kᵒᴿ]ᵒᴸ≡K K)
[Mᵒᴸ]ᵒᴿ≡M (μθ S)       = cong μθ     ([Sᵒᶜ]ᵒᶜ≡S S)

[Kᵒᴿ]ᵒᴸ≡K (` α)        = cong `_     ([xᵒⱽ]ᵒⱽ≡x α)
[Kᵒᴿ]ᵒᴸ≡K (`[ K , L ]) = cong₂ `[_,_] ([Kᵒᴿ]ᵒᴸ≡K K) ([Kᵒᴿ]ᵒᴸ≡K L)
[Kᵒᴿ]ᵒᴸ≡K (fst[ K ])   = cong fst[_] ([Kᵒᴿ]ᵒᴸ≡K K)
[Kᵒᴿ]ᵒᴸ≡K (snd[ K ])   = cong snd[_] ([Kᵒᴿ]ᵒᴸ≡K K)
[Kᵒᴿ]ᵒᴸ≡K (not⟨ M ⟩)    = cong not⟨_⟩ ([Mᵒᴸ]ᵒᴿ≡M M)
[Kᵒᴿ]ᵒᴸ≡K (μγ S)       = cong μγ     ([Sᵒᶜ]ᵒᶜ≡S S)

[Sᵒᶜ]ᵒᶜ≡S (M ● K)     = cong₂ _●_   ([Mᵒᴸ]ᵒᴿ≡M M) ([Kᵒᴿ]ᵒᴸ≡K K)

--A Dual Calculus term is derivable iff its dual is derivable--

Γ⟶Θ∣A⇒Aᵒ∣Θᵒ⟶Γᵒ : ∀ {Γ Θ A} → (Γ ⟶ Θ ∣ A) → A ᵒᵀ ∣ Θ ᵒˣ ⟶ Γ ᵒˣ
Γ⟶Θ∣A⇒Aᵒ∣Θᵒ⟶Γᵒ M = M ᵒᴸ

Γ⟶Θ∣A⇐Aᵒ∣Θᵒ⟶Γᵒ : ∀ {Γ Θ A} → (A ᵒᵀ ∣ Θ ᵒˣ ⟶ Γ ᵒˣ) → Γ ⟶ Θ ∣ A
Γ⟶Θ∣A⇐Aᵒ∣Θᵒ⟶Γᵒ Mᵒᴸ = Mᵒᴸ ᵒᴿ 

A∣Γ⟶Θ⇒Θᵒ⟶Γᵒ∣Aᵒ : ∀ {Γ Θ A} → (A ∣ Γ ⟶ Θ) → Θ ᵒˣ ⟶ Γ ᵒˣ ∣ A ᵒᵀ
A∣Γ⟶Θ⇒Θᵒ⟶Γᵒ∣Aᵒ K = K ᵒᴿ

A∣Γ⟶Θ⇐Θᵒ⟶Γᵒ∣Aᵒ : ∀ {Γ Θ A} → (Θ ᵒˣ ⟶ Γ ᵒˣ ∣ A ᵒᵀ) → A ∣ Γ ⟶ Θ
A∣Γ⟶Θ⇐Θᵒ⟶Γᵒ∣Aᵒ Kᵒᴿ = Kᵒᴿ ᵒᴸ

Γ↦Θ⇒Θᵒ↦Γᵒ : ∀ {Γ Θ} → (Γ ↦ Θ) → Θ ᵒˣ ↦ Γ ᵒˣ
Γ↦Θ⇒Θᵒ↦Γᵒ S = S ᵒᶜ

Γ↦Θ⇐Θᵒ↦Γᵒ : ∀ {Γ Θ} → (Θ ᵒˣ ↦ Γ ᵒˣ) → Γ ↦ Θ
Γ↦Θ⇐Θᵒ↦Γᵒ Sᵒᶜ = Sᵒᶜ ᵒᶜ


--Call-by-Value CPS Transformation--


--Types and Contexts--

_ⱽᵀ : Type → Set
_ⱽˣ : Context → Set

`ℕ ⱽᵀ       = ℕ
(A `× B) ⱽᵀ = (A ⱽᵀ) × (B ⱽᵀ)
(A `+ B) ⱽᵀ = (A ⱽᵀ) ⊎ (B ⱽᵀ)
(`¬ A) ⱽᵀ   = (A ⱽᵀ) → ⊥

∅ ⱽˣ       = ⊤
(Γ , A) ⱽˣ = Γ ⱽˣ  × A ⱽᵀ  


--Variables--

_ⱽⱽ : ∀ {Γ A} → (Γ ∋ A) → ((Γ ⱽˣ) → (A ⱽᵀ))
_ⱽⱽ `Z     = λ x → proj₂ x 
_ⱽⱽ (`S x) = λ c → ((x ⱽⱽ) (proj₁ c))

Γ∋A⇒¬Γ∋¬A : ∀ {Γ A} → (Γ ∋ A) → (`¬ˣ Γ) ∋ (`¬ A)
Γ∋A⇒¬Γ∋¬A `Z = `Z
Γ∋A⇒¬Γ∋¬A (`S x) = `S (Γ∋A⇒¬Γ∋¬A x)


--Terms--

_ⱽᴸ : ∀ {Γ Θ A} → (Γ ⟶ Θ ∣ A) → (Γ ⱽˣ × (`¬ˣ Θ) ⱽˣ) → ((`¬ `¬ A) ⱽᵀ)
_ⱽᴿ : ∀ {Γ Θ A} → (A ∣ Γ ⟶ Θ) → (Γ ⱽˣ × (`¬ˣ Θ) ⱽˣ) → ((`¬ A) ⱽᵀ)
_ⱽᶜ : ∀ {Γ Θ} → (Γ ↦ Θ) → Γ ⱽˣ × (`¬ˣ Θ) ⱽˣ → ⊥

_ⱽᴸ (` x)            = λ c k → k ((x ⱽⱽ) (proj₁ c))
`⟨ M , N ⟩ ⱽᴸ         = λ c k → (M ⱽᴸ) c (λ x → (N ⱽᴸ) c (λ y → k ⟨ x , y ⟩))
inl⟨ M ⟩ ⱽᴸ           = λ c k → (M ⱽᴸ) c (λ x → k (inj₁ x))
inr⟨ M ⟩ ⱽᴸ           = λ c k → (M ⱽᴸ) c (λ x → k (inj₂ x))
not[ K ] ⱽᴸ          = λ c k → k (λ z → (K ⱽᴿ) c z)
_ⱽᴸ {Γ}{Θ}{A} (μθ S) = λ c α → (S ⱽᶜ) ⟨ (proj₁ c) , ⟨ (proj₂ c) , α ⟩ ⟩

(` α) ⱽᴿ             = λ c z → ((Γ∋A⇒¬Γ∋¬A α) ⱽⱽ) (proj₂ c) z 
`[ K , L ] ⱽᴿ        = λ c → λ{ (inj₁ x) → (K ⱽᴿ) c x ; (inj₂ y) → (L ⱽᴿ) c y}
fst[ K ] ⱽᴿ          = λ c → λ{ ⟨ x , _ ⟩ → (K ⱽᴿ) c x} 
snd[ L ] ⱽᴿ          = λ c → λ{ ⟨ _ , y ⟩ → (L ⱽᴿ) c y}
not⟨ M ⟩ ⱽᴿ           = λ c z → (λ k → (M ⱽᴸ) c k) z
_ⱽᴿ {Γ}{Θ}{A} (μγ S) = λ c x →  (S ⱽᶜ) ⟨ ⟨ proj₁ c , x ⟩ , (proj₂ c) ⟩

(M ● K) ⱽᶜ           = λ c → ((M ⱽᴸ) c) ((K ⱽᴿ) c)


--Call-by-Name CPS Transformation--


--Types and Contexts--
_ᴺᵀ : Type → Set
_ᴺˣ : Context → Set

`ℕ ᴺᵀ = ℕ
(A `× B) ᴺᵀ  = (A ᴺᵀ) ⊎ (B ᴺᵀ)
(A `+ B) ᴺᵀ  = (A ᴺᵀ) × (B ᴺᵀ)
(`¬ A) ᴺᵀ = (A ᴺᵀ) → ⊥

∅ ᴺˣ = ⊤
(Γ , A) ᴺˣ =  Γ ᴺˣ × A ᴺᵀ 


--Variables--
_ᴺⱽ : ∀ {Θ A} → (Θ ∋ A) → (Θ ᴺˣ) → (A ᴺᵀ)
_ᴺⱽ `Z     = λ x → proj₂ x 
_ᴺⱽ (`S x) = λ c → ((x ᴺⱽ) (proj₁ c))


--Terms--
_ᴺᴸ : ∀ {Γ Θ A} → (Γ ⟶ Θ ∣ A) → (Θ ᴺˣ × (`¬ˣ Γ) ᴺˣ) → (`¬ A) ᴺᵀ
_ᴺᴿ : ∀ {Γ Θ A} → (A ∣ Γ ⟶ Θ) → (Θ ᴺˣ × (`¬ˣ Γ) ᴺˣ) → (`¬ `¬ A) ᴺᵀ
_ᴺᶜ : ∀ {Γ Θ}   → (Γ ↦ Θ)     → (Θ ᴺˣ × (`¬ˣ Γ) ᴺˣ) → ⊥

(` x) ᴺᴸ             = λ c k → ((Γ∋A⇒¬Γ∋¬A x) ᴺⱽ) (proj₂ c) k
`⟨ M , N ⟩ ᴺᴸ         = λ c → λ{(inj₁ α) → (M ᴺᴸ) c α ; (inj₂ β) → (N ᴺᴸ) c β}
inl⟨ M ⟩ ᴺᴸ           = λ c → λ{⟨ α , _ ⟩ → (M ᴺᴸ) c α}
inr⟨ N ⟩ ᴺᴸ           = λ c → λ{⟨ _ , β ⟩ → (N ᴺᴸ) c β}
not[ K ] ᴺᴸ          = λ c k → (λ z → (K ᴺᴿ) c z) k
_ᴺᴸ {Γ}{Θ}{A} (μθ S) = λ c α → (S ᴺᶜ) ⟨ ⟨ proj₁ c , α ⟩ , proj₂ c ⟩

(` α) ᴺᴿ             = λ c z → z ((α ᴺⱽ) (proj₁ c))
`[ K , L ] ᴺᴿ        = λ c z → (K ᴺᴿ) c (λ α → (L ᴺᴿ) c (λ β → z ⟨ α , β ⟩))
fst[ K ] ᴺᴿ          = λ c z → (K ᴺᴿ) c (λ α → z (inj₁ α))
snd[ L ] ᴺᴿ          = λ c z → (L ᴺᴿ) c (λ β → z (inj₂ β))
not⟨ M ⟩ ᴺᴿ           = λ c z → z(λ k → (M ᴺᴸ) c k)
_ᴺᴿ {Γ}{Θ}{A} (μγ S) = λ c x →  (S ᴺᶜ) ⟨ proj₁ c , ⟨ proj₂ c , x ⟩ ⟩

(M ● K) ᴺᶜ           = λ c → ((K ᴺᴿ) c) ((M ᴺᴸ) c)

Aⱽ≡Aᵒᴺ : ∀ {A} → A ⱽᵀ ≡ (A ᵒᵀ) ᴺᵀ
Aⱽ≡Aᵒᴺ {`ℕ}     = refl 
Aⱽ≡Aᵒᴺ {A `+ B} = cong₂ _⊎_ (Aⱽ≡Aᵒᴺ {A}) (Aⱽ≡Aᵒᴺ {B})
Aⱽ≡Aᵒᴺ {A `× B} = cong₂ _×_ (Aⱽ≡Aᵒᴺ {A}) (Aⱽ≡Aᵒᴺ {B})
Aⱽ≡Aᵒᴺ {`¬ A}   = cong ¬_ Aⱽ≡Aᵒᴺ

Γⱽ≡Γᵒᴺ : ∀ {Γ} → Γ ⱽˣ ≡ (Γ ᵒˣ) ᴺˣ
Γⱽ≡Γᵒᴺ {∅}       = refl
Γⱽ≡Γᵒᴺ {(Γ , A)} = cong₂ _×_ Γⱽ≡Γᵒᴺ Aⱽ≡Aᵒᴺ

{-# REWRITE Aⱽ≡Aᵒᴺ #-}
{-# REWRITE Γⱽ≡Γᵒᴺ #-}

[¬Γ]ᵒ≡¬[Γᵒ] : ∀ {Γ} → (`¬ˣ Γ) ᵒˣ ≡ `¬ˣ (Γ ᵒˣ)
[¬Γ]ᵒ≡¬[Γᵒ] {∅} = refl
[¬Γ]ᵒ≡¬[Γᵒ] {(Γ , A)} = cong₂ _,_ ([¬Γ]ᵒ≡¬[Γᵒ] {Γ}) refl

{-# REWRITE [¬Γ]ᵒ≡¬[Γᵒ] #-}

postulate
  ext  : Extensionality 0ℓ 0ℓ
  ext₂ : {A : Set} {B : A → Set}{C : (x : A) → B x → Set}
         {f g : (x : A) → (y : B x) → C x y}
      -> (∀ x y → f x y ≡ g x y)
      -> (λ x y → f x y) ≡ (λ x y → g x y)

[Γ∋A⇒¬Γ∋¬Aα]ᵒ≡Γ∋A⇒¬Γ∋¬A[xᵒ] : ∀ {Γ A} (x : Γ ∋ A) → Γ∋A⇒¬Γ∋¬A x ᵒⱽ ≡ Γ∋A⇒¬Γ∋¬A (x ᵒⱽ)
[Γ∋A⇒¬Γ∋¬Aα]ᵒ≡Γ∋A⇒¬Γ∋¬A[xᵒ] `Z = refl
[Γ∋A⇒¬Γ∋¬Aα]ᵒ≡Γ∋A⇒¬Γ∋¬A[xᵒ] (`S x) = cong `S ([Γ∋A⇒¬Γ∋¬Aα]ᵒ≡Γ∋A⇒¬Γ∋¬A[xᵒ] x)

{-# REWRITE [Γ∋A⇒¬Γ∋¬Aα]ᵒ≡Γ∋A⇒¬Γ∋¬A[xᵒ] #-}

xⱽ≡xᵒᴺ : ∀ {Γ A} (x : Γ ∋ A) → x ⱽⱽ ≡ ((x ᵒⱽ) ᴺⱽ)
Mⱽ≡Mᵒᴺ : ∀ {Γ Θ A} (M : Γ ⟶ Θ ∣ A) → M ⱽᴸ ≡ (M ᵒᴸ) ᴺᴿ 
Kⱽ≡Kᵒᴺ : ∀ {Γ Θ A} (K : A ∣ Γ ⟶ Θ) → K ⱽᴿ ≡ ((K ᵒᴿ) ᴺᴸ)
Sⱽ≡Sᵒᴺ : ∀ {Γ Θ}   (S : Γ ↦ Θ)     → S ⱽᶜ ≡ (S ᵒᶜ) ᴺᶜ

xⱽ≡xᵒᴺ `Z         = refl
xⱽ≡xᵒᴺ (`S x)     = ext (λ c → cong (λ - → - (proj₁ c)) (xⱽ≡xᵒᴺ x))

Mⱽ≡Mᵒᴺ (` x)      = ext₂ (λ c k → cong (λ - → k(- (proj₁ c))) (xⱽ≡xᵒᴺ x)) 
Mⱽ≡Mᵒᴺ `⟨ M , N ⟩  = ext₂ (λ c k → cong₂ (λ x₁ x₂ → x₁ c (λ x → x₂ c (λ y → k ⟨ x , y ⟩))) (Mⱽ≡Mᵒᴺ M) (Mⱽ≡Mᵒᴺ N)) 
Mⱽ≡Mᵒᴺ inl⟨ M ⟩    = ext₂ (λ c k → cong ((λ - → -  c (λ x → k (inj₁ x)))) (Mⱽ≡Mᵒᴺ M))
Mⱽ≡Mᵒᴺ inr⟨ M ⟩    = ext₂ (λ c k → cong ((λ - → -  c (λ x → k (inj₂ x)))) (Mⱽ≡Mᵒᴺ M))
Mⱽ≡Mᵒᴺ not[ K ]   = ext₂ (λ c z → cong (λ - → z (- c)) (Kⱽ≡Kᵒᴺ K))
Mⱽ≡Mᵒᴺ (μθ S)     = ext₂ (λ c α → cong (λ - → -  ⟨ proj₁ c , ⟨ proj₂ c , α ⟩ ⟩) (Sⱽ≡Sᵒᴺ S))

Kⱽ≡Kᵒᴺ (` α)      = ext₂ (λ c z → cong (λ - → - (proj₂ c) z)  (xⱽ≡xᵒᴺ(Γ∋A⇒¬Γ∋¬A α))) --(Γ∋A⇒¬Γ∋¬A α ⱽⱽ) (proj₂ c) z ≡ (Γ∋A⇒¬Γ∋¬A (α ᵒⱽ) ᴺⱽ) (proj₂ c) z
Kⱽ≡Kᵒᴺ `[ K , L ] = ext₂ (λ c z → cong₂ (λ x₁ x₂ → (λ { (inj₁ x) → x₁ c x ; (inj₂ y) → x₂ c y }) z) (Kⱽ≡Kᵒᴺ K) (Kⱽ≡Kᵒᴺ L)) -- (λ { (inj₁ x) → (K ⱽᴿ) c x ; (inj₂ y) → (L ⱽᴿ) c y }) z ≡ (λ { (inj₁ α) → ((K ᵒᴿ) ᴺᴸ) c α ; (inj₂ β) → ((L ᵒᴿ) ᴺᴸ) c β }) z
Kⱽ≡Kᵒᴺ fst[ K ]   = ext₂ (λ c z → cong (λ - → (λ { ⟨ x , _ ⟩ → - c x }) z) (Kⱽ≡Kᵒᴺ K)) -- (λ { ⟨ x , _ ⟩ → (K ⱽᴿ) c x }) z ≡ (λ { ⟨ α , _ ⟩ → ((K ᵒᴿ) ᴺᴸ) c α }) z
Kⱽ≡Kᵒᴺ snd[ K ]   = ext₂ (λ c z → cong (λ - → (λ { ⟨ _ , y ⟩ → - c y }) z) (Kⱽ≡Kᵒᴺ K))
Kⱽ≡Kᵒᴺ not⟨ M ⟩    = ext₂ (λ c k → cong (λ - → - c k) (Mⱽ≡Mᵒᴺ M))
Kⱽ≡Kᵒᴺ (μγ S)     = ext₂ (λ c x → cong (λ - → - ⟨ ⟨ proj₁ c , x ⟩ , proj₂ c ⟩) (Sⱽ≡Sᵒᴺ S))

Sⱽ≡Sᵒᴺ (M ● K)    = ext (λ c → cong₂ (λ x₁ x₂ → x₁ c (x₂ c)) (Mⱽ≡Mᵒᴺ M) (Kⱽ≡Kᵒᴺ K)) 

-- Mⱽ≡Mᵒᴺ : ∀ {Γ Θ A} (M : Γ ⟶ Θ ∣ A) (c : Γ ⱽˣ × (`¬ˣ Θ) ⱽˣ) (k : ((`¬ A) ⱽᵀ)) → (M ⱽᴸ) c k ≡ ((M ᵒᴸ) ᴺᴿ) c k
-- Mⱽ≡Mᵒᴺ (` x) ⟨ c , _ ⟩ k = cong  (λ - → k(-  c)) (xⱽ≡xᵒᴺ x)
-- Mⱽ≡Mᵒᴺ `⟨ M , M₁ ⟩ c k = {!   !}
-- Mⱽ≡Mᵒᴺ inl⟨ M ⟩ c k = cong (λ - → -  c (λ x → k (inj₁ x))) (Mⱽ≡Mᵒᴺ M c k) -- (M ⱽᴸ) c (λ x → k (inj₁ x)) ≡ ((M ᵒᴸ) ᴺᴿ) c (λ α → k (inj₁ α))
-- Mⱽ≡Mᵒᴺ inr⟨ M ⟩ c k = {!   !}
-- Mⱽ≡Mᵒᴺ not[ x ] c k = {!   !}
-- Mⱽ≡Mᵒᴺ (μθ x) c k = {!   !} 