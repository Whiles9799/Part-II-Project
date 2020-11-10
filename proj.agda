{-# OPTIONS --rewriting #-}

module proj where

  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; cong; cong₂; sym)
  open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
  open import Relation.Nullary using (¬_)
  open import Relation.Nullary.Decidable using (True; toWitness)
  open import Agda.Builtin.Equality.Rewrite

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

    ⟨_,_⟩ : ∀ {Γ Θ A B}
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

    [_,_] : ∀ {Γ Θ A B}
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

  M ·ⱽ N = not⟨ ⟨ M , not[ N ] ⟩ ⟩

  M ·ᴺ N = [ not⟨ M ⟩ , N ]


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
  (⟨ M , N ⟩) ᵒᴸ           = [ M ᵒᴸ , N ᵒᴸ ]
  (inl⟨ M ⟩) ᵒᴸ            = fst[ M ᵒᴸ ] 
  (inr⟨ M ⟩) ᵒᴸ            = snd[ M ᵒᴸ ]
  (not[ K ]) ᵒᴸ           = not⟨ K ᵒᴿ ⟩
  (μθ {Γ} {Θ} {A} (S)) ᵒᴸ = μγ( _ᵒᶜ {Γ} {(Θ , A)} S )

  (` α) ᵒᴿ                = ` (α ᵒⱽ)
  ([ K , L ]) ᵒᴿ          = ⟨ K ᵒᴿ , L ᵒᴿ ⟩
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

  [Mᵒᴸ]ᵒᴿ≡M (` x)       = cong `_     ([xᵒⱽ]ᵒⱽ≡x x)
  [Mᵒᴸ]ᵒᴿ≡M (⟨ M , N ⟩)  = cong₂ ⟨_,_⟩ ([Mᵒᴸ]ᵒᴿ≡M M) ([Mᵒᴸ]ᵒᴿ≡M N)
  [Mᵒᴸ]ᵒᴿ≡M (inl⟨ M ⟩)   = cong inl⟨_⟩ ([Mᵒᴸ]ᵒᴿ≡M M)
  [Mᵒᴸ]ᵒᴿ≡M (inr⟨ M ⟩)   = cong inr⟨_⟩ ([Mᵒᴸ]ᵒᴿ≡M M)
  [Mᵒᴸ]ᵒᴿ≡M (not[ K ])  = cong not[_] ([Kᵒᴿ]ᵒᴸ≡K K)
  [Mᵒᴸ]ᵒᴿ≡M (μθ S)      = cong μθ     ([Sᵒᶜ]ᵒᶜ≡S S)

  [Kᵒᴿ]ᵒᴸ≡K (` α)       = cong `_     ([xᵒⱽ]ᵒⱽ≡x α)
  [Kᵒᴿ]ᵒᴸ≡K ([ K , L ]) = cong₂ [_,_] ([Kᵒᴿ]ᵒᴸ≡K K) ([Kᵒᴿ]ᵒᴸ≡K L)
  [Kᵒᴿ]ᵒᴸ≡K (fst[ K ])  = cong fst[_] ([Kᵒᴿ]ᵒᴸ≡K K)
  [Kᵒᴿ]ᵒᴸ≡K (snd[ K ])  = cong snd[_] ([Kᵒᴿ]ᵒᴸ≡K K)
  [Kᵒᴿ]ᵒᴸ≡K (not⟨ M ⟩)   = cong not⟨_⟩ ([Mᵒᴸ]ᵒᴿ≡M M)
  [Kᵒᴿ]ᵒᴸ≡K (μγ S)      = cong μγ     ([Sᵒᶜ]ᵒᶜ≡S S)

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



  


  

