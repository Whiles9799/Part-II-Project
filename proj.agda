module proj where

  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
  open import Relation.Nullary using (¬_)
  open import Relation.Nullary.Decidable using (True; toWitness)

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
  infixl 7 _·_
  infix  9 `_
  infix  9 `S_
  infix  9 θ_
  infix  9 γ_


  data Type : Set where
    `ℕ : Type
    _`×_ : Type → Type → Type
    _`+_ : Type → Type → Type
    `¬_ : Type → Type
    
  _⇒ⱽ_ : Type → Type → Type
  A ⇒ⱽ B = `¬ (A `× `¬ B)

  _⇒ᴺ_ : Type → Type → Type
  A ⇒ᴺ B = `¬ A `+ B

  data Context : Set where
    ∅ : Context
    _,_ : Context → Type → Context

  data _∋_ : Context → Type → Set where

    `Z : ∀ {Γ A}
        ---------
      → Γ , A ∋ A

    `S_ : ∀ {Γ A B}
      → Γ ∋ A
        ---------
      → Γ , B ∋ A

  data _⟶_∣_ : Context → Context → Type → Set 

  data _∣_⟶_ : Type → Context → Context → Set

  data _↦_ : Context → Context → Set

  ƛⱽ_ : ∀ {Γ Θ A B}
    → Γ , A ⟶ Θ ∣ B
      ---------------
    → Γ ⟶ Θ ∣ A ⇒ⱽ B 

  ƛᴺ_ : ∀ {Γ Θ A B}
    → Γ , A ⟶ Θ ∣ B
      ---------------
    → Γ ⟶ Θ ∣ A ⇒ᴺ B

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

    --ƛ_ : ∀ {Γ Θ A B}
      --→ Γ , A ⟶ Θ ∣ B
        --------------
      --→ Γ ⟶ Θ ∣ A ⇒ B

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

    _·_ : ∀ {Γ Θ A B}
      → Γ ⟶ Θ ∣ A
      → B ∣ Γ ⟶ Θ
        ---------------
      → A ⇒ B ∣ Γ ⟶ Θ 
     
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

   
  ƛⱽ N = not[ μγ(γ 0 ● fst[ μγ (γ 1 ● snd[ not⟨ N ⟩ ]) ]) ]


  ƛᴺ N = μθ (inl⟨ not[ μγ(inr⟨ N ⟩ ● θ 0) ] ⟩ ● θ 0) 

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

  γ_ : ∀ {Γ Θ} → (n : ℕ) → Γ ⟶ Θ ∣ lookup Γ n
  γ n = ` count n

  θ_ : ∀ {Γ Θ} → (n : ℕ) → lookup Θ n ∣ Γ ⟶ Θ
  θ n = ` count n
  
  _ᵒᵀ : Type → Type
  _ᵒˣ : Context → Context
  ᵒᶜ : ∀ {Γ Θ} → (Γ ↦ Θ) → (Θ ᵒˣ ↦ Γ ᵒˣ)
  _ᵒᴸ : ∀ {Γ Θ A B} → (Γ ⟶ Θ ∣ A) → (A ᵒᵀ ∣ Θ ᵒˣ ⟶ Γ ᵒˣ)
  _ᵒᴿ : ∀ {Γ Θ A B} → (A ∣ Γ ⟶ Θ) → (Θ ᵒˣ ⟶ Γ ᵒˣ ∣ A ᵒᵀ)


  (A `+ B)ᵒᵀ  = (A ᵒᵀ `× B ᵒᵀ)
  (A `× B)ᵒᵀ  = (A ᵒᵀ `+ B ᵒᵀ)
  (`¬ A)ᵒᵀ    = (`¬ (A)ᵒᵀ) 
  (`ℕ)ᵒᵀ      = `ℕ
  --(A ⇒ B)ᵒᵀ   = (A ᵒᵀ ⇒ B ᵒᵀ) this is temporary until ive worked out how to handle function types

  (∅ ᵒˣ)     = ∅
  (Γ , A) ᵒˣ = ((Γ ᵒˣ) , (A ᵒᵀ))
  
  ᵒᶜ (M ● K) = K ᵒᴿ ● M ᵒᴸ

  (⟨ M , N ⟩) ᵒᴸ = [ M ᵒᴸ , N ᵒᴸ ]
  (inl⟨ M ⟩) ᵒᴸ  = fst[ M ᵒᴸ ] 
  (inr⟨ M ⟩) ᵒᴸ  = snd[ M ᵒᴸ ]
  (not[ K ]) ᵒᴸ  = not⟨ K ᵒᴿ ⟩
  (μθ {Γ} {Θ} {A} (S)) ᵒᴸ   = μγ( ᵒᶜ {Γ} {(Θ , A)} S )

  ([ K , L ]) ᵒᴿ  = ⟨ K ᵒᴿ , L ᵒᴿ ⟩
  (fst[ K ]) ᵒᴿ   = inl⟨ K ᵒᴿ ⟩
  (snd[ K ]) ᵒᴿ   = inr⟨ K ᵒᴿ ⟩
  (not⟨ M ⟩) ᵒᴿ    = not[ M ᵒᴸ ]
  (μγ {Γ} {Θ} {A} (S)) ᵒᴿ    = μθ( ᵒᶜ {(Γ , A)} {Θ} (S) )
  
  excludedmid : ∀ {Γ Θ A} → Γ ⟶ Θ ∣ A `+ `¬ A
  excludedmid = μθ (inr⟨ not[ μγ (inl⟨ γ 0 ⟩ ● θ 0) ] ⟩ ● θ 0)

  





  


  

