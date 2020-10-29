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

  infixr 7 _⇒_
  infix 8 _`+_
  infix 9 _`×_
  infix 10 `¬_

  infix 4 _●_
  infix  5 ƛ_
  infix  5 μθ_
  infix  5 μγ_
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
    _⇒_ : Type → Type → Type

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

    ƛ_ : ∀ {Γ Θ A B}
      → Γ , A ⟶ Θ ∣ B
        --------------
      → Γ ⟶ Θ ∣ A ⇒ B

    μθ_ : ∀ {Γ Θ A}
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
     
    μγ_ : ∀ {Γ Θ A}
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

  γ_ : ∀ {Γ Θ} → (n : ℕ) → Γ ⟶ Θ ∣ lookup Γ n
  γ n = ` count n

  θ_ : ∀ {Γ Θ} → (n : ℕ) → lookup Θ n ∣ Γ ⟶ Θ
  θ n = ` count n
  
  _ᵒᵀ : Type → Type
  _ᵒᴸ : ∀ {Γ Θ A B} → (Γ ⟶ Θ ∣ A) → (A ᵒᵀ ∣ Γ ⟶ Θ)
  _ᵒᴿ : ∀ {Γ Θ A B} → (A ∣ Γ ⟶ Θ) → (Γ ⟶ Θ ∣ A ᵒᵀ)
  _ᵒᶜ : ∀ {Γ Θ} → (Γ ↦ Θ) → (Γ ↦ Θ)


  (A `+ B)ᵒᵀ  = (A ᵒᵀ `× B ᵒᵀ)
  (A `× B)ᵒᵀ  = (A ᵒᵀ `+ B ᵒᵀ)
  (`¬ A)ᵒᵀ    = (`¬ (A)ᵒᵀ) 
  (`ℕ)ᵒᵀ      = `ℕ
  (A ⇒ B)ᵒᵀ   = (A ᵒᵀ ⇒ B ᵒᵀ) -- this is temporary until ive worked out how to handle function types

  (⟨ M , N ⟩) ᵒᴸ = [ M ᵒᴸ , N ᵒᴸ ]
  (inl⟨ M ⟩) ᵒᴸ  = fst[ M ᵒᴸ ] 
  (inr⟨ M ⟩) ᵒᴸ  = snd[ M ᵒᴸ ]
  (not[ K ]) ᵒᴸ  = not⟨ K ᵒᴿ ⟩
  (μθ( S )) ᵒᴸ   = μγ( S ᵒᶜ )

  ([ K , L ]) ᵒᴿ  = ⟨ K ᵒᴿ , L ᵒᴿ ⟩
  (fst[ K ]) ᵒᴿ   = inl⟨ K ᵒᴿ ⟩
  (snd[ K ]) ᵒᴿ   = inr⟨ K ᵒᴿ ⟩
  (not⟨ M ⟩) ᵒᴿ    = not[ M ᵒᴸ ]
  (μγ( S )) ᵒᴿ    = μθ( S ᵒᶜ )

  (M ● K) ᵒᶜ = K ᵒᴿ ● M ᵒᴸ
  

  excludedmid : ∀ {Γ Θ A} → Γ ⟶ Θ ∣ A `+ `¬ A
  excludedmid = μθ (inr⟨ not[ μγ (inl⟨ γ 0 ⟩ ● θ 0) ] ⟩ ● θ 0)

  





  


  

