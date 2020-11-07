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
  --(A ⇒ B)ᵒᵀ   = (A ᵒᵀ ⇒ B ᵒᵀ) this is temporary until ive worked out how to handle function types

  (∅ ᵒˣ)     = ∅
  (Γ , A) ᵒˣ = ((Γ ᵒˣ) , (A ᵒᵀ))
  
  (M ● K) ᵒᶜ = K ᵒᴿ ● M ᵒᴸ

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


  type-duality-involution : ∀ {A} → (A ᵒᵀ) ᵒᵀ ≡ A
  type-duality-involution {`ℕ}     = refl
  type-duality-involution {`¬ A}   = cong `¬_ type-duality-involution 
  type-duality-involution {A `+ B} = cong₂ _`+_ (type-duality-involution {A}) (type-duality-involution {B})
  type-duality-involution {A `× B} = cong₂ _`×_ (type-duality-involution {A}) (type-duality-involution {B})

  context-duality-involution : ∀ {Γ} → (Γ ᵒˣ) ᵒˣ ≡ Γ
  context-duality-involution {∅}       = refl
  context-duality-involution {(Γ , A)} = cong₂ _,_ context-duality-involution type-duality-involution

  {-# REWRITE type-duality-involution #-}
  {-# REWRITE context-duality-involution #-}

  variable-duality-involution : ∀ {Γ A} {x : Γ ∋ A} → ((x ᵒⱽ) ᵒⱽ) ≡ x
  variable-duality-involution {_} {_} {`Z}   = refl
  variable-duality-involution {_} {_} {`S x} = cong `S variable-duality-involution

  RL-duality-involution : ∀ {Γ Θ A} {K : A ∣ Γ ⟶ Θ} → (K ᵒᴿ) ᵒᴸ ≡ K
  LR-duality-involution : ∀ {Γ Θ A} {M : Γ ⟶ Θ ∣ A} → (M ᵒᴸ) ᵒᴿ ≡ M 
  CC-duality-involution : ∀ {Γ Θ}   {S : Γ ↦ Θ}     → (S ᵒᶜ) ᵒᶜ ≡ S

  LR-duality-involution {_} {_} {_} {` x}       = cong `_ variable-duality-involution
  LR-duality-involution {_} {_} {_} {⟨ M , N ⟩}  = cong₂ ⟨_,_⟩ (LR-duality-involution {_}{_}{_}{M}) (LR-duality-involution{_}{_}{_}{N})
  LR-duality-involution {_} {_} {_} {inl⟨ M ⟩}   = cong inl⟨_⟩ LR-duality-involution
  LR-duality-involution {_} {_} {_} {inr⟨ M ⟩}   = cong inr⟨_⟩ LR-duality-involution
  LR-duality-involution {_} {_} {_} {not[ K ]}  = cong not[_] RL-duality-involution
  LR-duality-involution {_} {_} {_} {μθ S}      = cong μθ CC-duality-involution

  RL-duality-involution {_} {_} {_} {` α}       = cong `_ variable-duality-involution
  RL-duality-involution {_} {_} {_} {[ K , L ]} = cong₂ [_,_] (RL-duality-involution {_}{_}{_}{K}) (RL-duality-involution {_}{_}{_}{L})
  RL-duality-involution {_} {_} {_} {fst[ K ]}  = cong fst[_] RL-duality-involution
  RL-duality-involution {_} {_} {_} {snd[ K ]}  = cong snd[_] RL-duality-involution
  RL-duality-involution {_} {_} {_} {not⟨ M ⟩}   = cong not⟨_⟩ LR-duality-involution
  RL-duality-involution {_} {_} {_} {μγ S}      = cong μγ CC-duality-involution

  CC-duality-involution {_} {_} {M ● K}         = cong₂ _●_ (LR-duality-involution {_}{_}{_}{M}) (RL-duality-involution {_}{_}{_}{K})
  

  excludedmid : ∀ {Γ Θ A} → Γ ⟶ Θ ∣ A `+ `¬ A
  excludedmid = μθ (inr⟨ not[ μγ (inl⟨ γ 0 ⟩ ● θ 0) ] ⟩ ● θ 0)

  





  


  

