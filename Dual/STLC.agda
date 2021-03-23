module Dual.STLC where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Data.Product using (_×_ ; proj₁ ; proj₂) renaming (_,_ to ⟨_,_⟩)
import Dual.ContextandVars as DC


record λ-Type (A : Set) : Set where
  infixr 7 _⇒_
  field
    B : A
    _⇒_ : A → A → A


record λ-Term (T : Set) (TΛ : λ-Type T) (Λ : DC.Context T → T → Set): Set where
  open DC T
  open λ-Type TΛ
  infix  5 ƛ
  infixl 7 _·_
  infix  9 `
  field
    ` : ∀ {Γ A} → Γ ∋ A → Λ Γ A
    ƛ : ∀ {Γ A B} → Λ (Γ , A) B → Λ Γ (A ⇒ B)
    _·_ : ∀ {Γ A B} → Λ Γ (A ⇒ B) → Λ Γ A → Λ Γ B

  lookup : Context → ℕ → T
  lookup (Γ , A) zero    = A
  lookup (Γ , _) (suc n) = lookup Γ n
  lookup ∅       _       = ⊥-elim impossible
    where postulate impossible : ⊥ 

  count : ∀ {Γ} → (n : ℕ) → Γ ∋ lookup Γ n
  count {Γ , _} zero    = `Z
  count {Γ , _} (suc n) = `S (count n)
  count {∅}     _       = ⊥-elim impossible
    where postulate impossible : ⊥

  # : ∀ {Γ} → (n : ℕ) → Λ Γ (lookup Γ n)
  # n = ` (count n)

  id : ∀ {Γ A} → Λ Γ (A ⇒ A)
  id = ƛ (` `Z)

  CN : T
  CN = (B ⇒ B) ⇒ (B ⇒ B)

  z : ∀ {Γ} → Λ Γ CN
  z = ƛ (ƛ (# 0))

  s : ∀ {Γ} → Λ Γ (CN ⇒ CN)
  s = ƛ (ƛ (ƛ (# 1 · ((# 2 · # 1) · # 0))))

  sum : ∀ {Γ} → Λ Γ (CN ⇒ CN ⇒ CN)
  sum = ƛ (ƛ (ƛ (ƛ ((# 3 · # 1) · ((# 2 · # 1) · # 0)))))

  mult : ∀ {Γ} → Λ Γ (CN ⇒ CN ⇒ CN)
  mult = ƛ (ƛ (ƛ (ƛ (((# 3) · (# 2 · # 1)) · # 0))))

  -- exp : ∀ {Γ} → Λ Γ (CN ⇒ CN ⇒ CN)
  -- exp = ƛ (ƛ ( # 1 · # 0))

record λ+-Type (T : Set) : Set where
  infixr 7 _⇒_
  infix 10 ¬
  field
    B : T
    _⇒_ : T → T → T
    ¬ : T → T


record λ+-Term (T : Set) (TΛ : λ+-Type T) (Λ : DC.Context T → T → Set): Set where
  open DC T
  open λ+-Type TΛ
  infix  5 ƛ
  infixl 7 _·_
  infix  9 `
  field
    ` : ∀ {Γ A} → Γ ∋ A → Λ Γ A
    ƛ : ∀ {Γ A B} → Λ (Γ , A) B → Λ Γ (A ⇒ B)
    _·_ : ∀ {Γ A B} → Λ Γ (A ⇒ B) → Λ Γ A → Λ Γ B
    letcont : ∀ {Γ A} → Λ (Γ , ¬ A) A → Λ Γ A
    throw[_,_] : ∀ {Γ A B} → Λ Γ (¬ A) → Λ Γ A → Λ Γ B

  lookup : Context → ℕ → T
  lookup (Γ , A) zero    = A
  lookup (Γ , _) (suc n) = lookup Γ n
  lookup ∅       _       = ⊥-elim impossible
    where postulate impossible : ⊥ 

  count : ∀ {Γ} → (n : ℕ) → Γ ∋ lookup Γ n
  count {Γ , _} zero    = `Z
  count {Γ , _} (suc n) = `S (count n)
  count {∅}     _       = ⊥-elim impossible
    where postulate impossible : ⊥

  # : ∀ {Γ} → (n : ℕ) → Λ Γ (lookup Γ n)
  # n = ` (count n)

  
record λμ-Term (T : Set) (TΛ : λ+-Type T) (Λ-Term : DC.Context T → DC.Context T → T → Set) (Λ-Comm : DC.Context T → DC.Context T → Set): Set where
  open DC T
  open λ+-Type TΛ
  field
    ` : ∀ {Γ Δ A} → Γ ∋ A → Λ-Term Γ Δ A
    ƛ : ∀ {Γ Δ A B} → Λ-Term (Γ , A) Δ B → Λ-Term Γ Δ (A ⇒ B)
    _·_ : ∀ {Γ Δ A B} → Λ-Term Γ Δ (A ⇒ B) → Λ-Term Γ Δ A → Λ-Term Γ Δ B
    μ : ∀ {Γ Δ A} → Λ-Comm Γ (Δ , A) → Λ-Term Γ Δ A
    
  lookup : Context → ℕ → T
  lookup (Γ , A) zero    = A
  lookup (Γ , _) (suc n) = lookup Γ n
  lookup ∅       _       = ⊥-elim impossible
    where postulate impossible : ⊥ 

  count : ∀ {Γ} → (n : ℕ) → Γ ∋ lookup Γ n
  count {Γ , _} zero    = `Z
  count {Γ , _} (suc n) = `S (count n)
  count {∅}     _       = ⊥-elim impossible
    where postulate impossible : ⊥

  # : ∀ {Γ Δ} → (n : ℕ) → Λ-Term Γ Δ (lookup Γ n)
  # n = ` (count n)


record λμ-Command (T : Set) (TΛ : λ+-Type T) (Λ-Term : DC.Context T → DC.Context T → T → Set) (Λ-Comm : DC.Context T → DC.Context T → Set) : Set where
  open DC T
  open λ+-Type TΛ
  field
    [_]_ : ∀ {Γ Δ A} → Δ ∋ A → Λ-Term Γ Δ A → Λ-Comm Γ Δ


open import Dual.Syntax
open import Dual.Substitution
open import Dual.Values

DC-λ-Type : λ-Type Type
DC-λ-Type = record { B = `ℕ ; _⇒_ = _⇒ⱽ_ }

DC-λ-Term : λ-Term Type DC-λ-Type (λ Γ A → Γ ⟶ ∅ ∣ A)
DC-λ-Term = record { 
  ` = `_ ; 
  ƛ = λ M → not[ μγ(γ 0 ● fst[ μγ (γ 1 ● snd[ not⟨ rename-term (rename-lift (λ x → `S x)) id-var M ⟩ ]) ]) ] ; 
  _·_ = λ M N → μθ (wkΘᵗ M ● wkΘᵗ N ·ⱽ θ 0)
  }

DC-λ+-Type : λ+-Type Type
DC-λ+-Type = record { B = `ℕ ; _⇒_ = _⇒ⱽ_ ; ¬ = `¬_ }

DC-λ+-Term : λ+-Term Type DC-λ+-Type (λ Γ A → Γ ⟶ ∅ ∣ A)
DC-λ+-Term = record 
  { ` = `_ 
  ; ƛ = λ M → not[ μγ(γ 0 ● fst[ μγ (γ 1 ● snd[ not⟨ rename-term (rename-lift (λ x → `S x)) id-var M ⟩ ]) ]) ] 
  ; _·_ = λ M N → μθ (wkΘᵗ M ● wkΘᵗ N ·ⱽ θ 0) 
  ; letcont = λ M → μθ (not[ (θ 0) ] ● (μγ ((wkΘᵗ M) ● (θ 0))))
  ; throw[_,_] = λ M N → μθ (wkΘᵗ N ● μγ ((wkΘᵗ (wkΓᵗ M)) ● not⟨ (γ 0) ⟩))
  }


DC-λμ-Term : λμ-Term Type DC-λ+-Type _⟶_∣_ _↦_
DC-λμ-Term = record 
  { ` = `_ 
  ; ƛ = λ M → not[ μγ(γ 0 ● fst[ μγ (γ 1 ● snd[ not⟨ rename-term (rename-lift (λ x → `S x)) id-var M ⟩ ]) ]) ] 
  ; _·_ = λ M N → μθ (wkΘᵗ M ● wkΘᵗ N ·ⱽ θ 0) 
  ; μ = λ C → μθ C
  }

DC-λμ-Command : λμ-Command Type DC-λ+-Type _⟶_∣_ _↦_
DC-λμ-Command = record { [_]_ = λ α M → M ● (` α) }


module STLC-DC where
  open λ-Type DC-λ-Type  
  open λ-Term DC-λ-Term
  open import Dual.CPSTransformation ℕ

  DC-2 : ∀ {Γ} → Γ ⟶ ∅ ∣ CN
  DC-2 = s · (s · z)

  DC-3 : ∀ {Γ} → Γ ⟶ ∅ ∣ CN
  DC-3 = s · DC-2

  DC-5 : ∀ {Γ} → Γ ⟶ ∅ ∣ CN
  DC-5 = s · (s · DC-3)

  DC-2+2 : ∀ {Γ} → (Γ ⱽˣ × (`¬ˣ ∅) ⱽˣ) → ((`¬ `¬ CN) ⱽᵀ)
  DC-2+2 {Γ} = ((sum {Γ} · DC-2) · DC-2) ⱽᴸ 

  2+2 : (∅ , `ℕ , `ℕ ⇒ `ℕ) ⟶ ∅ ∣ `ℕ
  2+2 = (((sum · DC-2) · DC-2) · (# 0)) · (# 1)

  2+2ⱽ : ℕ
  2+2ⱽ = (2+2 ⱽᴸ) ⟨ ⟨ ⟨ tt , ℕ.zero ⟩ , (λ x → proj₂ x (ℕ.suc (proj₁ x))) ⟩ , tt ⟩ (λ x → x)

  3*5 : (∅ , `ℕ , `ℕ ⇒ `ℕ) ⟶ ∅ ∣ `ℕ
  3*5 = (((mult · DC-3) · DC-5) · (# 0)) · (# 1)

  3*5ⱽ : ℕ
  3*5ⱽ = (3*5 ⱽᴸ) ⟨ ⟨ ⟨ tt , ℕ.zero ⟩ , ((λ x → proj₂ x (ℕ.suc (proj₁ x)))) ⟩ , tt ⟩ (λ x → x)

module STLC+-DC where
  open λ+-Type DC-λ+-Type
  open λ+-Term DC-λ+-Term
  open import Dual.CPSTransformation ℕ 

  DC-DNE : ∀ {Γ A} → Γ ⟶ ∅ ∣ (¬ (¬ A)) ⇒ A
  DC-DNE = ƛ (letcont throw[ # 1 , # 0 ])

  DC-peirce : ∀ {Γ A B} → Γ ⟶ ∅ ∣ ((A ⇒ B) ⇒ A) ⇒ A 
  DC-peirce = ƛ (letcont ((# 1) · (ƛ throw[ (# 1) , (# 0) ])))

  DC-and-I : ∀ {Γ A B} → Γ , A , B ⟶ ∅ ∣ ¬ (A ⇒ ¬ B)
  DC-and-I = letcont throw[ ((DC-DNE · (# 0)) · (# 2)) , (# 1) ]
  
  DC-and-E₁ : ∀ {Γ A B} → Γ , ¬ (A ⇒ ¬ B) ⟶ ∅ ∣ A
  DC-and-E₁ = letcont throw[ (# 1) , (ƛ throw[ (# 1) , (# 0) ]) ]

  DC-and-E₂ : ∀ {Γ A B} → Γ , ¬ (A ⇒ ¬ B) ⟶ ∅ ∣ B
  DC-and-E₂ = letcont throw[ (# 1) , (ƛ (# 1)) ]
  
  DC-or-I₁ : ∀ {Γ A B} → Γ , A ⟶ ∅ ∣ ¬ A ⇒ B
  DC-or-I₁ = ƛ throw[ (# 0) , (# 1) ]

  DC-or-I₂ : ∀ {Γ A B} → Γ , B ⟶ ∅ ∣ ¬ A ⇒ B
  DC-or-I₂ = ƛ (# 1)

  -- DC-or-E : ∀ {Γ A B C} → Γ , ¬ A ⇒ B , A ⇒ C , B ⇒ C ⟶ ∅ ∣ C
  -- DC-or-E = {!   !}

module λμ-DC where
  open λ+-Type DC-λ+-Type
  open λμ-Term DC-λμ-Term
  open λμ-Command DC-λμ-Command
  open import Dual.CPSTransformation ℕ

  λμ-peirce : ∀ {Γ Δ A B} → Γ ⟶ Δ ∣ ((A ⇒ B) ⇒ A) ⇒ A
  λμ-peirce = ƛ (μ ([ `Z ] ((# 0) · (ƛ (μ ([ (`S `Z) ] (# 0)))))))

  
