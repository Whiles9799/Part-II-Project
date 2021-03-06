\begin{code}

module fragments.Simulation where

open import Data.Empty using (⊥; ⊥-elim)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym; trans)
import Dual.DenotationalSemantics.CPSTransformation as CPS
open CPS CPS.ℕ
import Dual.Syntax.ContextandVars as DC

\end{code}

%<*lam-type>
\begin{code}
record λ-Type (T : Set) : Set where
  infixr 7 _⇒_
  field
    B : T
    _⇒_ : T → T → T
  
  CN : T
  CN = (B ⇒ B) ⇒ (B ⇒ B)
\end{code}
%</lam-type>

%<*lam-term>
\begin{code}
record λ-Term (T : Set) (TΛ : λ-Type T) (Λ : DC.Context T → T → Set): Set where
  open DC T
  open λ-Type TΛ
  field
    var : ∀ {Γ A} → Γ ∋ A → Λ Γ A
    ƛ : ∀ {Γ A B} → Λ (Γ , A) B → Λ Γ (A ⇒ B)
    _·_ : ∀ {Γ A B} → Λ Γ (A ⇒ B) → Λ Γ A → Λ Γ B

\end{code}
%</lam-term>
\begin{code}
  infix  5 ƛ
  infixl 7 _·_
  infix  9 var
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
  # n = var (count n)

  id : ∀ {Γ A} → Λ Γ (A ⇒ A)
  id = ƛ (# 0)

\end{code}
%<*CN>
\begin{code}
  z : ∀ {Γ} → Λ Γ CN
  z = ƛ (ƛ (# 0))

  s : ∀ {Γ} → Λ Γ (CN ⇒ CN)
  s = ƛ (ƛ (ƛ (# 1 · ((# 2 · # 1) · # 0))))
\end{code}
%</CN>
%<*sum+mult>
\begin{code}
  sum : ∀ {Γ} → Λ Γ (CN ⇒ CN ⇒ CN)
  sum = ƛ (ƛ (ƛ (ƛ ((# 3 · # 1) · ((# 2 · # 1) · # 0)))))

  mult : ∀ {Γ} → Λ Γ (CN ⇒ CN ⇒ CN)
  mult = ƛ (ƛ (ƛ (ƛ (((# 3) · (# 2 · # 1)) · # 0))))
\end{code}
%</sum+mult>

\begin{code}
record λ+-Type (T : Set) : Set where
  infixr 7 _⇒_
  infix 10 ¬′
  field
    B : T
    _⇒_ : T → T → T
    ¬′ : T → T

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
\end{code}
%<*DC-lam+-int>
\begin{code}
    letcont : ∀ {Γ A} → Λ (Γ , ¬′ A) A → Λ Γ A
    throw[_,_] : ∀ {Γ A B} → Λ Γ (¬′ A) → Λ Γ A → Λ Γ B
\end{code}
%</DC-lam+-int>
\begin{code}
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

\end{code}
%<*mu-term-ty>
\begin{code}
record λμ-Term (T : Set) (TΛ : λ+-Type T) (Λ-Term : DC.Context T → DC.Context T → T → Set)
   (Λ-Comm : DC.Context T → DC.Context T → Set): Set where
  open DC T
  open λ+-Type TΛ
  field
    var : ∀ {Γ Δ A} → Γ ∋ A → Λ-Term Γ Δ A
    ƛ : ∀ {Γ Δ A B} → Λ-Term (Γ , A) Δ B → Λ-Term Γ Δ (A ⇒ B)
    _·_ : ∀ {Γ Δ A B} → Λ-Term Γ Δ (A ⇒ B) → Λ-Term Γ Δ A → Λ-Term Γ Δ B
    μ : ∀ {Γ Δ A} → Λ-Comm Γ (Δ , A) → Λ-Term Γ Δ A
\end{code}
%</mu-term-ty>
\begin{code}
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
  # n = var (count n)

\end{code}
%<*comm-ty>
\begin{code}
record λμ-Command (T : Set) (TΛ : λ+-Type T) (Λ-Term : DC.Context T → DC.Context T → T → Set) 
  (Λ-Comm : DC.Context T → DC.Context T → Set) : Set where
  open DC T
  open λ+-Type TΛ
  field
    [_]_ : ∀ {Γ Δ A} → Δ ∋ A → Λ-Term Γ Δ A → Λ-Comm Γ Δ
\end{code}
%</comm-ty>

\begin{code}

open import Dual.Syntax.Core
open import Dual.Syntax.Substitution
open import Dual.Syntax.Values
open import Dual.Syntax.Implication

DC-λ-Type : λ-Type Type
DC-λ-Type = record { B = X ; _⇒_ = _⇒ⱽ_ }

\end{code}
%<*DC-lam-term>
\begin{code}
DC-λ-Term : λ-Term Type DC-λ-Type (λ Γ A → Γ ⟶ ∅ ∣ A)
DC-λ-Term = record { 
  var = `_ ; 
  ƛ = ƛⱽ_ ; 
  _·_ = λ M N → μθ (wkΘᵗ M ● wkΘᵗ N ·ⱽ θ 0)
  }
\end{code}
%</DC-lam-term>
\begin{code}
DC-λ+-Type : λ+-Type Type
DC-λ+-Type = record { B = X ; _⇒_ = _⇒ⱽ_ ; ¬′ = `¬_ }

DC-λ+-Term : λ+-Term Type DC-λ+-Type (λ Γ A → Γ ⟶ ∅ ∣ A)
DC-λ+-Term = record 
  { ` = `_ 
  ; ƛ = ƛⱽ_
  ; _·_ = λ M N → μθ (wkΘᵗ M ● wkΘᵗ N ·ⱽ θ 0)
\end{code}
%<*DC-lam+-imp>
\begin{code} 
  ; letcont = λ M → μθ (not[ (θ 0) ] ● (μγ ((wkΘᵗ M) ● (θ 0))))
  ; throw[_,_] = λ M N → μθ (wkΘᵗ N ● μγ ((wkΘᵗ (wkΓᵗ M)) ● not⟨ (γ 0) ⟩))
\end{code}
%</DC-lam+-imp>
\begin{code}
  }
\end{code}
%<*mu-term>
\begin{code}
DC-λμ-Term : λμ-Term Type DC-λ+-Type _⟶_∣_ _↦_
DC-λμ-Term = record 
  { var = `_ 
  ; ƛ = ƛⱽ_
  ; _·_ = λ M N → μθ (wkΘᵗ M ● wkΘᵗ N ·ⱽ θ 0) 
  ; μ = μθ
  }
\end{code}
%</mu-term>
%<*comm>
\begin{code}
DC-λμ-Command : λμ-Command Type DC-λ+-Type _⟶_∣_ _↦_
DC-λμ-Command = record 
  { 
    [_]_ = λ α M → M ● (` α) 
  }
\end{code}
%</comm>

%<*module>
\begin{code}
module STLC-DC where
  open λ-Type DC-λ-Type  
  open λ-Term DC-λ-Term
\end{code}
%</module>

%<*CN-2>
\begin{code}
  CN-2 : ∀ {Γ} → Γ ⟶ ∅ ∣ CN
  CN-2 = s · (s · z)

  CN-2+2 : ∀ {Γ} → Γ ⟶ ∅ ∣ CN
  CN-2+2 = sum · CN-2 · CN-2
\end{code}
%</CN-2>
%<*2+2>
\begin{code}
  2+2 : (∅ , X , X ⇒ X) ⟶ ∅ ∣ X
  2+2 = CN-2+2 · (# 0) · (# 1)
\end{code}
%</2+2>
%<*2+2V>
\begin{code}
  2+2ⱽ : ℕ
  2+2ⱽ = (2+2 ⱽᴸ) ⟨ ⟨ ⟨ tt , ℕ.zero ⟩ , (λ{ ⟨ n , k ⟩ → k (ℕ.suc n) }) ⟩ , tt ⟩ (λ x → x)
\end{code}
%</2+2V>
\begin{code}
  CN-3 : ∀ {Γ} → Γ ⟶ ∅ ∣ CN
  CN-3 = s · CN-2

  CN-5 : ∀ {Γ} → Γ ⟶ ∅ ∣ CN
  CN-5 = s · (s · CN-3)

  3*5 : (∅ , X , X ⇒ X) ⟶ ∅ ∣ X
  3*5 = (((mult · CN-3) · CN-5) · (# 0)) · (# 1)

  3*5ⱽ : ℕ
  3*5ⱽ = (3*5 ⱽᴸ) ⟨ ⟨ ⟨ tt , ℕ.zero ⟩ , (λ{ ⟨ n , k ⟩ → k (ℕ.suc n) }) ⟩ , tt ⟩ (λ x → x)

module STLC+-DC where
  open λ+-Type DC-λ+-Type
  open λ+-Term DC-λ+-Term
  \end{code}

%<*STLC+-DNE>
\begin{code}
  DNE : ∀ {Γ A} → Γ ⟶ ∅ ∣ (¬′ (¬′ A)) ⇒ A
  DNE = ƛ (letcont throw[ (# 1) , (# 0) ])

  _ : ∀ {Γ A} → 
      DNE {Γ}{A} 
      ≡ not[ μγ (γ 0 ● fst[ μγ (γ 1 ● snd[ not⟨ 
          μθ (not[ θ 0 ] ● μγ (μθ (γ 0 ● μγ (γ 2 ● not⟨ γ 0 ⟩)) ● θ 0)) ⟩ ]) ]) ]
  _ = refl
\end{code}
%</STLC+-DNE>
%<*STLC+-peirce>
\begin{code}
  peirce : ∀ {Γ A B} → Γ ⟶ ∅ ∣ ((A ⇒ B) ⇒ A) ⇒ A 
  peirce = ƛ (letcont (# 1 · (ƛ throw[ # 1 , # 0 ])))

  _ : ∀ {Γ A B} → 
      peirce {Γ}{A}{B}
      ≡ not[ μγ (γ 0 ● fst[ μγ (γ 1 ● snd[ not⟨ μθ (
          not[ θ 0 ] ● μγ ( μθ (γ 1
          ● not⟨ `⟨ not[ μγ (γ 0 ● fst[ μγ (γ 1 ● snd[ not⟨ μθ (γ 0 ●
          μγ ( γ 3 ● not⟨ γ 0 ⟩)) ⟩ ]) ]) ] 
          , not[ θ 0 ] ⟩ ⟩) ● θ 0)) ⟩ ]) ]) ]
  _ = refl
\end{code}
%</STLC+-peirce>
%<*STLC+-and>
\begin{code}
  and : Type → Type → Type
  and A B = ¬′ (A ⇒ ¬′ B)

  and-I : ∀ {Γ A B} → Γ , A , B ⟶ ∅ ∣ and A B
  and-I = letcont throw[ ((DNE · (# 0)) · (# 2)) , (# 1) ]
  
  and-E₁ : ∀ {Γ A B} → Γ , and A B ⟶ ∅ ∣ A
  and-E₁ = letcont throw[ (# 1) , (ƛ throw[ (# 1) , (# 0) ]) ]

  and-E₂ : ∀ {Γ A B} → Γ , and A B ⟶ ∅ ∣ B
  and-E₂ = letcont throw[ (# 1) , (ƛ (# 1)) ]
\end{code}
%</STLC+-and>

\begin{code}

module λμ-DC where
  open λ+-Type DC-λ+-Type
  open λμ-Term DC-λμ-Term
  open λμ-Command DC-λμ-Command
  
\end{code}
%<*lm-peirce>
\begin{code}

  λμ-peirce : ∀ {Γ Δ A B} → Γ ⟶ Δ ∣ ((A ⇒ B) ⇒ A) ⇒ A
  λμ-peirce = ƛ (μ ([ `Z ] ((# 0) · (ƛ (μ ([ `S `Z ] (# 0)))))))

  _ : ∀ {Γ Δ A B} →
      λμ-peirce {Γ}{Δ}{A}{B}
      ≡ not[ μγ (γ 0 ● fst[ μγ (γ 1 ● snd[ not⟨ μθ (
          μθ (γ 0 
          ● not⟨ `⟨ not[ μγ (γ 0 ● fst[ μγ (γ 1 ● snd[ not⟨ μθ (γ 0 ● 
          θ 2) ⟩ ]) ]) ] 
          , not[ θ 0 ] ⟩ ⟩) ● θ 0) ⟩ ]) ]) ]
  _ = refl
\end{code}
%</lm-peirce>

