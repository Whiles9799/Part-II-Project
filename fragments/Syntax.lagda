\begin{code}

module fragments.Syntax where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)

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

infix  4 _∋_
infixl 5 _,_

infix  9 `S


\end{code}
--Types--

%<*type>
\begin{code}
data Type : Set where
  X : Type
  _`×_ : Type → Type → Type
  _`+_ : Type → Type → Type
  `¬_ : Type → Type
\end{code}
%</type>
  
--implication is defined in terms of other connectives
--it is defined differently for CBN and CBV

%<*ctx>
\begin{code}
data Context : Set where
  ∅ : Context
  _,_ : Context → Type → Context
\end{code}
%</ctx>

%<*var>
\begin{code}
data _∋_ : Context → Type → Set where
  `Z : ∀ {Γ A}             → Γ , A ∋ A
  `S : ∀ {Γ A B}  → Γ ∋ A  → Γ , B ∋ A
\end{code}
%</var>

\begin{code}
`¬ˣ : Context → Context
`¬ˣ ∅ = ∅
`¬ˣ (Γ , A) = (`¬ˣ Γ) , (`¬ A)
\end{code}

--Sequents--
%<*seqdef>
\begin{code}
data _⟶_∣_ : Context → Context → Type → Set 
data _∣_⟶_ : Type → Context → Context → Set
data _↦_ : Context → Context → Set
\end{code}
%</seqdef>

--lambdas and function application are syntactic sugar


%<*lseq>
\begin{code}
data _⟶_∣_ where
  
  `_ : ∀ {Γ Θ A}
    → Γ ∋ A
    → Γ ⟶ Θ ∣ A 

  `⟨_,_⟩ : ∀ {Γ Θ A B}
    → Γ ⟶ Θ ∣ A
    → Γ ⟶ Θ ∣ B
    → Γ ⟶ Θ ∣ A `× B

  inl⟨_⟩ : ∀ {Γ Θ A B}
    → Γ ⟶ Θ ∣ A
    → Γ ⟶ Θ ∣ A `+ B 

  inr⟨_⟩ : ∀ {Γ Θ A B}
    → Γ ⟶ Θ ∣ B
    → Γ ⟶ Θ ∣ A `+ B

  not[_] : ∀ {Γ Θ A}
    → A ∣ Γ ⟶ Θ
    → Γ ⟶ Θ ∣ `¬ A

  μθ : ∀ {Γ Θ A}
    → Γ ↦ Θ , A
    → Γ ⟶ Θ ∣ A
\end{code}
%</lseq>

%<*rseq>
\begin{code}
data _∣_⟶_ where
  
  `_ : ∀ {Γ Θ A}
    → Θ ∋ A
    → A ∣ Γ ⟶ Θ

  `[_,_] : ∀ {Γ Θ A B}
    → A ∣ Γ ⟶ Θ
    → B ∣ Γ ⟶ Θ
    → A `+ B ∣ Γ ⟶ Θ

  fst[_] : ∀ {Γ Θ A B}
    → A ∣ Γ ⟶ Θ
    → A `× B ∣ Γ ⟶ Θ

  snd[_] : ∀ {Γ Θ A B}
    → B ∣ Γ ⟶ Θ
    → A `× B ∣ Γ ⟶ Θ

  not⟨_⟩ : ∀ {Γ Θ A}
    → Γ ⟶ Θ ∣ A
    → `¬ A ∣ Γ ⟶ Θ
    
  μγ : ∀ {Γ Θ A}
    → Γ , A ↦ Θ
    → A ∣ Γ ⟶ Θ
\end{code}
%</rseq>

%<*cseq>
\begin{code}
data _↦_ where
  _●_ : ∀ {Γ Θ A} → (Γ ⟶ Θ ∣ A) → (A ∣ Γ ⟶ Θ) → (Γ ↦ Θ)
\end{code}
%</cseq>


\begin{code}

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
\end{code}



--Lambda Abstraction and Function Application--

