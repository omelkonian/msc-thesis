%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Appendix
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{appendix}
For the sake of brevity and clarity, we have omitted various technical details
throughout the presentation of our formal development.
We present those which we deem relevant in this Appendix.

\section{Generalized Variables}
We use Agda's recent capabilities for \textit{generalized variables},
which allow one to declare variable names of a certain type at the top-level
and then omit them from their usage in type definitions for clarity.

Below we give a complete set of all variables used throughout this thesis:
\begin{agda}\begin{code}
variable
  -- General
  ℓ : Level
  A B C D : Set ℓ
##
  -- UTxO
  l l′ l″ :  Ledger
  tx :  Tx
  i :  TxInput
  i∈ :  i ∈ inputs tx
##
  -- BitML
  p A B : Participant
  A₁ DOTS A SUBN : Participant
  a₁ DOTS a SUBN : Secret
  N₁ DOTS N SUBN : ℕ ⊎ ⊥
  v v′ : Value
  vs vs SC vs SV vs SP : List Value
  ad : Advertisement v vs SC vs SV vs SP
  contract C D : List (Contract v vs)
  i : Index C
##
  ads ads′ ads″ rads ads SR rads SR ads SL rads SL : AdvertisedContracts
  cs  cs′ cs″ rcs cs SR rcs SR cs SL rcs SL : ActiveContracts
  ds  ds′ ds″ rds ds SR rds SR ds SL rds SL : Deposits
  Γ Γ₀ L M N : Configuration ads cs ds
  Γ′ : Configuration ads′ cs′ ds′
  Γ″ : Configuration ads″ cs″ ds″
  t δ : Time
##
  α : Label
  αs : List Label
  R R′ R″ : Trace
  T T′ T″ : ∃TimedConfigurations
  S : HonestStrategies
  S† : AdversarialStrategy
  SS : Strategies
\end{code}\end{agda}

\section{List Utilities}

\subsection{Indexed Operations}
When we lookup elements in a list, we use indices that are finite numbers less than the length of the list:
\begin{agda}\begin{code}
open import Fin using (Fin, zero, suc)
##
Index : List A → Set
Index = Fin ∘ length
##
indices : List A → List ℕ
indices = upTo ∘ length
##
_ ‼ _ : (vs : List A) → Index vs → A
(x  ∷  _)   ‼  zero     =  x
(_  ∷  xs)  ‼  (suc i)  =  xs ‼ i
##
delete : (vs : List A) → Index vs → List A
delete  []        ()
delete  (_ ∷ xs)  zero     = xs
delete  (x ∷ vs)  (suc f)  = x ∷ delete vs f
##
_ ‼ _ := _ : (vs : List A) → Index vs → A → List A
[]        ‼  ()     := _
(_ ∷ xs)  ‼  zero   := y  = y ∷ xs
(x ∷ xs)  ‼  suc i  := y  = x ∷ (xs ‼ i ⟨ y ⟩)
\end{code}\end{agda}
Also note the type-safe operations of lookup (|_ ‼ _|, deletion (|delete|) and update (|_ ‼ _ := _|).

\subsection{Set-like Interface}
\label{subsec:set}
When calculating the set of unspent transaction outputs of a ledger in the UTxO model (Section~\ref{subsec:utxo}),
we used set-theoretic operations, namely
empty set |∅|; set difference |_ ─ _|; set union |_ ∪ _|; set membership |_ ∈ _|; set cardinality |BAR _ BAR|.
First, note that these require that we can decide (i.e. compute) equality between elements of a set.
We model this by encapsulating all set-related definitions in a module parametrised by an abstract data type, which
is however equipped with \textit{decidable equality}:
\begin{agda}\begin{code}
module Data.Set' {A : Set} (_ ≟ _ : Decidable (_ ≡ _ {A = A})) where
##
  open import Data.List.Membership.DecPropositional _ ≟ _
    using (_ ∈? _)
    renaming (_ ∈ _ to _ ∈′ _)
##
  _ ≟ SUBL _ : Decidable {A = List A} _ ≡ _
  []      ≟ SUBL  []      = yes refl
  []      ≟ SUBL  _ ∷ _   = no λ ()
  _ ∷ _   ≟ SUBL  []      = no λ ()
  x ∷ xs  ≟ SUBL  y ∷ ys  with x ≟ y
  ... | no ¬p      = no λ{refl → ¬p refl}
  ... | yes refl   with xs ≟ SUBL ys
  ... | no ¬pp     = no λ{refl → ¬pp refl}
  ... | yes refl   = yes refl
\end{code}\end{agda}

We now define a set as a list coupled with a proof that it does not contain duplicate elements:
\begin{agda}\begin{code}
open import Data.List.Relation.Unary.Unique.Propositional {A} using (Unique)
##
record Set' : Set where
  constructor ⟨ _ ⟩∶- _
  field  list   : List A
         .uniq  : Unique list
\end{code}\end{agda}

The implementation of the set-theoretic operations now has to preserve the proofs of uniqueness:
\begin{agda}\begin{code}
∅ : Set'
∅ = ⟨ [] ⟩∶- DOTS
##
_ ∈ _ : A → Set' → Set
o ∈ ⟨ os ⟩∶- _ = o ∈′ os
##
∣ _ ∣ : Set' → ℕ
∣ _ ∣ = length ∘ list
##
_ ─ _ : Set' → Set' → Set'
⟨ xs ⟩∶- DOTS ─ ⟨ ys ⟩∶- DOTS = ⟨ filter (λ x → ¬? (x ∈? ys)) xs ⟩∶- DOTS
##
_ ∪ _ : Set' → Set' → Set'
x@(⟨ xs ⟩∶- DOTS) ∪ y@(⟨ ys ⟩∶- DOTS) = ⟨ xs ++ list (y ─ x) ⟩∶- DOTS
\end{code}\end{agda}

\section{Decidable Equality}
Our decision procedures always rely on the fact that we have decidable equality for the types
involved in the propositions under question (see Section~\ref{subsec:decprop}).
Here, we demonstrate how to decide equality of the type of actions in the
semantics of BitML, but a very similar procedure applies for all other cases:
\begin{agda}\begin{code}
_ ≟ _ : Decidable {A = Action p ads cs vs ds} _ ≡ _
##
(HTRI ad) ≟ (HTRI .ad)      = yes refl
(HTRI ad) ≟ (.ad ATRI i)  = no λ ()
##
(ad ATRI i) ≟ (HTRI .ad) = no λ ()
(ad ATRI i) ≟ (.ad TRIˢ i′) with i SET-fin.≟ i′
... | no ¬p     = no λ{refl → ¬p refl}
... | yes refl  = yes refl
##
(c BTRI i) ≟ (.c BTRI i′) with i SET-fin.≟ i′
... | no ¬p     = no λ{refl → ¬p refl}
... | yes refl  = yes refl
##
(x ↔ y) ≟ (x′ ↔ y′)
  with x SET-fin.≟ x′
... | no ¬p     = no λ{refl → ¬p refl}
... | yes refl
  with y SET-fin.≟ y′
... | no ¬p     = no λ{refl → ¬p refl}
... | yes refl  = yes refl
(x ↔ y) ≟ (i TRI v₁ , v₂)  = no λ ()
(x ↔ y) ≟ (i DTRI p′)      = no λ ()
(x ↔ y) ≟ destroy i        = no λ ()
##
(i TRI v₁ , v₂) ≟ (i′ TRI v₁′ , v₂′)
  with i SET-fin.≟ i′
... | no ¬p     = no λ{refl → ¬p refl}
... | yes refl
  with v₁ SET-ℕ.≟ v₁′
... | no ¬p     = no λ{refl → ¬p refl}
... | yes refl
  with v₂ SET-ℕ.≟ v₂′
... | no ¬p     = no λ{refl → ¬p refl}
... | yes refl  = yes refl
(i TRI v₁ , v₂) ≟ (x ↔ y)       = no λ ()
(i TRI v₁ , v₂) ≟ (i₁ DTRI p′)  = no λ ()
(i TRI v₁ , v₂) ≟ destroy i₁    = no λ ()
##
(i DTRI a) ≟ (i′ DTRI b)
  with i SET-fin.≟ i′
... | no ¬p     = no λ{refl → ¬p refl}
... | yes refl
  with a SET-participant.≟ b
... | no ¬p     = no λ{refl → ¬p refl}
... | yes refl  = yes refl
(i DTRI p′) ≟ (x ↔ y)           = no λ ()
(i DTRI p′) ≟ (i₁ TRI v₁ , v₂)  = no λ ()
(i DTRI p′) ≟ destroy i₁        = no λ ()
##
destroy i ≟ destroy i′
  with i SET-fin.≟ i′
... | no ¬p     = no λ{refl → ¬p refl}
... | yes refl  = yes refl
destroy i ≟ (x ↔ y)           = no λ ()
destroy i ≟ (i₁ TRI v₁ , v₂)  = no λ ()
destroy i ≟ (i₁ DTRI p′)      = no λ ()
##
_ ∃≟ _ : Decidable {A = ∃Action} _ ≡ _
(p , ads , cs , vs , ds , a) ∃≟ (p′ , ads′ , cs′ , vs′ , ds′ , a′)
  with p SET-participant.≟ p′
... | no   ¬p    = no λ{ refl → ¬p refl}
... | yes  refl
  with ads SET-advert.≟ ads′
... | no   ¬p    = no λ{ refl → ¬p refl}
... | yes  refl
  with cs SET-contract.≟ cs′
... | no   ¬p    = no λ{ refl → ¬p refl}
... | yes  refl
  with vs SET-ℕ.≟ vs′
... | no   ¬p    = no λ{ refl → ¬p refl}
... | yes  refl
  with ds SET-deposit.≟ ds′
... | no   ¬p    = no λ{ refl → ¬p refl}
... | yes  refl
  with a ≟ a′
... | no   ¬p    =  no λ{ refl → ¬p refl}
... | yes  refl  =  yes refl
\end{code}\end{agda}

We can then rightfully use the set-like operations, as described in Appendix~\ref{subset:set}:
\begin{agda}\begin{code}
import Data.Set' as SET
module SET-action = SET _ ∃≟ _

Set⟨ Action ⟩ : Set
Set⟨ Action ⟩ = Set'
  where open SET-action
\end{code}\end{agda}

\end{appendix}
