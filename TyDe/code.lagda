%include polycode.fmt
%include stylish.lhs

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                  UTxO                                      %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Inlined code
\newcommand{\inlineTrue}{|true|}
\newcommand{\inlineAst}{|UNDERL ** UNDER ~~ UNDERR|}
\newcommand{\inlineLedger}{|Ledger|}
\newcommand{\inlineNDS}{|Unique (outRef <$> inputs tx)|}
\newcommand{\inlinePV}{|forge + Σ IN ≡ fee + Σ OUT |}

%% Code blocks
\newcommand\basic{
\savecolumns
\begin{myagda}\begin{code}
module UTxO (Address : Set) (UNDERL ♯ : Address → ℕ) where

record OutputRef : Set where
  field  id     : ℕ  -- hash of the transaction
         index  : ℕ  -- index in the list of outputs

record Input {R D : Set} : Set where
  field  outRef     : OutputRef
         redeemer   : State → R
         validator  : State → R → D → Bool

record Output {D : Set} : Set where
  field  value    : Value
         address  : Address
         DATA     : State → D

record Tx : Set where
  field  inputs   : List Input
         outputs  : List Output
         forge    : Value
         fee      : Value
\end{code}\end{myagda}
}

\newcommand\auth{
\begin{myagda}\begin{code}
authorize :: Input → List Tx → Bool
authorize i l = let s = getState l in
  validator i s (redeemer i s) (DATA (lookup l (outRef i)) s)
\end{code}\end{myagda}
}

\newcommand\utxo{
\begin{myagda}\begin{code}
utxo : List Tx → List OutputRef
utxo []         =  ∅
utxo (tx :: l)  =  utxo l ^^ ∖ (outRef <$> inputs tx)
                ∪  outputs tx
\end{code}\end{myagda}
}

\newcommand\valid{
\begin{myagda}\begin{code}
record IsValidTx (tx : Tx) (l : List Tx) : Set where
  field  validOutputRefs :
           ∀ i → i ∈ inputs tx → outRef i ∈ utxo l
         allInputsValidate :
           ∀ i → i ∈ inputs tx → authorize i l ≡ true
         DOTS
\end{code}\end{myagda}
}

\newcommand\weakening{
\begin{myagda}\begin{code}
weakening  :  (f : A ↪ B) → Ledger l → Ledger (weaken f l)
\end{code}\end{myagda}
}

\newcommand\combining{
\begin{myagda}\begin{code}
UNDEER ↔ UNDEER ⊢ UNDEER  :  Ledger l → Ledger l′ → l ** l′ ~~ l″
                          →  Ledger l″
\end{code}\end{myagda}
}
