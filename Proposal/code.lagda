%include polycode.fmt
%include stylish.lhs

\def\commentbegin{}
\def\commentend{}

%%%%%%%%%%%%%%%%%%
%% Inlined code %%
%%%%%%%%%%%%%%%%%%
\newcommand{\inlineMaybe}{|Maybe|}
\newcommand{\inlinePrefix}{|Prefix as bs|}
\newcommand{\inlineSubset}{|as ⊆ bs|}

%%%%%%%%%%%%%%%%%
%% Code blocks %%
%%%%%%%%%%%%%%%%%
\newcommand\UTXObasicTypes{
\begin{myagda}\begin{code}
Address : Set
Address = Nat
##
Value : Set
Value = Nat
##
BIT : Nat -> Value
BIT v = v
\end{code}\end{myagda}
}

\newcommand\UTXOstate{
\begin{myagda}\begin{code}
record State : Set where
  field
    height : Nat
    ⋮
\end{code}\end{myagda}
}

\newcommand\UTXOhash{
\begin{myagda}\begin{code}
postulate
  _♯ : ∀ {A : Set} -> A -> Address
  ♯-injective : ∀ {A : Set} {x y : A} -> x ♯ ≡ y ♯ -> x ≡ y
\end{code}\end{myagda}
}

\newcommand\UTXOinsOutRefs{
\begin{myagda}\begin{code}
record TxOutputRef : Set where
  field
    id     : Address
    index  : Nat
##
record TxInput : Set where
  field
    outputRef  : TxOutputRef

    R          : Set
    redeemer   : State -> R
    D          : Set
    validator  : State ->  Value ->  R ->  D ->  Bool
\end{code}\end{myagda}
}

\newcommand\UTXOoutTx{
\begin{myagda}\begin{code}
module UTxO (addresses : List Address) where
##
record TxOutput : Set where
  field
    value       : Value
    address     : Index addresses

    Data        : Set
    dataScript  : State -> Data
##
record Tx : Set where
  field
    inputs   : Set⟨ TxInput ⟩
    outputs  : List TxOutput
    forge    : Value
    fee      : Value

Ledger : Set
Ledger = List Tx
\end{code}\end{myagda}
}

\newcommand\UTXOrunValidation{
\begin{myagda}\begin{code}
runValidation : (i : TxInput) -> (o : TxOutput) -> D i ≡ Data o -> State -> Bool
runValidation i o refl st = validator i st (value o) (redeemer i st) (dataScript o st)
\end{code}\end{myagda}
}

\newcommand\UTXOutxo{
\begin{myagda}\begin{code}
unspentOutputsTx : Tx -> Set⟨ TxOutputRef ⟩
unspentOutputsTx tx = fromList (map ((tx ♯) indexed-at_) (indices (outputs tx)))
##
spentOutputsTx : Tx -> Set⟨ TxOutputRef ⟩
spentOutputsTx tx = fromList (map outputRef (inputs tx))
##
unspentOutputs : Ledger -> Set⟨ TxOutputRef ⟩
unspentOutputs []           = ∅
unspentOutputs (tx :: txs)  = unspentOutputs txs SETDIFF spentOutputsTx tx
                            ∪ unspentOutputsTx tx
\end{code}\end{myagda}
}

\newcommand\UTXOvalid{
\begin{myagda}\begin{code}
record IsValidTx (tx : Tx) (l : Ledger) : Set where
  field

    validTxRefs :
      ∀ i -> i ∈ inputs tx ->
        Any (λ t -> t ♯ ≡ id (outputRef i)) l

    validOutputIndices :
      ∀ i -> (iin : i ∈ inputs tx) ->
        index (outputRef i) <
          length (outputs (lookupTx l (outputRef i) (validTxRefs i iin)))

    validOutputRefs :
      ∀ i -> i ∈ inputs tx ->
        outputRef i SETₒ.∈′ unspentOutputs l

    validDataScriptTypes :
      ∀ i -> (iin : i ∈ inputs tx) ->
        D i ≡ Data (lookupOutput l (outputRef i) (validTxRefs i iin) (validOutputIndices i iin))

{- $\hspace{30pt}\rule{11cm}{0.4pt}$ -}

    preservesValues :
      forge tx + sum (mapWith∈ (inputs tx) λ {i} iin ->
                       lookupValue l i (validTxRefs i iin) (validOutputIndices i iin))
        ≡
      fee tx + sum (map value (outputs tx))

    noDoubleSpending :
      SETₒ.noDuplicates (map outputRef (inputs tx))

    allInputsValidate :
      ∀ i -> (iin : i ∈ inputs tx) ->
        let
          out : TxOutput
          out = lookupOutput l (outputRef i) (validTxRefs i iin) (validOutputIndices i iin)
        in
          ∀ (st : State) ->
            T (runValidation i out (validDataScriptTypes i iin) st)

    validateValidHashes :
      ∀ i -> (iin : i ∈ inputs tx) ->
        let
          out : TxOutput
          out = lookupOutput l (outputRef i) (validTxRefs i iin) (validOutputIndices i iin)
        in
          toNat (address out) ≡ (validator i) ♯
\end{code}\end{myagda}
}

\newcommand\UTXOprimedTypes{
\begin{myagda}\begin{code}
Ledger′ : List Address -> Set
Ledger′ as = Ledger
  where open import UTxO as

Tx′ : List Address -> Set
Tx′ as = Tx
  where open import UTxO as

IsValidTx′ : (as : List Address) -> Tx′ as -> Ledger′ as -> Set
IsValidTx′ as t l = IsValidTx t l
  where open import UTxO as

TxOutput′ : List Address -> Set
TxOutput′ as = TxOutput
  where open import UTxO as
\end{code}\end{myagda}
}

\newcommand\UTXOweaken{
\begin{myagda}\begin{code}
weakenTxOutput : ∀ {as bs} -> Prefix as bs -> TxOutput′ as -> TxOutput′ bs
weakenTxOutput {as} {bs} pr
     record { value = v ; dataScript = ds ; address = addr }
  =  record { value = v ; dataScript = ds ; address = inject≤ addr (prefix-length pr) }
  where open import UTxO bs
##
weakenTx : ∀ {as bs} -> Prefix as bs -> Tx′ as -> Tx′ bs
weakenTx {as} {bs}  pr  record  { inputs   = inputs
                                ; outputs  = outputs
                                ; forge    = forge
                                ; fee      = fee
                                }
                    =   record  { inputs   = inputs
                                ; outputs  = map (weakenTxOutput pr) outputs
                                ; forge    = forge
                                ; fee      = fee
                                }
##
weakenLedger : ∀ {as bs} -> Prefix as bs -> Ledger′ as -> Ledger′ bs
weakenLedger pr = map (weakenTx pr)
\end{code}\end{myagda}
}

\newcommand\UTXOweakenLemma{
\begin{myagda}\begin{code}
weakening : ∀ {as bs : List Address} {tx : Tx′ as} {l : Ledger′ as}
          -> (pr : Prefix as bs)
          -> IsValidTx′ as tx l
          {- $\hspace{15pt}\rule{8cm}{0.4pt}$ -}
          -> IsValidTx′ bs (weakenTx pr tx) (weakenLedger pr l)

weakening = ...
\end{code}\end{myagda}
}

\newcommand\UTXOexampleSetup{
\begin{myagda}\begin{code}
addresses : List Address
addresses = 1 :: 2 :: 3 :: []
##
open import UTxO addresses
##
dummyValidator : State -> Value -> Nat -> Nat -> Bool
dummyValidator = λ _ _ _ _ -> true
##
withScripts : TxOutputRef -> TxInput
withScripts tin = record  { outputRef  = tin
                          ; redeemer   = λ _ -> 0
                          ; validator  = dummyValidator
                          }
##
BIT UNDER at UNDER : Value -> Index addresses -> TxOutput
BIT v at addr = record  { value       = v
                        ; address     = addr
                        ; dataScript  = λ _ -> 0
                        }
##
postulate
  validator♯ : ∀ {i : Index addresses} -> toNat i ≡ dummyValidator ♯
\end{code}\end{myagda}
}

\newcommand\UTXOexampleA{
\begin{myagda}\begin{code}
t₁ : Tx
t₁ = record  { inputs   = []
             ; outputs  = [ BIT 1000 at 0 ]
             ; forge    = BIT 1000
             ; fee      = BIT 0
             }

t₂ : Tx
t₂ = record  { inputs   = [ withScripts t₁₀ ]
             ; outputs  = BIT 800 at 1 :: BIT 200 at 0 :: []
             ; forge    = BIT 0
             ; fee      = BIT 0
             }

t₃ : Tx
t₃ = record  { inputs   = [ withScripts t₂₁ ]
             ; outputs  = [ BIT 199 at 2 ]
             ; forge    = BIT 0
             ; fee      = BIT 1
             }

t₄ : Tx
t₄ = record  { inputs   = [ withScripts t₃₀ ]
             ; outputs  = [ BIT 207 at 1 ]
             ; forge    = BIT 10
             ; fee      = BIT 2
             }

t₅ : Tx
t₅ = record  { inputs   = withScripts t₂₀ :: withScripts t₄₀ :: []
             ; outputs  = BIT 500 at 1 :: BIT 500 at 2 :: []
             ; forge    = BIT 0
             ; fee      = BIT 7
             }

t₆ : Tx
t₆ = record  { inputs   = withScripts t₅₀ :: withScripts t₅₁ :: []
             ; outputs  = [ BIT 999 at 2 ]
             ; forge    = BIT 0
             ; fee      = BIT 1
             }

\end{code}\end{myagda}
}

\newcommand\UTXOexampleB{
\begin{myagda}\begin{code}
ex-ledger : Ledger
ex-ledger =  ∙ t₁ ∶- record  { validTxRefs           = λ i ()
                             ; validOutputIndices    = λ i ()
                             ; validOutputRefs       = λ i ()
                             ; validDataScriptTypes  = λ i ()
                             ; preservesValues       = refl
                             ; noDoubleSpending      = tt
                             ; allInputsValidate     = λ i ()
                             ; validateValidHashes   = λ i ()
                             }
             ⊕ t₂ ∶- record { ... }
             ⊕ t₃ ∶- record { ... }
             ⊕ t₄ ∶- record { ... }
             ⊕ t₅ ∶- record { ... }
             ⊕ t₆ ∶- record { ... }
\end{code}\end{myagda}
}

\newcommand\UTXOexampleC{
\begin{myagda}\begin{code}
utxo-l₆ : list (unspentOutputs l₆) ≡ [ t₆₀ ]
utxo-l₆ = refl
\end{code}\end{myagda}
}
