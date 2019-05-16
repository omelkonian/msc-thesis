%include polycode.fmt
%include stylish.lhs

\def\commentbegin{}
\def\commentend{}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                  UTxO                                      %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Inlined code
\newcommand{\inlineValue}{|Value|}
\newcommand{\inlineMaybe}{|Maybe|}
\newcommand{\inlinePrefix}{|Prefix as bs|}
\newcommand{\inlineSubset}{|as ⊆ bs|}
\newcommand{\inlineListCons}{|(l : Ledger) → (t : Tx) → IsValidTx t l → Ledger|}

%% Code blocks
\newcommand\UTXObasicTypes{
\begin{myagda}\begin{code}
postulate
  Address : Set
  Value : Set
  BIT : ℕ -> Value
\end{code}\end{myagda}
}

\newcommand\UTXOstate{
\begin{myagda}\begin{code}
record State : Set where
  field  height : ℕ
         VDOTS
\end{code}\end{myagda}
}

\newcommand\UTXOhash{
\begin{myagda}\begin{code}
postulate
  UNDERL ♯ : ∀ {A : Set} -> A -> Address
  ♯-injective : ∀ {x y : A} -> x ♯ ≡ y ♯ -> x ≡ y
\end{code}\end{myagda}
}

\newcommand\UTXOinsOutRefs{
\begin{myagda}\begin{code}
record TxOutputRef : Set where
  constructor UNDERL at UNDERR
  field  id     : Address
         index  : ℕ

record TxInput {R D : Set} : Set where
  field  outputRef  : TxOutputRef
         redeemer   : State -> R
         validator  : State ->  Value ->  R ->  D ->  Bool
\end{code}\end{myagda}
}

\newcommand\UTXOoutTxA{
\savecolumns
\begin{myagda}\begin{code}
module UTxO (addresses : List Address) where

record TxOutput {D : Set} : Set where
  field  value       : Value
         address     : Index addresses
         dataScript  : State -> D

record Tx : Set where
  field  inputs   : Set⟨ TxInput ⟩
         outputs  : List TxOutput
\end{code}\end{myagda}
}
\newcommand\UTXOoutTxB{
\restorecolumns
\begin{myagda}\begin{code}
         forge    : Value
         fee      : Value

Ledger : Set
Ledger = List Tx
\end{code}\end{myagda}
}

\newcommand\UTXOrunValidation{
\begin{myagda}\begin{code}
runValidation : (i : TxInput) -> (o : TxOutput) -> D i ≡ D o -> State -> Bool
runValidation i o refl st = validator i st (value o) (redeemer i st) (dataScript o st)
\end{code}\end{myagda}
}

\newcommand\UTXOutxo{
\begin{myagda}\begin{code}
unspentOutputs : Ledger -> Set⟨ TxOutputRef ⟩
unspentOutputs []           = ∅
unspentOutputs (tx :: txs)  = (unspentOutputs txs ∖ spentOutputsTx tx) ∪ unspentOutputsTx tx
  where
    spentOutputsTx, unspentOutputsTx : Tx -> Set⟨ TxOutputRef ⟩
    spentOutputsTx       = (outputRef <$$> UNDERR) ∘ inputs
    unspentOutputsTx tx  = ((tx ♯) ^^ at UNDERR) <$$> (indices (outputs tx))
\end{code}\end{myagda}
}

\newcommand\UTXOvalidA{
\savecolumns
\begin{myagda}\begin{code}
record IsValidTx (tx : Tx) (l : Ledger) : Set where
  field
    validTxRefs :
      ∀ i -> i ∈ inputs tx ->
        Any (λ t -> t ♯ ≡ id (outputRef i)) l
##
    validOutputIndices :
      ∀ i -> (iin : i ∈ inputs tx) ->
        index (outputRef i) <
          length (outputs (lookupTx l (outputRef i) (validTxRefs i iin)))
\end{code}\end{myagda}
}
\newcommand\UTXOvalidB{
\restorecolumns
\begin{myagda}\begin{code}
    validOutputRefs :
      ∀ i -> i ∈ inputs tx ->
        outputRef i ∈ unspentOutputs l
##
    validDataScriptTypes :
      ∀ i -> (iin : i ∈ inputs tx) ->
        D i ≡ D (lookupOutput l (outputRef i) (validTxRefs i iin) (validOutputIndices i iin))
##
      {- $\inferVeryLarge$ -}
##
    preservesValues :
      forge tx + sum (mapWith∈ (inputs tx) λ {i} iin ->
                       lookupValue l i (validTxRefs i iin) (validOutputIndices i iin))
        ≡
      fee tx + sum (value <$$> outputs tx)
##
    noDoubleSpending :
      noDuplicates (outputRef <$$> inputs tx)
##
    allInputsValidate :
      ∀ i -> (iin : i ∈ inputs tx) ->
        let  out : TxOutput
             out = lookupOutput l (outputRef i) (validTxRefs i iin) (validOutputIndices i iin)
        in   ∀ (st : State) ->
               T (runValidation i out (validDataScriptTypes i iin) st)
##
    validateValidHashes :
      ∀ i -> (iin : i ∈ inputs tx) ->
        let  out : TxOutput
             out = lookupOutput l (outputRef i) (validTxRefs i iin) (validOutputIndices i iin)
        in   toℕ (address out) ≡ (validator i) ♯
\end{code}\end{myagda}
}

\newcommand\UTXOprimedTypes{
\begin{myagda}\begin{code}
Ledger′ : List Address -> Set
Ledger′ as = Ledger
  where open import UTxO as
VDOTS
\end{code}\end{myagda}
}

\newcommand\UTXOweaken{
\begin{myagda}\begin{code}
weakenTxOutput : Prefix as bs -> TxOutput′ as -> TxOutput′ bs
weakenTxOutput pr txOut = txOut { address = inject≤ addr (prefix-length pr) }
  where open import UTxO bs
\end{code}\end{myagda}
}

\newcommand\UTXOweakenLemma{
\begin{myagda}\begin{code}
weakening : ∀ {as bs : List Address} {tx : Tx′ as} {l : Ledger′ as}
  ->  (pr : Prefix as bs)
  ->  IsValidTx′ as tx l
      {- $\inferLarge$ -}
  ->  IsValidTx′ bs (weakenTx pr tx) (weakenLedger pr l)

weakening = DOTS
\end{code}\end{myagda}
}

\newcommand\UTXOexampleSetupA{
\savecolumns
\begin{myagda}\begin{code}
addresses : List Address
addresses = 1 :: 2 :: 3 :: []
##
open import UTxO addresses
##
dummyValidator : State -> Value -> ℕ -> ℕ -> Bool
dummyValidator = λ _ _ _ _ -> true
##
withScripts : TxOutputRef -> TxInput
withScripts tin = record  { outputRef  = tin
                          ; redeemer   = λ _ -> 0
                          ; validator  = dummyValidator
                          }
\end{code}\end{myagda}
}
\newcommand\UTXOexampleSetupB{
\restorecolumns
\begin{myagda}\begin{code}
BIT UNDERL at UNDERR : Value -> Index addresses -> TxOutput
BIT v at addr = record  { value       = v
                        ; address     = addr
                        ; dataScript  = λ _ -> 0
                        }
##
postulate
  validator♯ : ∀ {i : Index addresses} -> toℕ i ≡ dummyValidator ♯
\end{code}\end{myagda}
}

\newcommand\UTXOexampleAA{
\savecolumns
\begin{myagda}\begin{code}
t₁ , t₂ , t₃ , t₄ , t₅ , t₆ : Tx
t₁ = record  { inputs   = []
             ; outputs  = [ BIT 1000 at 0 ]
             ; forge    = BIT 1000
             ; fee      = BIT 0
             }
t₂ = record  { inputs   = [ withScripts t₁₀ ]
             ; outputs  = BIT 800 at 1 :: BIT 200 at 0 :: []
             ; forge    = BIT 0
             ; fee      = BIT 0
             }
t₃ = record  { inputs   = [ withScripts t₂₁ ]
             ; outputs  = [ BIT 199 at 2 ]
             ; forge    = BIT 0
             ; fee      = BIT 1
             }
t₄ = record  { inputs   = [ withScripts t₃₀ ]
             ; outputs  = [ BIT 207 at 1 ]
             ; forge    = BIT 10
             ; fee      = BIT 2
             }
\end{code}\end{myagda}
}
\newcommand\UTXOexampleAB{
\restorecolumns
\begin{myagda}\begin{code}
t₅ = record  { inputs   = withScripts t₂₀ :: withScripts t₄₀ :: []
             ; outputs  = BIT 500 at 1 :: BIT 500 at 2 :: []
             ; forge    = BIT 0
             ; fee      = BIT 7
             }
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
             ⊕ t₂ ∶- record { DOTS }
             ⊕ t₃ ∶- record { DOTS }
             ⊕ t₄ ∶- record { DOTS }
             ⊕ t₅ ∶- record { DOTS }
             ⊕ t₆ ∶- record { DOTS }
\end{code}\end{myagda}
}

\newcommand\UTXOexampleC{
\begin{myagda}\begin{code}
utxo : list (unspentOutputs ex-ledger) ≡ [ t₆₀ ]
utxo = refl
\end{code}\end{myagda}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%                                 BitML                                      %%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Inlined code
\newcommand{\inlineA}{|A|}
\newcommand{\inlineB}{|B|}
\newcommand{\inlineIf}{|if|}
\newcommand{\inlinePut}{|put|}
\newcommand{\inlineSplit}{|split|}
\newcommand{\inlineWithdraw}{|withdraw|}
\newcommand{\inlineAuthDecoration}{|UNDER : UNDER|}
\newcommand{\inlineTimeDecoration}{|after UNDER : UNDER|}
\newcommand{\inlineSimplePut}{|put UNDER ⇒ UNDER|}
\newcommand{\inlineOplus}{|⊕|}
\newcommand{\inlineMonoid}{|(UNDERL BAR UNDERR , ∅)|}
\newcommand{\inlineAfter}{|after UNDER : UNDER|}
\newcommand{\inlineAuthJoinRule}{|[DEP-AuthJoin]|}
\newcommand{\inlineJoinRule}{|[DEP-Join]|}
\newcommand{\inlineAdvertiseRule}{|[C-Advertise]|}
\newcommand{\inlineAuthCommitRule}{|[C-AuthCommit]|}
\newcommand{\inlineAuthInitRule}{|[C-AuthInit]|}
\newcommand{\inlineInitRule}{|[C-Init]|}
\newcommand{\inlineControlRule}{|[C-Control]|}
\newcommand{\inlineAuthRevRule}{|[C-AuthRev]|}
\newcommand{\inlinePutRevRule}{|[C-PutRev]|}
\newcommand{\inlineWithdrawRule}{|[C-Withdraw]|}

%% Code blocks
\newcommand\BITbasicTypesA{
\savecolumns
\begin{myagda}\begin{code}
module Types (Participant : Set) (Honest : List SUPPLUS Participant) where
##
Time : Set
Time = ℕ
##
Value : Set
Value = ℕ
\end{code}\end{myagda}
}
\newcommand\BITbasicTypesB{
\restorecolumns
\begin{myagda}\begin{code}
record Deposit : Set where
  constructor UNDERL has UNDERR
  field  participant : Participant
         value       : Value
##
Secret : Set
Secret = String
##
data Arith : List Secret → Set where DOTS
ℕ⟦ UNDER ⟧ : ∀ {s} → Arith s → ℕ
ℕ⟦ UNDER ⟧ = DOTS
##
data Predicate : List Secret → Set where DOTS
𝔹⟦ UNDER ⟧ : ∀ {s} → Predicate s → Bool
𝔹⟦ UNDER ⟧ = DOTS
\end{code}\end{myagda}
}

\newcommand\BITpreconditions{
\begin{myagda}\begin{code}
data Precondition : List Value → Set where
  -- volatile deposit
  UNDER ? UNDER : Participant → (v : Value) → Precondition [ v ]
  -- persistent deposit
  UNDER ! UNDER : Participant → (v : Value) → Precondition [ v ]
  -- committed secret
  UNDERL ♯ UNDERR : Participant → Secret → Precondition []
  -- conjunction
  UNDER ∧ UNDER : Precondition vs SUBL → Precondition vs SUBR → Precondition (vs SUBL ++ vs SUBR)
\end{code}\end{myagda}
}

\newcommand\BITcontracts{
\begin{myagda}\begin{code}
data Contract  :  Value   -- the monetary value it carries
               →  Values  -- the deposits it presumes
               →  Set where
  -- collect deposits and secrets
  put UNDER reveal UNDER if UNDER ⇒ UNDER ∶- UNDER :
    (vs : List Value) → (s : Secrets) → Predicate s′  → Contract (v + sum vs) vs′ →  s′ ⊆ s
    → Contract v (vs′ ++ vs)
  -- transfer the remaining balance to a participant
  withdraw : ∀ {v} → Participant → Contract v []
  -- split the balance across different branches
  split :  (cs : List (∃[ v ] ^^ ∃[ vs ] ^^ Contract v vs))
        →  Contract (sum (proj₁ <$$> cs)) (concat (proj₂ <$$> cs))
  -- wait for participant's authorization
  UNDER : UNDER : Participant → Contract v vs → Contract v vs
  -- wait until some time passes
  after UNDER : UNDER : Time → Contract v vs → Contract v vs
\end{code}\end{myagda}
}

\newcommand\BITlollipop{
\begin{myagda}\begin{code}
UNDERL ⊸ UNDERR : ∀ {vs : Values} → (v : Value) → Contract v vs → ∃[ v ] ^^ ∃[ vs ] ^^ Contract v vs
UNDERL ⊸ UNDERR {vs} v c = v , vs , c
\end{code}\end{myagda}
}

\newcommand\BITadvertisements{
\begin{myagda}\begin{code}
record Advertisement (v : Value) (vs SUPC vs SUPG : List Value) : Set where
  constructor UNDER ⟨ UNDER ⟩∶- UNDER
  field  G      :  Precondition vs
         C      :  Contracts v vs
         valid  :  length vs SUPC ≤ length vs SUPG
                ×  participants SUPG G ++ participants SUPC C ⊆ (participant <$$> persistentDeposits SUPP G)
\end{code}\end{myagda}
}

\newcommand\BITexampleAdvertisement{
\begin{myagda}\begin{code}
open BitML (A | B) [ A ] SUPPLUS

ex-ad : Advertisement 5 [ 200 ] (200 ∷ 100 ∷ [])
ex-ad =  ⟨  B ! 200 ∧ A ! 100 ^^ ⟩
          split  (  2 ⊸ withdraw B
                 ⊕  2 ⊸ after 100 ∶ withdraw A
                 ⊕  1 ⊸ put [ 200 ] ⇒ B ∶ withdraw {201} A ∶- DOTS
                 )
          ∶- DOTS
\end{code}\end{myagda}
}

\newcommand\BITactions{
\begin{myagda}\begin{code}
AdvertisedContracts : Set
AdvertisedContracts = List (∃[ v ] ^^ ∃[ vs SUPC ] ^^ ∃[ vs SUPG ] ^^ Advertisement v vs SUPC vs SUPG)
##
ActiveContracts : Set
ActiveContracts = List (∃[ v ] ^^ ∃[ vs ] ^^ List (Contract v vs))
##
data Action (p : Participant)  -- the participant that authorises this action
  :  AdvertisedContracts       -- the contract advertisments it requires
  →  ActiveContracts           -- the active contracts it requires
  →  Values                    -- the deposits it requires from this participant
  →  List Deposit              -- the deposits it produces
  →  Set where
##
  -- commit secrets to stipulate an advertisement
  HTRI UNDERR  :  (ad : Advertisement v vs SUPC vs SUPG)
               →  Action p [ v , vs SUPC , vs SUPG , ad ] [] [] []

  -- spend x to stipulate an advertisement
  UNDER STRI UNDERR  :  (ad : Advertisement v vs SUPC vs SUPG)
                     →  (i : Index vs SUPG)
                     →  Action p [ v , vs SUPC , vs SUPG , ad ] [] [ vs SUPG ‼ i ] []

  -- pick a branch
  UNDER BTRI UNDERR  :  (c : List (Contract v vs))
                     →  (i : Index c)
                     →  Action p [] [ v , vs , c ] [] []

  VDOTS
\end{code}\end{myagda}
}

\newcommand\BITactionExample{
\begin{myagda}\begin{code}
ex-spend : Action A [ 5 , [ 200 ] , 200 ∷ 100 ∷ [] , ex-ad ] [] [ 100 ] []
ex-spend = ex-ad STRI 1
\end{code}\end{myagda}
}

\newcommand\BITconfigurations{
\begin{myagda}\begin{code}
data Configuration′  :  -- $\hspace{22pt}$ current $\hspace{20pt}$ $\times$ $\hspace{15pt}$ required
                        AdvertisedContracts  × AdvertisedContracts
                     →  ActiveContracts      × ActiveContracts
                     →  List Deposit         × List Deposit
                     →  Set where

  -- empty
  ∅ : Configuration′ ([] , []) ([] , []) ([] , [])

  -- contract advertisement
  ` UNDER  :  (ad : Advertisement v vs SUPC vs SUPG)
           →  Configuration′ ([ v , vs SUPC , vs SUPG , ad ] , []) ([] , []) ([] , [])

  -- active contract
  ⟨ UNDER , UNDER ⟩ SUPCC  :  (c : List (Contract v vs)) → Value
                           →  Configuration′ ([] , []) ([ v , vs , c ] , []) ([] , [])

  -- deposit redeemable by a participant
  ⟨ UNDERR , UNDER ⟩ SUPD  :  (p : Participant) → (v : Value)
                           →  Configuration′ ([] , []) ([] , []) ([ p has v ] , [])

  -- authorization to perform an action
  UNDERL [ UNDER ]  : (p : Participant) → Action p ads cs vs ds
                    → Configuration′ ([] , ads) ([] , cs) (ds , ((p has UNDER) <$$> vs))

  -- committed secret
  ⟨ UNDER ∶ UNDER ♯ UNDER ⟩  :  Participant →  Secret →  ℕ ⊎ ⊥
                             →  Configuration′ ([] , []) ([] , []) ([] , [])
  -- revealed secret
  UNDER ∶ UNDER ♯ UNDER  :  Participant →  Secret → ℕ
                         →  Configuration′ ([] , []) ([] , []) ([] , [])

  -- parallel composition
  UNDER | UNDER  :  Configuration′ (ads SUPL , rads SUPL) (cs SUPL , rcs SUPL) (ds SUPL , rds SUPL)
                 →  Configuration′ (ads SUPR , rads SUPR) (cs SUPR , rcs SUPR) (ds SUPR , rds SUPR)
                 →  Configuration′  (ads SUPL                    ++ ads SUPR  , rads SUPL  ++ (rads SUPR  ∖ ads SUPL))
                                    (cs SUPL                     ++ cs SUPR   , rcs SUPL   ++ (rcs SUPR   ∖ cs SUPL))
                                    ((ds SUPL ∖ rds SUPR)        ++ ds SUPR   , rds SUPL   ++ (rds SUPR   ∖ ds SUPL))
\end{code}\end{myagda}
}

\newcommand\BITclosedConfigurations{
\begin{myagda}\begin{code}
Configuration : AdvertisedContracts → ActiveContracts → List Deposit → Set
Configuration ads cs ds = Configuration′ (ads , []) (cs , []) (ds , [])
\end{code}\end{myagda}
}

\newcommand\BITrules{
\begin{myagda}\begin{code}
data UNDER —→ UNDER : Configuration ads cs ds → Configuration ads′ cs′ ds′ → Set where
  DEP-AuthJoin :
    ⟨ A , v ⟩ SUPD | ⟨ A , v′ ⟩ SUPD | Γ —→ ⟨ A , v ⟩ SUPD | ⟨ A , v′ ⟩ SUPD | A [ 0 ↔ 1 ] | Γ
##
  DEP-Join :
    ⟨ A , v ⟩ SUPD | ⟨ A , v′ ⟩ SUPD | A [ 0 ↔ 1 ] | Γ —→ ⟨ A , v + v′ ⟩ SUPD | Γ
##
  C-Advertise : ∀ {Γ ad}
    →  ∃[ p ∈ participants SUPG (G ad) ] p ∈ Hon
       {- $\inferLarge$ -}
    →  Γ —→ ` ad | Γ
##
  C-AuthCommit : ∀ {A ad Γ}
    →  secrets (G ad) ≡ a₀ DOTS aₙ
    →  (A ∈ Hon → ∀[ i ∈ 0 DOTS n ] a SUBI ≢ ⊥)
       {- $\inferLarge$ -}
    →  ` ad | Γ —→ ` ad | Γ | DOTS ⟨ A : a SUBI ♯ N SUBI ⟩ DOTS ^^ BAR ^^ A [ ♯▷ ^^ ad ]
##
  C-Control : ∀ {Γ C i D}
    →  C ‼ i ≡ A₁ : A₂ : DOTS : Aₙ : D
       {- $\inferLarge$ -}
    →  ⟨ C , v ⟩ SUPCC | DOTS A SUBI [ C BTRI i ] DOTS | Γ —→ ⟨ D , v ⟩ SUPCC | Γ
  VDOTS
\end{code}\end{myagda}
}

\newcommand\BITtimedRules{
\begin{myagda}\begin{code}
record Configuration SUPT (ads : AdvertisedContracts) (cs  : ActiveContracts) (ds  : Deposits) : Set where
  constructor UNDER at UNDER
  field  cfg   : Configuration ads cs ds
         time  : Time
##
data UNDER —→ SUBT UNDER : Configuration SUPT ads cs ds → Configuration SUPT ads′ cs′ ds′ → Set where

  Action : ∀ {Γ Γ′ t}
    →  Γ —→ Γ′
       {- $\inferSmall$ -}
    →  Γ at t —→ SUBT Γ′ at t

  Delay : ∀ {Γ t δ}
       {- $\inferMedium$ -}
    →  Γ at t —→ SUBT Γ at (t + δ)

  Timeout : ∀ {Γ Γ′ t i contract}
    →  All (UNDER ≤ t) (timeDecorations (contract ‼ i))  -- all time constraints are satisfied
    →  ⟨ [ contract ‼ i ] , v ⟩ SUPCC | Γ —→ Γ′          -- resulting state if we pick this branch
       {- $\inferMedium$ -}
    →  (⟨ contract , v ⟩ SUPCC | Γ) at t —→ SUBT Γ′ at t
\end{code}\end{myagda}
}

\newcommand\BITeqReasoning{
\begin{myagda}\begin{code}
data UNDER —↠ UNDER : Configuration ads cs ds → Configuration ads′ cs′ ds′ → Set where

  UNDER ∎ : (M : Configuration ads cs ds) → M —↠ M

  UNDER —→ ⟨ UNDER ⟩ UNDER : ∀ {M  N} (L : Configuration ads cs ds)
    →  L —→ M → M —↠ N
       {- $\inferMedium$ -}
    →  L —↠ N

begin UNDER : ∀ {M N} → M —↠ N → M —↠ N
\end{code}\end{myagda}
}

\newcommand\BITexampleA{
\begin{myagda}\begin{code}
tc : Advertisement 1 [] (1 ∷ 0 ∷ [])
tc =  ⟨ A ! 1 ∧ A ♯ a ∧ B ! 0 ⟩ ^^ reveal [ a ] ⇒ withdraw A ∶- DOTS ^^ ⊕ ^^ after t ∶ withdraw B
\end{code}\end{myagda}
}

\newcommand\BITexampleB{
\begin{myagda}\begin{code}
tc-semantics : ⟨ A , 1 ⟩ SUPD —↠ ⟨ A , 1 ⟩ SUPD | A ∶ a ♯ 6
tc-semantics =
  begin
    ⟨ A , 1 ⟩ SUPD
  —→⟨ C-Advertise ⟩
    ` tc | ⟨ A , 1 ⟩ SUPD
  —→⟨ C-AuthCommit ⟩
    ` tc | ⟨ A , 1 ⟩ SUPD | ⟨A ∶ a ♯ 6⟩ | A [ HTRI tc ]
  —→⟨ C-AuthInit ⟩
    ` tc | ⟨ A , 1 ⟩ SUPD | ⟨A ∶ a ♯ 6⟩ | A [ HTRI tc ] | A [ tc STRI 0 ]
  —→⟨ C-Init ⟩
    ⟨ tc , 1 ⟩ SUPCC | ⟨ A ∶ a ♯ inj₁ 6 ⟩
  —→⟨ C-AuthRev ⟩
    ⟨ tc , 1 ⟩ SUPCC | A ∶ a ♯ 6
  —→⟨ C-Control ⟩
    ⟨ [ reveal [ a ] ⇒ withdraw A ∶- DOTS ] , 1 ⟩ SUPCC | A ∶ a ♯ 6
  —→⟨ C-PutRev ⟩
    ⟨ [ withdraw A ] , 1 ⟩ SUPCC | A ∶ a ♯ 6
  —→⟨ C-Withdraw ⟩
    ⟨ A , 1 ⟩ SUPD | A ∶ a ♯ 6
  ∎
\end{code}\end{myagda}
}

\newcommand\BITreordering{
\begin{myagda}\begin{code}
UNDER ≈ UNDER : Configuration ads cs ds → Configuration ads cs ds → Set
c ≈ c′ = cfgToList c ↭ cfgToList c′
  where
    open import Data.List.Permutation using (UNDER ↭ UNDER)

    cfgToList : Configuration′ p₁ p₂ p₃ → List (∃[ p₁ ] ^^ ∃[ p₂ ] ^^ ∃[ p₃ ] ^^ Configuration′ p₁ p₂ p₃)
    cfgToList  ∅                 = []
    cfgToList  (l | r)           = cfgToList l ++ cfgToList r
    cfgToList  {p₁} {p₂} {p₃} c  = [ p₁ , p₂ , p₃ , c ]
\end{code}\end{myagda}
}

\newcommand\BITgeneralRule{
\begin{myagda}\begin{code}
  DEP-AuthJoin :
       Γ′ ≈ ⟨ A , v ⟩ SUPD | ⟨ A , v′ ⟩ SUPD | Γ                ^^  ∈ Configuration ads cs (A has v ∷ A has v′ ∷ ds)
    →  Γ″ ≈ ⟨ A , v ⟩ SUPD | ⟨ A , v′ ⟩ SUPD | A [ 0 ↔ 1 ] | Γ  ^^  ∈ Configuration ads cs (A has (v + v′) ∷ ds)
       {- $\inferMedium$ -}
    →  Γ′ —→ Γ″
\end{code}\end{myagda}
}
