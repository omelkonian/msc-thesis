%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Formal Model I: Extended UTxO}
\label{sec:eutxo}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%$%%%%%%%%%%%%%%%%%%%%

We now set out to model the accounting model of a UTxO-based ledger.
We will provide a inherently-typed model of transactions and ledgers;
this gives rise to a notion of \textit{weakening} of available addresses, which we formalize.
Moreover, we showcase the reasoning abilities of our model by giving
an example of a correct-by-construction ledger.
All code is publicly available on Github\site{https://github.com/omelkonian/formal-utxo}.

We start with the basic types, keeping them abstract since we do not care about details arising from the encoding in an
actual implementation:
\begin{agda}\begin{code}
postulate
  Address : Set
  Value : Set
  BIT : ℕ -> Value
\end{code}\end{agda}
We assume there are types representing addresses and bitcoin values, but also require the ability to construct
a value out of a natural number. In the examples that follow, we assume the simplest representation, where
both types are the natural numbers.

There is also the notion of the \textit{state} of a ledger, which will be provided to transaction scripts and allow
them to have stateful behaviour for more complicated schemes (e.g. imposing time constraints).
\begin{agda}\begin{code}
record State : Set where
  field  height : ℕ
         VDOTS
\end{code}\end{agda}
The state components have not been finalized yet, but can easily be extended later when we actually investigate
examples with expressive scripts that make use of state information, such as the current length of the ledger (\textit{height}).

As mentioned previously, we will not dive into the verification of the cryptological components of the model,
hence we postulate an \textit{irreversible} hashing function which, given any value of any type,
gives back an address (i.e. a natural number) and is furthermore injective (i.e. it is highly unlikely for two different
values to have the same hash).
\begin{agda}\begin{code}
postulate
  UL ♯ : ∀ {A : Set} -> A -> Address
  ♯-injective : ∀ {x y : A} -> x ♯ ≡ y ♯ -> x ≡ y
\end{code}\end{agda}

\subsection{Transactions}
In order to model transactions that are part of a distributed ledger, we need to first define
transaction \textit{inputs} and \textit{outputs}.
\begin{agda}\begin{code}
record TxOutputRef : Set where
  constructor UL at UR
  field  id     : Address
         index  : ℕ

record TxInput {R D : Set} : Set where
  field  outputRef  : TxOutputRef
         redeemer   : State -> R
         validator  : State ->  Value ->  R ->  D ->  Bool
\end{code}\end{agda}
\textit{Output references} consist of the address that a transaction hashes to,
as well as the index in this transaction's list of outputs.
\textit{Transaction inputs} refer to some previous output in the ledger, but also contain two types of scripts.
The \textit{redeemer} provides evidence of authorization to spend the output.
The \textit{validator} then checks whether this is so, having access to the current state of the ledger, the bitcoin output
and data provided by the redeemer and the \textit{data script} (residing in outputs).
It is also noteworthy that we immediately model scripts by their \textit{denotational semantics},
omitting unnecessary details relating to concrete syntax, lexing and parsing.

Transaction outputs send a bitcoin amount to a particular address, which either corresponds to a public key hash of a
blockchain participant (P2PKH) or a hash of a next transaction's script (P2SH).
Here, we opt to embrace the \textit{inherently-typed} philosophy of Agda and model available addresses as module parameters.
That is, we package the following definitions in a module with such a parameter, as shown below:
\begin{agda}\begin{code}
module UTxO (addresses : List Address) where

record TxOutput {D : Set} : Set where
  field  value       : Value
         address     : Index addresses
         dataScript  : State -> D

record Tx : Set where
  field  inputs   : Set⟨ TxInput ⟩
         outputs  : List TxOutput
         forge    : Value
         fee      : Value

Ledger : Set
Ledger = List Tx
\end{code}\end{agda}
\textit{Transaction outputs} consist of a bitcoin amount and the address (out of the available ones) this amount is sent to,
as well as the data script, which provides extra information to the aforementioned validator and allows for more expressive schemes.
Investigating exactly the extent of this expressiveness is one of the main goals of this thesis.

For a transaction to be submitted, one has to check that each input can actually spend the output it refers to.
At this point of interaction, one must combine all scripts, as shown below:
\begin{agda}\begin{code}
runValidation : (i : TxInput) -> (o : TxOutput) -> D i ≡ D o -> State -> Bool
runValidation i o refl st = validator i st (value o) (redeemer i st) (dataScript o st)
\end{code}\end{agda}
Note that the intermediate types carried by the respective input and output must align, evidenced by the
equality proof that is required as an argument.

\subsection{Unspent Τransaction Οutputs}
With the basic modelling of a ledger and its transaction in place, it is fairly straightforward to
inductively define the calculation of a ledger's unspent transaction outputs:
\begin{agda}\begin{code}
unspentOutputs : Ledger -> Set⟨ TxOutputRef ⟩
unspentOutputs []           = ∅
unspentOutputs (tx :: txs)  = (unspentOutputs txs ∖ spentOutputsTx tx) ∪ unspentOutputsTx tx
  where
    spentOutputsTx, unspentOutputsTx : Tx -> Set⟨ TxOutputRef ⟩
    spentOutputsTx       = (outputRef <$$> UR) ∘ inputs
    unspentOutputsTx tx  = ((tx ♯) ^^ at UR) <$$> (indices (outputs tx))
\end{code}\end{agda}

\subsection{Validity of Τransactions}
In order to submit a transaction, one has to make sure it is valid with respect to the current ledger.
We model validity as a record indexed by the transaction to be submitted and the current ledger:
\begin{agda}\begin{code}
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
##
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
\end{code}\end{agda}
The first four conditions make sure the transaction references and types are well-formed, namely that
inputs refer to actual transactions (\textit{validTxRefs}, \textit{validOutputIndices})
which are unspent so far (\textit{validOutputRefs}), but also that intermediate types used in interacting
inputs and outputs align (\textit{validDataScriptTypes}).

The last four validation conditions are more interesting, as they ascertain the validity of the submitted transaction,
namely that the bitcoin values sum up properly (\textit{preservesValues}), no output is spent twice (\textit{noDoubleSpending}),
validation succeeds for each input-output pair (\textit{allInputsValidate}) and outputs hash to the hash of their corresponding
validator script (\textit{validateValidHashes}).

The definitions of lookup functions are omitted, as they are uninteresting. The only important design choice is that,
instead of modelling lookups as partial functions (i.e. returning |Maybe|), they require a membership
proof as an argument moving the responsibility to the caller (as evidenced by their usage in the validity conditions).

\subsection{Decision Procedure}
Intrinsically-typed ledgers are correct-by-construction, but this does not come for free;
we now need to provide substantial proofs alongside each time we submit a new transaction.

To make the proof process more ergonomic for the user of the framework,
we prove that all involved propositions appearing in the |IsValidTx| record are \textit{decidable},
thus defining a decision procedure for closed formulas that do not contain any free variable.
This process is commonly referred to as \textit{proof-by-reflection}~\cite{proofbyreflection}.

Most operations already come with a decidable counterpart, e.g. |_ < _| can be decided by |_ <? _| that exists
in Agda's standard library. Therefore, what we are essentially doing is copy the initial propositions and replace
such operators with their decision procedures. Decidability is captured by the |Dec| datatype, ensuring that we
can answer a yes/no question over the enclosed proposition:
\begin{agda}\begin{code}
data Dec (P : Set) : Set where
  yes : ( p  :   P)  → Dec P
  no  : (¬p  : ¬ P)  → Dec P
\end{code}\end{agda}

Having a proof of decidability means we can replace a proof of proposition |P| with a simple call to |toWitness {Q = P?} tt|,
where |P?| is the decidable counterpart of |P|.
\begin{agda}\begin{code}
True : Dec P → Set
True (yes _)  = ⊤
True (no _)   = ⊥
##
toWitness : {Q : Dec P} → True Q → P
toWitness {Q = yes p}  _  = p
toWitness {Q = no  _}  ()
\end{code}\end{agda}
For this to compute though, the decided formula needs to be \textit{closed}, meaning it does not contain any variables.
One could even go beyond closed formulas by utilizing Agda's recent \textit{meta-programming} facilities (macros),
but this is outside of the scope of this thesis.

But what about universal/existential quantification?
We certainly know that it is not possible to decide on an arbitrary quantified proposition.
Hopefully, all our uses of the |∀| operator later constrain the quantified argument to be an element of a list.
Therefore, we can define a specific decidable variant of this format:
\begin{agda}\begin{code}
∀?  :  (xs : List A)
    →  {P : (x : A) (x∈ : x ∈ xs) → Set}
    →  (∀ x → (x∈ : x ∈ xs) → Dec (P x x∈))
    →  Dec (∀ x x∈ → P x x∈)
∀? []        P?  = yes λ _ ()
∀? (x ∷ xs)  P?  with ∀? xs (λ x′ x∈ → P? x′ (there x∈))
... | no   ¬p    = no λ p → ¬p (λ x′ x∈ → p x′ (there x∈))
... | yes  p′    with P? x (here refl)
... | no   ¬p    = no λ p → ¬p (p x (here refl))
... | yes  p     = yes λ  {  x′ (here refl) → p
                          ;  x′ (there x∈)  → p′ x′ x∈ }
\end{code}\end{agda}

We follow a similar process for existential quantification:
\begin{agda}\begin{code}
∃?  :  (xs : List A)
    →  {P : (x : A) (x∈ : x ∈ xs) → Set ℓ′}
    →  (∀ x → (x∈ : x ∈ xs) → Dec (P x x∈))
    →  Dec (∃[ x ] ∃ λ (x∈ : x ∈ xs) → P x x∈)
∃? []  P?               = no λ { (x , () , p) }
∃? (x ∷ xs) P?          with P? x (here refl)
... | yes p             = yes (x , here refl , p)
... | no ¬p             with ∃? xs (λ x′ x∈ → P? x′ (there x∈))
... | yes (x′ , x∈ , p) = yes (x′ , there x∈ , p)
... | no ¬pp            = no λ { (x′ , here refl , p) → ¬p p
                               ; (x′ , there x∈ , p) → ¬pp (x′ , x∈ , p) }
\end{code}\end{agda}

Finally, we are ready to provide a decision procedure for each validity condition using the aforementioned operators
for quantification and the decidable counterparts for the standard operators we use.
Below we give an example for the |validOutputRefs| condition:
\begin{agda}\begin{code}
validOutputRefs? : ∀ (tx : Tx) (l : Ledger)
  → Dec (∀ i → i ∈ inputs tx → outputRef i ∈ unspentOutputs l)
validOutputRefs? tx l =
  ∀? (inputs tx) λ i _ →
    outputRef i ∈? unspentOutputs l
\end{code}\end{agda}

In Section~\ref{subsec:utxo-example} we give an example construction of a valid ledger
and demonstrate that our decision procedure discharges all proof obligations with calls to |toWitness|.

\subsection{Weakening Lemma}
We have defined everything with respect to a fixed set of available addresses, but it would make sense to be able to include
additional addresses without losing the validity of the ledger constructed thus far.

In order to do, we need to first expose the basic datatypes from inside the module,
introducing their \textit{primed} version which takes the corresponding module parameter as an index:

\begin{agda}\begin{code}
Ledger′ : List Address -> Set
Ledger′ as = Ledger
  where open import UTxO as
VDOTS
\end{code}\end{agda}

We can now precisely define what it means to weaken an address space;
the only necessary ingredient is a \textit{hash-preserving injection}
from a smaller address space |𝔸| to a larger address space |𝔹|:
\begin{agda}\begin{code}
module Weakening
  (𝔸 : Set) (_♯ SA : Hash 𝔸) (_ ≟ SA _ : Decidable {A = 𝔸} _ ≡ _)
  (𝔹 : Set) (_♯ SB : Hash 𝔹) (_ ≟ SB _ : Decidable {A = 𝔹} _ ≡ _)
  (A↪B : 𝔸 , _♯ SA ↪ 𝔹 , _♯ SB)
  where
##
  import UTxO.Validity      𝔸 _♯ SA _ ≟ SA _ as A
  open import UTxO.Validity 𝔹 _♯ SB _ ≟ SB _ as B
##
  weakenTxOutput : A.TxOutput → B.TxOutput
  weakenTxOutput out = out { address = A↪B ⟨$⟩ (address out) }
##
  weakenTx : A.Tx → B.Tx
  weakenTx tx = tx { outputs = map weakenTxOutput (outputs tx) }
##
  weakenLedger : A.Ledger → B.Ledger
  weakenLedger = map weakenTx
\end{code}\end{agda}
Notice also that the only place where weakening takes place are transaction outputs, since all other
components do not depend on the available address space.

With the weakening properly defined, we can finally prove the \textit{weakening lemma} for the available address space:
\begin{agda}\begin{code}
  weakening : ∀ {tx : A.Tx} {l : A.Ledger}

    →  A.IsValidTx tx l
       {-\inferLine{6cm}-}
    →  B.IsValidTx (weakenTx tx) (weakenLedger l)
  weakening = DOTS
\end{code}\end{agda}
The weakening lemma states that the validity of a transaction with respect to a ledger is preserved if
we choose to weaken the available address space, which we estimate to be useful when we later prove more
intricate properties of the extended UTxO model.

One practical use-case for weakening is moving from a bit representation of addresses to one with more available bits
(e.g. 32-bit to 64-bit conversion).
This, of course, preserves hashes since the numeric equivalent of the converted addresses will be the same.
For instance, as we come closer to the quantum computing age, addresses will have to transition to other
encryption schemes involving many more bits\footnote{
It is believed that even 2048-bit keys will become vulnerable to rapid decryption from quantum computers.
}.
Since we allow the flexibility for arbitrary injective functions,
our weakening result will hopefully prove resilient to such scenarios.

\subsection{Combining}
Ideally, one would wish for a modular reasoning process, where it is possible to examine subsets of
unrelated transactions in a compositional manner.
This has to be done in a constrained manner, since we need to preserve the proof of validity
when combining two ledgers |l| and |l′|.

First of all, the ledgers should not share any transactions with each other: |Disjoint l l′|.
Secondly, the resulting ledger |l″| will be some interleaving of these two: |Interleaving l l′ l″|.
These conditions are actually sufficient to preserve all validity conditions, except |allInputsValidate|.
The issue arises from the dependence of validation results on the current state of the ledger,
which is given as argument to each validation script.
To remedy this, we further require that the new state, corresponding to a particular interleaving,
does not break previous validation results:
\begin{agda}\begin{code}
PreserveValidations : (l : Ledger) (l″ : Ledger) → Interleaving l _ l″ → Set
PreserveValidations l₀ _ inter =
  ∀ tx → (p : tx ∈ l₀) →
    let l   = ∈-tail p
        l″  = ∈-tail (interleave⊆ inter p)
    in ^^ ∀ {ptx i out vds}  →  runValidation ptx i out vds (getState l″)
                             ≡  runValidation ptx i out vds (getState l)
\end{code}\end{agda}

Putting all conditions together, we are now ready to formulate a \textit{combining} operation for valid ledgers:
\begin{agda}\begin{code}
_ ↔ _ ∶- _ : ∀ {l l′ l″ : Ledger}
  →  ValidLedger l
  →  ValidLedger l′
  →  Σ[ i ∈ Interleaving l l′ l″ ]
  ×  Disjoint l l′
  ×  PreserveValidations l l″ i
  ×  PreserveValidations l′ l″ (swap i)
     {-\inferLine{6cm}-}
  →  ValidLedger l″
\end{code}\end{agda}
The proof inductively proves validity of each transaction in the interleaved ledger,
essentially reusing the validity proofs of the ledger constituents.

It is important to notice a useful interplay between weakening and combining:
if we wish to combine ledgers that use different addresses, we can now just apply weakening
first and then combine in a type-safe manner.

\subsection{Extension I: Data Scripts}
The |dataScript| field in transaction outputs does not appear in the original abstract UTxO model~\cite{utxo},
but is available in the extended version of the UTxO model used in the Cardano blockchain~\cite{eutxo}.
This addition raises the expressive level of UTxO-based transaction, since it is now possible
to simulate stateful behaviour, passing around state in the data scripts (i.e. |D = State|).

This technique is successfully employed in \textit{Marlowe},
a DSL for financial contracts that compiles down to eUTxO transactions~\cite{marlowe}.
Marlowe is accompanied by a simple small-step semantics, i.e. a state transition system.
Using data scripts, compilation is rather straightforward since we can pass around
the state of the semantics in the data scripts.

\subsection{Extension II: Multi-currency}
\TODO{Value Generalization: Currency maps}
...
\TODO{Monoidal structure preserved -> modified validity conditions}
...

\subsection{Example} \label{subsec:utxo-example}
To showcase how we can use our model to construct \textit{correct-by-construction} ledgers,
let us revisit the example ledger presented in the Chimeric Ledgers paper~\cite{chimeric}.

Any blockchain can be visually represented as a \textit{directed acyclic graph} (DAG), with transactions as nodes
and input-output pairs as edges, as shown in Figure~\ref{fig:utxo-ledger}.
\begin{figure}
\newcommand\forge[1]{forge: \bitcoin ~#1}
\newcommand\fee[1]{fee:\hspace{7pt} \bitcoin ~#1}
\begin{tikzpicture}
  [basic box/.style = {
     draw,
     shape = rectangle,
     align = left,
     %minimum width=2cm,
     minimum height=1.2cm,
     rounded corners},
   redge/.style = {
     bend right = 50},
   upedge/.style = {
     transform canvas={yshift=12pt}},
   downedge/.style = {
     transform canvas={yshift=-12pt}},
   to/.style = {
     ->,
     >=stealth',
     semithick},
  every matrix/.style={column sep=0.9cm},
  font=\footnotesize
  ]
  \matrix{
    \node[basic box, label = $t_1$] (t)
      {\forge{1000}\\ \fee{0}};
    & \node[basic box, label = $t_2$] (tt)
      {\forge{0}\\ \fee{0}};
    & \node {};
    & \node {};
    & \node[basic box, label = $t_5$] (tfive)
      {\forge{0}\\ \fee{7}};
    & \node[basic box, label = $t_6$] (tsix)
      {\forge{0}\\ \fee{1}};
    & \node (end) {}; \\

    \node {};
    & \node {};
    & \node[basic box, label = $t_3$] (ttt)
      {\forge{0}\\ \fee{1}};
    & \node[basic box, label = $t_4$] (tfour)
      {\forge{10}\\ \fee{2}};
    & \node {};
    & \node {};
    & \node {}; \\
  };

  \path
  (t)     edge[to]           node[anchor=south,above]{\bitcoin ~1000}
                             node[anchor=north,below]{@@1} (tt)
  (tt)    edge[to, redge]    node[anchor=south,above]{\hspace{10pt} \bitcoin ~200}
                             node[anchor=north,below]{\hspace{-10pt} @@1} (ttt)
  (tt)    edge[to]           node[anchor=south,above]{\bitcoin ~800}
                             node[anchor=north,below]{@@2} (tfive)
  (ttt)   edge[to]           node[anchor=south,above]{\bitcoin ~199}
                             node[anchor=north,below]{@@3} (tfour)
  (tfour) edge[to, redge]    node[anchor=south,above]{\hspace{-10pt} \bitcoin ~207}
                             node[anchor=north,below]{\hspace{10pt} @@2} (tfive)
  (tfive) edge[to, upedge]   node[anchor=south,above]{\bitcoin ~500}
                             node[anchor=north,below]{@@2} (tsix)
  (tfive) edge[to, downedge] node[anchor=south,above]{\bitcoin ~500}
                             node[anchor=north,below]{@@3} (tsix)
  (tsix)  edge[to, red]      node[anchor=south,above]{\bitcoin ~999}
                             node[anchor=north,below]{@@3} (end)
  ;
\end{tikzpicture}
\caption{Example ledger with six transactions (unspent outputs are coloured in red)}
\label{fig:utxo-ledger}
\end{figure}

First, we need to set things up by declaring the list of available addresses and opening our module with this parameter.
\begin{agda}\begin{code}
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
##
BIT UL at UR : Value -> Index addresses -> TxOutput
BIT v at addr = record  { value       = v
                        ; address     = addr
                        ; dataScript  = λ _ -> 0
                        }
##
postulate
  validator♯ : ∀ {i : Index addresses} -> toℕ i ≡ dummyValidator ♯
\end{code}\end{agda}
Note that, since we will not utilize the expressive power of scripts in this example, we also provide convenient short cuts for
defining inputs and outputs with dummy default scripts.
Furthermore, we postulate that the addresses are actually the hashes of validators scripts, corresponding to the P2SH scheme
in Bitcoin.

We can then proceed to define the individual transactions\footnote{
The first sub-index of each variable refers to the order the transaction are submitted,
while the second sub-index refers to which output of the given transaction we select.
}
depicted in Figure~\ref{fig:utxo-ledger}:
\begin{agda}\begin{code}
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
\end{code}\end{agda}

Finally, we can construct a correct-by-construction ledger, by iteratively submitting each transaction along with
the proof that it is valid with respect to the ledger constructed thus far\footnote{
Here, we use a specialized notation of the form $\bullet t_1 \vdash p_1 \oplus t_2 \vdash p_2 \oplus \dots \oplus t_n \vdash p_n$,
where each insertion of transaction $t_x$ requires a proof of validity $p_x$ as well.
Technically, the $\oplus$ operator has type |(l : Ledger) → (t : Tx) → IsValidTx t l → Ledger|.
}:
\begin{agda}\begin{code}
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
\end{code}\end{agda}
The proof validating the submission of the first transaction $t_1$ is trivially discharged.
While the rest of the proofs are quite involved, it is worthy to note that their size/complexity stays constant
independently of the ledger length. This is mainly due to the re-usability of proof components, arising from
the main functions being inductively defined.

It is now trivial to verify that the only unspent transaction output of our ledger is the output of the last
transaction $t_6$, as demonstrated below:
\begin{agda}\begin{code}
utxo : list (unspentOutputs ex-ledger) ≡ [ t₆₀ ]
utxo = refl
\end{code}\end{agda}
