%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Extended UTxO}
\label{sec:eutxo}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

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
\TODO{Describe how proof-by-reflection fits in here}
...
\TODO{Give some insight on the Dec definitions}
...
\TODO{Reference example}

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

We can now precisely define what it means to weaken an address space; one just adds more available
addresses without removing any of the pre-existing addresses:

\begin{agda}\begin{code}
weakenTxOutput : Prefix as bs -> TxOutput′ as -> TxOutput′ bs
weakenTxOutput pr txOut = txOut { address = inject≤ addr (prefix-length pr) }
  where open import UTxO bs
\end{code}\end{agda}
For simplicity's sake, we allow extension at the end of the address space instead of anywhere in
between\footnote{Technically, we require |Prefix as bs| instead of the more flexible |as ⊆ bs|.}.
Notice also that the only place where weakening takes place are transaction outputs, since all other
components do not depend on the available address space.

With the weakening properly defined, we can finally prove the \textit{weakening lemma} for the available address space:

\begin{agda}\begin{code}
weakening : ∀ {as bs : List Address} {tx : Tx′ as} {l : Ledger′ as}
  ->  (pr : Prefix as bs)
  ->  IsValidTx′ as tx l
      {- $\inferLarge$ -}
  ->  IsValidTx′ bs (weakenTx pr tx) (weakenLedger pr l)

weakening = DOTS
\end{code}\end{agda}
The weakening lemma states that the validity of a transaction with respect to a ledger is preserved if
we choose to weaken the available address space, which we estimate to be useful when we later prove more
intricate properties of the extended UTxO model.

\subsection{Combining}
\TODO{disjointness}
...
\TODO{basic theorem}
...
\TODO{interplay with weakening}

\subsection{Extension I: Data Scripts}
\TODO{More expressiveness}
...
\TODO{Explain how to use data scripts to simulate state}
...
\TODO{Showcase Marlowe's approach for compiling to eUTxO}

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
