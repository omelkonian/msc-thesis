%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Formal Model II: BitML Calculus}
\label{sec:bitml}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Now let us shift our focus to our second subject of study, the BitML calculus for modelling smart contracts.
In this subsection we sketch the formalized part of BitML we have covered so far, namely the syntax and small-step
semantics of BitML contracts, its game-theoretic symbolic model,
as well as an example execution of a contract under these semantics.
All code is publicly available on Github\site{https://github.com/omelkonian/formal-bitml}.

First, we begin with some basic definitions that will be used throughout this section.
Instead of giving a fixed datatype of participants, we parametrise our module with a given
\textit{abstract data type} of participants that we can check for equality, as well as
non-empty list of honest participants:
\begin{agda}\begin{code}
module BitML  (Participant : Set) (_ ≟ SUBP _ : Decidable {A = Participant} _ ≡ _)
              (Honest : List SPLUS Participant)
              where
##
Time : Set
Time = ℕ
##
Value : Set
Value = ℕ
##
Secret : Set
Secret = String
##
record Deposit : Set where
  constructor UL has UR
  field  participant : Participant
         value       : Value
\end{code}\end{agda}
Representation of time and monetary values is again simplistic, both modelled as natural numbers.
while we model participant secrets as simple strings\footnote{
Of course, one could provide more realistic types (e.g. support for multiple currencies or words of specific length)
to be closer to the implementation, as shown for the UTxO model in Section~\ref{sec:eutxo}.
}.
A deposit consists of the participant that owns it and the number of bitcoins it carries.

We, furthermore, introduce a simplistic language of logical predicates and arithmetic expressions with the usual constructs (e.g. numerical addition, logical conjunction) and give the usual semantics (predicates on booleans and arithmetic on naturals).
A more unusual feature of these expressions is the ability to calculate length of secrets (within arithmetic expressions)
and, in order to ensure more type safety later on, all expressions are indexed by the secrets they internally use.
\begin{agda}\begin{code}
data Arith : List Secret → Set where

  ` _ : ℕ → Arith []

  `len : (s : Secret) → Arith [ s ]

  _ `+ _ : Arith s SUBL → Arith s SUBR → Arith (s SUBL ++ s SUBR)

  _ `- _ : Arith s SUBL → Arith s SUBR → Arith (s SUBL ++ s SUBR)
##
NN _ ⟧ : ∀ {s} → Arith s → ℕ
NN _ ⟧ = DOTS
##
data Predicate : List Secret → Set where

  `True : Predicate []

  _ `∧ _ : Predicate s SUBL → Predicate s SUBR → Predicate (s SUBL ++ s SUBR)

  `¬ _ : ∀ {s} → Predicate s → Predicate s

  _ `≡ _ : Arith s SUBL → Arith s SUBR → Predicate (s SUBL ++ s SUBR)

  _ `< _ : Arith s SUBL → Arith s SUBR → Predicate (s SUBL ++ s SUBR)
##
BB _ ⟧ : ∀ {s} → Predicate s → Bool
BB _ ⟧ = DOTS
\end{code}\end{agda}

\subsection{Contracts in BitML}
A \textit{contract advertisement} consists of a set of \textit{preconditions},
which require some resources from the involved participants prior to the contract's execution,
and a \textit{contract}, which specifies the rules according to which bitcoins are transferred between participants.

Preconditions either require participants to have a deposit of a certain value on their name (volatile or not) or
commit to a certain secret.
A \textit{persistent} deposit has to be provided before the contract is stipulated, while a \textit{volatile} deposit
may be needed dynamically during the execution of the contract.
Both volatile and persistent deposits required by a precondition are captured in its two type-level indices,
respectively:
\begin{agda}\begin{code}
data Precondition : List Value → List Value → Set where

  -- volatile deposit
  _ :? _ : Participant → (v : Value) → Precondition [ v ] []

  -- persistent deposit
  _ :! _ : Participant → (v : Value) → Precondition [] [ v ]

  -- committed secret
  _ ♯♯ _ : Participant → Secret → Precondition [] []

  -- conjunction
  _ ∧ _  :  Precondition vs SV vs SP → Precondition vs SV ′ vs SP ′
         →  Precondition (vs SV ++ vs SV ′) (vs SP ++ vs SP ′)
\end{code}\end{agda}

Moving on to actual contracts, we define them by means of a collection of five types of commands;
|put| injects participant deposits and revealed secrets in the remaining contract,
|withdraw| transfers the current funds to a participant,
|split| distributes the current funds across different individual contracts,
|_ : _| requires the authorization from a participant to proceed
and |after _ : _| allows further execution of the contract only after some time has passed.
\begin{agda}\begin{code}
data Contract  :  Value       -- the monetary value it carries
               →  List Value  -- the volatile deposits it presumes
               →  Set where

  -- collect deposits and secrets
  put _ reveal _ if _ ⇒ _ ∶- _ : ∀ {s′ : List Secret} {
    →  (vs : List Value) → (s : List Secret) → Predicate s′ → Contract (v + sum vs) vs′
    →  s′ ⊆ s
    →  Contract v (vs′ ++ vs)

  -- transfer the remaining balance to a participant
  withdraw : ∀ {v vs} → Participant → Contract v vs

  -- split the balance across different branches
  split :  ∀ {vs}
    →  (cs : List (∃[ v ] ^^ Contract v vs))
    →  Contract (sum (proj₁ ⟨$⟩ cs)) vs

  -- wait for participant's authorization
  _ : _ : Participant → Contract v vs → Contract v vs

  -- wait until some time passes
  after _ : _ : Time → Contract v vs → Contract v vs
\end{code}\end{agda}
There is a lot of type-level manipulation across all constructors, since we need to make sure that indices are
calculated properly. For instance, the total value in a contract constructed by the |split| command is the
sum of the values carried by each branch.
The |put| command\footnote{
|put| comprises of several components and we will omit those that do not contain any helpful information,
e.g. write |put _ ⇒ U| when there are no revealed secrets and the predicate trivially holds.
} additionally requires an explicit proof that the predicate
of the |if| part only uses secrets revealed by the same command.

We also introduce an intuitive syntax for declaring the different branches of a |split| command, emphasizing the
\textit{linear} nature of the contract's total monetary value:
\begin{agda}\begin{code}
_ ⊸ _ : ∀ {vs} → (v : Value) → Contract v vs → ∃[ v ] ^^ Contract v vs
v ⊸ c = v , c
\end{code}\end{agda}

Having defined both preconditions and contracts, we arrive at the definition of a contract advertisement:
\begin{agda}\begin{code}
record Advertisement (v : Value) (vs SC vs SV vs SP : List Value) : Set where
  constructor _ ⟨ _ ⟩∶- _
  field  G      :  Precondition vs SV vs SP
         C      :  Contracts v vs SC
         valid  :  length vs SC ≤ length vs SV
                ×  participants SG G ++ participants SC C ⊆ (participant ⟨$⟩ persistentDeposits G)
\end{code}\end{agda}
Notice that in order to construct an advertisement, one has to also provide proof of the contract's validity with respect to
the given preconditions, namely that all deposit references in the contract are declared in the precondition
and each involved participant is required to have a persistent deposit.

To clarify things so far, let us see a simple example of a contract advertisement.
We first open the |BitML| module with a trivial datatype for participants, consisting of |A| and |B|:
\begin{agda}\begin{code}
data Participant : Set where
  A B : Participant
##
_ ≟ _ : Decidable {A = Participant} _ ≡ _
VDOTS
##
Honest : Σ[ ps ∈ List Participant ] (length ps > 0)
Honest = [ A ] , ≤-refl
##
open BitML Participant ^^ _ ≟ _ ^^ [ A ] SPLUS
\end{code}\end{agda}

We then define an advertisement, whose type already says a lot about what is going on;
it carries \bitcoin ~5, presumes the existence of at least one deposit of \bitcoin ~200, and requires a single deposit
of \bitcoin ~100 before stipulation.
\begin{agda}\begin{code}
ex-ad : Advertisement 5 [ 200 ] [ 200 ] [ 100 ]
ex-ad =  ⟨  B :? 200 ∧ A :! 100 ^^ ⟩
          split  (  2 ⊸ withdraw B
                 ⊕  2 ⊸ after 100 ∶ withdraw A
                 ⊕  1 ⊸ put [ 200 ] ⇒ B ∶ withdraw {201} A ∶- DOTS
                 )
          ∶- DOTS
\end{code}\end{agda}
Looking at the precondition itself, we see that the required deposit will be provided by |A|.
The contract first splits the bitcoins across three branches:
the first one gives \bitcoin ~2 to |B|, the second one gives \bitcoin ~2 to |A| after some time period,
while the third one retrieves |B|'s deposit of \bitcoin ~200 and allows |B| to authorize the
withdrawal of the remaining funds (currently \bitcoin ~201) from |A|.

We have omitted the proofs that ascertain the well-formedness of the |put| command and the advertisement, as
they are straightforward and do not provide any more intuition\footnote{
In fact, we have defined decidable procedures for all such proofs using the
\textit{proof-by-reflection} pattern~\cite{proofbyreflection}.
These automatically discharge all proof obligations, when there are no variables involved.}.

\subsection{Small-step Semantics}
\label{subsec:bitml-semantics}
BitML is a \textit{process calculus}, which is geared specifically towards smart contracts.
Contrary to most process calculi that provide primitive operators for inter-process communication via
message-passing~\cite{csp}, the BitML calculus does not provide such built-in features.

It, instead, provides domain-specific synchronization mechanisms through its \textit{small-step} reduction semantics.
These essentially define a \textit{labelled transition system} between \textit{configurations}, where
\textit{action} labels are emitted on every transition and represent the required actions of the participants.
This symbolic model consists of two layers; the bottom one transitioning between \textit{untimed} configurations and the top one
that works on \textit{timed} configurations.

We start with the datatype of actions, which showcases the principal actions required to satisfy an advertisement's preconditions
and an action to pick one branch of a collection of contracts (introduced by the choice operator |⊕|).
We have omitted uninteresting actions concerning the manipulation of deposits, such as dividing, joining, donating and destroying them.
Since we will often need versions of the types of advertisements/contracts with their
indices existentially quantified, we first provide aliases for them.
For convenience in notation, we will sometimes write |∃A| to mean this existential packing of the indices of |A|:
\begin{agda}\begin{code}
AdvertisedContracts : Set
AdvertisedContracts = List (∃[ v ] ^^ ∃[ vs SC ] ^^ ∃[ vs SV ] ^^ ∃[ vs SP ] ^^ Advertisement v vs SC vs SV vs SP)
##
ActiveContracts : Set
ActiveContracts = List (∃[ v ] ^^ ∃[ vs ] ^^ List (Contract v vs))
##
data Action (p : Participant)  -- the participant that authorizes this action
  :  AdvertisedContracts       -- the contract advertisements it requires
  →  ActiveContracts           -- the active contracts it requires
  →  List Value                -- the deposits it requires from this participant
  →  List Deposit              -- the deposits it produces
  →  Set where
##
  -- join two deposits deposits
  _ ↔ _  :  ∀ {vs}
         →  (i : Index vs)
         →  (j : Index vs)
         →  Action p [] [] vs ((p has UR) ⟨$⟩ updateAt ((i , vs ‼ i + vs ‼ j) ∷ (j , 0) ∷ []) vs)

  -- commit secrets to stipulate an advertisement
  HTRI UR  :  (ad : Advertisement v vs SC vs SV vs SP)
           →  Action p [ v , vs SC , vs SV , vs SP , ad ] [] [] []

  -- spend x to stipulate an advertisement
  _ STRI UR  :  (ad : Advertisement v vs SC vs SV vs SP)
             →  (i : Index vs SP)
             →  Action p [ v , vs SC , vs SV , vs SP , ad ] [] [ vs SP ‼ i ] []

  -- pick a branch
  _ BTRI UR  :  (c : List (Contract v vs))
             →  (i : Index c)
             →  Action p [] [ v , vs , c ] [] []

  VDOTS
\end{code}\end{agda}
The action datatype is parametrised\footnote{
In Agda, datatype parameters are similar to indices, but are not allowed to vary across constructors.
}
over the participant who performs it
and includes several indices representing the prerequisites the current configuration has to satisfy, in order for
the action to be considered valid (e.g. one cannot spend a deposit to stipulate an advertisement that does not exist).

The first index refers to advertisements that appear in the current configuration, the second to contracts that have
already been stipulated, the third to deposits owned by the participant currently performing the action and the fourth
declares new deposits that will be created by the action.
For instance, the join operation |_ ↔ _| requires a non-empty list of deposits and produces a modification,
where the two values at indices |i| and |j| are merged in position |i|.

Although our indexing scheme might seem a bit heavyweight now, it makes many little details and assumptions explicit,
which would bite us later on when we will need to reason about them.

Continuing from our previous example advertisement, let's see an example action where |A| spends the required \bitcoin ~100
to stipulate the example contract\footnote{
Notice that we have to make all indices of the advertisement explicit in the second index in the action's type signature.
}:
\begin{agda}\begin{code}
ex-spend : Action A [ 5 , [ 200 ] , [ 200 ] , [ 100 ] , ex-ad ] [] [ 100 ] []
ex-spend = ex-ad STRI 0 SF
\end{code}\end{agda}
The |0 SF| is not a mere natural number, but inhibits |Fin (length vs SP)|, which ensures we
can only construct actions that spend valid persistent deposits.

BitML's small-step semantics is a state transition system, whose states we call \textit{configurations}.
These are built from advertisements, active contracts, deposits, action authorizations and committed/revealed secrets:
\begin{agda}\begin{code}
data Configuration′  :  -- $\hspace{22pt}$ current $\hspace{20pt}$ $\times$ $\hspace{15pt}$ required
                        AdvertisedContracts  × AdvertisedContracts
                     →  ActiveContracts      × ActiveContracts
                     →  List Deposit         × List Deposit
                     →  Set where

  -- empty configuration
  ∅ : Configuration′ ([] , []) ([] , []) ([] , [])

  -- contract advertisement
  ` _  :  (ad : Advertisement v vs SC vs SV vs SP)
       →  Configuration′ ([ v , vs SC , vs SV , vs SP , ad ] , []) ([] , []) ([] , [])

  -- active contract
  ⟨ _ , _ ⟩ SCC  :  (c : List (Contract v vs)) → Value
                 →  Configuration′ ([] , []) ([ v , vs , c ] , []) ([] , [])

  -- deposit redeemable by a participant
  ⟨ _ , _ ⟩ SDD  :  (p : Participant) → (v : Value)
                  →  Configuration′ ([] , []) ([] , []) ([ p has v ] , [])

  -- authorization to perform an action
  _ [ _ ]  :  (p : Participant) → Action p ads cs vs ds
           →  Configuration′ ([] , ads) ([] , cs) (ds , ((p has _) ⟨$⟩ vs))

  -- committed secret
  ⟨ _ ∶ _ ♯ _ ⟩  :  Participant → Secret → Maybe ℕ
                 →  Configuration′ ([] , []) ([] , []) ([] , [])
  -- revealed secret
  _ ∶ _ ♯ _  :  Participant → Secret → ℕ
             →  Configuration′ ([] , []) ([] , []) ([] , [])

  -- parallel composition
  _ | _  :  Configuration′ (ads SL , rads SL) (cs SL , rcs SL) (ds SL , rds SL)
         →  Configuration′ (ads SR , rads SR) (cs SR , rcs SR) (ds SR , rds SR)
         →  Configuration′  (ads SL                  ++ ads SR  , rads SL  ++ (rads SR  ∖ ads SL))
                            (cs SL                   ++ cs SR   , rcs SL   ++ (rcs SR   ∖ cs SL))
                            ((ds SL ∖ rds SR)        ++ ds SR   , rds SL   ++ (rds SR   ∖ ds SL))
\end{code}\end{agda}
The indices are quite involved, since we need to record both the current advertisements, stipulated contracts and deposits
and the required ones for the configuration to become valid. The most interesting case is the parallel composition
operator, where the resources provided by the left operand might satisfy some requirements of the right operand. Moreover,
consumed deposits have to be eliminated as there can be no double spending, while the number of advertisements and contracts
always grows.

By composing configurations, we will eventually end up in a \textit{closed} configuration, where
all required indices are empty (i.e. the configuration is self-contained):
\begin{agda}\begin{code}
Configuration : AdvertisedContracts → ActiveContracts → List Deposit → Set
Configuration ads cs ds = Configuration′ (ads , []) (cs , []) (ds , [])
\end{code}\end{agda}

We are now ready to declare the inference rules of the bottom layer of our small-step semantics,
by defining an inductive datatype modelling the binary step relation between untimed configurations:
\begin{agda}\begin{code}
data _ —→ _ : Configuration ads cs ds → Configuration ads′ cs′ ds′ → Set where
  DEP-AuthJoin :
    ⟨ A , v ⟩ SDD | ⟨ A , v′ ⟩ SDD | Γ —→ ⟨ A , v ⟩ SDD | ⟨ A , v′ ⟩ SDD | A [ 0 ↔ 1 ] | Γ
##
  DEP-Join :
    ⟨ A , v ⟩ SDD | ⟨ A , v′ ⟩ SDD | A [ 0 ↔ 1 ] | Γ —→ ⟨ A , v + v′ ⟩ SDD | Γ
##
  C-Advertise : ∀ {Γ ad}
    →  ∃[ p ∈ participants SG (G ad) ] p ∈ Hon
       {-\inferLine{6cm}-}
    →  Γ —→ ` ad | Γ
##
  C-AuthCommit : ∀ {A ad Γ}
    →  secrets (G ad) ≡ a₀ DOTS aₙ
    →  (A ∈ Hon → ∀[ i ∈ 0 DOTS n ] a SUBI ≢ ⊥)
       {-\inferLine{8cm}-}
    →  ` ad | Γ —→ ` ad | Γ | DOTS ⟨ A : a SUBI ♯ N SUBI ⟩ DOTS ^^ BAR ^^ A [ ♯▷ ^^ ad ]
##
  C-Control : ∀ {Γ C i D}
    →  C ‼ i ≡ A₁ : A₂ : DOTS : Aₙ : D
       {-\inferLine{8cm}-}
    →  ⟨ C , v ⟩ SCC | DOTS A SUBI [ C BTRI i ] DOTS | Γ —→ ⟨ D , v ⟩ SCC | Γ
  VDOTS
\end{code}\end{agda}
There is a total of 18 rules we need to define, but we choose to depict only a representative subset of them.
For a detailed overview of all the rules, we refer the reader to the original BitML paper~\cite{bitml},
as well as to the source code of the BitML compiler~\site{https://github.com/bitml-lang/bitml-compiler}.

The first pair of rules initially appends the authorization to merge
two deposits to the current configuration (rule |DEP-AuthJoin|) and then performs the actual join (rule |DEP-Join|).
This is a common pattern across all rules, where we first collect authorizations for an action by all involved participants,
and then we fire a subsequent rule to perform this action.
|C-Advertise| advertises a new contract, mandating that at least one of the participants involved in the pre-condition
is honest and requiring that all deposits needed for stipulation are available in the surrounding context.
|C-AuthCommit| allows participants to commit to the secrets required by the contract's pre-condition, but only dishonest
ones can commit to the invalid length $\bot$.
Lastly, |C-Control| allows participants to give their authorization required by a particular branch out of the current
choices present in the contract, discarding any time constraints along the way.

It is noteworthy to mention that during the transcriptions of the complete set of rules from the paper~\cite{bitml}
to our dependently-typed setting,
we discovered some discrepancies or over-complications, which we document extensively in Section~\ref{subsec:fixes}.

The inference rules above have elided any treatment of time constraints;
this is handled by the top layer, whose states are now timed configurations.
The only interesting inference rule is the one that handles time decorations of the form |after _ : U|,
since all other cases are dispatched to the bottom layer (which just ignores timing aspects).
\begin{agda}\begin{code}
record Configuration ST  (ads : AdvertisedContracts)
                         (cs  : ActiveContracts)
                         (ds  : Deposits) : Set where
  constructor _ at _
  field  cfg   : Configuration ads cs ds
         time  : Time
##
data _ —→ SUBT _ : Configuration ST ads cs ds → Configuration ST ads′ cs′ ds′ → Set where

  Action : ∀ {Γ Γ′ t}
    →  Γ —→ Γ′
       {-\inferLine{3cm}-}
    →  Γ at t —→ SUBT Γ′ at t

  Delay : ∀ {Γ t δ}
       {-\inferLine{4cm}-}
    →  Γ at t —→ SUBT Γ at (t + δ)

  Timeout : ∀ {Γ Γ′ t i contract}
    →  All (U ≤ t) (timeDecorations (contract ‼ i))  -- all time constraints are satisfied
    →  ⟨ [ contract ‼ i ] , v ⟩ SCC | Γ —→ Γ′        -- resulting state if we pick this branch
       {-\inferLine{6cm}-}
    →  (⟨ contract , v ⟩ SCC | Γ) at t —→ SUBT Γ′ at t
\end{code}\end{agda}

\subsection{Reasoning Modulo Permutation}
In the definitions above, we have assumed that |(UL BAR UR , ∅)| forms a \textit{commutative monoid}, which allowed us
to always present the required sub-configuration individually on the far left of a composite configuration.
While such definitions enjoy a striking similarity to the ones appearing in the original paper~\cite{bitml}
(and should always be preferred in an informal textual setting),
this approach does not suffice for a mechanized account of the model.
After all, this explicit treatment of all intuitive assumptions/details is what makes our approach robust and will lead to
a deeper understanding of how these systems behave.
To overcome this intricacy, we introduce an \textit{equivalence relation} on configurations, which holds when
they are just permutations of one another:
\begin{agda}\begin{code}
U ≈ _ : Configuration ads cs ds → Configuration ads cs ds → Set
c ≈ c′ = cfgToList c ↭ cfgToList c′
  where
    open import Data.List.Permutation using (U ↭ U)

    cfgToList : Configuration′ p₁ p₂ p₃ → List (∃[ p₁ ] ^^ ∃[ p₂ ] ^^ ∃[ p₃ ] ^^ Configuration′ p₁ p₂ p₃)
    cfgToList  ∅                 = []
    cfgToList  (l | r)           = cfgToList l ++ cfgToList r
    cfgToList  {p₁} {p₂} {p₃} c  = [ p₁ , p₂ , p₃ , c ]
\end{code}\end{agda}
Given this reordering mechanism, we now need to generalize all our inference rules to implicitly
reorder the current and next configuration of the step relation.
We achieve this by introducing a new variable for each of the operands of the resulting step relations,
replacing the operands with these variables and requiring that they are
re-orderings of the previous configurations, as shown in the following generalization of the |DEP-AuthJoin| rule\footnote{
In fact, it is not necessary to reorder both ends for the step relation; at least one would be adequate.
}:
\begin{agda}\begin{code}
  DEP-AuthJoin :
       Γ′  ≈ ⟨ A , v ⟩ SDD | ⟨ A , v′ ⟩ SDD | Γ
           ∈ Configuration ads cs (A has v ∷ A has v′ ∷ ds)
    →  Γ″  ≈ ⟨ A , v ⟩ SDD | ⟨ A , v′ ⟩ SDD | A [ 0 ↔ 1 ] | Γ
           ∈ Configuration ads cs (A has (v + v′) ∷ ds)
       {-\inferLine{8cm}-}
    →  Γ′ —→ Γ″
\end{code}\end{agda}

Unfortunately, we now have more proof obligations of the re-ordering relation lying around, which makes reasoning about
our semantics rather tedious. We are currently investigating different techniques to model such reasoning up to equivalence:
\begin{itemize}
\item \textit{Quotient types}~\cite{quotient} allow equipping a type with an equivalence relation.
If we assume the axiom that two elements of the underlying type are \textit{propositionally} equal when they are equivalent,
we could discharge our current proof burden trivially by reflexivity.
Unfortunately, while one can easily define \textit{setoids} in Agda, there is not enough support from the underlying type system to make reasoning about such an equivalence as easy as with built-in equality.
\item Going a step further into more advanced notions of equality, we arrive at \textit{homotopy type theory}~\cite{homotopy},
which tries to bridge the gap between reasoning about isomorphic objects in informal pen-paper proofs
and the way we achieve this in mechanized formal methods.
Again, realizing practical systems with such an enriched theory is a topic of current research~\cite{cubical} and no mature implementation exists yet, so we cannot integrate it with our current development in any pragmatic way.
\item The crucial problems we have encountered so far are attributed to the non-deterministic nature of BitML, which is actually
inherent in any process calculus.
Building upon this idea, we plan to take a step back and investigate
different reasoning techniques for a minimal process calculus.
Once we have an approach that is more suitable, we will incorporate it in our full-blown BitML calculus.
Current efforts are available on Github\site{https://github.com/omelkonian/formal-process-calculus}.
\end{itemize}

For the time being, the complexity that arises from having the permutation proofs in the
premises of each and every one of the 18 rules, poses a significant burden to our development.
As a quick workaround, we can factor out the permutation relation in the \textit{reflexive transitive closure}
of the step relation, which will eventually constitute our custom syntax for proving derivations,
inspired by equational reasoning:
\begin{agda}\begin{code}
data _ —↠ _ : Configuration ads cs ds → Configuration ads′ cs′ ds′ → Set where
##
  _ ∎ :

       (M : Configuration ads cs ds)
       {-\inferLine{2.5cm}-}
    →  M —↠ M
##
  _ —→⟨ _ ⟩ _ : ∀ {L′ M M′ N}

    →  (L : Configuration ads cs ds)
    →  L′ —→ M′
    →  M —↠ N
    →  { _ : L ≈ L′ × M ≈ M′ }
       {-\inferLine{4cm}-}
    →  L —↠ N
##
begin _ : ∀ {M N}

  →  M —↠ N
     {-\inferLine{2.5cm}-}
  →  M —↠ N
begin x = x
\end{code}\end{agda}
The permutation relation is actually decidable, so we can always discharge the implicitly required proof,
similarly to the techniques described in Section~\ref{subsec:utxo-example}.

\subsection{Example: Timed-commitment Protocol}
\label{subsec:bitml-example}
We are finally ready to see a more intuitive example of the \textit{timed-commitment protocol}, where a participant
commits to revealing a valid secret $a$ (e.g. "qwerty") to another participant,
but loses her deposit of \bitcoin ~1 if she does not meet a certain deadline $t$:
\begin{agda}\begin{code}
tc : Advertisement 1 [] [] (1 ∷ 0 ∷ [])
tc =  ⟨ A :! 1 ∧ A ♯♯ a ∧ B :! 0 ⟩ ^^ reveal [ a ] ⇒ withdraw A ∶- DOTS ^^ ⊕ ^^ after t ∶ withdraw B
\end{code}\end{agda}

Below is one possible reduction in the bottom layer of our small-step semantics, demonstrating the case where
the participant actually meets the deadline:
\begin{agda}\begin{code}
tc-semantics : ⟨ A , 1 ⟩ SDD —↠ ⟨ A , 1 ⟩ SDD | A ∶ a ^^ ♯ ^^ 6
tc-semantics =
  begin
    ⟨ A , 1 ⟩ SDD
  —→⟨ C-Advertise DOTS ⟩
    ` tc | ⟨ A , 1 ⟩ SDD
  —→⟨ C-AuthCommit DOTS ⟩
    ` tc | ⟨ A , 1 ⟩ SDD | ⟨A ∶ a ♯♯ 6⟩ | A [ HTRI tc ]
  —→⟨ C-AuthInit DOTS ⟩
    ` tc | ⟨ A , 1 ⟩ SDD | ⟨A ∶ a ♯♯ 6⟩ | A [ HTRI tc ] | A [ tc STRI 0 ]
  —→⟨ C-Init DOTS ⟩
    ⟨ tc , 1 ⟩ SCC | ⟨ A ∶ a ♯♯ inj₁ 6 ⟩
  —→⟨ C-AuthRev DOTS ⟩
    ⟨ tc , 1 ⟩ SCC | A ∶ a ♯♯ 6
  —→⟨ C-Control DOTS ⟩
    ⟨ [ reveal [ a ] ⇒ withdraw A ∶- DOTS ] , 1 ⟩ SCC | A ∶ a ♯♯ 6
  —→⟨ C-PutRev DOTS ⟩
    ⟨ [ withdraw A ] , 1 ⟩ SCC | A ∶ a ♯♯ 6
  —→⟨ C-Withdraw DOTS ⟩
    ⟨ A , 1 ⟩ SDD | A ∶ a ♯♯ 6
  ∎
\end{code}\end{agda}
At first, |A| holds a deposit of \bitcoin ~1, as required by the contract's precondition.
Then, the contract is advertised and the participants slowly provide the corresponding prerequisites
(i.e. |A| commits to a secret via |C-AuthCommit| and spends the required deposit via |C-AuthInit|,
while |B| does not do anything).
After all pre-conditions have been satisfied, the contract is stipulated (rule |C-Init|) and the secret is successfully
revealed (rule |C-AuthRev|).
Finally, the first branch is picked (rule |C-Control|) and |A| retrieves her deposit back
(rules |C-PutRev| and |C-Withdraw|).

We chose to omit the proofs required at the application of each inference rules (replaced with |DOTS| above),
since these are tedious and mostly uninteresting. Moreover, we plan to develop decision procedures for these
proofs\footnote{
Most proofs of decidability are in the Agda standard library already, but there is still a lot of ``plumbing''
to be done.
} to automate this part of the proof development process.

\subsection{Symbolic Model}
The approach taken by BitML defines two models that describe participant interaction;
the \textit{symbolic model} works on the abstract level of BitML contracts,
while the \textit{computational model} is defined at the level of concrete Bitcoin transactions.

In order to formalize the BitML's symbolic model, we first notice that a constructed derivation
witnesses one of many possible contract executions.
In other words, derivations of our small-step semantics model \textit{traces} of the contract execution.
Our symbolic model will provide a game-theoretic view over those traces, where each participant has a certain
\textit{strategy} that selects moves depending on the current trace of previous moves.
Moves here should be understood just as emissions of a label, i.e. application of a certain inference rule.

\subsubsection{Labelled Step Relation}
To that end, we associate a label to each inference rule and
extend the original step relation to additionally emit labels,
hence defining a \textit{labelled transition system}.

We first define the set of labels, which basically distinguish which rule was used,
along with all (non-proof) arguments that are required by the rule:
\begin{agda}\begin{code}
data Label : Set where
##
  auth-join[ _ , _ ↔ _ ] : Participant →  DepositIndex → DepositIndex → Label
  join[ _ ↔ _ ] :                         DepositIndex → DepositIndex → Label
##
  advertise[ _ ] : ∃Advertisement → Label
##
  auth-commit[ _ , _ , _ ] : Participant → ∃Advertisement → List CommittedSecret → Label
  auth-init[ _ , _ , _ ] : Participant → ∃Advertisement → DepositIndex → Label
  init[ _ ] : ∃Advertisement → Label
##
  auth-control[ _ , _ ▷ SB _] : Participant → (c : ∃Contracts) → Index (proj₂ (proj₂ c)) → Label
  control : Label

  VDOTS

  delay[ _ ] : Time → Label
\end{code}\end{agda}
Notice how we existentially pack indexed types, so that |Label| remains simply-typed.
This is essential, as it would be tedious to manipulate indices when there is no need for them.
Moreover, some indices are now just |ℕ| instead of |Fin|, losing the guarantee to remain well-scoped.

The step relation will now emit the corresponding label for each rule. Below, we give
the updated kind signature and an example for the |DEP-AuthJoin| rule:
\begin{agda}\begin{code}
data _ —→⟦ _ ⟧ _  :  Configuration ads cs ds
                  →  Label
                  →  Configuration ads′ cs′ ds′
                  →  Set where
  VDOTS
  DEP-AuthJoin :
    ⟨ A , v ⟩ SDD | ⟨ A , v′ ⟩ SDD | Γ
  —→⟦ auth-join[ A , 0 ↔ 1 ] ⟧
    ⟨ A , v ⟩ SDD | ⟨ A , v′ ⟩ SDD | A [ 0 ↔ 1 ] | Γ
  VDOTS
\end{code}\end{agda}

Naturally, the reflexive transitive closure of the augmented step relation will now hold a sequence of labels as well:
\begin{agda}\begin{code}
data _ —↠⟦ _ ⟧ _  :  Configuration ads cs ds
                  →  List Label
                  →  Configuration ads′ cs′ ds′
                  →  Set where
##
  _ ∎  :

       (M : Configuration ads cs ds)
       {-\inferLine{2.5cm}-}
    →  M —↠⟦ [] ⟧ M
##
  _ —→⟨ _ ⟩ _ : ∀ {L′ M M′ N}

    →  (L : Configuration ads cs ds)
    →  L′ —→⟦ a ⟧ M′
    →  M —↠⟦ as ⟧  N
    →  { _ : L ≈ L′ × M ≈ M′ }
       {-\inferLine{4cm}-}
    →  L —↠⟦ a ∷ as ⟧ N
##
begin _ : ∀ {M N}

  →  M —↠⟦ as ⟧ N
     {-\inferLine{2.5cm}-}
  →  M —↠⟦ as ⟧ N

begin x = x
\end{code}\end{agda}
The timed variants of the step relation follow exactly the same procedure, so we do not repeat the definitions here.

\subsubsection{Traces}
Values of type |_ —↠⟦ _ ⟧ _| model execution traces.
Since the complex type indices of the step-relation datatype is not as useful here,
we define a simpler datatype of execution traces that is a list of labelled transitions
between (existentially-packed) timed configurations:
\begin{agda}\begin{code}
data Trace : Set where
  _ ∙         :  ∃TimedConfiguration → Trace
##
  _ ∷⟦ _ ⟧ _  :  ∃TimedConfiguration → Label → Trace → Trace
\end{code}\end{agda}

\paragraph{Stripping}
Strategies will make moves based on these traces,
so we need a \textit{stripping} operation that traverses a configuration with its emitted labels
and removes any sensitive information (i.e. committed secrets):
\begin{agda}\begin{code}
stripCfg : Configuration′ p₁ p₂ p₃ → Configuration′ p₁ p₂ p₃
stripCfg ⟨ p ∶ a ♯♯ _ ⟩  =  ⟨ p ∶ a ♯♯ nothing ⟩
stripCfg (l | r ∶- p)   =  stripCfg l | stripCfg r ∶- p
stripCfg c              =  c

stripLabel : Label → Label
stripLabel auth-commit[ p , ad , _ ] = auth-commit[ p , ad , [] ]
stripLabel a = a

_∗ : Trace → Trace
(DOTS , Γ at t) ∗          = (DOTS , stripCfg Γ at t)
(DOTS , Γ at t) ∷⟦ α ⟧ ts  = (DOTS , stripCfg Γ at t) ∷⟦ stripLabel α ⟧ (ts ∗)
\end{code}\end{agda}

\subsubsection{Strategies}
\textit{Participant strategies} are functions which, given the (stripped) trace so far, pick
a set of possible next moves for its participant.
These moves cannot be arbitrary; they have to satisfy several validity conditions which
we require as proof in the datatype definition itself.

Strategies are expected to be PPTIME algorithms, so as to have a certain computational bound
that guarantees secrets are sufficiently hard to guess by adversaries, etc.
While recent research suggests that it is possible to track complexity bounds in the type system~\cite{timecomplexity},
working on a resource-aware logic would make this much more difficult in search of tooling and infrastructure,
thus we ignore this requirement and simply model strategies as regular functions.

Before we define the types of strategies, we give a convenient notation to extend a trace
with another (timed) transition, which essentially projects the last timed configuration out of a trace and
relates it to the second operand:
\begin{agda}\begin{code}
_ ——→⟦ _ ⟧ _ : Trace → Label → ∃TimedConfiguration → Set
R ——→⟦ α ⟧ (_ , _ , _ , tc′)
  = proj₂ (proj₂ (proj₂ (lastCfg R))) —→⟦ α ⟧ tc′
\end{code}\end{agda}

\paragraph{Honest strategies}
Each honest participant is modelled by a symbolic strategy that outputs a set of possible next
moves with respect to the current trace. These moves have to be \textit{valid}, thus we define
\textit{honest strategies} as a dependent record:
\begin{agda}\begin{code}
record HonestStrategy (A : Participant) : Set where
  field
    strategy  :  Trace → List Label

    valid     :  A ∈ Hon                         {-\hspace{7cm}-}  {-(1)-}
              ×  (∀ R α → α ∈ strategy (R ∗) →                     {-(2)-}
                   ∃[ R′ ] (R ——→⟦ α ⟧ R′))
              ×  (∀ R α → α ∈ strategy (R ∗) →                     {-(3)-}
                   Allₘ (_≡ A) (authDecoration α))
              ×  (∀ R Δ Δ′ ad →                                    {-(4)-}
                   auth-commit[ A , ad , Δ  ] ∈ strategy (R ∗) →
                   auth-commit[ A , ad , Δ′ ] ∈ strategy (R ∗) →
                     Δ ≡ Δ′)
              ×  (∀ R T′ α → α ∈ strategy (R ∗) →                  {-(5)-}
                   ∃[ α′ ] (R ——→⟦ α′ ⟧ T′) →
                   ∃[ R″ ] (T′ ∷⟦ α ⟧ R ——→⟦ α ⟧ R″) →
                     α ∈ strategy ((T′ ∷⟦ α ⟧ R) ∗))
\end{code}\end{agda}
Condition $(1)$ restricts our participants to the honest subset\footnote{
Recall that |Hon| is non-empty, i.e. there is always at least one honest participant.
} and condition $(2)$ requires that chosen moves are in accordance to the small-step semantics of BitML.
Condition $(3)$ states that one cannot authorize moves for other participants,
condition $(4)$ requires that the lengths of committed secrets are \textit{coherent}
(i.e. no different lengths for the same secrets across moves) and
condition $(5)$ dictates that decisions are \textit{consistent}, such that moves that are not chosen will still be
selected by the strategy in a future run (if they remain valid).

All honest participants should be accompanied by such a strategy,
so we pack all honest strategies in one single datatype:
\begin{agda}\begin{code}
HonestStrategies : Set
HonestStrategies = ∀ {A} → A ∈ Hon → ParticipantStrategy A
\end{code}\end{agda}

\paragraph{Adversary strategies}
All dishonest participant will be modelled by a single adversary |Adv|, whose strategy now additionally
takes the moves chosen by the honest participants and makes the final decision.

Naturally, the chosen move is subject to certain conditions and is again a dependent record:
\begin{agda}\begin{code}
record AdversarialStrategy (Adv : Participant) : Set where
  field
    strategy  :  Trace → List (Participant × List Label) → Label

    valid     :  Adv ∉ Hon                                                                    {-(1)-}
              ×  (∀ {B ad Δ} → B ∉ Hon → α ≡ auth-commit[ B , ad , Δ ] →  {-\hspace{1.5cm}-}  {-(2)-}
                   α ≡ strategy (R ∗) [])
              ×  ∀ {R : Trace} {moves : List (Participant × List Label)} →                    {-(3)-}
                  let α = strategy (R ∗) moves in
                  (  ∃[ A ]
                       (  A ∈ Hon
                       ×  authDecoration α ≡ just A
                       ×  α ∈ concatMap proj₂ moves )
                  ⊎  (  authDecoration α ≡ nothing
                     ×  (∀ δ → α ≢ delay[ δ ])
                     ×  ∃[ R′ ] (R ——→⟦ α ⟧ R′) )
                  ⊎  (∃[ B ]
                        (  (authDecoration α ≡ just B)
                        ×  (B ∉ Hon)
                        ×  (∀ s → α ≢ auth-rev[ B , s ])
                        ×  ∃[ R′ ] (R ——→⟦ α ⟧ R′) ))
                  ⊎  ∃[ δ ]
                       (  (α ≡ delay[ δ ])
                       ×  All (λ{ (_ , Λ)  →  (Λ ≡ [])
                                           ⊎  Any (λ{ delay[ δ′ ] → δ′ ≥ δ ; _ → ⊥ }) Λ}) moves )
                  ⊎  ∃[ B ] ∃[ s ]
                       (  α ≡ auth-rev[ B , s ]
                       ×  B ∉ Hon
                       ×  ⟨ B ∶ s ♯ nothing ⟩ ∈ (R ∗)
                       ×  ∃[ R∗′ ] ∃[ Δ ] ∃[ ad ]
                            (  R∗′ ∈ prefixTraces (R ∗)
                            ×  strategy R∗′ [] ≡ auth-commit[ B , ad , Δ ]
                            ×  (s , nothing) ∈ Δ )))
\end{code}\end{agda}
The first two conditions state that the adversary is not one of the honest participants
and that committing cannot depend on the honest moves, respectively.
Condition $(3)$ constraints the move that is chosen by the adversary, such that
one of the following conditions hold:
\begin{enumerate}
\item The move was chosen out of the available honest moves.
\item It is not a |delay|, nor does it require any authorization.
\item It is authorized by a dishonest participant, but is not a secret-revealing move.
\item It is a |delay|, but one that does not influence the time constraints of the honest participants.
\item It reveals a secret from a dishonest participant, in which case there is valid commit (i.e. with non-|⊥| length)
somewhere in the previous trace.
\end{enumerate}

A complete set of strategies includes a strategy for each honest participant and a single adversarial strategy:
\begin{agda}\begin{code}
Strategies : Set
Strategies = AdversarialStrategy × HonestStrategies
\end{code}\end{agda}

We can now describe how to proceed execution on the current trace,
namely by retrieving possible moves from all honest participants
and giving control to the adversary to make the final choice for a label:
\begin{agda}\begin{code}
runAdversary : Strategies → Trace → Label
runAdversary (S† , S) R = strategy ^^ S† ^^ (R ∗) (runHonestAll (R ∗) S)
  where
    runHonestAll : Trace → List (Participant × List Label) → HonestMoves
    runHonestAll R S = mapWith∈ Hon (λ {A} A∈ → A , strategy (S A∈) (R ∗))
\end{code}\end{agda}

\paragraph{Symbolic Conformance}
Given a trace, we can formulate a notion of \textit{conformance} of a trace with respect to a set of strategies,
namely when we transitioned from an initial configuration to the current trace using only moves obtained by those strategies:
\begin{agda}\begin{code}
data _ -conforms-to- _ : Trace → Strategies → Set where
##
    base : ∀ {Γ : Configuration ads cs ds} {SS : Strategies}

      →  Initial Γ
         {-\inferLine{6cm}-}
      →  (ads , cs , ds , Γ at 0) ∙ ^^ ^^ -conforms-to- ^^ ^^ SS
##
    step : ∀ {R : Trace} {T′ : ∃TimedConfiguration} {SS : Strategies}
      →  R -conforms-to- SS
      →  R ——→⟦ runAdversary SS R ⟧ T′
         {-\inferLine{7cm}-}
      →  (T′ ∷⟦ runAdversary SS R ⟧ R) ^^ ^^ -conforms-to- ^^ ^^ SS
\end{code}\end{agda}

\subsubsection{Meta-theoretical results}
\label{subsec:bitml-metatheory}
To increase confidence in our symbolic model, we proceed with the mechanization of two meta-theoretical lemmas.

\paragraph{Stripping preserves semantics}
The first one concerns the operation of stripping sensitive values out of a trace.
If we exclude moves that reveal or commit secrets (i.e. rules |AuthRefv| and |AuthCommit|),
we can formally prove that stripping preserves the small-step semantics:
\begin{agda}\begin{code}
∗-preserves-semantics :
  (∀ A s     → α ≢ auth-rev[ A , s ]) →
  (∀ A ad Δ  → α ≢ auth-commit[ A , ad , Δ ])
  →  ( ∀ T′  →  R   ——→⟦ α ⟧ T′
                {-\inferLine{2.5cm}-}
             →  R ∗ ——→⟦ α ⟧ T′ ∗ )

  ×  ( ∀ T′  →  R ∗ ——→⟦ α ⟧ T′
                {-\inferLine{5cm}-}
             →  ∃[ T″ ] (R ——→⟦ α ⟧ T″) × (T′ ∗ ≡ T″ ∗ )
\end{code}\end{agda}
The second part of the conclusion states that if we have a transition from a stripped state,
then there is an equivalent target state (modulo additional sensitive information)
to which the un-stripped state can transition.

\paragraph{Adversarial moves are always semantic}
Lastly, it holds that all moves that can be chosen by the adversary are admitted by the small-step semantics:
\begin{agda}\begin{code}
adversarial-move-is-semantic :
  ∃[ T′ ] ( R ——→⟦ runAdversary (S† , S) R ⟧ T′)
\end{code}\end{agda}

The proofs have not been completely formalized yet, since there are a lot of cases to cover
and our ``over-indexing'' approach has proven difficult to work with.
More specifically, as our type indices get increasingly complicated,
we get a lot of proof obligations at the usage sites of the indexed datatypes,
where the Agda compiler will encounter complicated equalities during normalization (e.g. |ys ─ ([] ─ ys) ≡ ys|),
which cannot be automatically solved. In these cases, we need to always rewrite the goal manually until it reaches
a point where statements become trivial.

A possible way of tackling this issue is factoring complex index dependencies out of datatype constructors and
requiring them as additional \textit{explicit} proof arguments.
For example, instead of accumulating secrets in pre-condition expressions, we could do the following:
\begin{agda}\begin{code}
-- before
_ `+ _ : Arith s SUBL → Arith s SUBR → Arith (s SUBL ++ s SUBR)
##
-- after
_ `+ _ ∶- _ : Arith s SUBL → Arith s SUBR → s ≡ s SUBL ++ s SUBR → Arith s
\end{code}\end{agda}
That way, we can get a hold of these proof requirements explicitly, instead of
implicitly guiding the Agda compiler through rewriting.

In retrospect, it might be worthwhile to take a step back and simplify indices across the whole development.
One such simplification would be to remove secrets as indices of expressions in contract pre-conditions,
but this would mean type-safety has to be sacrificed in the typing of |put| commands.
Another approach would be to follow the original BitML formulation and identify resources with string identifiers,
instead of the DeBruijn encoding we followed throughout our work (via the use of |Fin| numbers).
However, we do not recommend totally abandoning type-safety, but rather move to a string-based representation
where you extrinsically ensure that deposits in configurations are well-scoped.

\subsection{BitML Paper Fixes}
\label{subsec:fixes}
It is expected in any mechanization of a substantial amount of theoretical work to encounter
inconsistencies in the pen-and-paper version, ranging from simple typographical mistakes and omissions to
fundamental design problems.
This is certainly one of the primary selling points for formal verification;
corner cases that are difficult to find by testing or similar methods, can instead be discovered with rigorous formal methods.

Our formal development was no exception, since we encountered several issues with the original presentation, which
led to the modifications presented below.

\paragraph{Inference Rules}
Rule |DEP-Join| requires two symmetric invocations of the |DEP-AuthJoin| rule,
but it is unclear if this gives us anything meaningful.
Instead, we choose to simplify the rule by requiring just one authorization.

When rule |C-AuthRev| is presented in the original BitML paper,
it seems to act on an atomic configuration |⟨ A ∶ α ♯ ℕ ⟩|. This renders the rule useless in any practical scenario,
so we extend the rule to include a surrounding context:
\begin{agda}\begin{code}
⟨ A ∶ s ♯ just n ⟩ ∣ Γ —→⟦ auth-rev[ A , s ] ⟧ A ∶ s ♯ n ∣ Γ
\end{code}\end{agda}

\paragraph{Small-step Derivations as Equational Reasoning}
In Section~\ref{subsec:bitml-example}, we saw an example derivation of our small-step semantics, given in an equational-reasoning style.
This is possible, because the involved rules follow a certain format.

Alas, rule |C-Control| includes another transition in its premises which results in the same state |Γ′| as the transition in
the conclusion,
resulting in a tree-like proof structure.
which is arguably inconvenient for textual presentation.
This is problematic when we try to reason in an equational-reasoning style using our multi-step relation |_ —↠ _|,
since this branching will break our sequential way of presenting the proof step by step.

To avoid this issue, notice how we can ``linearize'' the proof structure by removing the premise and replacing the
target configuration of the conclusion with the source configuration of the removed premise.
Our version of |C-Control| in Section~\ref{subsec:bitml-semantics} reflects this important refactoring.

\paragraph{Conditions for Adversarial Strategies}
Moves chosen by an adversarial strategy come in two forms: labels and pairs |(A , j)| of an honest participant |A|
with an index into his/her current moves.
However, this is unnecessary, since we can both cases uniformly using our |Label| type.

\paragraph{Semantics-preserving Stripping}
The meta-theoretical lemma concerning stripping in the original paper (\textit{Lemma 3}) requires that the
transition considered is not an application of the |Auth-Rev| rule.
It turns out this is not a strong enough guarantee, since the |AuthCommit| rule also contains sensitive information,
thus would not be preserved after stripping.
We, therefore, fix the statement in Lemma 3 to additionally require that |α ≢ A ∶ ⟨ G ⟩ C , Δ|.
