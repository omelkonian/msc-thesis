\documentclass[acmsmall,nonacm=true,screen=true]{acmart}
\settopmatter{printfolios=true,printccs=false,printacmref=false}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Bibliography style
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\bibliographystyle{ACM-Reference-Format}
%\citestyle{acmauthoryear}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Packages
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% US letter size
%% \usepackage{geometry}
%% \setlength{\paperheight}{11in}
%% \setlength{\paperwidth}{8.5in}
%% \geometry{paperwidth=6.75in, paperheight=10in}

% URLs
\newcommand\site[1]{\footnote{\url{#1}}}

%include polycode.fmt
%include stylish.lhs
\def\commentbegin{}
\def\commentend{}

\begin{document}
\sloppy % for proper justification (no overflows to the right)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Title
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\title{Formalizing BitML Calculus in Agda}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Authors
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\author{Orestis Melkonian}
\orcid{0000-0003-2182-2698}
\affiliation{
  \department{Information and Computing Sciences}
  \institution{Utrecht University}
  \city{Utrecht}
  \country{The Netherlands}
}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Abstract
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{abstract}
\textbf{Email}: melkon.or@@gmail.com,
\textbf{Advisor}: Wouter Swierstra,
\textbf{ACM No}: 4094241
\textbf{Category}: Graduate (MSc)
\end{abstract}

\maketitle

\section{Introduction}
Blockchain technology has opened a whole array of interesting new applications,
such as secure multi-party computation\cite{mpc}, fair protocol design fair~\cite{fair} and
zero-knowledge proof systems~\cite{zeroproof}.
Nonetheless, bugs in \textit{smart contracts} -- programs that run on the blockchain --
have led to significant financial losses\site{https://en.wikipedia.org/wiki/The_DAO_(organization)},
thus it is crucial we can automatically detect them.
Moreover, we must detect them statically, since contracts become immutable once deployed.
This is exceptionally hard though, due to the concurrent execution inherent in smart contracts,
which is why most efforts so far have been on \textit{static analysis} techniques
for particular classes of bugs~\cite{mooly,madmax,liquidity}.

Recently there has been increased demand for more rigid formal methods in this domain~\cite{opportunities}
and we believe the field would greatly benefit from a language-based, type-driven approach~\cite{langverif}
alongside a mechanized meta-theory.
One such example is \textsc{Scilla}, an intermediate language for smart contracts,
with a formal semantics based on communicating automata~\cite{scilla}.
\textsc{Scilla} follows an \textit{extrinsic} approach to software verification;
contracts are written in a simply-typed DSL embedded in Coq~\cite{coq},
and dependent types are used to verify their safety and temporal properties.

In contrast, our work explores a new point in the design space,
exploiting the dependent type system of Agda~\cite{agda} to encode well-formed contracts,
whose behaviour is more predictable and easier to reason about.
To this end, we formalize an idealistic process calculus for Bitcoin smart contracts,
\textit{the Bitcoin Modelling Language} (BitML)~\cite{bitml}.
We give an intrinsically-typed model of BitML contracts and a small-step semantics of their execution,
as well as a game-theoretic symbolic model that enables reasoning over participant strategies.
We have not yet formalized the compiler from BitML contracts to Bitcoin transactions presented in the original paper,
but we hope our work paves the way to a fully \textit{certified} compiler.

\section{The BitML Calculus}
For the sake of brevity, we only give an overview of the major design decisions we made, mostly focusing on the
kind signatures of the basic types along with a representative subset of its constructors.
The complete formalization is publicly available on Github\site{https://github.com/omelkonian/formal-bitml}.

\paragraph{\textbf{Basic Types}}
First, we parametrize our module with the \textit{abstract data type} of participants,
equipped with decidable equality and a non-empty set of \textit{honest} participants |Hon|.
Monetary values are represented by natural numbers and a |Deposit| is a |Value| owned by a |Participant|.

\paragraph{\textbf{Contracts}}
The type of a contract is indexed by the total monetary value it carries and a set of deposits that guarantee
it will not get stuck: |data Contract : Value → List Value → Set|.
Its constructors comprise the available commands:
|UL ⊕ UR| declares possible branches with equal indices,
|split| divides the available funds to multiple contracts (whose values must sum to the initial value),
|UL ∶ UR| requires an authorization by a participant to proceed
and |after U : U| allows further execution of the contract only after some time has passed.
Lastly, |withdraw| transfers all remaining funds to a given participant and
|put| injects new deposits and secrets to the inner contract:
\begin{myagda}\begin{code}
put U reveal U ⇒ U : (vs : Values) → Secrets → Contract (v + Σ vs) vs′ → Contract v (vs′ ++ vs)
\end{code}\end{myagda}
A contract is initially made public through an |Advertisement|, denoted |⟨ G ⟩ C|, which includes a contract |C| along
with some preconditions |G| that have to be met before it is stipulated.

\paragraph{\textbf{Small-step Semantics}}
Our reduction semantics consists of transitions between \textit{configurations}, which are indexed by assets |(List A , List A)|,
whose first and second element represent produced and required quantities respectively\footnote{
We prepend an $\exists$ to the name of a type to denote that we existentially pack its indices.
}:
\begin{myagda}\begin{code}
data Configuration′ : Asset ^^ ∃Advertisement → Asset ^^ ∃Contract → Asset Deposit → Set
\end{code}\end{myagda}
A configuration can hold advertisements |` U|, deposits |⟨ U , U ⟩ SD|, contracts |⟨ U , U ⟩ SC|, secrets |U ∶ U ♯ U|
and action authorizations |UL [ U ]|.
All asset management occurs when composing configuration with the |UL BAR UR| operator;
assets required by the right operand can be provided by the left operand.
Note that advertisements and contracts are \textit{affine}, but deposits are handled \textit{linearly} (i.e. used only once).

We can now formally define the small-step semantics as a binary relation
on \textit{closed} configurations that do not require any assets, i.e. empty in the second position of the tuple.
Instead of presenting the entirety of the rules, we choose a representative subset instead:
\begin{myagda}\begin{code}
data UL —→ UR : Configuration ads cs ds → Configuration ads′ cs′ ds′ → Set where

  D-AuthJoin :                                                   D-Join :
        ⟨ A , v ⟩ SD | ⟨ A , v′ ⟩ SD | Γ                                 ⟨ A , v ⟩ SD | ⟨ A , v′ ⟩ SD | A [ 0 ↔ 1 ] | Γ
    —→  ⟨ A , v ⟩ SD | ⟨ A , v′ ⟩ SD | A [ 0 ↔ 1 ] | Γ SP SP SP  SP  —→  ⟨ A , v + v′ ⟩ SD | Γ

  C-Advertise   :  Any (UL ∈ Hon) (participants (G ad)) → (Γ —→ ad | Γ)

  C-AuthCommit  :  (secrets A (G ad) ≡ a₀ DOTS aₙ) × (A ∈ Hon → All (U ≢ ^^ nothing) a SUBI)
                →  ` ad | Γ —→ ` ad | Γ | DOTS ⟨ A : a SUBI ♯ N SUBI ⟩ DOTS ^^ BAR ^^ A [ ♯▷ ^^ ad ]
\end{code}\end{myagda}
Most rules come in pairs; one rule introduces an authorization of a participant to perform an action
and a subsequent rule performs the action. For instance, a participant can join two of her deposits by
first authorizing the join action (|D-AuthJoin|) and then actually merging the two deposits (|D-Join|).
Other rules are a bit more involved, requiring that certain premises are met before a transition can take place.
|C-Advertise| will advertise a contract with at least one honest participant to the current configuration
and |C-AuthCommit| authorizes a participant's commitment to all secrets mentioned in the advertisement's precondition,
making sure that honest participants only commit to valid secrets.

In all of the rules above, configuration elements of interest always appear on the left of a composition,
relying on the fact that |(Configuration, ULL BAR URR)| forms a \textit{commutative monoid}.
In a machine-checked setting this is not enough; we have to somehow reorder the input and output configurations.
We first define an \textit{equivalence} |UL ≈ UR|, relating configurations that are equal up to permutation.
We then factor out the equivalence relation in the reflexive transitive closure of the step relation,
which will eventually constitute our equational reasoning device:
\begin{myagda}\begin{code}
data UL —↠ UR : Configuration ads cs ds → Configuration ads′ cs′ ds′ → Set where

  U —→ ⟨ U ⟩ U  :  (L : Configuration ads cs ds) {_ : L ≈ L′ × M ≈ M′}
                →  (L′ —→ M′) → (M —↠ N) → (L —↠ N)

\end{code}\end{myagda}

\paragraph{\textbf{Example}}
Let us give a mechanized derivation for a contract implementing the \textit{timed-commitment protocol}~\cite{timed},
where a participant commits to revealing a valid secret |a| to another participant,
but loses her deposit of \bitcoin~1 if she does not meet a certain deadline |t|:
\begin{myagda}\begin{code}
tc-deriv : ⟨ A , 1 ⟩ SD —↠ ⟨ A , 1 ⟩ SD | A ∶ a ♯ 6
tc-deriv = let tc = ⟨ A ! 1 ∧ A ♯ a ⟩ ^^ reveal [ a ] ⇒ withdraw A ^^ ⊕ ^^ after t ∶ withdraw B in
  ⟨ A , 1 ⟩ SD                                                   SP  —→⟨ C-Advertise ⟩
  ` tc | ⟨ A , 1 ⟩ SD                                            SP  DOTS
  ⟨ withdraw A , 1 ⟩ SC | A ∶ a ♯ 6                              SP  —→⟨ C-Withdraw  ⟩
  ⟨ A , 1 ⟩ SD | A ∶ a ♯ 6 SP                                    SP  SP ∎
\end{code}\end{myagda}
First, |A| holds a deposit of \bitcoin~1, as required by the advertised contract's precondition (|C-Advertise|).
The contract is stipulated after the prerequisites are satisfied and the first branch is picked when |A| reveals her secret.
Finally, |A| retrieves the deposit back (|C-Withdraw|).

\paragraph{\textbf{Symbolic model}}
Moving on to the definition of BitML's symbolic model, we associate a label to each inference rule and
extend the step relation to emit labels, thus defining a \textit{labelled transition system}.
A multi-step derivation |UL —↠ UR| now accumulates a list of labels and essentially models possible
traces of the execution.
We can now define \textit{participant strategies} as functions that, given a current trace\footnote{
Before we give an execution trace as input to a strategy,
we traverse the derivation and strip out all secrets using |UL ∗|.
}, select
a number of possible next moves that are admissible by the semantics.
Since only a certain class of strategies is considered valid (e.g. the participant cannot authorize actions by others),
we model strategies as dependent record types:
\begin{myagda}\begin{code}
record HonestStrategy (A : Participant) where
  field  strategy  : Trace → Label
         valid     : (A ∈ Hon) × (∀ R α → α ∈ strategy (R ∗) → authorizers α ⊆ [ A ]) × DOTS

record AdversaryStrategy (Adv : Participant) where
  field  strategy  : Trace → (∀ A → A ∈ Hon → HonestStrategy A) → Label
         valid     : (Adv ∉ Hon) × DOTS
\end{code}\end{myagda}
The final choice out of all moves submitted by the honest participants is made by a single adversary,
whose strategy additionally takes the honest strategies as input and the chosen action is subject to
another set of conditions (e.g. the adversary cannot delay time for an arbitrary amount of time).
We can now formulate when a trace \textit{conforms} to a set of strategies,
namely when each step in the derivation is a (valid) adversarial choice over the available honest moves.
Lastly, we prove several meta-theoretical lemmas, e.g. that derivations in the small-step semantics
are preserved even if we strip out sensitive information: |∀ R′ → (R ARR R′) → (R ∗ ARR R′ ∗)|.

\paragraph{\textbf{Towards certified compilation}}
In contrast to the compiler proposed in the original BitML paper,
we aim to give a compiler to a more abstract accounting model for ledgers based on \textit{unspent output transactions} (UTxO)~\cite{utxo}
and mechanize a similar proof for \textit{compilation correctness}, stating that
attacks in the compiled contracts can always be observed in the symbolic model.
We already have an Agda formalization for such ledgers\site{https://github.com/omelkonian/formal-utxo},
which statically enforces the validity of their transactions (e.g. all referenced addresses exist).

Our formalization actually covers extensions to the basic UTxO model of Bitcoin, as employed by the Cardano blockchain~\cite{eutxo}.
Since these extensions allow for more expressive power in the scripts residing in transactions\footnote{
For instance, the addition of \textit{data scripts} in transaction outputs makes stateful behaviour possible.
}, we expect the translation to be more straightforward,
much like how the financial DSL \textit{Marlowe} is implemented on top of an extended-UTxO ledger~\cite{marlowe}.
Most importantly, compilation down to our dependently-typed ledgers will guarantee that we only ever get valid ledgers.

\newpage
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Bibliography
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\bibliography{sources}

\end{document}
