\documentclass[acmsmall,nonacm=true,screen=true]{acmart}
\settopmatter{printfolios=false,printccs=false,printacmref=false}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Bibliography style
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\bibliographystyle{ACM-Reference-Format}
\citestyle{acmauthoryear}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Packages
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% URLs
\newcommand\site[1]{\footnote{\url{#1}}}

% Quotes
\usepackage{csquotes}

% Graphics
\usepackage{graphicx}
\graphicspath{ {img/} }

% Tikz
\usepackage{tikz}
\usetikzlibrary{chains,arrows,automata,fit,positioning,calc}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Macros
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\newcommand\TODO[1]{\textcolor{red}{TODO: #1}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Agda imports
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%include polycode.fmt
%include stylish.lhs
\def\commentbegin{}
\def\commentend{}

%% TOC formatting
\setcounter{tocdepth}{2} % + subsections

% Line spacing
\renewcommand{\baselinestretch}{1.15}

\begin{document}
\sloppy % for proper justification (no overflows to the right)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Title
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\title{Formal investigation of the Extended UTxO model}
\subtitle{Laying the foundations for the formal verification of smart contracts}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Authors
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\author{Orestis Melkonian}
\orcid{0000-0003-2182-2698}
\affiliation{
  \position{MSc Student}
  \department{Information and Computing Sciences}
  \institution{Utrecht University}
  \city{Utrecht}
  \country{The Netherlands}
}
\email{melkon.or@@gmail.com}

% Title Page
\begin{center}\begin{minipage}{0.8\linewidth}
  \centering
\vspace{3cm}
% Title
{
\textsc{\Large{Formal Investigation of the Extended UTxO Model}} \\[.5cm]
\large{\textit{Laying the foundations for the formal verification of smart contracts}}
\par} \vspace{1cm}
% Author's name
{
\Large Orestis Melkonian
\par} \vspace{1cm}
% Line
{
\rule{\linewidth}{1pt}
\par} \vspace{1cm}
% Degree
{
\textit{A thesis submitted for the Master of Science degree} \\[.2cm]
\textit{Department of Information and Computing Sciences} \\[.2cm]
\textit{Utrecht University}
\par} \vspace{2cm}
% University logo
\includegraphics[width=0.4\linewidth]{logo.pdf} \\[.5cm]
\vspace{1cm}
%Date
{\Large July 2019}
\end{minipage}\end{center}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Abstract
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\newpage
\begin{abstract}
This report serves as the proposal of my MSc thesis, supervised by Wouter Swierstra from
Utrecht University and Manuel Chakravarty from IOHK.
\end{abstract}

%% \maketitle

\newpage
\tableofcontents

\newpage
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Introduction}
\label{sec:intro}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Distributed ledger technology creates issues
Blockchain technology has opened a whole array of interesting new applications
(e.g. secure multi-party computation\cite{mpc}, fair protocol design fair\cite{fair}, zero-knowledge proof systems\cite{zeroproof}).
Nonetheless, reasoning about the behaviour of such systems is an exceptionally hard task, mainly due to their distributed nature.
Moreover, the fiscal nature of the majority of these applications requires a much higher degree of rigorousness compared to
conventional IT applications, hence the need for a more formal account of their behaviour.

% Smart contracts create issues
The advent of smart contracts (programs that run on the blockchain itself) gave
rise to another source of vulnerabilities.
One primary example of such a vulnerability caused by the use of smart contracts is the
DAO attack\site{https://en.wikipedia.org/wiki/The_DAO_(organization)},
where a security flaw on the model of Ethereum's scripting language led to the exploitation of a venture capital fund
worth 150 million dollars at the time.
The solution was to create a hard fork of the Ethereum blockchain, clearly going against the decentralized spirit
of cryptocurrencies.
Since these (possibly Turing-complete) programs often deal with transactions of significant funds,
it is of utmost importance that one can reason and ideally provide formal proofs about their behaviour
in a concurrent/distributed setting.

% Aim of thesis
\paragraph{Research Question}
The aim of this thesis is to provide a mechanized formal model of an abstract distributed ledger equipped with
smart contracts, in which one can begin to formally investigate the expressiveness of the extended UTxO model.
Moreover, we hope to lay a foundation for a formal comparison with account-based
models used in Ethereum. Put concisely, the research question posed is:
\begin{displayquote}
	\textit{How much expressiveness do we gain by extending the UTxO model?} \\
	\textit{Is it as expressive as the account-based model used in Ethereum?}
\end{displayquote}

\paragraph{Overview}
\begin{itemize}
\item % Background
Section~\ref{sec:background} reviews some basic definitions related to blockchain
technology and introduces important literature, which will be the main subject of study
throughout the development of our reasoning framework.
Moreover, we give an overview of related work, putting an emphasis on existing tools based on static analysis.
\item % Methodology
Section~\ref{sec:methodology} describes the technology we will use to formally reason
about the problem at hand and some key design decisions we set upfront.
\item % UTxO
Section~\ref{sec:eutxo} describes the formalization of an abstract model for UTxO-based blockchain ledgers.
\item % BitML
Section~\ref{sec:bitml} concerns the formalization of our second object of study, the Bitcoin Modelling Language.
\item % Next steps
Section~\ref{sec:next} discusses next steps for the remainder of the thesis, as well as a rough estimate
on when these milestones will be completed.
\item % Conclusion
Section~\ref{sec:conclusion} concludes with a general overview of our contributions and reflects on the chosen methodology.

\end{itemize}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Background \& Related Work}
\label{sec:background}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% ?? Add cryptography section for:
%   1. hashes
%   2. private-pub key pairs for encryption/authentication

\subsection{Distributed Ledger Technology: Blockchain} \label{subsec:dlt}
Cryptocurrencies rely on distributed ledgers, where there is no central authority managing the accounts
and keeping track of the history of transactions.

One particular instance of distributed ledgers are blockchain systems, where transactions are
bundled together in blocks, which are linearly connected with hashes and distributed to all peers.
The blockchain system, along with a consensus protocol deciding on which competing fork of the chain is to be included,
maintains an immutable distributed ledger (i.e. the history of transactions).

Validity of the transactions is tightly coupled with a consensus protocol, which makes sure
peers in the network only validate well-behaved and truthful transactions and are, moreover,
properly incentivized to do so.

The absence of a single central authority that has control over all assets of the participants allows
for shared control of the evolution of data (in this case transactions)
and generally leads to more robust and fair management of assets.

While cryptocurrencies are the major application of blockchain systems, one could easily
use them for any kind of valuable asset, or even as general distributed databases.

\subsection{Smart Contracts} \label{subsec:smartcontracts}
Most blockchain systems come equipped with a scripting language, where one can write
\textit{smart contracts} that dictate how a transaction operates. A smart contract
could, for instance, pose restrictions on who can redeem the output funds of a transaction.

One could view smart contracts as a replacement of legal frameworks, providing the means
to conduct contractual relationships completely algorithmically.

While previous work on writing financial contracts~\cite{spj} suggests it
is fairly straightforward to write such programs embedded in a general-purpose
language (in this case Haskell) and to reason about them with \textit{equational reasoning},
it is restricted in the centralized setting and, therefore, does not suffice for our needs.

Things become much more complicated when we move to the distributed setting of a blockchain~\cite{setzer,short,scilla}.
Hence, there is a growing need for methods and tools that will
enable tractable and precise reasoning about such systems.

Numerous scripting languages have appeared recently~\cite{scriptlangs}, spanning a wide
spectrum of expressiveness and complexity. While language design can impose restrictions
on what a language can express, most of these restrictions are inherited from
the accounting model to which the underlying system adheres.

In the next section, we will discuss the two main forms of accounting models:
\begin{enumerate}
\item \textbf{UTxO-based}: stateless models based on \textit{unspent transaction outputs}
\item \textbf{Account-based}: stateful models that explicitly model interaction between \textit{user accounts}
\end{enumerate}

\subsection{UTxO-based: Bitcoin} \label{subsec:bitcoin}
The primary example of a UTxO-based blockchain is Bitcoin~\cite{bitcoin}.
Its blockchain is a linear sequence of \textit{blocks} of transactions,
starting from the initial \textit{genesis} block.
Essentially, the blockchain acts as a public log of all transactions that have taken place, where
each transaction refers to outputs of previous transactions,
except for the initial \textit{coinbase} transaction of each block.
Coinbase transactions have no inputs, create new currency and reward the miner of that block with a fixed amount.
Bitcoin also provides a cryptographic protocol to make sure no adversary can tamper with the transactional history,
e.g. by making the creation of new blocks computationally hard and invalidating the ``truthful" chain statistically impossible.

A crucial aspect of Bitcoin's design is that there are no explicit addresses included in the transactions.
Rather, transaction outputs are actually program scripts, which allow someone to claim the funds by giving the proper inputs.
Thus, although there are no explicit user accounts in transactions, the effective available funds of a user
are all the \textit{unspent transaction outputs} (UTxO) that he can claim (e.g. by providing a digital signature).

\subsubsection{\textsc{Script}}
In order to write such scripts in the outputs of a transaction, Bitcoin provides a low-level, Forth-like,
stack-based scripting language, called \textsc{Script}.
\textsc{Script} is intentionally not Turing-complete (e.g. it does not provide looping structures),
in order to have more predictable behaviour.
Moreover, only a very restricted set of ``template" programs are considered standard, i.e.
allowed to be relayed from node to node.

\newcommand\ttt{\texttt}
\newcommand\stack[1]{\text{\ttt{#1}}}
\newcommand\Semantics[1]{\llbracket \stack{#1} \rrbracket}

\paragraph{\textsc{Script} Notation}
Programs in script are a linear sequence of either data values (e.g. numbers, hashes) or
built-in operations (distinguished by their $\stack{OP\_\ }$ prefix).

The stack is initially considered empty and we start reading inputs from left to right.
When we encounter a data item, we simply push it to the top of the stack.
On encountering an operation, we pop the necessary number of arguments from the stack, apply
the operation and push the result back.
The evaluation function $\llbracket \_ \rrbracket$ executes the given program and returns the final
result at the top of the stack. For instance, adding two numbers looks like this:
\[
  \Semantics{1 2 OP\_ADD} = \stack{3}
\]
\paragraph{P2PKH}
The most frequent example of a 'standard' program in \textsc{Script} is the
\textit{pay-to-pubkey-hash} (P2PKH) type of scripts. Given a hash of a public key \texttt{<pub\#>},
a P2PKH output carries the following script:
\[
  \stack{OP\_DUP OP\_HASH <pub\#> OP\_EQ OP\_CHECKSIG}
\]
where \ttt{OP\_DUP} duplicates the top element of the stack, \ttt{OP\_HASH} replaces the top element with its hash,
\ttt{OP\_EQ} checks that the top two elements are equal, \ttt{OP\_CHECKSIG} verifies that the top two elements
are a valid pair of a digital signature of the transaction data and a public key hash.

The full script will be run when the output is claimed (i.e. used as input in a future transaction)
and consists of the P2PKH script, preceded by the digital signature of the transaction by its owner and a hash of
his public key. Given a digital signature \ttt{<sig>} and a public key hash \ttt{<pub>}, a transaction is valid
when the execution of the script below evaluates to \ttt{True}.
\[
  \stack{<sig> <pub> OP\_DUP OP\_HASH <pub\#> OP\_EQ OP\_CHECKSIG}
\]

To clarify, assume a scenario where Alice want to pay Bob \bitcoin ~10.
Bob provides Alice with the cryptographic hash of his public key (\ttt{<pub\#>})
and Alice can submit a transaction of \bitcoin ~10 with the following output script:
\[
  \stack{OP\_DUP OP\_HASH <pub\#> OP\_EQ OP\_CHECKSIG}
\]
After that, Bob can submit another transaction that uses this output by providing the digital signature
of the transaction \ttt{<sig>} (signed with his private key) and his public key \ttt{<pub>}.
It is easy to see that the resulting script evaluates to \ttt{True}.

\paragraph{P2SH}
A more complicated script type is \textit{pay-to-script-hash} (P2SH), where output scripts simply authenticate
against a hash of a \textit{redeemer} script \ttt{<red\#>}:
\[
  \stack{OP\_HASH <red\#> OP\_EQ}
\]

A redeemer script \ttt{<red>} resides in an input which uses the corresponding output. The following two conditions
must hold for the transaction to go through:
\begin{enumerate}
\item $\Semantics{<red>} = \stack{True}$
\item $\Semantics{<red> OP\_HASH <red\#> OP\_EQ} = \stack{True}$
\end{enumerate}
Therefore, in this case the script residing in the output is simpler, but inputs can also contain arbitrary redeemer scripts
(as long as they are of a standard ``template").

In this thesis, we will model scripts in a much more general, mathematical sense, so
we will eschew from any further investigation of properties particular to \textsc{Script}.

\subsubsection{The BitML Calculus}
Although Bitcoin is the most widely used blockchain to date, many aspects of it are poorly documented.
In general, there is a scarcity of formal models, most of which are either introductory or exploratory.

One of the most involved and mature previous work on formalizing the operation of Bitcoin
is the Bitcoin Modelling Language (BitML)~\cite{bitml}. First, an idealistic \textit{process calculus}
that models Bitcoin contracts is introduced, along with a detailed small-step reduction semantics that
models how contracts interact and its non-determinism accounts for the various outcomes.

The semantics consist of transitions between \textit{configurations}, abstracting away all the
cryptographic machinery and implementation details of Bitcoin.
Consequently, such operational semantics allow one to reason about the concurrent behaviour of
the contracts in a \textit{symbolic} setting.

The authors then provide a compiler from BitML contracts to 'standard' Bitcoin transactions, proven
correct via a correspondence between the symbolic model and the computational model operating on
the Bitcoin blockchain. We will return for a more formal treatment of BitML in Section~\ref{subsec:bitml}.

\subsubsection{Extended UTxO}
In this work, we will consider the version of the UTxO model used by IOHK's Cardano blockchain\site{www.cardano.org}.
In contrast to Bitcoin's \textit{proof-of-work} consensus protocol~\cite{bitcoin},
Cardano's \textit{Ouroboros} protocol~\cite{ouroboros} is \textit{proof-of-stake}.
This, however, does not concern our study of the abstract accounting model, thus we
refrain from formally modelling and comparing different consensus techniques.

The actual extension we care about is the inclusion of \textit{data scripts} in transaction
outputs, which essentially provide the validation script in the corresponding input with additional
information of an arbitrary type.

This extension of the UTxO model has already been
implemented\site{https://github.com/input-output-hk/plutus/tree/master/wallet-api/src/Ledger}, but
only informally documented\site{https://github.com/input-output-hk/plutus/blob/master/docs/extended-utxo/README.md}.
The reason to extend the UTxO model with data scripts is to bring more expressive power to UTxO-based blockchains,
hopefully bringing it on par with Ethereum's account-based scripting model (see Section~\ref{subsec:ethereum}).

However, there is no formal argument to support this claim, and it is the goal of this thesis
to provide the first formal investigation of the expressiveness introduced by this extension.

\subsection{Account-based: Ethereum} \label{subsec:ethereum}
On the other side of the spectrum, lies the second biggest cryptocurrency today, Ethereum~\cite{ethereum}.
In contrast to UTxO-based systems, Ethereum has a built-in notion of user addresses and operates on a
stateful accounting model. It goes even further to distinguish \textit{human accounts}
(controlled by a public-private key pair) from \textit{contract accounts} (controlled by some EVM code).

This added expressiveness is also reflected in the quasi-Turing-complete low-level stack-based bytecode language
in which contract code is written, namely the \textit{Ethereum Virtual Machine} (EVM).
EVM is mostly designed as a target, to which other high-level user-friendly languages will compile to.

\paragraph{Solidity}
The most widely adopted language that targets the EVM is \textit{Solidity},
whose high-level object-oriented design makes writing common contract use-cases (e.g. crowdfunding campaigns, auctions)
rather straightforward.

One of Solidity's most distinguishing features is the concept of a contract's \textit{gas}; a limit to the amount
of computational steps a contract can perform.
At the time of the creation of a transaction, its owner specifies a certain amount of gas the contract can consume and
pays a transaction fee proportional to it. In case of complete depletion (i.e. all gas has been consumed before the contract
finishes its execution), all global state changes are reverted as if the contract had never been run.
This is a necessary ingredient for smart contract languages that provide
arbitrary looping behaviour, since non-termination of the validation phase is certainly undesirable.

If time permits, we will initially provide a formal justification of Solidity and proceed to
formally compare the extended UTxO model against it.
Since Solidity is a fully-fledged programming language with lots of features
(e.g. static typing, inheritance, libraries, user-defined types), it makes sense to
restrict our formal study to a compact subset of Solidity that is easy to reason about.
This is the approach also taken in Featherweight Java~\cite{featherweightjava}; a subset
of Java that omits complex features such as reflection, in favour of easier behavioural reasoning
and a more formal investigation of its semantics.
In the same vein, we will try to introduce a lightweight version of Solidity, which we will refer to as
\textit{Featherweight Solidity}.

\subsection{Static Analysis Tools}
\TODO{BitML Liquidity}
...
\TODO{Madmax}
...
\TODO{Mooly}
...

\subsection{Scilla}
\TODO{extrinsic}
...

\subsection{Setzer's Agda model}
\TODO{similar, but}
...

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Methodology}
\label{sec:methodology}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\subsection{Scope}
At this point, we have to stress the fact that we are not aiming for a formalization of a fully-fledged
blockchain system with all its bells and whistles, but rather focus on the underlying accounting model.
Therefore, we will omit details concerning cryptographic operations and aspects of the actual implementation
of such a system. Instead, we will work on an abstract layer that postulates the well-behavedness of these
subcomponents, which will hopefully lend itself to more tractable reasoning and
give us a clear overview of the essence of the problem.

Restricting the scope of our attempt is also motivated from the fact that individual
components such as cryptographic protocols are orthogonal to the functionality we study here.
This lack of tight cohesion between the components of the system allows one to
safely factor each one out and formalize it independently.

It is important to note that this is not always the case for every domain. A prominent example of
this are operating systems, which consist of intricately linked subcomponents (e.g. drivers, memory modules),
thus making it impossible to trivially divide the overall proof into small independent ones.
In order to overcome this complexity burden, one has to invent novel ways of modular proof mechanization, as
exemplified by \textit{CertiKOS}~\cite{certikos}, a formally verified concurrent OS.

\subsection{Proof Mechanization}
Fortunately, the sub-components of the system we are examining are not no interdependent,
thus lending themselves to separate treatment.
Nonetheless, the complexity of the sub-system we care about is still high and requires rigorous investigation.
Therefore, we choose to conduct our formal study in a mechanized manner, i.e. using a proof assistant
along the way and formalizing all results in Type Theory.
Proof mechanization will allow us to discover edge cases and increase the confidence of the model under investigation.

\subsection{Agda}
As our proof development vehicle, we choose Agda~\cite{agda}, a dependently-typed total functional language
similar to Haskell~\cite{haskell}.

Agda embraces the \textit{Curry-Howard correspondence}, which states that types are isomorphic to statements in
(intuitionistic) logic and their programs correspond to the proofs of these statements~\cite{itt}.
Through its unicode-based \textit{mixfix} notational system, one can easily translate a mathematical theorem
into a valid Agda type.
Moreover, programs and proofs share the same structure, e.g. induction
in the proof manifests itself as recursion in the program.

While Agda is not ideal for large software development, its flexible notation
and elegant design is suitable for rapid prototyping of new ideas and exploratory purposes.
We do not expect to hit such problems,
since we will stay on a fairly abstract level which postulates cryptographic operations and other implementation details.

\paragraph{Limitation}
The main limitation of Agda lies in its lack of a proper proof automation system.
While there has been work on providing Agda with such capabilities~\cite{agdaauto},
it requires moving to a meta-programming mindset which would be an additional programming hindrance.

A reasonable alternative would be to use Coq~\cite{coq}, which provides a pragmatic
scripting language for programming \textit{tactics}, i.e. programs that work on proof contexts and can
generate new sub-goals.
This approach to proof mechanization has, however, been criticized for widening the gap between informal proofs
and programs written in a proof assistant.
This clearly goes against the aforementioned principle of \textit{proofs-as-programs}.

\subsection{The IOHK approach}
At this point, we would like to mention the specific approach taken by IOHK\site{https://iohk.io/}.
In contrast to numerous other companies currently creating cryptocurrencies, its main focus
is on provably correct protocols with a strong focus on peer-reviewing and robust implementations, rather
than fast delivery of results.
This is evidenced by the choice of programming languages (Agda/Coq/Haskell/Scala)
-- all functional programming languages with rich type systems --
and the use of \textit{property-based testing}~\cite{quickcheck} for the production code.

IOHK's distinct feature is that it advocates a more rigorous development pipeline;
ideas are initially worked on paper by pure academics,
which create fertile ground for starting formal verification in Agda/Coq for more confident results,
which result in a prototype/reference implementation in Haskell,
which informs the production code-base (also written in Haskell) on the properties that should be tested.

Since this thesis is done in close collaboration with IOHK, it is situated on the second step of aforementioned pipeline;
while there has been work on writing papers about the extended UTxO model along with the actual implementation in Haskell,
there is still no complete and mechanized account of its properties.

\subsection{Functional Programming Principles}
One last important manifestation of the functional programming principles behind IOHK is the choice
of a UTxO-based cryptocurrency itself.

On the one hand, one can view a UTxO ledger as a dataflow diagram, whose nodes are the submitted transactions
and edges represent links between transaction inputs and outputs.
On the other hand, account-based ledgers rely on a global state and transaction have a much more complicated
specification.

The key point here is that UTxO-based transaction are just pure mathematical functions, which are much more
straightforward to model and reason about.
Coming back to the principles of functional programming, one could contrast this with the difference between
functional and imperative programs.
One can use \textit{equational reasoning} for functional programs, due to their \textit{referential transparency},
while this is not possible for imperative programs that contain side-effectful commands.
Therefore, we hope that these principles will be reflected in the proof process itself;
one would reason about purely functional UTxO-based ledgers in a compositional manner.


This section gives an overview of the progress made so far in the on-going Agda formalization of the two main subjects of study,
namely the Extended UTxO model and the BitML calculus.
For the sake of brevity, we refrain from showing the full Agda code along with the complete proofs, but rather
provide the most important datatypes and formalized results and explain crucial design choices we made along the way.
Furthermore, we will omit notational burden imposed by technicalities particular to Agda, such as \textit{universe polymorphism}
and \textit{proof irrelevance}.

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

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Formal Model II: BitML Calculus}
\label{sec:bitml}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

Now let us shift our focus to our second subject of study, the BitML calculus for modelling smart contracts.
In this subsection we sketch the formalized part of BitML we have covered so far, namely the syntax and small-step
semantics of BitML contracts, as well as an example execution of a contract under these semantics.
All code is publicly available on Github\site{https://github.com/omelkonian/formal-bitml}.

First, we begin with some basic definitions that will be used throughout this section:
\begin{agda}\begin{code}
module Types (Participant : Set) (Honest : List SUPPLUS Participant) where
##
Time : Set
Time = ℕ
##
Value : Set
Value = ℕ
##
record Deposit : Set where
  constructor UL has UR
  field  participant : Participant
         value       : Value
##
Secret : Set
Secret = String
##
data Arith : List Secret → Set where DOTS
ℕ⟦ U ⟧ : ∀ {s} → Arith s → ℕ
ℕ⟦ U ⟧ = DOTS
##
data Predicate : List Secret → Set where DOTS
𝔹⟦ U ⟧ : ∀ {s} → Predicate s → Bool
𝔹⟦ U ⟧ = DOTS
\end{code}\end{agda}
Instead of giving a fixed datatype of participants, we parametrise our module with a given \textit{universe} of participants
and a non-empty list of honest participants.
Representation of time and monetary values is again done using natural numbers,
while we model participant secrets as simple strings\footnote{
Of course, one could provide more realistic types (e.g. words of specific length)
to be closer to the implementation, as shown for the UTxO model in Section~\ref{subsec:eutxo}.
}.
A deposits consists of the participant that owns it and the number of bitcoins it carries.
We, furthermore, introduce a simplistic language of logical predicates and arithmetic expressions with the usual constructs (e.g. numerical addition, logical conjunction) and give the usual semantics (predicates on booleans and arithmetic on naturals).
A more unusual feature of these expressions is the ability to calculate length of secrets (within arithmetic expressions)
and, in order to ensure more type safety later on, all expressions are indexed by the secrets they internally use.

\subsection{Contracts in BitML}
A \textit{contract advertisement} consists of a set of \textit{preconditions},
which require some resources from the involved participants prior to the contract's execution,
and a \textit{contract}, which specifies the rules according to which bitcoins are transferred between participants.

Preconditions either require participants to have a deposit of a certain value on their name (volatile or not) or
commit to a certain secret. Notice the index of the datatype below, which captures the values of all required deposits:
\begin{agda}\begin{code}
data Precondition : List Value → Set where
  -- volatile deposit
  U ? U : Participant → (v : Value) → Precondition [ v ]
  -- persistent deposit
  U ! U : Participant → (v : Value) → Precondition [ v ]
  -- committed secret
  UL ♯ UR : Participant → Secret → Precondition []
  -- conjunction
  U ∧ U : Precondition vs SUBL → Precondition vs SUBR → Precondition (vs SUBL ++ vs SUBR)
\end{code}\end{agda}

Moving on to actual contracts, we define them by means of a collection of five types of commands;
|put| injects participant deposits and revealed secrets in the remaining contract,
|withdraw| transfers the current funds to a participant,
|split| distributes the current funds across different individual contracts,
|U : U| requires the authorization from a participant to proceed
and |after U : U| allows further execution of the contract only after some time has passed.
\begin{agda}\begin{code}
data Contract  :  Value   -- the monetary value it carries
               →  Values  -- the deposits it presumes
               →  Set where
  -- collect deposits and secrets
  put U reveal U if U ⇒ U ∶- U :
    (vs : List Value) → (s : Secrets) → Predicate s′  → Contract (v + sum vs) vs′ →  s′ ⊆ s
    → Contract v (vs′ ++ vs)
  -- transfer the remaining balance to a participant
  withdraw : ∀ {v} → Participant → Contract v []
  -- split the balance across different branches
  split :  (cs : List (∃[ v ] ^^ ∃[ vs ] ^^ Contract v vs))
        →  Contract (sum (proj₁ <$$> cs)) (concat (proj₂ <$$> cs))
  -- wait for participant's authorization
  U : U : Participant → Contract v vs → Contract v vs
  -- wait until some time passes
  after U : U : Time → Contract v vs → Contract v vs
\end{code}\end{agda}
There is a lot of type-level manipulation across all constructors, since we need to make sure that indices are
calculated properly. For instance, the total value in a contract constructed by the |split| command is the
sum of the values carried by each branch.
The |put| command\footnote{
|put| comprises of several components and we will omit those that do not contain any helpful information,
e.g. write |put U ⇒ U| when there are no revealed secrets and the predicate trivially holds.
} additionally requires an explicit proof that the predicate
of the |if| part only uses secrets revealed by the same command.

We also introduce an intuitive syntax for declaring the different branches of a |split| command, emphasizing the
\textit{linear} nature of the contract's total monetary value:
\begin{agda}\begin{code}
UL ⊸ UR : ∀ {vs : Values} → (v : Value) → Contract v vs → ∃[ v ] ^^ ∃[ vs ] ^^ Contract v vs
UL ⊸ UR {vs} v c = v , vs , c
\end{code}\end{agda}

Having defined both preconditions and contracts, we arrive at the definition of a contract advertisement:
\begin{agda}\begin{code}
record Advertisement (v : Value) (vs SUPC vs SUPG : List Value) : Set where
  constructor U ⟨ U ⟩∶- U
  field  G      :  Precondition vs
         C      :  Contracts v vs
         valid  :  length vs SUPC ≤ length vs SUPG
                ×  participants SUPG G ++ participants SUPC C ⊆ (participant <$$> persistentDeposits SUPP G)
\end{code}\end{agda}
Notice that in order to construct an advertisement, one has to also provide proof of the contract's validity with respect to
the given preconditions, namely that all deposit references in the contract are declared in the precondition
and each involved participant is required to have a persistent deposit.

To clarify things so far, let us see a simple example of a contract advertisement:
\begin{agda}\begin{code}
open BitML (A | B) [ A ] SUPPLUS

ex-ad : Advertisement 5 [ 200 ] (200 ∷ 100 ∷ [])
ex-ad =  ⟨  B ! 200 ∧ A ! 100 ^^ ⟩
          split  (  2 ⊸ withdraw B
                 ⊕  2 ⊸ after 100 ∶ withdraw A
                 ⊕  1 ⊸ put [ 200 ] ⇒ B ∶ withdraw {201} A ∶- DOTS
                 )
          ∶- DOTS
\end{code}\end{agda}
We first need to open our module with a fixed set of participants (in this case |A| and |B|).
We then define an advertisement, whose type already says a lot about what is going on;
it carries \bitcoin ~5, presumes the existence of at least one deposit of \bitcoin ~200, and requires two deposits
of \bitcoin ~200 and \bitcoin ~100.

Looking at the precondition itself, we see that the required deposits will be provided by |B| and |A|, respectively.
The contract first splits the bitcoins across three branches:
the first one gives \bitcoin ~2 to |B|, the second one gives \bitcoin ~2 to |A| after some time period,
while the third one retrieves |B|'s deposit of \bitcoin ~200 and allows |B| to authorise the
withdrawal of the remaining funds (currently \bitcoin ~201) from |A|.

We have omitted the proofs that ascertain the well-formedness of the |put| command and the advertisement, as
they are straightforward and do not provide any more intuition\footnote{
In fact, we have defined decidable procedures for all such proofs using the
\textit{proof-by-reflection} pattern~\cite{proofbyreflection}.
These automatically discharge all proof obligations, when there are no variables involved.}.

\subsection{Small-step Semantics}
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
\begin{agda}\begin{code}
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
  HTRI UR  :  (ad : Advertisement v vs SUPC vs SUPG)
               →  Action p [ v , vs SUPC , vs SUPG , ad ] [] [] []

  -- spend x to stipulate an advertisement
  U STRI UR  :  (ad : Advertisement v vs SUPC vs SUPG)
                     →  (i : Index vs SUPG)
                     →  Action p [ v , vs SUPC , vs SUPG , ad ] [] [ vs SUPG ‼ i ] []

  -- pick a branch
  U BTRI UR  :  (c : List (Contract v vs))
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
declares new deposits that will be created by the action
(e.g. dividing a deposit would require a single deposit as the third index and produce two other deposits in its fourth index).

Although our indexing scheme might seem a bit heavyweight now, it makes many little details and assumptions explicit,
which would bite us later on when we will need to reason about them.

Continuing from our previous example advertisement, let's see an example action where |A| spends the required \bitcoin ~100
to stipulate the example contract\footnote{
Notice that we have to make all indices of the advertisement explicit in the second index in the action's type signature.
}:
\begin{agda}\begin{code}
ex-spend : Action A [ 5 , [ 200 ] , 200 ∷ 100 ∷ [] , ex-ad ] [] [ 100 ] []
ex-spend = ex-ad STRI 1
\end{code}\end{agda}

Configurations are now built from advertisements, active contracts, deposits, action authorizations and committed/revealed secrets:
\begin{agda}\begin{code}
data Configuration′  :  -- $\hspace{22pt}$ current $\hspace{20pt}$ $\times$ $\hspace{15pt}$ required
                        AdvertisedContracts  × AdvertisedContracts
                     →  ActiveContracts      × ActiveContracts
                     →  List Deposit         × List Deposit
                     →  Set where

  -- empty
  ∅ : Configuration′ ([] , []) ([] , []) ([] , [])

  -- contract advertisement
  ` U  :  (ad : Advertisement v vs SUPC vs SUPG)
           →  Configuration′ ([ v , vs SUPC , vs SUPG , ad ] , []) ([] , []) ([] , [])

  -- active contract
  ⟨ U , U ⟩ SUPCC  :  (c : List (Contract v vs)) → Value
                           →  Configuration′ ([] , []) ([ v , vs , c ] , []) ([] , [])

  -- deposit redeemable by a participant
  ⟨ UR , U ⟩ SUPD  :  (p : Participant) → (v : Value)
                           →  Configuration′ ([] , []) ([] , []) ([ p has v ] , [])

  -- authorization to perform an action
  UL [ U ]  : (p : Participant) → Action p ads cs vs ds
                    → Configuration′ ([] , ads) ([] , cs) (ds , ((p has U) <$$> vs))

  -- committed secret
  ⟨ U ∶ U ♯ U ⟩  :  Participant →  Secret →  ℕ ⊎ ⊥
                             →  Configuration′ ([] , []) ([] , []) ([] , [])
  -- revealed secret
  U ∶ U ♯ U  :  Participant →  Secret → ℕ
                         →  Configuration′ ([] , []) ([] , []) ([] , [])

  -- parallel composition
  U | U  :  Configuration′ (ads SUPL , rads SUPL) (cs SUPL , rcs SUPL) (ds SUPL , rds SUPL)
                 →  Configuration′ (ads SUPR , rads SUPR) (cs SUPR , rcs SUPR) (ds SUPR , rds SUPR)
                 →  Configuration′  (ads SUPL                    ++ ads SUPR  , rads SUPL  ++ (rads SUPR  ∖ ads SUPL))
                                    (cs SUPL                     ++ cs SUPR   , rcs SUPL   ++ (rcs SUPR   ∖ cs SUPL))
                                    ((ds SUPL ∖ rds SUPR)        ++ ds SUPR   , rds SUPL   ++ (rds SUPR   ∖ ds SUPL))
\end{code}\end{agda}
The indices are quite involved, since we need to record both the current advertisements, stipulated contracts and deposits
and the required ones for the configuration to become valid. The most interesting case is the parallel composition
operator, where the resources provided by the left operand might satisfy some requirements of the right operand. Moreover,
consumed deposits have to be eliminated as there can be no double spending, while the number of advertisements and contracts
always grows.

By composing configurations together, we will eventually end up in a \textit{closed} configuration, where
all required indices are empty (i.e. the configuration is self-contained):
\begin{agda}\begin{code}
Configuration : AdvertisedContracts → ActiveContracts → List Deposit → Set
Configuration ads cs ds = Configuration′ (ads , []) (cs , []) (ds , [])
\end{code}\end{agda}

We are now ready to declare the inference rules of the bottom layer of our small-step semantics,
by defining an inductive datatype modelling the binary step relation between untimed configurations:
\begin{agda}\begin{code}
data U —→ U : Configuration ads cs ds → Configuration ads′ cs′ ds′ → Set where
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
\end{code}\end{agda}
There is a total of 18 rules we need to define, but we choose to depict only a representative subset of them.
The first pair of rules initially appends the authorisation to merge
two deposits to the current configuration (rule |[DEP-AuthJoin]|) and then performs the actual join (rule |[DEP-Join]|).
This is a common pattern across all rules, where we first collect authorisations for an action by all involved participants,
and then we fire a subsequent rule to perform this action.
|[C-Advertise]| advertises a new contract, mandating that at least one of the participants involved in the pre-condition
is honest and requiring that all deposits needed for stipulation are available in the surrounding context.
|[C-AuthCommit]| allows participants to commit to the secrets required by the contract's pre-condition, but only dishonest
ones can commit to the invalid length $\bot$.
Lastly, |[C-Control]| allows participants to give their authorization required by a particular branch out of the current
choices present in the contract, discarding any time constraints along the way.

It is noteworthy to mention that during the transcriptions of the complete set of rules from the paper~\cite{bitml}
to our dependently-typed setting,
we discovered a discrepancy in the |[C-AuthRev]| rule, namely that there was no context $\Gamma$.
Moreover, in order to later facilitate equational reasoning, we re-factored the |[C-Control]|
to not contain the inner step as a hypothesis, but instead immediately inject it in the result operand of the step relation.

The inference rules above have elided any treatment of timely constraints;
this is handled by the top layer, whose states are now timed configurations.
The only interesting inference rule is the one that handles time decorations of the form |after U : U|,
since all other cases are dispatched to the bottom layer (which just ignores timely aspects).
\begin{agda}\begin{code}
record Configuration SUPT (ads : AdvertisedContracts) (cs  : ActiveContracts) (ds  : Deposits) : Set where
  constructor U at U
  field  cfg   : Configuration ads cs ds
         time  : Time
##
data U —→ SUBT U : Configuration SUPT ads cs ds → Configuration SUPT ads′ cs′ ds′ → Set where

  Action : ∀ {Γ Γ′ t}
    →  Γ —→ Γ′
       {- $\inferSmall$ -}
    →  Γ at t —→ SUBT Γ′ at t

  Delay : ∀ {Γ t δ}
       {- $\inferMedium$ -}
    →  Γ at t —→ SUBT Γ at (t + δ)

  Timeout : ∀ {Γ Γ′ t i contract}
    →  All (U ≤ t) (timeDecorations (contract ‼ i))  -- all time constraints are satisfied
    →  ⟨ [ contract ‼ i ] , v ⟩ SUPCC | Γ —→ Γ′          -- resulting state if we pick this branch
       {- $\inferMedium$ -}
    →  (⟨ contract , v ⟩ SUPCC | Γ) at t —→ SUBT Γ′ at t
\end{code}\end{agda}

Having defined the step relation in this way allows for equational reasoning, a powerful tool for
writing complex proofs:
\begin{agda}\begin{code}
data U —↠ U : Configuration ads cs ds → Configuration ads′ cs′ ds′ → Set where

  U ∎ : (M : Configuration ads cs ds) → M —↠ M

  U —→ ⟨ U ⟩ U : ∀ {M  N} (L : Configuration ads cs ds)
    →  L —→ M → M —↠ N
       {- $\inferMedium$ -}
    →  L —↠ N

begin U : ∀ {M N} → M —↠ N → M —↠ N
\end{code}\end{agda}

\subsection{Example}
We are finally ready to see a more intuitive example of the \textit{timed-commitment protocol}, where a participant
commits to revealing a valid secret $a$ (e.g. "qwerty") to another participant,
but loses her deposit of \bitcoin ~1 if she does not meet a certain deadline $t$:
\begin{agda}\begin{code}
tc : Advertisement 1 [] (1 ∷ 0 ∷ [])
tc =  ⟨ A ! 1 ∧ A ♯ a ∧ B ! 0 ⟩ ^^ reveal [ a ] ⇒ withdraw A ∶- DOTS ^^ ⊕ ^^ after t ∶ withdraw B
\end{code}\end{agda}

Below is one possible reduction in the bottom layer of our small-step semantics, demonstrating the case where
the participant actually meets the deadline:
\begin{agda}\begin{code}
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
\end{code}\end{agda}
At first, |A| holds a deposit of \bitcoin ~1, as required by the contract's precondition.
Then, the contract is advertised and the participants slowly provide the corresponding prerequisites
(i.e. |A| commits to a secret via |[C-AuthCommit]| and spends the required deposit via |[C-AuthInit]|,
while |B| does not do anything).
After all pre-conditions have been satisfied, the contract is stipulated (rule |[C-Init]|) and the secret is successfully
revealed (rule |[C-AuthRev]|).
Finally, the first branch is picked (rule |[C-Control]|) and |A| retrieves her deposit back
(rules |[C-PutRev]| and |[C-Withdraw]|).

\subsection{Reasoning Modulo Permutation}
In the definitions above, we have assumed that |(UL BAR UR , ∅)| forms a commutative monoid, which allowed us
to always present the required sub-configuration individually on the far left of a composite configuration.
While such definitions enjoy a striking similarity to the ones appearing in the original paper~\cite{bitml}
(and should always be preferred in an informal textual setting),
this approach does not suffice for a mechanized account of the model.
After all, this explicit treatment of all intuitive assumptions/details is what makes our approach robust and will lead to
a deeper understanding of how these systems behave.
To overcome this intricacy, we introduce an \textit{equivalence relation} on configurations, which holds when
they are just permutations of one another:
\begin{agda}\begin{code}
U ≈ U : Configuration ads cs ds → Configuration ads cs ds → Set
c ≈ c′ = cfgToList c ↭ cfgToList c′
  where
    open import Data.List.Permutation using (U ↭ U)

    cfgToList : Configuration′ p₁ p₂ p₃ → List (∃[ p₁ ] ^^ ∃[ p₂ ] ^^ ∃[ p₃ ] ^^ Configuration′ p₁ p₂ p₃)
    cfgToList  ∅                 = []
    cfgToList  (l | r)           = cfgToList l ++ cfgToList r
    cfgToList  {p₁} {p₂} {p₃} c  = [ p₁ , p₂ , p₃ , c ]
\end{code}\end{agda}
Given this reordering mechanism, we now need to generalise all our inference rules to implicitly
reorder the current and next configuration of the step relation.
We achieve this by introducing a new variable for each of the operands of the resulting step relations,
replacing the operands with these variables and requiring that they are
re-orderings of the previous configurations, as shown in the following generalisation of the |[DEP-AuthJoin]| rule\footnote{
In fact, it is not necessary to reorder both ends for the step relation; at least one would be adequate.
}:
\begin{agda}\begin{code}
  DEP-AuthJoin :
       Γ′ ≈ ⟨ A , v ⟩ SUPD | ⟨ A , v′ ⟩ SUPD | Γ                ^^  ∈ Configuration ads cs (A has v ∷ A has v′ ∷ ds)
    →  Γ″ ≈ ⟨ A , v ⟩ SUPD | ⟨ A , v′ ⟩ SUPD | A [ 0 ↔ 1 ] | Γ  ^^  ∈ Configuration ads cs (A has (v + v′) ∷ ds)
       {- $\inferMedium$ -}
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
inherent in any process calculus. Building upon this idea, we plan to take a step back and investigate different reasoning
techniques for a minimal process calculus. Once we have an approach that is more suitable, we will incorporate it
in our full-blown BitML calculus.
\end{itemize}

\subsection{Symbolic Model}
In order to formalize the BitML's symbolic model, we first notice that a constructed derivation
witnesses one of many possible contract executions.
That is, derivations of our small-step semantics model \textit{traces} of the contract execution.
Our symbolic model will provide a game-theoretic view over those traces, where each participant has a certain
\textit{strategy} that selects moves depending on the current trace of previous moves.
Moves here should be understood just as emissions of a certain label, i.e. application of a certain inference rule.

To that end, we associate a label to each inference rule and
extend the original step relation to additionally emit labels,
hence defining a \textit{labelled transition system}.

We first define the set of labels, which basically distinguish which rule was used,
along with all (non-proof) arguments that are required by the rule.
Below we give an example label for the |[C-AuthControl]| rule:~\footnote{
Notice how we existentially pack indexed types.
}
\begin{agda}\begin{code}
data Label : Set where
##
  auth-control[ U , U ▷ SB U] : Participant → (c : ∃Contracts) → Index (proj₂ (proj₂ c)) → Label
##
  VDOTS
\end{code}\end{agda}

Naturally, the reflexive transitive closure of the augmented step relation will now hold a sequence of labels as well:
\begin{agda}\begin{code}
data U —↠ [ U ] U  :  Configuration ads cs ds
                   →  Labels
                   →  Configuration ads′ cs′ ds′
                   →  Set where

  UL ∎∎  : (M : Configuration ads cs ds)

       ------------
    →  M —↠[ [] ] M

  U —→⟨ U ⟩ U ⊢ U : (L : Configuration ads cs ds) {L′ : Configuration ads cs ds}
                    {M M′ : Configuration ads′ cs′ ds′} {N : Configuration ads″ cs″ ds″}

    →  L′ —→[ a ] M′
    →  (L ≈ L′) × (M ≈ M′)
    →  M —↠[ as ]  N
       -------------------
    →  L —↠[ a ∷ as ] N

start_ : {M : Configuration ads cs ds} {N : Configuration ads′ cs′ ds′}

  →  M —↠[ as ] N
     ------------
  →  M —↠[ as ] N

start M—↠N = M—↠N
\end{code}\end{agda}
The timed variants of the step relation follow exactly the same procedure, so we do not repeat the definitions here.



We can now extract
Since the complex type indices of the step-relation datatype is not as useful here,
we define a simpler datatype of execution traces that is a list of labelled transitions
between (existentially-packed) timed configurations:
\begin{agda}\begin{code}
data Trace =
\end{code}\end{agda}


\subsubsection{Labels}
\TODO{One-to-one correspondence with rules}
...
\TODO{Extend step relation}

\subsubsection{Runs}
\TODO{Existentially-packed timed rules}
...
\paragraph{Stripping}
...

\subsubsection{Strategies}
\TODO{assume PPTIME complexity ... too difficult to model complexity-aware models ...}
...
\paragraph{Honest strategies}
...
\paragraph{Adversary strategies}
...

\subsubsection{Meta-theoretical results}
\paragraph{Stripping preserves semantics}
...
\paragraph{Adversial moves are always semantic}
...

\subsection{BitML Paper Fixes}

\subsubsection{[DEP-Join]}
\TODO{why symmetric?}

\subsubsection{[C-AuthRev]}
\TODO{missing |DOTS ∣∣ Γ|}

\subsubsection{[C-Control]}
\TODO{Refactor to allow for ``linear'' equational reasoning}

\subsubsection{Adversarial Strategy}
\TODO{No need for λ = (Aj,j)}

\subsubsection{Stripping premises}
\TODO{Not only AuthRev, but also AuthCommit}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Next steps}
\label{sec:next}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
In this section, I describe possible next steps I plan to investigate during the remainder of my thesis.
It is impossible to accurately predict what will be achieved in the following five months
and there will definitely be some surprises along the way,
but I hope it will give realistic expectations of the final results of my thesis.

\subsection{Extended UTxO}
Many major blockchain systems today support the creation of secondary cryptocurrencies, which are independent of the main  currency.
In Bitcoin, for instance, \textit{colored coins} allow transactions to assign additional meaning to their outputs
(e.g. each coin could correspond to a real-world asset, such as company shares)~\cite{coloredcoins}.

This approach, however, has the disadvantage of larger transactions and less efficient processing.
One could instead bake the multi-currency feature into the base system, mitigating the need for
larger transactions and slow processing.
Building on the abstract UTxO model, there are current research efforts on a general framework that provides mechanisms
to establish and enforce monetary policies for multiple currencies~\cite{multicurrency}.

Fortunately, the extensions proposed by the multi-currency are orthogonal to the functionality I have currently formalized.
In order to achieve this, one has to generalize the |Value| datatype to account for multiple currencies.
Hence, I plan to integrate this with my current formal development of the extended UTxO model and,
by doing so, provide the first formalization of a UTxO ledger that supports multiple cryptocurrencies.

\subsubsection{2-level Multi-currency}
\TODO{... non-fungible tokens ...}

\subsubsection{Multi-signature Scheme}
\TODO{... where multiple parties have to synchonize authorisation ...}

\subsubsection{Plutus Integration}
In my current formalization of the extended UTxO model, scripts are immediately modelled by their denotations
(i.e. pure mathematical functions). This is not accurate, however, since scripts are actually pieces of program text.
However, there is current development by James Chapman of IOHK to formalize the meta-theory of Plutus,
Cardano's scripting language\site{https://github.com/input-output-hk/plutus-metatheory}.

Since we mostly care about Plutus as a scripting language, it would be possible to replace the denotations with
actual Plutus Core source code and utilize the formalized meta-theory to acquire the denotational semantics when needed.

\subsection{BitML}

\subsubsection{Decision Procedures}
\TODO{more ergonomic proof-development process ...}

\subsubsection{Towards Completeness}
Continuing my work on the formalization of the BitML paper~\cite{bitml},
there is still a lot of theoretical results to be covered:
\begin{itemize}
\item While I currently have the symbolic model in place, there is still no formalization of \textit{symbolic strategies},
where one can reason about different adversary strategies and prove that certain scenarios are impossible.
\item Another import task is to define the computational model; a counterpart of the symbolic model augmented
with pragmatic computational properties to more closely resemble the low-level details of Bitcoin.
\item When both symbolic and computational strategies have been formalized, I will be able to finally
prove the correctness of the BitML compiler, which translates high-level BitML contracts to
low-level standard Bitcoin transactions. The symbolic model concerns the input of the compiler, while
the computational one concerns the output.
This endeavour will involve implementing the actual translation and proving \textit{coherence} between the
symbolic and the computational model.
Proving coherence essentially requires providing a (weak) \textit{simulation} between the two models;
each step in the symbolic part is matched by (multiple) steps in the computational one.
\end{itemize}

\subsection{UTxO-BitML Integration}
So far I have worked separately on the two models under study, but it would be interesting to see whether these
can be intertwined in some way.
This would possibly involve a translation from BitML contracts to contracts modelled in our extended UTxO models,
along with corresponding meta-theoretical properties (e.g. validity of UTxO transactions correspond to another notion
of validity of BitML contracts).

Moreover, and it would be beneficial to review the different modelling techniques used across both models,
identifying their key strengths and witnesses.
With this in mind, I could refactor crucial parts of each model for the sake of elegance, clarity and ease of reasoning.

\TODO{BitML → eUTxO compiler ... Compilation correctness ... full abstraction}

\subsection{Featherweight Solidity}
One of the posed research questions concerns the expressiveness of the extended UTxO model with respect to
Ethereum-like account-based ledgers.

In order to investigate this in a formal manner, one has to initially model a reasonable subset of Solidity,
so a next step would be to model \textit{Featherweight Solidity}, taking inspiration from the
approach taken in the formalization of Java using \textit{Featherweight Java}~\cite{featherweightjava}.
Fortunately, I will not have to start from scratch, since there have been recent endeavours in F$^*$ to analyse and
verify Ethereum smart contracts, which already describe a simplified model of Solidity~\cite{short}.

As a next step, one could try out different example contracts in Solidity and check whether they can be transcribed to
contracts appropriate for an extended UTxO ledger.

\subsection{Proof Automation}
Last but not least, our current dependently-typed approach to formalizing our models has led to a significant proof burden,
as evidenced by the complicated type signatures presented throughout this proposal.
This certainly makes the reasoning process quite tedious and time consuming, so a reasonable task would be
to implement automatic proof-search procedures using Agda meta-programming~\cite{agdaauto}.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Conclusion}
\label{sec:conclusion}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\newpage
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Bibliography
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\bibliography{sources}

\newpage
\begin{appendix}
... used throughout our formalization ...

\section{List Utilities}
\subsection{Indexed Operations}
\subsection{Inductive Relations}

\section{Set-like Interface for Lists}
\subsection{Decidable equality}
\subsection{Set Operations}

\section{Generalized Variables}
We (ab)use Agda's recent capabilities for \textit{generalized variables},
which allow one to declare variable names of a certain type at the top-level
and then omit them from their usage in type definitions for clarity.

Below we give a complete set of all variables used throughout this thesis:
\begin{agda}\begin{code}
keyword variable
  ads ads′ ads″ rads adsʳ radsʳ adsˡ radsˡ : AdvertisedContracts
  cs  cs′  cs″  rcs  csʳ  rcsʳ  csˡ  rcsˡ  : ActiveContracts
  ds  ds′  ds″  rds  dsʳ  rdsʳ  dsˡ  rdsˡ  : Deposits
  Γ Γ₀ : Configuration ads  cs  ds
  Γ′   : Configuration ads′ cs′ ds′
  Γ″   : Configuration ads″ cs″ ds″

  p₁ p₁′ : AdvertisedContracts × AdvertisedContracts
  p₂ p₂′ : ActiveContracts     × ActiveContracts
  p₃ p₃′ : Deposits            × Deposits
  Γp  : Configuration′ p₁  p₂  p₃
  Γp′ : Configuration′ p₁′ p₂′ p₃′
\end{code}\end{agda}

\listoffigures
\listoftables
\end{appendix}

\end{document}
