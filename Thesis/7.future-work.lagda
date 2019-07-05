%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Future Work}
\label{sec:future}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
In this section, we describe possible next steps for both our formalizations,
namely the (extended) UTxO model and the BitML calculus.

The majority of the suggestions are straightforward or completely orthogonal to our current system,
therefore we believe they can be incorporated in a relatively short-term period.

Most importantly, we give the ambitious vision of integrating our two objects of study, giving rise
to a \textit{certified compiler} from BitML contracts to UTxO transactions;
this will constitute a major part of the author's upcoming PhD studies.

\subsection{Extended UTxO}

\subsubsection{Non-fungible Tokens}
Although we have implemented and formalized support for user-issued cryptocurrencies,
the multi-currency infrastacture in the current development of Cardano also supports
\textit{non-fungible tokens} (NFTs)~\cite{eutxo}.
These tokens represent unique assets that are not interchangable (i.e. fungible) and have
already be used in crypto-gaming, where in-game assets are controlled by the player instead of the game developer.

In order to accommodate NFTs, a very similar extension to the one employed for the initial support
for multiple currencies is needed. Specifically, again we have to generalize the |Value| type from
\textit{single-level} maps from currency identifiers to quantities, to \textit{two-level} maps
that introduce an intermediate level of \textit{tokens}.
In other words, a currency can hold items of a distinct identity (token), which can in turn
have a certain amount of supply (quantity).

As expected, the necessary refactoring is simple:
\begin{itemize}
\item Generalize from |Map Hash ℕ| to |Map Hash (Map Token ℕ)|.
\item Lift algebraic operations to the new representation point-wise,
just like we did to initially support multiple currencies.
\end{itemize}

An interesting side-effect of this way of implementing NFTs is the ability to investigate
a whole spectrum between fungible and non-fungible token currencies, e.g. when having more
than one distinct tokens.

\subsubsection{Plutus Integration}
In our current formalization of the extended UTxO model, scripts are immediately modelled by their denotations
(i.e. pure mathematical functions). This is not accurate, however, since scripts are actually pieces of program text.
However, there is current development by James Chapman of IOHK to formalize the meta-theory of Plutus,
Cardano's scripting language\site{https://github.com/input-output-hk/plutus-metatheory}.

Since we mostly care about Plutus as a scripting language, it would be possible to replace the denotations with
actual Plutus Core source code and utilize the formalized meta-theory to acquire the denotational semantics when needed.
Arguably, this has certain benefits, such as providing decidable equality for our scripts\footnote{
Of course, two arbitrary Agda functions cannot be checked for equality.
} and, consequently, decidable equality for whole transactions and ledgers.

\subsubsection{Multi-signature Scheme}
Another extension we deem worthy of being included in our eUTxO formalization,
is the recent proposal to support \textit{multi-signature} transactions~\cite{multisig}.
This extension introduces a new validation scheme for transactions, where an
unspent output can only be consumed if a pre-defined set of digital signatures
from different participants is provided.

The main changes involve adding a new witness type to the transactions, namely
the set of required signatures. Then, the validation mechanism enforces a check
between the pre-defined set of signatures and the required ones.
A slight increase in the complexity of our formal framework is necessary,
but we, nevertheless, expect this extension to be more-or-less orthogonal to the existing features.

\subsection{BitML}

\subsubsection{Decision Procedures}
The current proof development process of our BitML formal model is far from user-friendly;
the user has to supply inline proofs in copious amounts while using our dependently-typed definitions.
Thankfully, most of these can be proven decidable once and for all,
and then a simple call to the decision procedure would do the work.

As shown in Section~\ref{subsec:utxo-example},
we could use Agda's latest feature for \textit{tactic arguments} to mitigate the need
for the user to provide any proofs, e.g. when writing contracts or small-step derivations.

\subsubsection{Towards Completeness}
Continuing our work on the formalization of the BitML paper~\cite{bitml},
there is still a lot of theoretical ground to be covered:
\begin{itemize}
\item While we currently have the symbolic model and its meta-theory in place, there are still
various holes in the proofs; nothing major, but it is always a good idea to cover all corner cases.
Most of these holes correspond to insignificant proof obligations that arise from our,
such as the list equalities arising from the uses of the composition operator |_ BAR _| for BitML configurations.
However, a few remaining holes are not as trivial and should be investigated for further confidence in the model,
such as covering all possible cases in the meta-theoretical proofs of BitML's symbolic model
in Section~\ref{subsec:bitml-metatheory}.
\item Another import task is to define the computational model; a counterpart of the symbolic model augmented
with pragmatic computational properties to more closely resemble the low-level details of Bitcoin.
\item When both symbolic and computational strategies have been formalized, we will be able to finally
prove the correctness of the BitML compiler, which translates high-level BitML contracts to
low-level standard Bitcoin transactions. The symbolic model concerns the input of the compiler, while
the computational one concerns the output.
This endeavour will involve implementing the actual translation and proving \textit{coherence} between the
symbolic and the computational model.
Proving coherence essentially requires providing a (weak) \textit{simulation} between the two models;
each step in the symbolic part is matched by (multiple) steps in the computational one.
\end{itemize}

\subsection{UTxO-BitML Integration}
So far we have investigated the two models under study separately,
but it would be interesting to see whether these can be intertwined in some way.

First, note that it is entirely possible to simulate the compilation scheme given in~\cite{bitml} with our
eUTxO model, but now compiling to a more abstract notion of UTxO transactions, rather than \textit{standard}
Bitcoin transactions.
Nonetheless, we believe this would be overly complicated for our purposes,
since the extensions our eUTxO model supports can make things much simpler.
For instance, \textit{data scripts} make it possible to simulate \textit{stateful}, \textit{on-chain} computation.
This is ideal for implementing a small-step interpreter, since our reduction semantics is defined
as a (labelled) transition system itself.
In fact, this has already been successfully employed by \textit{Marlowe},
whose implementation of the small-step semantics of its financial contracts
follows exactly this stateful scheme via data scripts\site{https://github.com/input-output-hk/marlowe/blob/master/docs/tutorial-v2.0/marlowe-plutus.md}.

One could argue that the original BitML-to-Bitcoin compiler is less useful than a compiler to our eUTxO formal model,
due to the latter being more abstract without consideration for ad-hoc features of Bitcoin,
thus more amendable to easier reasoning and generally more flexible.
Therefore, it might be worthwhile to skip the formalization of BitML's computational model all together,
and instead focus on a BitML-to-eUTxO compiler instead.

A significant benefit of compiling down to our intrinsically-typed ledgers, is the guarantee that
we only ever get \textbf{valid} transactions.
Alas, we need to have a similar operational semantics for our eUTxO model to state a \textit{compilation correctness} theorem.
Fortunately, IOHK's internal formal methods team already has an up-to-date mathematical specification of
small-step semantics for Cardano ledgers~\cite{smallsteps}, upon which we can rely for a \textit{mechanical} reduction semantics
and eventually a \textit{certified compiler}.

Lastly, and it would be beneficial to review the different modelling techniques used across both models,
identifying their key strengths and witnesses.
With this in mind, we could refactor crucial parts of each model for the sake of elegance, clarity and ease of reasoning.

\subsection{BitML-Marlowe Comparison}
Another possible research endeavour is a formal comparison between the BitML calculus and the Marlowe DSL.
In fact, this is already under investigation by the Marlowe team, as recent commits on Github
suggest\site{https://github.com/input-output-hk/marlowe/blob/master/semantics-3.0/BItSem.hs}.

They both provide a high-level description of smart contracts
and they both lend themselves to an operational reduction semantics.
Looking at the mere size of BitML's inference rules,
Marlowe's small-step semantics seems a lot simpler.
Therefore, we believe it would be interesting to investigate
whether BitML's formulation can be simplified, possibly taking inspiration
by the language constructs of Marlowe.

To this end, a formalization of Marlowe in Agda should be prototyped, followed by a mechanization of its meta-theory.
Then, a compilation correctness results would guarantee that any step taken by Marlowe can be simulated
by one or more steps in BitML's semantics, essentially leading to a \textit{full abstraction} result;
Marlowe exhibits the same behavioural properties as BitML, and we can safely
reason in its more abstract framework.
If that is indeed the case, effort should be probably better spent on the eUTxO-Marlowe integration, rather
than eUTxO-BitML.

\subsection{Featherweight Solidity}
One of the posed research questions concerns the expressiveness of the extended UTxO model with respect to
Ethereum-like account-based ledgers.

Since Solidity is a fully-fledged programming language with lots of features
(e.g. static typing, inheritance, libraries, user-defined types), it makes sense to
restrict our formal study to a compact subset of Solidity that is easy to reason about.
This is the approach also taken in Featherweight Java~\cite{featherweightjava}; a subset
of Java that omits complex features such as reflection, in favour of easier behavioural reasoning
and a more formal investigation of its semantics.
In a similar vein, we will attempt to formalize a lightweight version of Solidity, which we will refer to as
\textit{Featherweight Solidity}.
Fortunately, there have already been recent efforts in F$^*$ to analyze and
verify Ethereum smart contracts, which already describe a simplified model of Solidity~\cite{short}.

As an initial step, one should try out different example contracts in Solidity and check whether they can be transcribed to
contracts appropriate for an extended UTxO ledger.

\subsection{Proof Automation}
Last but not least, our current dependently-typed approach to formalizing our models has led to a significant proof burden,
as evidenced by the complicated type signatures presented throughout our formal development.
This certainly makes the reasoning process quite tedious and time consuming, so a reasonable task would be
to implement automatic proof-search procedures using Agda meta-programming~\cite{agdaauto}.
We have already done so for the validity condition of UTxO ledgers (Section~\ref{subsec:decproc}), but wish to
also provide decision procedures for the ledgers weakening and combining, as well as for significant proof obligations
in the BitML model.
