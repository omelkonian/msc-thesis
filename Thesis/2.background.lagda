%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Background}
\label{sec:background}
%%%%%%%%%%%%%%%%%%%%%%%%%%%

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
