%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Related Work}
\label{sec:related}
%%%%%%%%%%%%%%%%%%%%%%%%%%%

\subsection{Static Analysis Tools}

Bugs in smart contracts have led to significant financial losses (c.f. DAO attach),
thus it is crucial we can automatically detect them.
Moreover, we must detect them statically, since contracts become immutable once deployed.
This is exceptionally hard though, due to the concurrent execution inherent in smart contracts,
which is why most efforts so far have been on static analysis techniques for particular classes of bugs.

\paragraph{MadMax}
In Ethereum smart contracts, programs written or compiled to EVM bytecode,
hold a valuable resource called \textit{gas} (c.f. Section~\ref{subsec:ethereum}).
This amount puts a threshold on the number of computational steps a contract can execute until it completes.
Out-of-gas errors can lead to undefined behaviour, that can be exploited by a malicious attacker.

MadMax is a scalable program analysis tool, that achieves to statically
detect such gas-related vulnerabilities with very high precision~\cite{madmax}.
The techniques employed include \textit{control-flow analysis} and declarative
logic programs that form queries about the program structure.

\paragraph{Effectively Callback Free (ECF) Analysis}
A lot of security issues in Ethereum arise from the use of callback functions in smart contracts.
This abstraction poses a great deal of complexity on understanding contract behaviour, since they break modular reasoning.

In~\cite{mooly}, a class of \textit{effectively callback-free} (ECF) programs is defined,
where such issues are not possible.
Then, a program analysis tool is provided to verify such a property, which can additionally
be realized either statically or dynamically.

\paragraph{Verifying Liquidity in BitML Contracts}
The BitML compiler that accompanies the original paper~\cite{bitml}, written in
Racket\site{https://github.com/bitml-lang/bitml-compiler},
also provides a \textit{model checker} to verify \textit{liquidity} of contracts written in its DSL;
liquid contracts never freeze funds, i.e. making them irredeemable by any participant\footnote{
An example vulnerability occurred in the Ethereum Parity Wallet, which froze \textasciitilde 160$M$ USD.
}.

The crucial observation that makes verification possible, is that liquidity is a decidable
property.
Model-checking is possible in a finite state space, derived from a finite variant of BitML's
infinite semantics.

\subsection{Type-driven Approaches}
Recently there has been increased demand for more rigid formal methods in the blockchain domain~\cite{opportunities}
and we believe the field would greatly benefit from a language-based, type-driven approach~\cite{langverif}
alongside a mechanized meta-theory.

\paragraph{\textsc{Scilla}}
One such example is \textsc{Scilla}, an intermediate language for
smart contracts, with a formal semantics based on communicating automata~\cite{scilla}.
\textsc{Scilla}, however, follows an \textit{extrinsic} approach to software verification:
contracts are written in a simply-typed DSL embedded in Coq~\cite{coq}
and dependent types are used to verify their safety and temporal properties.

On the other hand, our work explores a new point in the design space, exploiting the dependent type
system of Agda~\cite{agda} to encode \textit{intrinsically}-typed contracts, whose behaviour is more predictable and easier to reason about.
Nonetheless, this comes with the price of tedious type-level manipulation,
as witnessed throughout our formal development.
Intricate datatype indices, in particular, are notoriously difficult to get right and refactor in an iterative fashion.

\paragraph{Setzer's Bitcoin Model}
A formal model, which is very similar to our own formal model of UTxO-based ledgers,
is Setzer's effort to model Bitcoin in Agda~\cite{setzer}.

There, Setzer utilizes an extended form of Agda's unique feature of \textit{induction-recursion};
the types of transactions and ledgers are mutually, inductively defined
and, at the same time, the set of unspent transaction outputs is recursively computed.
This mitigates the need to carry proofs that ascertain all lookups succeed and references have valid targets.

Alas, these advanced techniques create a significant gap between the pen-and-paper mathematical formulation
and the corresponding mechanized model.
This is the primary reason we chose to have a simpler treatment of the basic types,
treating the well-scopedness of lookups extrinsically (i.e. within the |IsValidTx| dependent record).
Another reason for being skeptical to such a statically-defined model is the difficulty
to later extend it with dynamic operations, such as continuous change of the participant set.
