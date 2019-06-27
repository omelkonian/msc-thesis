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
\item % Related Work
Section~\ref{sec:related} gives an overview of relavant previous work, ranging
from static analysis tools to type-driven verification approaches.
\item % Future Work
Section~\ref{sec:future} discusses possible next steps to continue the line of work
stemming from this thesis.
\item % Conclusion
Section~\ref{sec:conclusion} concludes with a general overview of our contributions and reflects on the chosen methodology.

\end{itemize}
