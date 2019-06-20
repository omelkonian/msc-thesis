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
