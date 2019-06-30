%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Conclusion}
\label{sec:conclusion}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
Our main contributions are the formalization of two existing mathematical models, namely
the abstract model for UTxO-based ledgers and the BitML calculus.

We start with an intrinsically-typed model of UTxO ledgers,
as presented in the mathematical formulation in \cite{utxo}.
Moreover, we further account for two extensions currently used in the Cardano blockchain:
\textit{data scripts} to make more expressive transactional schemes possible and
\textit{multi-currency} support to allow multiple cryptocurrencies to coexist in the same ledger.
Having a formal framework at hand allows us to proceed with a more algebraic treatment of UTxO ledgers,
which we demonstrate with the introduction of two operations:
\textit{weakening} injects the abstract type of the available address space to a larger type,
while \textit{combining} allows merging two disjoint ledgers, automatically extracting
a proof of validity for the resulting ledger from the existing proofs of the sub-ledgers.
Finally, an example construction of a correct-by-definition ledger is given, where
no manual proof is necessary, since all proofs can be discharged with the decision procedure for the validity conditions.

Our BitML formalization closely follows the original BitML paper~\cite{bitml}, but we also
impose a lot of type-level invariants, in order to have a more clear view of what constitutes a \textit{well-formed} contract.
We carry this type-driven mentality over to the \textit{small-step semantics} of BitML contracts, where the type system
keeps our inference rules in check.
To showcase that the proposed modelling of the semantics can accommodate ordinary proof methods,
we give an example derivation for the standard contract implementing the \textit{timed-commitment protocol}.
We do not go as far as mechanizing the proposed translation from BitML contracts to Bitcoin transactions,
but rather restrain our formalization efforts to BitML's \textit{symbolic model}:
a game-theoretic reasoning framework for participant strategies, accompanied by
mechanized meta-theoretical results that gives us more confidence for the model.

Apart from the individual formalization of our two objects of study, we also deem it worthy to investigate
on how to combine these two, envisioning a \textit{certified compiler} from BitML contracts to
to UTxO-based transactions with (extended) scripts.
There, any attack scenario that we would discover in BitML's symbolic model,
could be safely determined to manifest in the UTxO semantics as well.

While the original BitML paper gives a compiler from BitML contracts to standard Bitcoin transactions,
along with a compilation correctness proof,
we believe that the abstract UTxO model would be a more suitable target.
Not only will the translation be more useful, since we abstract away technicalities specific to Bitcoin
and can accommodate any UTxO-based blockchain system, but also more easier to implement and reason about,
since the added expressivity arising from the extensions will make the translation more straightforward.

Moving to a dependently-typed settings gives you a much more in-depth view on how everything works, but
there are also a lot of design decisions involved in the choice of datatypes and modelling approaches.
Throughout the thesis, we have described and justified our own decisions,
possibly driven by the particular advantages and disadvantages of Agda.
Nonetheless, there has also been discussion on alternative ways to approach the modelling process, as well
as thoughts for future directions.

In addition to the mechanization of existing formulations, we sketch a research plan to
ultimately get our hands on a \textit{certified} compiler from BitML contracts,
where we can reason in the BitML level and safely transfer the results to the actual behaviour in a UTxO-based ledger.

Through our current mechanized results, we hope to have further motivated the
use of language-oriented type-driven solutions to blockchain semantics in general,
and the semantics of smart contract behaviour in particular.
