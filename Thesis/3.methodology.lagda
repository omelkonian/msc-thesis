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
