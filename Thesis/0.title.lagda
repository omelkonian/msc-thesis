% Title Page
\thispagestyle{empty}
\begin{center}\begin{minipage}{0.8\linewidth}
\centering
\vspace{2cm}
% Title
{
\textsc{\Large{Formalizing Extended UTxO and BitML Calculus in Agda}} \\[.5cm]
\large{\textit{Laying the foundations for the formal verification of smart contracts}}
\par}
\vspace{1cm}
% Author's name
{
\Large Orestis Melkonian
\par}
\vspace{1cm}
% Line
{
\rule{\linewidth}{1pt}
\par}
\vspace{1cm}
% Degree
{
\textit{A thesis submitted for the Master of Science degree} \\[.2cm]
\textit{Department of Information and Computing Sciences} \\[.2cm]
\textit{Utrecht University}
\par}
\vspace{1cm}
% University logo
\includegraphics[width=0.4\linewidth]{logo.pdf} \\[.5cm]
\vspace{.5cm}
%Date
{\Large July 2019 \par}
\vspace{1.5cm}%
% Supervisors
{
\Large
\begin{tabular}{lll}
Supervisors:       & Wouter Swierstra        & (Utrecht University) \\
                   & Manuel M.T. Chakravarty & (Input Output HK)    \\[5pt]
2$^{nd}$ Examiner: & Gabriele Keller         & (Utrecht University) \\
\end{tabular}
\par}
\end{minipage}\end{center}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Abstract
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\newpage
\section*{Abstract}
Smart contracts -- programs that run on a blockchain -- allow for sophisticated transactional schemes,
but their concurrent execution makes it difficult to reason about their behaviour and
failing to do so leads to significant monetary losses (e.g. DAO attack).
For that reason, increasingly more attention is being drawn to rigid formal methods, which
guarantee that such fatal scenarios are not possible.

We attempt to advance the state-of-the-art for a language-oriented, type-driven account
of smart contracts, by formalizing two well-established models in Agda
and mechanizing the corresponding meta-theory.

The first concerns an abstract model for UTxO-based ledgers, such as Bitcoin,
which we further extend to cover features of the Cardano blockchain,
namely more expressive scripts and built-in support for user-issued cryptocurrencies.

The second object of study is BitML, a process calculus specifically targeting Bitcoin smart contracts.
We give a dependently-typed encoding of BitML contracts and its small-step semantics,
as well as a mechanized account of BitML's symbolic model over participant strategies.

Finally, we sketch the way towards a \textit{certified compiler} from BitML contracts to UTxO transactions,
where all behaviours manifesting on BitML's symbolic model can safely be transported to the UTxO level.

\newpage
\tableofcontents
