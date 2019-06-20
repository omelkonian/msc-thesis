%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Appendix
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
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
variable
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
