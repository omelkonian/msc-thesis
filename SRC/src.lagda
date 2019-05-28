\documentclass[acmsmall,nonacm=true,screen=true]{acmart}
\settopmatter{printfolios=true,printccs=false,printacmref=false}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Bibliography style
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\bibliographystyle{ACM-Reference-Format}
%\citestyle{acmauthoryear}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Packages
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% URLs
\newcommand\site[1]{\footnote{\url{#1}}}

%include polycode.fmt
%include stylish.lhs
\def\commentbegin{}
\def\commentend{}

\begin{document}
\sloppy % for proper justification (no overflows to the right)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Title
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\title{Formalization of the BitML Calculus in Agda}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Authors
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\author{Orestis Melkonian}
\orcid{0000-0003-2182-2698}
\affiliation{
  \department{Information and Computing Sciences}
  \institution{Utrecht University}
  \city{Utrecht}
  \country{The Netherlands}
}
%\email{melkon.or@@gmail.com}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Abstract
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\begin{abstract}
  \begin{description}
    \item[Email:] melkon.or@@gmail.com
    \item[Research Advisors:] Wouter Swierstra (UU) \& Manuel Chakravarty (IOHK)
    \item[ACM Student Number:] 4094241
    \item[Category:] Graduate (MSc Student)
  \end{description}
\end{abstract}

\maketitle

\section{Introduction}
... Bitcoin $\rightarrow$ smart contracts $\rightarrow$ bus $\rightarrow$ formal methods~\cite{opportunities} ...\\
... already some static analysis tools~cite{mooly,madmax,liquidity} ...\\
... advocate language-based, type-driven approach~\cite{langverif} ...\\
... especially proof assistants based on dependent types~\cite{agda} ... extrinsic vs intrinsic ...\\

... BitML: idealistic process calculus for Bitcoin smart contracts~\cite{bitml} ...\\
... provide the first formalization of the BitML calculus in Agda ...\\
... set the foundation to later accommodate a full compilation correctness proof ... full abstraction result ...\\

\section{The BitML Calculus} 
All code is publicly available on Github\site{https://github.com/omelkonian/formal-bitml}.

\subsection{Inherently-typed Contracts}
Moving on to actual contracts, we define them by means of a collection of five types of commands;
|put| injects participant deposits and revealed secrets in the remaining contract,
|withdraw| transfers the current funds to a participant,
|split| distributes the current funds across different individual contracts,
|UNDER : UNDER| requires the authorization from a participant to proceed
and |after UNDER : UNDER| allows further execution of the contract only after some time has passed.
\begin{myagda}\begin{code}
data Contract  :  Value   -- the monetary value it carries
               →  Values  -- the deposits it presumes
               →  Set where
  put UNDER reveal UNDER if UNDER ⇒ UNDER ∶- UNDER :
    (vs : List Value) → (s : Secrets) → Predicate s′  → Contract (v + sum vs) vs′ →  s′ ⊆ s
    → Contract v (vs′ ++ vs)
  withdraw : ∀ {v} → Participant → Contract v []
  split :  (cs : List (∃[ v ] ^^ ∃[ vs ] ^^ Contract v vs))
        →  Contract (sum (proj₁ <$$> cs)) (concat (proj₂ <$$> cs))
  UNDER : UNDER : Participant → Contract v vs → Contract v vs
  after UNDER : UNDER : Time → Contract v vs → Contract v vs
\end{code}\end{myagda}
There is a lot of type-level manipulation across all constructors, since we need to make sure that indices are
calculated properly. For instance, the total value in a contract constructed by the |split| command is the 
sum of the values carried by each branch.
The |put| command\footnote{
|put| comprises of several components and we will omit those that do not contain any helpful information,
e.g. write |put UNDER ⇒ UNDER| when there are no revealed secrets and the predicate trivially holds.
} additionally requires an explicit proof that the predicate
of the |if| part only uses secrets revealed by the same command.

\begin{myagda}\begin{code}
record Advertisement (v : Value) (vs SUPC vs SUPG : List Value) : Set where
  constructor UNDER ⟨ UNDER ⟩∶- UNDER
  field  G      :  Precondition vs
         C      :  Contracts v vs
         valid  :  length vs SUPC ≤ length vs SUPG
                ×  participants SUPG G ++ participants SUPC C ⊆ (participant <$$> persistentDeposits SUPP G) 
\end{code}\end{myagda} %$

\subsection{Small-step Semantics}
... indexed configuration (+ actions) ...
\begin{myagda}\begin{code}
data Configuration′  :  -- $\hspace{22pt}$ current $\hspace{20pt}$ $\times$ $\hspace{15pt}$ required
                        AdvertisedContracts  × AdvertisedContracts
                     →  ActiveContracts      × ActiveContracts
                     →  List Deposit         × List Deposit
                     →  Set where

  -- empty
  ∅ : Configuration′ ([] , []) ([] , []) ([] , [])

  -- contract advertisement
  ` UNDER  :  (ad : Advertisement v vs SUPC vs SUPG)
           →  Configuration′ ([ v , vs SUPC , vs SUPG , ad ] , []) ([] , []) ([] , [])

  -- active contract
  ⟨ UNDER , UNDER ⟩ SUPCC  :  (c : List (Contract v vs)) → Value
                           →  Configuration′ ([] , []) ([ v , vs , c ] , []) ([] , [])

  -- deposit redeemable by a participant
  ⟨ UNDERR , UNDER ⟩ SUPD  :  (p : Participant) → (v : Value)
                           →  Configuration′ ([] , []) ([] , []) ([ p has v ] , [])

  -- authorization to perform an action
  UNDERL [ UNDER ]  : (p : Participant) → Action p ads cs vs ds
                    → Configuration′ ([] , ads) ([] , cs) (ds , ((p has UNDER) <$$> vs))

  -- committed secret
  ⟨ UNDER ∶ UNDER ♯ UNDER ⟩  :  Participant →  Secret →  ℕ ⊎ ⊥
                             →  Configuration′ ([] , []) ([] , []) ([] , [])
  -- revealed secret
  UNDER ∶ UNDER ♯ UNDER  :  Participant →  Secret → ℕ
                         →  Configuration′ ([] , []) ([] , []) ([] , [])

  -- parallel composition
  UNDER | UNDER  :  Configuration′ (ads SUPL , rads SUPL) (cs SUPL , rcs SUPL) (ds SUPL , rds SUPL)
                 →  Configuration′ (ads SUPR , rads SUPR) (cs SUPR , rcs SUPR) (ds SUPR , rds SUPR)
                 →  Configuration′  (ads SUPL                    ++ ads SUPR  , rads SUPL  ++ (rads SUPR  ∖ ads SUPL))
                                    (cs SUPL                     ++ cs SUPR   , rcs SUPL   ++ (rcs SUPR   ∖ cs SUPL))
                                    ((ds SUPL ∖ rds SUPR)        ++ ds SUPR   , rds SUPL   ++ (rds SUPR   ∖ ds SUPL))

Configuration : AdvertisedContracts → ActiveContracts → List Deposit → Set
Configuration ads cs ds = Configuration′ (ads , []) (cs , []) (ds , [])
\end{code}\end{myagda} %$

... inference rules ...
\begin{myagda}\begin{code}
data UNDER —→ UNDER : Configuration ads cs ds → Configuration ads′ cs′ ds′ → Set where
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
\end{code}\end{myagda}

... mention timed-configurations at the upper level |UNDER —→ SUBT UNDER| ...

... implicit re-ordering in |UNDER —↠ UNDER| ...
\begin{myagda}\begin{code}
data UNDER —↠ UNDER : Configuration ads cs ds → Configuration ads′ cs′ ds′ → Set where

  UNDER ∎ : (M : Configuration ads cs ds) → M —↠ M

  UNDER —→ ⟨ UNDER ⟩ UNDER : ∀ {M  N} (L : Configuration ads cs ds)
    →  L —→ M → M —↠ N
       {- $\inferMedium$ -}
    →  L —↠ N

begin UNDER : ∀ {M N} → M —↠ N → M —↠ N
\end{code}\end{myagda}

\paragraph{Symbolic model}
\begin{itemize}
\item honest strategies
\item adversary strategy
\item conformance
\end{itemize}

\section{Example: Timed-commitment Protocol}
\begin{myagda}\begin{code}
tc : Advertisement 1 [] (1 ∷ 0 ∷ [])
tc =  ⟨ A ! 1 ∧ A ♯ a ∧ B ! 0 ⟩ ^^ reveal [ a ] ⇒ withdraw A ∶- DOTS ^^ ⊕ ^^ after t ∶ withdraw B

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
\end{code}\end{myagda}
At first, |A| holds a deposit of \bitcoin ~1, as required by the contract's precondition.
Then, the contract is advertised and the participants slowly provide the corresponding prerequisites
(i.e. |A| commits to a secret via |[C-AuthCommit]| and spends the required deposit via |[C-AuthInit]|,
while |B| does not do anything).
After all pre-conditions have been satisfied, the contract is stipulated (rule |[C-Init]|) and the secret is successfully
revealed (rule |[C-AuthRev]|).
Finally, the first branch is picked (rule |[C-Control]|) and |A| retrieves her deposit back
(rules |[C-PutRev]| and |[C-Withdraw]|).

\section{Future}
... instead of BitML->Bitcoin~\cite{bitml} ...\\
... BitML->FormalUTxO~\site{https://github.com/omelkonian/formal-utxo}~\cite{utxo} ...\\
... will be easier with the added expressivity from data scripts~\cite{eutxo} ... c.f. Marlowe~\cite{marlowe} ...\\

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Bibliography
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\bibliography{sources}

\end{document}
