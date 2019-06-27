\documentclass[acmsmall,nonacm=true,screen=true]{acmart}
\settopmatter{printfolios=false,printccs=false,printacmref=false}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Bibliography style
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\bibliographystyle{ACM-Reference-Format}
\citestyle{acmauthoryear}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Packages
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% URLs
\newcommand\site[1]{\footnote{\url{#1}}}

% Quotes
\usepackage{csquotes}

% Graphics
\usepackage{graphicx}
\graphicspath{ {img/} }

% Tikz
\usepackage{tikz}
\usetikzlibrary{chains,arrows,automata,fit,positioning,calc}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Macros
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\newcommand\TODO[1]{\textcolor{red}{TODO: #1}}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Agda imports
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%include polycode.fmt
%include stylish.fmt
\def\commentbegin{}
\def\commentend{}

%% TOC formatting
\setcounter{tocdepth}{2} % + subsections

% Line spacing
\renewcommand{\baselinestretch}{1.15}

%% Title formatting
\usepackage{titlesec}

\titleformat{\section} % command
[display] % shape
{\bfseries\huge\itshape} % format
{\filleft\MakeUppercase{Section} \Huge\thesection} % label
{2ex} % sep
{\titlerule
 \vspace{2ex}%
 \filright
} % before-code
[\vspace{2ex}%
 \titlerule
 \vspace{4ex}%
] % after-code

\titleformat{\subsection}[block]
{\normalfont\large\bfseries}{\thesubsection}{1em}{}
\titleformat{\subsubsection}[block]
{\itshape\normalsize\bfseries}{\thesubsubsection}{1em}{}
\titleformat{\paragraph}[runin]
{\itshape\normalsize\bfseries}{\theparagraph}{1em}{}[.]

\begin{document}
\sloppy % for proper justification (no overflows to the right)

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Title
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\title{Formal investigation of the Extended UTxO model}
\subtitle{Laying the foundations for the formal verification of smart contracts}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%% Authors
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\author{Orestis Melkonian}
\orcid{0000-0003-2182-2698}
\affiliation{
  \position{MSc Student}
  \department{Information and Computing Sciences}
  \institution{Utrecht University}
  \city{Utrecht}
  \country{The Netherlands}
}
\email{melkon.or@@gmail.com}

\pagestyle{plain}
%%include 0.title.lagda
\newpage
%include 1.intro.lagda
\newpage
%include 2.background.lagda
\newpage
%%include 3.methodology.lagda
\newpage
%include 4.utxo.lagda
\newpage
%%include 5.bitml.lagda
\newpage
%include 6.related-work.lagda
\newpage
%%include 7.future-work.lagda
\newpage
%%include 8.conclusion.lagda
\newpage
\bibliography{sources}
\newpage
%%include 9.appendix.lagda

\end{document}
