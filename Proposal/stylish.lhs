%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Agda Styling
%%
%% TODO: Figure out spacing!

% Bitcoin symbol
\def\bitcoin{%
  \leavevmode
  \vtop{\offinterlineskip %\bfseries
    \setbox0=\hbox{B}%
    \setbox2=\hbox to\wd0{\hfil\hskip-.03em
    \vrule height .3ex width .15ex\hskip .08em
    \vrule height .3ex width .15ex\hfil}
    \vbox{\copy2\box0}\box2}}

% Horizontal lines for inference rules
\newcommand\inferSmall{\rule[3pt]{2cm}{.6pt}}
\newcommand\inferMedium{\rule[3pt]{5cm}{.6pt}}
\newcommand\inferLarge{\rule[3pt]{8cm}{.6pt}}
\newcommand\inferVeryLarge{\rule[3pt]{11cm}{.6pt}}

%% Colors (from duo-tone light syntax)
\definecolor{hsblack}{RGB}{45,32,3}
\definecolor{hsgold1}{RGB}{179,169,149}
\definecolor{hsgold2}{RGB}{177,149,90}
\definecolor{hsgold3}{RGB}{190,106,13}%{192,96,4}%{132,97,19}
\definecolor{hsblue1}{RGB}{173,176,182}
\definecolor{hsblue2}{RGB}{113,142,205}
\definecolor{hsblue3}{RGB}{0,33,132}
\definecolor{hsblue4}{RGB}{97,108,132}
\definecolor{hsblue5}{RGB}{34,50,68}
\definecolor{hsred2}{RGB}{191,121,103}
\definecolor{hsred3}{RGB}{171,72,46}

%% LaTeX Kerning nastiness. By using curly braces to delimit color group,
%% it breaks spacing. The following seems to work:
%%
%% https://tex.stackexchange.com/questions/85033/colored-symbols/85035#85035
%%
\newcommand*{\mathcolor}{}
\def\mathcolor#1#{\mathcoloraux{#1}}
\newcommand*{\mathcoloraux}[3]{%
  \protect\leavevmode
  \begingroup
    \color#1{#2}#3%
  \endgroup
}

\newenvironment{myagda}
{ \par
  %\vspace{0.15cm}
  \begin{minipage}{\textwidth}
}
{ \end{minipage}
  %\vspace{0.15cm}
}

\newcommand{\HSKeyword}[1]{\mathcolor{hsgold3}{\textbf{#1}}}
\newcommand{\HSNumeral}[1]{\mathcolor{hsred3}{#1}}
\newcommand{\HSChar}[1]{\mathcolor{hsred2}{#1}}
\newcommand{\HSString}[1]{\mathcolor{hsred2}{#1}}
\newcommand{\HSSpecial}[1]{\mathcolor{hsblue4}{\ensuremath{#1}}}
\newcommand{\HSSym}[1]{\mathcolor{hsblue4}{\ensuremath{#1}}}
\newcommand{\HSCon}[1]{\mathcolor{hsblue3}{#1}}
\newcommand{\HSVar}[1]{\mathcolor{hsblue5}{\mathit{\ensuremath{#1}}}}
\newcommand{\HSComment}[1]{\mathcolor{hsgold2}{\textit{#1}}}

%subst keyword a = "\HSKeyword{" a "}"
%subst conid a   = "\HSCon{" a "}"
%subst varid a   = "\HSVar{" a "}"
%subst varsym a  = "\HSSym{" a "}"
%subst consym a  = "\HSSym{" a "}"
%subst numeral a = "\HSNumeral{" a "}"
%subst char a    = "\HSChar{''" a "''}"
%subst string a  = "\HSString{``" a "\char34 }"
%subst special a = "\HSSpecial{" a "}"
%subst comment a = "\HSComment{ -\! -" a "}"

%format Star       = "\HSCon{*}"

%%format :          = "\HSCon{\mathbin{:}}"
%format nil        = "\HSCon{[]}"

%format family     = "\HSKeyword{family}"
%format pattern    = "\HSKeyword{pattern}"
%format _          = "\HSSym{\anonymous} "
%format ->         = "\HSSym{\to} "
%format →          = "\HSSym{\to} "
%format <-         = "\HSSym{\leftarrow} "
%format =>         = "\HSSym{\Rightarrow} "
%format \          = "\HSSym{\lambda} "
%format |          = "\HSSym{\mid} "
%format {          = "\HSSym{\{\mskip1.5mu} "
%format }          = "\HSSym{\mskip1.5mu\}}"
%format [          = "\HSSym{[\mskip1.5mu} "
%format ]          = "\HSSym{\mskip1.5mu]}"
%format =          = "\HSSym{\mathrel{=}}"
%format ..         = "\HSSym{\mathinner{\ldotp\ldotp}}"
%format ~          = "\HSSym{\mathrel{\sim}}"
%format @          = "\HSSym{\mathord{@}}"
%%format .          = "\HSSym{\mathbin{\circ}}"
%format ^          = "\HSSym{\mathbin{\uparrow}}"
%format **         = "\HSSym{\mathbin{**}}"
%format /          = "\HSSym{\mathbin{/}}"
%format `quot`     = "\HSSym{\mathbin{`quot`}}"
%format `rem`      = "\HSSym{\mathbin{`rem`}}"
%format `div`      = "\HSSym{\mathbin{`div`}}"
%format `mod`      = "\HSSym{\mathbin{`mod`}}"
%format :%         = "\HSSym{\mathbin{:\%}}"
%format %          = "\HSSym{\mathbin{\%}}"
%format ++         = "\HSSym{\mathbin{\plus}}"
%format ==         = "\HSSym{\equiv}"
%format /=         = "\HSSym{\not\equiv}"
%format <=         = "\HSSym{\leq}"
%format >=         = "\HSSym{\geq}"
%format `elem`     = "\HSSym{\in}"
%format `notElem`  = "\HSSym{\notin}"
%format &&         = "\HSSym{\mathrel{\wedge}}"
%format ||         = "\HSSym{\mathrel{\vee}}"
%format >>         = "\HSSym{\sequ}"
%format >>=        = "\HSSym{\bind}"
%format =<<        = "\HSSym{\rbind}"
%format $          = "\HSSym{\mathbin{\$}}"
%format `seq`      = "\HSSym{\mathbin{`seq`}}"
%format !          = "\HSSym{\mathbin{!}}"
%format //         = "\HSSym{\mathbin{//}}"
%format \\         = "\HSSym{\mathbin{\\\\}}"
%format undefined  = "\HSSym{\bot}"
%format not	       = "\HSSym{\neg} "
%format >>>        = "\HSSym{\ggg}"
%format >=>        = "\HSSym{> \! = \! >}"

%%% Datatype Promotion
%format (P (a)) = "\HSSym{''}" a

%%% Agda things
%format record      = "\HSKeyword{record}"
%format data        = "\HSKeyword{data}"
%format postulate   = "\HSKeyword{postulate}"
%format field       = "\HSKeyword{field}"
%format constructor = "\HSKeyword{constructor}"
%format open        = "\HSKeyword{open}"
%format import      = "\HSKeyword{import}"
%%format as         = "\HSKeyword{as}"
%format using       = "\HSKeyword{using}"

%format refl      = "\HSCon{refl}"
%format ∷         = "\HSCon{::}"
%format tt        = "\HSCon{tt}"

%%% Formatting
%format DOTS     = "\HSSym{\dots}"
%format VDOTS    = "\HSSym{\vdots}"
%format ^^       = "\;"
%format ##       = "\vspace{10pt}"
%format UNDER    = "\HSSym{\_}"
%format UNDERL   = "\HSSym{\_\!}"
%format UNDERR   = "\HSSym{\!\_}"

%%% Usefull Notation
%format ,        = "\HSSym{\mathbin{,}}"
%format forall   = "\HSSym{\forall}"
%format dot      = "\HSSym{.}"
%format ^=       = "\HSSym{\bumpeq}"
%format alpha    = "\HSVar{\alpha}"
%format phi      = "\HSVar{\varphi}"
%format phi1     = "\HSVar{\varphi_1}"
%format phi2     = "\HSVar{\varphi_2}"
%format kappa    = "\HSVar{\kappa}"
%format kappa1   = "\HSVar{\kappa_1}"
%format kappa2   = "\HSVar{\kappa_2}"
%format eta      = "\HSVar{\eta}"
%format eta1     = "\HSVar{\eta_1}"
%format eta2     = "\HSVar{\eta_2}"
%format fSq      = "\HSVar{f}"
%format ~~       = "\HSSym{\approx}"
%format :>:      = "\HSCon{\triangleright}"
%format :*       = "\HSCon{\times}"
%format :*:      = "\HSCon{:\!*\!:}"
%format :+:      = "\HSCon{:\!+\!:}"
%format :@:      = "\HSCon{:\!@\!:}"
%format <>       = "\HSSym{\diamond}"
%format <$$>     = "\HSSym{<\!\!\$\!\!>}"
%format <*>      = "\HSSym{<\!\!*\!\!>}"
%format <->      = "\HSSym{\mathrel{\leftrightarrow}}"
%format <=>      = "\HSSym{\mathrel{\iff}}"
%format if       = "if"
%format ℕ        = "\HSSym{\mathbb{N}}"
%format 𝔹        = "\HSSym{\mathbb{B}}"
%format ∅        = "\HSSym{\varnothing}"
%format ∪        = "\HSSym{\mathbin{\cup}}"
%format ⟨        = "\HSSym{\langle\ }"
%format ⟩        = "\HSSym{\ \rangle}"
%format ∈        = "\HSSym{\mathrel{\in}}"
%format ∋        = "\HSSym{\mathrel{\ni}}"
%format iin      = "\HSSym{i\!\in}"
%format ⊆        = "\HSSym{\mathrel{\subseteq}}"
%format ≡        = "\HSSym{\mathrel{\equiv}}"
%%format λ       = "\HSSym{\lambda\ }"
%format BIT      = "\HSSym{\bitcoin}"
%format ‼        = "\HSSym{\mathbin{!!}}"
%format ♯        = "\HSSym{\ ♯}"
%format ∶-       = "\HSSym{\vdash}"
%format ⟩∶-      = "\HSSym{\ \rangle\vdash}"
%format ∙        = "\HSSym{\bullet}"
%format ⊕        = "\HSSym{\mathbin{\oplus}}"
%format -        = "\HSSym{\text{\textit{-}}}"
%format ♯-       = "\HSSym{♯\text{\textit{-}}}"
%format ∖        = "\HSSym{\setminus}"
%format ′        = "\HSSym{′\ }"
%format Γ        = "\HSSym{\Gamma}"
%format ⊎        = "\HSSym{\mathbin{\uplus}}"
%format ⊥        = "\HSSym{\bot}"
%format ×       = "\HSSym{\ \mathbin{\times}\ }"
%format ≤        = "\HSSym{\mathrel{\leq}}"
%format ⊆        = "\HSSym{\mathrel{\subseteq}}"
%format ⊸        = "\HSSym{\multimap}"
%format ∧        = "\HSSym{\mathbin{\land}}"
%format ∎        = "\HSSym{\text{\mbox{\tiny$\square$}}}"
%format —→⟨      = "\HSSym{\longrightarrow\!\langle\ }"
%format —→       = "\HSSym{\mathrel{\longrightarrow}}"
%format —↠       = "\HSSym{\mathrel{\twoheadrightarrow}}"
%format ↭        = "\HSSym{\mathrel{\leftrightsquigarrow}}"
%format ≈        = "\HSSym{\mathrel{≈}}"
%format ⇒        = "\HSSym{\mathrel{\Rightarrow}}"
%format at       = "\HSSym{@}"

%format BAR      = "\HSSym{\! | \!}"
%format TRI      = "\HSSym{\vartriangleright}"
%format HTRI     = "\HSSym{♯\!\vartriangleright}"
%format DTRI     = "\HSSym{{\vartriangleright}^d}"
%format STRI     = "\HSSym{{\vartriangleright}^s}"
%format BTRI     = "\HSSym{{\vartriangleright}^b}"

%format SUBL     = "\HSSym{\!\text{\textsubscript{\tiny l}}}"
%format SUBR     = "\HSSym{\!\text{\textsubscript{\tiny r}}}"
%format SUBT     = "\HSSym{\!\text{\textsubscript{\tiny t}}}"
%format SUBI     = "\HSSym{\!\text{\textsubscript{\tiny i}}}"
%format SUPC     = "\HSSym{\!\text{\textsuperscript{\tiny c}}}"
%format SUPG     = "\HSSym{\!\text{\textsuperscript{\tiny g}}}"
%format SUPA     = "\HSSym{\!\text{\textsuperscript{\tiny a}}}"
%format SUPL     = "\HSSym{\!\text{\textsuperscript{\tiny l}}}"
%format SUPR     = "\HSSym{\!\text{\textsuperscript{\tiny r}}}"
%format SUPP     = "\HSSym{\!\text{\textsuperscript{\tiny p}}}"
%format SUPPLUS  = "\HSSym{\!\text{\textsuperscript{\tiny +}}}"
%format SUPT     = "\HSSym{\!\text{\textsuperscript{\tiny t}}}"
%format SUPCC    = "\HSSym{\text{\textsuperscript{\tiny c}}}"
%format SUPD     = "\HSSym{\text{\textsuperscript{\tiny d}}}"
