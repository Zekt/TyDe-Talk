\documentclass[10pt,xcolor=svgnames,aspectratio=169]{beamer} %Beamer
\usepackage{palatino} %font type
\usefonttheme{metropolis} %Type of slides
\usefonttheme[onlymath]{serif} %font type Mathematical expressions
\usetheme[titleformat frame=smallcaps]{metropolis} %This adds a bar at the beginning of each section.
% \usetheme[progressbar=frametitle,titleformat frame=smallcaps,numbering=counter]{metropolis}
% \useoutertheme[subsection=false]{miniframes} %Circles in the top of each frame, showing the slide of each section you are at

\usepackage{appendixnumberbeamer} %enumerate each slide without counting the appendix
% \setbeamercolor{progress bar}{fg=Maroon!70!Coral} %These are the colours of the progress bar. Notice that the names used are the svgnames
\setbeamercolor{title separator}{fg=DarkSalmon} %This is the line colour in the title slide
\setbeamercolor{structure}{fg=black} %Colour of the text of structure, numbers, items, blah. Not the big text.
\setbeamercolor{normal text}{fg=black!87} %Colour of normal text
\setbeamercolor{alerted text}{fg=DarkRed!60!Gainsboro} %Color of the alert box
\setbeamercolor{example text}{fg=Maroon!70!Coral} %Colour of the Example block text


\setbeamercolor{palette primary}{bg=NavyBlue!50!DarkOliveGreen, fg=white} %These are the colours of the background. Being this the main combination and so one. 
\setbeamercolor{palette secondary}{bg=NavyBlue!50!DarkOliveGreen, fg=white}
\setbeamercolor{palette tertiary}{bg=NavyBlue!40!Black, fg= white}
\setbeamercolor{section in toc}{fg=NavyBlue!40!Black} %Color of the text in the table of contents (toc)

\usepackage[utf8]{inputenc}
% \usepackage{amsmath,amssymb}
\usepackage[Symbol]{upgreek}
\usepackage{newtxmath}
% \usepackage{slashed}
% \usepackage[capitalise,noabbrev]{cleveref}
% \usepackage{relsize}
% \usepackage{caption}
% \usepackage{subcaption}
\usepackage{multicol}
% \usepackage{booktabs}
% \usepackage[scale=2]{ccicons}
% \usepackage{pgfplots}
% \usepgfplotslibrary{dateplot}
% \usepackage{geometry}
% \usepackage{xspace}
% \usepackage{comment}
% \usepackage{ucs}
% \usepackage{bbm}
\usepackage[style=authortitle,backend=biber]{biblatex}
\addbibresource{bib.bib}
\usepackage[greek,english]{babel}
\usepackage{newunicodechar}
% \usepackage{polytable}


\newcommand{\themename}{\textbf{\textsc{bluetemp}\xspace}}%metropolis}}\xspace}

\newcommand{\awa}[2]{\mathrlap{#2}\phantom{#1}} % as wide as
\newcommand{\aha}[2]{\smash{\parbox{\linewidth}{#2}}\phantom{\parbox{\linewidth}{#1}}} % as high as
\newcommand{\parl}[1]{\parbox{\linewidth}{#1}} % as high as

\newcommand{\mi}[1]{\ensuremath{\mathit{#1}}}

\newunicodechar{???}{\ensuremath{\mathord{\rightarrow}}}
\newunicodechar{???}{\ensuremath{\Rightarrow}}
\newunicodechar{???}{\ensuremath{\mathord\vdash}}
\newunicodechar{???}{\ensuremath{\mathord\vDash}}
\newunicodechar{???}{\ensuremath{\forall}}
\newunicodechar{???}{\ensuremath{\mathbb{N}}}
\newunicodechar{??}{\ensuremath{\lambdaslash}}
\newunicodechar{??}{\ensuremath{\varGamma}}
\newunicodechar{??}{\ensuremath{\varDelta}}
\newunicodechar{???}{\ensuremath{\ni}}
\newunicodechar{??}{\ensuremath{\mu}}
\newunicodechar{??}{\ensuremath{\alpha}}
\newunicodechar{??}{\ensuremath{\rho}}
\newunicodechar{??}{\ensuremath{\sigma}}
\newunicodechar{??}{\ensuremath{\tau}}
\newunicodechar{??}{\ensuremath{\mathord\cdotp}}
\newunicodechar{???}{\ensuremath{_1}}
\newunicodechar{???}{\ensuremath{_2}}
\newunicodechar{??}{\ensuremath{\times}}
\newunicodechar{???}{\ensuremath{^d}}
\newunicodechar{??}{\ensuremath{\omega}}
\newunicodechar{??}{\ensuremath{\lambda}}
\newunicodechar{???}{\ensuremath{\blacksquare}}
\newunicodechar{???}{\ensuremath{\mathord{^\backprime}}}
\newunicodechar{???}{\ensuremath{::}}
\newunicodechar{???}{\ensuremath{\mathord\ast}}
\newunicodechar{???}{\ensuremath{\ell}}


%include polycode.fmt

\title{Syntax-Generic Operations, Reflectively Reified}
\author[Name]{Tzu-Chi Lin and Hsiang-Shang Ko} %With inst, you can change the institution they belong
\subtitle{Extended Abstract}
\institute[uni]{Institute of Information Science \\ Academia Sinica, Taiwan}
\date{\today}

\begin{document}
{
	\setbeamercolor{background canvas}{bg=NavyBlue!50!DarkOliveGreen, fg=white}
	\setbeamercolor{normal text}{fg=white}
	\setbeamercovered{transparent}
	\maketitle
}%This is the colour of the first slide. bg= background and fg=foreground

\metroset{titleformat frame=smallcaps} %This changes the titles for small caps

\begin{frame}[fragile]{Outline}
\setbeamertemplate{section in toc}[sections numbered] %This is numbering the sections
\tableofcontents[hideallsubsections] %You can comment this line if you want to show the subsections in the table of contents
\end{frame}

\section{Introduction}

\begin{frame}[fragile]{Motivation}
\emph{Intrinsic typing} is a common pattern that dependently typed programmers use to define $\uplambda$-calculus with De Bruijn indices.
\metroset{block=fill}
\begin{exampleblock}{Example 2.}
	\aha{%
		\begin{code}
data _???_ : Context ??? Type ??? Set where
  `_     : ?? ??? A ??? ?? ??? A
  ??_     : ?? , A ??? B ??? ?? ??? A ??? B
  _??_    : ?? ??? A ??? B ??? ?? ??? A ??? ?? ??? B
  `zero  : ?? ??? `???
  `suc_  : ?? ??? `??? ??? ?? ??? `???
  case   : ?? ??? `??? ??? ?? ??? A ??? ?? , `??? ??? A ??? ?? ??? A
  ??_     : ?? , A ??? A ??? ?? ??? A
		\end{code}
	}{%
		\begin{code}
data _???_ : List Type ??? Type ??? Set where
  `_     : ?? ??? A ??? ?? ??? A
  ??_     : ?? , A ??? B ??? ?? ??? A ??? B
  _??_    : ?? ??? A ??? B ??? ?? ??? A ??? ?? ??? B
		\end{code}
	}
\end{exampleblock}
\end{frame}

\begin{frame}[fragile]{Motivation}
\emph{Intrinsic typing} is a common pattern that dependently typed programmers use to define $\uplambda$-calculus with De Bruijn indices.
\metroset{block=fill}
\begin{exampleblock}{Example 2.}
	\parl{
	\begin{code}
data _???_ : Context ??? Type ??? Set where
  `_     : ?? ??? A ??? ?? ??? A
  ??_     : ?? , A ??? B ??? ?? ??? A ??? B
  _??_    : ?? ??? A ??? B ??? ?? ??? A ??? ?? ??? B
  `zero  : ?? ??? `???
  `suc_  : ?? ??? `??? ??? ?? ??? `???
  case   : ?? ??? `??? ??? ?? ??? A ??? ?? , `??? ??? A ??? ?? ??? A
  ??_     : ?? , A ??? A ??? ?? ??? A
	\end{code}
	}
\end{exampleblock}
\end{frame}

\begin{frame}[fragile]{Motivation}
Scope-safe syntax operations can be defined with the help of intrinsic typing:
	\metroset{block=fill}
	\begin{exampleblock}{Example 2.1.}
		\begin{code}
rename : ??? {?? ??}  ??? (??? {A} ??? ?? ???  A ??? ?? ???  A)
                  ??? (??? {A} ??? ?? ???  A ??? ?? ???  A)
rename ?? (` x)          =  ` (?? x)
rename ?? (?? N)          =  ?? (rename (ext ??) N)
rename ?? (L ?? M)        =  (rename ?? L) ?? (rename ?? M)
rename ?? (`zero)        =  `zero
rename ?? (`suc M)       =  `suc (rename ?? M)
rename ?? (case L M N)   =  case  (rename ?? L)
                                 (rename ?? M)
                                 (rename (ext ??) N)
rename ?? (?? N)          =  ?? (rename (ext ??) N)
		\end{code}
	\end{exampleblock}
\end{frame}

\begin{frame}[fragile]{Motivation}
Programmers may change/extend the object language they are interested in:
	\metroset{block=fill}
		\begin{exampleblock}{Example 3, extending example 2.}
		\begin{code}
data _???_ : Context ??? Type ??? Set where
	...
  con       : ??? ??? ?? ??? Nat
  _`???_      : ?? ??? Nat ??? ?? ??? Nat ??? ?? ??? Nat
  `let      : ?? ??? A ??? ?? , A ??? B ??? ?? ??? B
  `???_ , _???  : ?? ??? A ??? ?? ??? B ??? ?? ??? A `?? B
  `proj???    : ?? ??? A `?? B ??? ?? ??? A
  `proj???    : ?? ??? A `?? B ??? ?? ??? B
  case??     : ?? ??? A `?? B ??? ?? , A , B ??? C ??? ?? ??? C
		\end{code}
	\end{exampleblock}
\end{frame}

\begin{frame}[fragile]{Motivation}
The syntax operations need to be redefined/extended accordingly:
	\metroset{block=fill}
	\begin{exampleblock}{Example 3.1, extending example 2.1.}
		\begin{code}
rename ?? (con n)        =  con n
rename ?? (M `??? N)       =  rename ?? M `??? rename ?? N
rename ?? (`let M N)     =  `let (rename ?? M) (rename (ext ??) N)
rename ?? `??? M , N ???     =  `??? rename ?? M , rename ?? N ???
rename ?? (`proj??? L)     =  `proj??? (rename ?? L)
rename ?? (`proj??? L)     =  `proj??? (rename ?? L)
rename ?? (case?? L M)    =  case??  (rename ?? L)
                                  (rename (ext (ext ??)) M)
		\end{code}
	\end{exampleblock}
\end{frame}

\begin{frame}[fragile]{Motivation}
All the other operations are to be repeated:
		\begin{code}
subst : ??? {?? ??}  ??? (??? {A} ??? ?? ???  A ??? ?? ??? A)
                 ??? (??? {A} ??? ?? ???  A ??? ?? ??? A)


print : ?? ??? A ??? String


...
		\end{code}
\end{frame}

\begin{frame}[fragile]{Existing work}
  There have been generic libraries providing constructions that can be specialised for a whole family of syntaxes with binders~\footcite{Allais-generic-syntax}\footcite{Fiore-SOAS-Agda}\footcite{Ahrens-typed-abstract-syntax}.

	We take a closer look on Allais et al.'s approach\footnotemark[1] published at ICFP '18.
\end{frame}

\begin{frame}[fragile]{Existing work by Allais et al.}
	Allais et al. present a universe of syntaxes \mi{Desc},
	\begin{code}
data Desc (I : Set) : Set??? where
	?????  : (A : Set) ??? (A ??? Desc I) ??? Desc I
	???X  : List I ??? I ??? Desc I ??? Desc I
	??????  : I ??? Desc I
	\end{code}
\end{frame}

\begin{frame}[fragile]{Existing work by Allais et al.}
Simply typed $\uplambda$-calculus
	\begin{code}
data STLC : Type ??? List Type ??? Set where
  ???var : Var ?? ?? ??? STLC ?? ??
  ???app : STLC (?? ?????? ??) ?? ??? STLC ?? ?? ??? STLC ?? ??
  ???lam : STLC ?? (?? ??? ??) ??? STLC (?? ?????? ??) ??
	\end{code}
	\pause
can be encoded in \mi{Desc}:
	\metroset{block=fill}
	\begin{exampleblock}{Example 4, description of simply typed $\uplambda$-calculus.}
	\begin{code}
STLC : Desc Type
STLC = ?? ???STLC ?? where
  (App  i j) ??? ???X [] (i ?????? j) (???X [] i (??? j))
  (Lam  i j) ??? ???X (i ??? []) j (??? (i ?????? j))
	\end{code}
	\end{exampleblock}
\end{frame}

\begin{frame}[fragile]{Existing work by Allais et al.}
	\metroset{block=fill}
	\begin{exampleblock}{Example 4 in full.}
	\begin{code}
data Type : Set where
  ??     : Type
  _??????_  : Type ??? Type ??? Type

data ???STLC : Set where
  App Lam : Type ??? Type ??? ???STLC

STLC : Desc Type
STLC = ?? ???STLC ?? where
  (App  i j) ??? ???X [] (i ?????? j) (???X [] i (??? j))
  (Lam  i j) ??? ???X (i ??? []) j (??? (i ?????? j))
	\end{code}
	\end{exampleblock}
\end{frame}

\begin{frame}[fragile]{Existing work by Allais et al.}
	Generic programs are described by \mi{Semantics} records.

	They can be realized as functions on the fixpoint constructor \mi{Tm} via \mi{semantics}.
	\metroset{block=fill}
	\begin{exampleblock}{Example 5, generic rename function.}
	\begin{code}
Renaming : ??? {d : Desc I} ??? Semantics d Var (Tm d)

rename : ??? {d : Desc I} ??? (??? {i}  ??? Var i ?? ??? Var i ??)
                                  ??? Tm d j ?? ??? Tm d j ??
rename ?? t = semantics Renaming ?? t
	\end{code}
	\end{exampleblock}
\mi{rename} is generic as it can be applied to fixpoints of any description (e.g. $\mi{Tm}\ \mi{STLC}$).
\end{frame}

\begin{frame}[fragile]{Motivation cont.}
	Problems with applying standard datatype-generic programming to syntax-generic operations:
	\pause
	\begin{enumerate}
		\item datatype/function definitions are non-intuitive (no more beautiful typing rules \& IDE supports!),
		\pause
		\item requiring the programmer to understand the syntax universe, and
		\pause
		\item interoperability: difficult (if not impossible) to work with existing libraries or other generic libraries.
	\end{enumerate}
\end{frame}

\begin{frame}[fragile]{Motivation cont.}
	Programmers prefer ``natural'' datatype and function definitions,
	\aha{
		\begin{code}
rename : ??? {?? ??}  ??? (??? {A} ??? ?? ???  A ??? ?? ???  A)
                  ??? (??? {A} ??? ?? ???  A ??? ?? ???  A)
rename ?? (` x)          =  ` (?? x)
rename ?? (?? N)          =  ?? (rename (ext ??) N)
rename ?? (L ?? M)        =  (rename ?? L) ?? (rename ?? M)

Renaming : Semantics Var Lam
Renaming = record
  { th^V  = th^Var
  ; var   = ???var
  ; app   = ???app
  ; lam   = ?? b ??? ???lam (b weaken z) }
rename = semantics Renaming
		\end{code}
	}{
		\begin{code}
data _???_ : Context ??? Type ??? Set where
  `_     : ?? ??? A ??? ?? ??? A
  ??_     : ?? , A ??? B ??? ?? ??? A ??? B
  _??_    : ?? ??? A ??? B ??? ?? ??? A ??? ?? ??? B
		\end{code}
	\begin{code}
STLC : Desc Type
STLC = ?? ???STLC ?? where
  (App  i j) ??? ???X [] (i ?????? j) (???X [] i (??? j))
  (Lam  i j) ??? ???X (i ??? []) j (??? (i ?????? j))
	\end{code}
	}
\end{frame}

\begin{frame}[fragile]{Motivation cont.}
	Programmers prefer ``natural'' datatypes and functions,
		\begin{code}
rename : ??? {?? ??}  ??? (??? {A} ??? ?? ???  A ??? ?? ???  A)
                  ??? (??? {A} ??? ?? ???  A ??? ?? ???  A)
rename ?? (` x)          =  ` (?? x)
rename ?? (?? N)          =  ?? (rename (ext ??) N)
rename ?? (L ?? M)        =  (rename ?? L) ?? (rename ?? M)

Renaming : Semantics Var Lam
Renaming = record
  { th^V  = th^Var
  ; var   = ???var
  ; app   = ???app
  ; lam   = ?? b ??? ???lam (b weaken z) }
rename = semantics Renaming
	\end{code}
\end{frame}

\section{Elaborator Reflection to the Rescue}

\begin{frame}[fragile]{Elaborator Reflection to the Rescue}
	In our published work at ICFP, we have provided:
	\pause
	\begin{itemize}
		\item a description \mi{DataD} generic enough for any Agda's inductive datatypes,
		\pause
		\item generic program descriptions \mi{FoldP} for folds (and \mi{IndP} for inductions),
		\pause
		\item a metaprogram \mi{genDataD} that generates datatype descriptions from their native definitions, and 
		\pause
		\item a metaprogram \mi{defineFold} that generates function definitions from their generic representations.
	\end{itemize}
\end{frame}

\begin{frame}[fragile]{Motivation cont.}
	We further define:
	\begin{itemize}
		\item a predicate \mi{Syntax} on \mi{DataD} that captures a subset equivalent to \mi{Desc}.
		\item a function \mi{SemP} that generates descriptions (typed \mi{FoldP}) of generic fold operations, given proofs of the predicate.
	\end{itemize}
It turns out all programs defined with \mi{Semantics} are folds.
\end{frame}

\begin{frame}[fragile]{Flow Chart}
\includegraphics[width=\columnwidth]{Diagram.pdf}
\end{frame}

\begin{frame}[fragile]{The \mi{Syntax} Predicate}
	\begin{code}
Syntax : Set ??? ??? DataD ??? Set??
	\end{code}
All syntaxes in \mi{Desc} should be captured by the \mi{Syntax} predicate:
	\pause
	\begin{itemize}
		\item each of them has a variable rule as its first rule,
		\pause
		\item they are not universe polymorphic,
		\pause
		\item each have two indices, $I$ and $\mi{List}\ I$, and
		\pause
		\item allow and only allow context extensions in subterms.
	\end{itemize}
\end{frame}

\begin{frame}[fragile]{The \mi{Syntax} Predicate}
Does \mi{PCF} satisfies \mi{Syntax}?
	\begin{code}
data PCF : Type ??? List Type ??? Set where
  ???var   : Var ?? ?? ??? PCF ?? ??
  ???app   : PCF (?? ?????? ??) ?? ??? PCF ?? ?? ??? PCF ?? ??
  ???lam   : PCF ?? (?? ??? ??)  ??? PCF (?? ?????? ??) ??
  ???zero  : PCF ?????? ??
  ???suc_  : PCF ?????? ?? ??? PCF ?????? ??
	\end{code}
\end{frame}

\begin{frame}[fragile]{The \mi{Syntax} Predicate}
	\metroset{block=fill}
	\begin{exampleblock}{A Syntax proof example}
		\begin{code}
SyntaxPCF : Syntax Type (genDataD (quote PCF))
SyntaxPCF = _
        , refl
        , (refl ,refl)
        , _
        , refl
        , refl
        , (_ , _ , _ , refl , (?? _ ??? refl))
        , (_ , _ , _ , refl , (?? _ ??? refl))
        , (_ , _ , _ , refl , (?? _ ??? refl))
        , (_ , _ , _ , refl , (?? _ ??? refl))
        , tt
		\end{code}
	\end{exampleblock}
\end{frame}

% \begin{frame}[fragile]{Translation from Semantics to natural looking functions}
% \end{frame}

\section{Demo}

\section{Discussion: towards datatype-generic libraries for syntaxes?}

\begin{frame}[fragile]{Future Works \& Issues}
	\begin{itemize}
		\item Proof automation with elaborator reflection 
		\item Better user interface
		\item Applying the framework to more generic libraries
		\pause
			\begin{itemize}
				\item Expressiveness is limited by Agda datatypes as well as the generic universe, a \mi{Syntax} predicate must be defined.
				\pause
				\item Even if we can define \mi{Syntax}, the proof could be more complicated, even require programmers to understand the generic universe.
				\pause
				\item Obstacles of using multiple generic libraries at once.
				\pause
				\item Are folds and inductions enough?
			\end{itemize}
	\pause
	\item Is it worth it?
	\end{itemize}
\end{frame}

\section{Q \& A}

\end{document}

