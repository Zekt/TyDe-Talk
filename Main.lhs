\documentclass[10pt,xcolor=svgnames]{beamer} %Beamer
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
\usepackage[style=verbose,backend=biber]{biblatex}
\addbibresource{bib.bib}
\usepackage[greek,english]{babel}
\usepackage{newunicodechar}
% \usepackage{polytable}


\newcommand{\themename}{\textbf{\textsc{bluetemp}\xspace}}%metropolis}}\xspace}

\newcommand{\awa}[2]{\mathrlap{#2}\phantom{#1}} % as wide as
\newcommand{\aha}[2]{\smash{\parbox{\linewidth}{#2}}\phantom{\parbox{\linewidth}{#1}}} % as high as
\newcommand{\parl}[1]{\parbox{\linewidth}{#1}} % as high as

\newcommand{\mi}[1]{\ensuremath{\mathit{#1}}}

\newunicodechar{→}{\ensuremath{\mathord{\rightarrow}}}
\newunicodechar{⇒}{\ensuremath{\Rightarrow}}
\newunicodechar{⊢}{\ensuremath{\vdash}}
\newunicodechar{∀}{\ensuremath{\forall}}
\newunicodechar{ℕ}{\ensuremath{\mathbb{N}}}
\newunicodechar{ƛ}{\ensuremath{\lambdaslash}}
\newunicodechar{Γ}{\ensuremath{\varGamma}}
\newunicodechar{Δ}{\ensuremath{\varDelta}}
\newunicodechar{∋}{\ensuremath{\ni}}
\newunicodechar{μ}{\ensuremath{\mu}}
\newunicodechar{α}{\ensuremath{\alpha}}
\newunicodechar{ρ}{\ensuremath{\rho}}
\newunicodechar{σ}{\ensuremath{\sigma}}
\newunicodechar{τ}{\ensuremath{\tau}}
\newunicodechar{·}{\ensuremath{\mathord\cdotp}}
\newunicodechar{₁}{\ensuremath{_1}}
\newunicodechar{₂}{\ensuremath{_2}}
\newunicodechar{×}{\ensuremath{\times}}
\newunicodechar{ᵈ}{\ensuremath{^d}}
\newunicodechar{ω}{\ensuremath{\omega}}
\newunicodechar{λ}{\ensuremath{\lambda}}
\newunicodechar{▪}{\ensuremath{\blacksquare}}
\newunicodechar{‵}{\ensuremath{\mathord{^\backprime}}}
\newunicodechar{∷}{\ensuremath{::}}
\newunicodechar{∗}{\ensuremath{\mathord\ast}}
\newunicodechar{ℓ}{\ensuremath{\ell}}

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
data _⊢_ : Context → Type → Set where
  `_     : Γ ∋ A → Γ ⊢ A
  ƛ_     : Γ , A ⊢ B → Γ ⊢ A ⇒ B
  _·_    : Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
  `zero  : Γ ⊢ `ℕ
  `suc_  : Γ ⊢ `ℕ → Γ ⊢ `ℕ
  case   : Γ ⊢ `ℕ → Γ ⊢ A → Γ , `ℕ ⊢ A → Γ ⊢ A
  μ_     : Γ , A ⊢ A → Γ ⊢ A
		\end{code}
	}{%
		\begin{code}
data _⊢_ : Context → Type → Set where
  `_     : Γ ∋ A → Γ ⊢ A
  ƛ_     : Γ , A ⊢ B → Γ ⊢ A ⇒ B
  _·_    : Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
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
data _⊢_ : Context → Type → Set where
  `_     : Γ ∋ A → Γ ⊢ A
  ƛ_     : Γ , A ⊢ B → Γ ⊢ A ⇒ B
  _·_    : Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
  `zero  : Γ ⊢ `ℕ
  `suc_  : Γ ⊢ `ℕ → Γ ⊢ `ℕ
  case   : Γ ⊢ `ℕ → Γ ⊢ A → Γ , `ℕ ⊢ A → Γ ⊢ A
  μ_     : Γ , A ⊢ A → Γ ⊢ A
	\end{code}
	}
\end{exampleblock}
\end{frame}

\begin{frame}[fragile]{Motivation}
Scope-safe syntax operations can be defined with the help of intrinsic typing:
	\metroset{block=fill}
	\begin{exampleblock}{Example 2.1.}
		\begin{code}
rename : ∀ {Γ Δ}  → (∀ {A} → Γ ∋  A → Δ ∋  A)
                  → (∀ {A} → Γ ⊢  A → Δ ⊢  A)
rename ρ (` x)          =  ` (ρ x)
rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)
rename ρ (`zero)        =  `zero
rename ρ (`suc M)       =  `suc (rename ρ M)
rename ρ (case L M N)   =  case  (rename ρ L)
                                 (rename ρ M)
                                 (rename (ext ρ) N)
rename ρ (μ N)          =  μ (rename (ext ρ) N)
		\end{code}
	\end{exampleblock}
\end{frame}

\begin{frame}[fragile]{Motivation}
Programmers may change/extend the object language they are interested in:
	\metroset{block=fill}
		\begin{exampleblock}{Example 3, extending example 2.}
		\begin{code}
data _⊢_ : Context → Type → Set where
	...
  con       : ℕ → Γ ⊢ Nat
  _`∗_      : Γ ⊢ Nat → Γ ⊢ Nat → Γ ⊢ Nat
  `let      : Γ ⊢ A → Γ , A ⊢ B → Γ ⊢ B
  `⟨_ , _⟩  : Γ ⊢ A → Γ ⊢ B → Γ ⊢ A `× B
  `proj₁    : Γ ⊢ A `× B → Γ ⊢ A
  `proj₂    : Γ ⊢ A `× B → Γ ⊢ B
  case×     : Γ ⊢ A `× B → Γ , A , B ⊢ C → Γ ⊢ C
		\end{code}
	\end{exampleblock}
\end{frame}

\begin{frame}[fragile]{Motivation}
The syntax operations need to be redefined/extended accordingly:
	\metroset{block=fill}
	\begin{exampleblock}{Example 3.1, extending example 2.1.}
		\begin{code}
rename ρ (con n)        =  con n
rename ρ (M `∗ N)       =  rename ρ M `∗ rename ρ N
rename ρ (`let M N)     =  `let (rename ρ M) (rename (ext ρ) N)
rename ρ `⟨ M , N ⟩     =  `⟨ rename ρ M , rename ρ N ⟩
rename ρ (`proj₁ L)     =  `proj₁ (rename ρ L)
rename ρ (`proj₂ L)     =  `proj₂ (rename ρ L)
rename ρ (case× L M)    =  case×  (rename ρ L)
                                  (rename (ext (ext ρ)) M)
		\end{code}
	\end{exampleblock}
\end{frame}

\begin{frame}[fragile]{Motivation}
All the other operations are to be repeated:
		\begin{code}
subst : ∀ {Γ Δ}  → (∀ {A} → Γ ∋  A → Δ ⊢ A)
                 → (∀ {A} → Γ ⊢  A → Δ ⊢ A)


print : Γ ⊢ A → String


...
		\end{code}
\end{frame}

\begin{frame}[fragile]{Existing work}
  There have been generic libraries providing constructions that can be specialised for a whole family of syntaxes with binders~\footcite{Allais-generic-syntax}\footcite{Fiore-SOAS-Agda}\footcite{Ahrens-typed-abstract-syntax}.

	We take a closer look on Allais et al.\footnotemark[1]'s approach.
\end{frame}

\begin{frame}[fragile]{Existing work by Allais et al.}
	Allais et al. present a universe of syntaxes \mi{Desc},
	\begin{code}
data Desc (I : Set) : Set₁ where
	‘σ  : (A : Set) → (A → Desc I) → Desc I
	‘X  : List I → I → Desc I → Desc I
	‘▪  : I → Desc I
	\end{code}
\end{frame}

\begin{frame}[fragile]{Existing work by Allais et al.}
Simply typed $\uplambda$-calculus
	\begin{code}
data STLC : Type → List Type → Set where
  ‵var : Var σ Γ → STLC σ Γ
  ‵app : STLC (σ ‵→ τ) Γ → STLC σ Γ → STLC τ Γ
  ‵lam : STLC τ (σ ∷ Γ) → STLC (σ ‵→ τ) Γ
	\end{code}
	\pause
can be encoded in \mi{Desc}:
	\metroset{block=fill}
	\begin{exampleblock}{Example 4, description of simply typed $\uplambda$-calculus.}
	\begin{code}
STLC : Desc Type
STLC = σ ‵STLC λ where
  (App  i j) → ‵X [] (i ‵→ j) (‵X [] i (▪ j))
  (Lam  i j) → ‵X (i ∷ []) j (▪ (i ‵→ j))
	\end{code}
	\end{exampleblock}
	\pause
where $‵STLC$ and $Type$ are defined as:
	\begin{multicols}{2}
	\begin{code}
data ‵STLC : Set where
  App Lam : Type → Type → ‵STLC
	\end{code}
	\columnbreak
	\begin{code}
data Type : Set where
  α     : Type
  _‵→_  : Type → Type → Type
	\end{code}
	\end{multicols}

\end{frame}

\begin{frame}[fragile]{Existing work by Allais et al.}
	Generic programs are defined as \mi{Semantics} records.

	A generic program, defined on the fixpoint constructor \mi{Tm}, is realized via \mi{semantics}.
	\metroset{block=fill}
	\begin{exampleblock}{Example 5, generic rename function.}
	\begin{code}
Renaming : ∀ {d : Desc I} → Semantics d Var (Tm d)

rename : ∀ {d : Desc I} → (∀ {i} → Var i Γ → Var i Δ)
                  → Tm d j Γ
                  → Tm d j Δ
rename ρ t = semantics Renaming ρ t
	\end{code}
	\end{exampleblock}
\mi{rename} is generic as it can be applied to fixpoints of any description (e.g. $\mi{Tm}\ \mi{STLC}$).
\end{frame}

\begin{frame}[fragile]{Motivation cont.}
	The problems with applying standard datatype-generic programming to syntax-generic operations are:
	\begin{enumerate}
		\item datatype/function definitions are non-intuitive (no more beautiful typing rules \& IDE supports!),
		\item requiring the programmer to understand the syntax universe, and
		\item interoperability: difficult (if not impossible) to work with existing libraries or other generic libraries.
	\end{enumerate}
\end{frame}

\begin{frame}[fragile]{Motivation cont.}
	Programmers prefer syntaxes and operations as natural datatypes and functions,
\end{frame}

\section{Elaborator Reflection to the Rescue}

\begin{frame}[fragile]{Elaborator Reflection to the Rescue}
	In our published work at ICFP, we have provided:
	\begin{itemize}
		\item a description \mi{DataD} generic enough for any Agda's inductive datatypes,
		\item generic program descriptions \mi{FoldP} for folds (and \mi{IndP} for inductions),
		\item a metaprogram \mi{genDataD} that generates datatype descriptions from their native definitions, and 
		\item a metaprogram \mi{defineFold} that generates function definitions from their generic representations.
	\end{itemize}
\end{frame}

\begin{frame}[fragile]{Motivation cont.}
	We define:
	\begin{itemize}
		\item a predicate \mi{Syntax} on \mi{DataD} that captures a subset equivalent to \mi{Desc}.
		\item a function \mi{SemP} that generates descriptions (typed \mi{FoldP}) of generic fold operations, given proofs of the predicate.
	\end{itemize}
\end{frame}

\begin{frame}[fragile]{Flow Chart}
\includegraphics[width=\columnwidth]{Diagram.pdf}
\end{frame}

\begin{frame}[fragile]{The \mi{Syntax} Predicate}
\mi{Syntax}, a predicate on \mi{DataD}, captures datatypes that are syntaxes in \mi{Desc}.
	\begin{code}
Syntaxᵈ : Set ℓ → DataD → Setω
	\end{code}
\end{frame}

\begin{frame}[fragile]{The \mi{Syntax} Predicate}
Let's specify what syntaxes are captured by \mi{Desc}:
	\begin{itemize}
		\item each of them has a variable rule as its first rule,
		\item they are not universe polymorphic,
		\item each have two indices, $I$ and $\mi{List}\ I$, and
		\item allow and only allow context extensions in subterms.
	\end{itemize}
There's a catch: \mi{DataD} satisfying \mi{Syntax} is not isomorphic to \mi{Desc}!
\end{frame}

\begin{frame}[fragile]{The \mi{Syntax} Predicate}
Does \mi{PCF} satisfies \mi{Syntax}?
	\begin{code}
data PCF : Type → List Type → Set where
  ‵var   : Var σ Γ → PCF σ Γ
  ‵app   : PCF (σ ‵→ τ) Γ → PCF σ Γ → PCF τ Γ
  ‵lam   : PCF τ (σ ∷ Γ)  → PCF (σ ‵→ τ) Γ
  ‵zero  : PCF ‵ℕ Γ
  ‵suc_  : PCF ‵ℕ Γ → PCF ‵ℕ Γ
	\end{code}
\end{frame}

\begin{frame}[fragile]{The Syntax Predicate}
	\metroset{block=fill}
	\begin{exampleblock}{A Syntax proof example}
		\begin{code}
SyntaxPCF : Syntaxᵈ Type (genDataD (quote PCF))
SyntaxPCF = _
        , refl
        , (refl ,refl)
        , _
        , refl
        , refl
        , (_ , _ , _ , refl , (λ _ → refl))
        , (_ , _ , _ , refl , (λ _ → refl))
        , (_ , _ , _ , refl , (λ _ → refl))
        , (_ , _ , _ , refl , (λ _ → refl))
        , tt
		\end{code}
	\end{exampleblock}
	\mi{Syntax} proofs in this case are amenable to be generated with elaborator reflection.
\end{frame}

% \begin{frame}[fragile]{Translation from Semantics to natural looking functions}
% \end{frame}

\section{Demo}

\section{Discussion}

\begin{frame}[fragile]{Towards datatype-generic libraries for syntaxes?}
\end{frame}

\end{document}

