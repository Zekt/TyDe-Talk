\documentclass[10pt,xcolor=svgnames,aspectratio=169,notesonly]{beamer} %Beamer
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
\usepackage[Symbol]{upgreek}
\usepackage{newtxmath}
\usepackage{multicol}
\usepackage[style=authortitle,backend=biber]{biblatex}
\addbibresource{bib.bib}
\usepackage[greek,english]{babel}
\usepackage{newunicodechar}
\usepackage{xcolor}
% \usepackage{polytable}


\newcommand{\themename}{\textbf{\textsc{bluetemp}\xspace}}%metropolis}}\xspace}

\newcommand{\awa}[2]{\mathrlap{#2}\phantom{#1}} % as wide as
\newcommand{\aha}[2]{\smash{\parbox{\linewidth}{#2}}\phantom{\parbox{\linewidth}{#1}}} % as high as
\newcommand{\parl}[1]{\parbox{\linewidth}{#1}} % as high as

\newcommand{\mi}[1]{\ensuremath{\mathit{#1}}}

\newunicodechar{→}{\ensuremath{\mathord{\rightarrow}}}
\newunicodechar{⇒}{\ensuremath{\mathord\Rightarrow}}
\newunicodechar{⊢}{\ensuremath{\mathord\vdash}}
\newunicodechar{⊨}{\ensuremath{\mathord\vDash}}
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
\newunicodechar{∅}{\ensuremath{\emptyset}}


%include polycode.fmt

\title{Syntax-Generic Operations, Reflectively Reified}
\author[Name]{Tzu-Chi Lin and Josh Ko} %With inst, you can change the institution they belong
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

\note{Hello everyone, my name is Tzu-Chi, I am a research assistant at Academia Sinica in Taiwan.
Today I will be talking about the joint work of my advisor's and mine, the title is "Syntax-generic Operations, Reflectively Reified". So firstly we will see what are syntax-generic operations, then I will elaborate on what Reflectively reified means.}

% \begin{frame}[fragile]{Outline}
% \setbeamertemplate{section in toc}[sections numbered] %This is numbering the sections
% \tableofcontents[hideallsubsections] %You can comment this line if you want to show the subsections in the table of contents
% \end{frame}

%\note{Firstly, I will introduce some backgrounds and our motivations, including the existing work we base on. In general, we apply the techniques we introduced in our another work, "Datatype-Generic Programming Meets Elaborator Reflection", which Josh will present on Tuesday. We apply the techniques in that work on a common problem for depentely typed programmers. I will show you a demo if we have time, and most importantly, we want to know your opinions on it. Is this a better approach? Will you want to use it? Hopefully we can get some feedbacks after this talk.}


\begin{frame}[fragile]{Typical Languages in Languages}
\emph{Intrinsic typing} is common for $\uplambda$-calculus with De Bruijn indices.
	% \aha{%
	% 	\begin{code}
	% data _⊢_ : Context → Type → Set where
  % ‵_     : Γ ∋ A → Γ ⊢ A
  % ƛ_     : Γ , A ⊢ B → Γ ⊢ A ⇒ B
  % _·_    : Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
  % ‵zero  : Γ ⊢ ‵ℕ
  % ‵suc_  : Γ ⊢ ‵ℕ → Γ ⊢ ‵ℕ
  % case   : Γ ⊢ ‵ℕ → Γ ⊢ A → Γ , ‵ℕ ⊢ A → Γ ⊢ A
  % μ_     : Γ , A ⊢ A → Γ ⊢ A
	% 	\end{code}
	% }{%
		\begin{columns}[T]
			\begin{column}{0.6\textwidth}
				\begin{code}
data _⊢_ : Context → Ty → Set where
  ‵_     : Γ ∋ A → Γ ⊢ A
  ƛ_     : Γ , A ⊢ B → Γ ⊢ A ⇒ B
  _·_    : Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
				\end{code}
			\end{column}
			\begin{column}{0.6\textwidth}
				\begin{code}
data Ty : Set where
  α    : Ty
  _⇒_  : Ty → Ty → Ty

data Context (A : Set) : Set where
  ∅    : Context A
  _,_  : (Γ : Context A) → A → Context A

data _∋_ : Context → Ty → Set where
  z : Γ , A ∋ A
  s : Γ ∋ A → Γ , B ∋ A
				\end{code}
			\end{column}
		\end{columns}
	% }
\end{frame}

\note{For starters, Let's take a look at a common thing dependently typed programmers would do, that is defining a programming language in a dependently typed programming language, such as Agda. Here is an example of the syntax of a language defined in Agda. It's a simply-typed lambda calculus. We define a datatype called Ty to describe the possible types for this language, a term has either a single type or a function type. Here \mi{Context} is defined as the List of Ty. And we have a simple ``has'' relation that represents variables. For if a variable is typed it must be in the context. And we know that a simply typed lambda calculus has three constructions, each corresponding a a typing rule. Here are three constructors, each of them corresponds to the variable rule, the abstraction rule, and the application rule. We can see for a term to be constructed, it must be well-typed by definition, that's what we call intrinsic typing.}

\begin{frame}
Scope-safe syntax operations:
	\begin{code}
rename : ∀ {Γ Δ}  → (∀ {A} → Γ ∋  A → Δ ∋  A)
                  → (∀ {A} → Γ ⊢  A → Δ ⊢  A)
rename ρ (‵ x)    =  ‵ (ρ x)
rename ρ (ƛ N)    =  ƛ (rename (ext ρ) N)
rename ρ (L · M)  =  (rename ρ L) · (rename ρ M)
	\end{code}
\end{frame}

\note{Then let's define some operations on this syntax. Again, because of intrinsic typing, such operations are scope-safe. For example, a \mi{rename} function says that if there's a mapping from every variable in a context $\varGamma$ to the other context $\varDelta$, we can always find a mapping from every term that is typed in $\varGamma$ to a term typed in $\varDelta$. Because we can remap every variable in that term. If we encounter a subterm that has a extended context, for example, the case of lambda abstraction, the variable mapping should be extended accordingly. We can see that rename is still called recursively, but the variable mapping function is modified with ext.}

\begin{frame}[fragile]{Motivation}
\emph{Intrinsic typing} is common for $\uplambda$-calculus with De Bruijn indices.
	\parl{
	\begin{code}
data Ty : Set where
  ...
  ‵ℕ : Ty

data _⊢_ : Context → Ty → Set where
  ...
  ‵zero  : Γ ⊢ ‵ℕ
  ‵suc_  : Γ ⊢ ‵ℕ → Γ ⊢ ‵ℕ
  case   : Γ ⊢ ‵ℕ → Γ ⊢ A → Γ , ‵ℕ ⊢ A → Γ ⊢ A
  μ_     : Γ , A ⊢ A → Γ ⊢ A
	\end{code}
	}
\end{frame}

\note{Now what if we extend the language? we might want natural number primitives in our language, so we extend the Ty datatype with a new type, we add four typing rules, two of them, zero and suc are for constructing natural numbers, and another two rules are for branching and recursion.}

\begin{frame}[fragile]{Motivation}
		\begin{code}
rename : ∀ {Γ Δ}  → (∀ {A} → Γ ∋  A → Δ ∋  A)
                  → (∀ {A} → Γ ⊢  A → Δ ⊢  A)
...
rename ρ (‵zero)        =  ‵zero
rename ρ (‵suc M)       =  ‵suc (rename ρ M)
rename ρ (case L M N)   =  case  (rename ρ L)
                                 (rename ρ M)
                                 (rename (ext ρ) N)
rename ρ (μ N)          =  μ (rename (ext ρ) N)
		\end{code}
\end{frame}

\note{If we want a rename function for this extended language, we can copy and paste the rename we just defined and add a new clause for each constructor. The patterns still follow, a renaming always take a term from a constructor to one with the same constructor, if encounter subterm, call rename recursively, if there's context extension, extend the variable mapping as well. So no matter how many constructors there are we follow the same logic.}

\begin{frame}[fragile]{Motivation}
Change/extend the object language even further:
		\begin{code}
data _⊢_ : Context → Ty → Set where
	...
  con       : ℕ → Γ ⊢ Nat
  _‵∗_      : Γ ⊢ Nat → Γ ⊢ Nat → Γ ⊢ Nat
  ‵let      : Γ ⊢ A → Γ , A ⊢ B → Γ ⊢ B
  ‵⟨_ , _⟩  : Γ ⊢ A → Γ ⊢ B → Γ ⊢ A ‵× B
  ‵proj₁    : Γ ⊢ A ‵× B → Γ ⊢ A
  ‵proj₂    : Γ ⊢ A ‵× B → Γ ⊢ B
  case×     : Γ ⊢ A ‵× B → Γ , A , B ⊢ C → Γ ⊢ C
		\end{code}
\end{frame}

\note{What if we extend the language even further? Here we add even more rules. syntax sugaring, pairs and projections, etc.}

\begin{frame}[fragile]{Motivation}
Redefine/extend syntax operations:
		\begin{code}
...
rename ρ (con n)        =  con n
rename ρ (M ‵∗ N)       =  rename ρ M ‵∗ rename ρ N
rename ρ (‵let M N)     =  ‵let (rename ρ M) (rename (ext ρ) N)
rename ρ ‵⟨ M , N ⟩     =  ‵⟨ rename ρ M , rename ρ N ⟩
rename ρ (‵proj₁ L)     =  ‵proj₁ (rename ρ L)
rename ρ (‵proj₂ L)     =  ‵proj₂ (rename ρ L)
rename ρ (case× L M)    =  case×  (rename ρ L)
                                  (rename (ext (ext ρ)) M)
		\end{code}
\end{frame}

\note{The \mi{rename} function must be extended as well, so everytime we make some changes to the object language, it becomes a very repeating work.}

\begin{frame}[fragile]{Motivation}
Other repeating operations:
		\begin{code}
subst : ∀ {Γ Δ}  → (∀ {A} → Γ ∋  A → Δ ⊢ A)
                 → (∀ {A} → Γ ⊢  A → Δ ⊢ A)


print : Γ ⊢ A → String


...
		\end{code}
\end{frame}

\note{There are other repeating operations that should be redefined for every change in the object language, you probaly would want some kind of generic programs that work for every syntax, or a mechanism that generates these operatoins from any given datatypes of this kind.}

\begin{frame}{Where we are going...}
\setbeamertemplate{section in toc}[sections numbered] %This is numbering the sections
\tableofcontents[hideallsubsections] %You can comment this line if you want to show the subsections in the table of contents
\end{frame}

\note{Now we know the problem we are dealing with. In the next section, I will introduce an existing work that eliminates the repetitions we just mentioned. After that I will illustrate how we develope an alternative approach based on this previous work, by incorporating elaborator reflection. We will make some comparisons along the way, and finally we raise some questions regarding our own work, and hopefully get some feedbacks from you.}

\section{Existing Work for Syntax-generic Operations}
\note{Let's start with the existing work.}

\begin{frame}[fragile]{Existing work}
There are generic libraries for a family/families of syntaxes with binders.

We improve upon Allais et al.'s approach presented at ICFP '18 (later published in JFP '21).
\end{frame}

\note{There have been some libraries that provide generic operations for the problem we introduced. Those programs are syntax-generic, that's the first part of our title. We focus on one of such works, that is the generic library by Allais et al. They have developed a framework with a variety of syntax-generic operations, such as renaming, subsitution, printing and scope checking.}

\begin{frame}[fragile]{Existing work by Allais et al.}
	Allais et al.'s \mi{Desc}:
	\begin{code}
data Desc (I : Set) : Set₁ where
	‵σ  : (A : Set) → (A → Desc I) → Desc I
	‵X  : List I → I → Desc I → Desc I
	‵▪  : I → Desc I
	\end{code}
	\hrulefill
	\begin{code}
data ‵STLC : Set where
  App Lam : Ty → Ty → ‵STLC

STLCD : Desc Ty
STLCD = ‵σ ‵STLC λ where
  (App  i j) →
    ‵X [] (i ⇒ j) (‵X [] i (▪ j))
  (Lam  i j) →
    ‵X (i ∷ []) j (▪ (i ⇒ j))
	\end{code}
\end{frame}

\note{How do they achieve it? They provide a universe of descriptions called Desc that describes a family of syntaxes. We won't go into its details here, but we can say that every inhabitant in this universe represents a syntax, and simply-typed lambda calculus is one of them. The parameter I in the Desc universe says that a syntax is intrinsically typed by I and has a context of List of I. So simply-typed lambda calculus can be encoded in the universe Desc}

\begin{frame}[fragile]{Existing work by Allais et al.}
\begin{columns}[T]
\begin{column}{0.5\textwidth}
Simply typed $\uplambda$-calculus
	\begin{code}
data _⊢_ : Context → Ty → Set where
  ‵_   : Γ ∋ A → Γ ⊢ A
  ƛ_   : Γ , A ⊢ B → Γ ⊢ A ⇒ B
  _·_  : Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
	\end{code}
\end{column}
\begin{column}{0.5\textwidth}
	\pause
encoded in \mi{Desc}:
	\begin{code}
STLCD : Desc Ty
STLCD = ‵σ ‵STLC λ where
  (App  i j) →
    ‵X [] (i ⇒ j) (‵X [] i (▪ j))
  (Lam  i j) →
    ‵X (i ∷ []) j (▪ (i ⇒ j))
	\end{code}
	\pause
	\begin{code}
STLC' = Tm STLCD
	\end{code}
\end{column}
\end{columns}
\pause
$$\mi{\_⊢\_} \cong \mi{STLC'}$$
\end{frame}

\note{A simply-typed lambda calculus here on the left hand side has just been rewritten as a description on the right hand side. In fact, to use such generic libraries, programmers must encode their syntax in the given description, because syntax-generic operations are defined on these descriptions. To acquire something structurally similar to the native symtax datatype, we can use the \mi{Tm} type constructor, which takes the fixpoint of the functor of a description. We may prove that a syntax defined as a isolated datatype is isomorphic to the fixpoint of such functor.}

% \begin{frame}[fragile]{Existing work by Allais et al.}
% 	\begin{code}
% STLC : Desc Ty
% STLC = σ ‵STLC λ where
%   (App  i j) → ‵X [] (i ⇒ j) (‵X [] i (▪ j))
%   (Lam  i j) → ‵X (i ∷ []) j (▪ (i ⇒ j))
% 	\end{code}
% \end{frame}

\begin{frame}[fragile]{Generic Functions for the Whole Universe}
	\begin{code}
Var σ Γ = Γ ∋ σ

Renaming : ∀ {d : Desc I} → Semantics d Var (Tm d)

rename : ∀ {d : Desc I} → (∀ {σ}  → Var σ Γ   → Var σ Δ)
                           ∀ {τ}  → Tm d τ Γ  → Tm d τ Δ
rename = semantics Renaming
	\end{code}
\pause
Generic programs are \mi{Semantics} records.
\pause

Functions are realized on fixpoints \mi{Tm} via \mi{semantics}.
\pause

\mi{rename} can be applied to fixpoints of any description (e.g. $\mi{Tm}\ \mi{STLCD}$).
\end{frame}

\note{With such a universe, Allais they can and have defined some generic functions that work for a whole family of syntaxes. For example, they have defined a generic renaming function. A semantics datatype with the upper case S is a description of a generic function given a syntax description d. You can see Renaming here is generic as it's quantified over d. The sementics function with lower case S is used to obtain the actual generic rename function, we can see for every description d, this function works on Tm d. It essentially says that there's a rename for every given d, and of course there's a rename for the description of simply-typed lambda calculus.}

% \begin{frame}[fragile]{Motivation cont.}
% 	Programmers prefer ``natural'' datatype and functions,
% 	\aha{
% 		\begin{code}
% rename : ∀ {Γ Δ}  → (∀ {A} → Γ ∋  A → Δ ∋  A)
%                   → (∀ {A} → Γ ⊢  A → Δ ⊢  A)
% rename ρ (‵ x)          =  ‵ (ρ x)
% rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
% rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)
% 
% Renaming : Semantics Var Lam
% Renaming = record
%   { th^V  = th^Var
%   ; var   = ‘var
%   ; app   = ‘app
%   ; lam   = λ b → ‘lam (b weaken z) }
% rename = semantics Renaming
% 		\end{code}
% 	}{
% 		\begin{code}
% data _⊢_ : Context → Ty → Set where
%   ‵_     : Γ ∋ A → Γ ⊢ A
%   ƛ_     : Γ , A ⊢ B → Γ ⊢ A ⇒ B
%   _·_    : Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
% 		\end{code}
% 	\begin{code}
% STLC : Desc Ty
% STLC = σ ‵STLC λ where
%   (App  i j) → ‵X [] (i ⇒ j) (‵X [] i (▪ j))
%   (Lam  i j) → ‵X (i ∷ []) j (▪ (i ⇒ j))
% 	\end{code}
% 	}
% \end{frame}

% \begin{frame}[fragile]{Motivation cont.}
% 	\begin{columns}[T]
% 		\begin{column}{0.5\textwidth}
% 		``Natural'' function:
% 		\begin{code}
% rename : ∀ {Γ Δ}
%        → (∀ {A} → Γ ∋  A → Δ ∋  A)
%        → (∀ {A} → Γ ⊢  A → Δ ⊢  A)
% rename ρ (‵ x)          =  ‵ (ρ x)
% rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
% rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)
% 		\end{code}
% 		\end{column}
% 
% 		\begin{column}{0.5\textwidth}
% 		Generic function:
% 		\begin{code}
% Renaming : Semantics Var Lam
% Renaming = record
%   { th^V  = th^Var
%   ; var   = ‘var
%   ; app   = ‘app
%   ; lam   = λ b → ‘lam (b weaken z) }
% rename = semantics Renaming
% 		\end{code}
% 		\end{column}
% 	\end{columns}
% \end{frame}
% 
% \note{We think that one of the reasons these generic libraries are not widely adopted is because the definitions are not intuitive. Here is a comparison, we think function definitions on the left is more popular and have better properties for programming language researchers. }

\begin{frame}[fragile]{Problems with Syntax Universes: Readability}
\begin{columns}[T]
\begin{column}{0.5\textwidth}
	\begin{code}
data _⊢_ : Context → Ty → Set where
  ‵_   : Γ ∋ A → Γ ⊢ A
  ƛ_   : Γ , A ⊢ B → Γ ⊢ A ⇒ B
  _·_  : Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
	\end{code}
\end{column}
\begin{column}{0.5\textwidth}
	\begin{code}
STLCD : Desc Ty
STLCD = ‵σ ‵STLC λ where
  (App  i j) →
    ‵X [] (i ⇒ j) (‵X [] i (▪ j))
  (Lam  i j) →
    ‵X (i ∷ []) j (▪ (i ⇒ j))

STLC' = Tm STLCD
	\end{code}
\end{column}
\end{columns}
\end{frame}

\note{We quickly summerize what we think are the reasons these libraries are not widely adopted. First of all is readability. One good thing about of intrinsic typing is that types of constructors closely resemble typing rules, and typing rules are less obvious for syntaxes defined in generic universes.}

\begin{frame}[fragile]{Problems with Syntax Universes: Burden on Programmers}
	\begin{code}
data Desc (I : Set) : Set₁ where
	‵σ  : (A : Set) → (A → Desc I) → Desc I
	‵X  : List I → I → Desc I → Desc I
	‵▪  : I → Desc I
	\end{code}
\end{frame}

\note{Secondly, to utilize such generic libraries, programmers are required to understand the generic universe instead of just defining syntaxes the way they want. }

\begin{frame}[fragile]{Problems with Syntax Universes: Interoperability}
	\begin{code}
STLCD : Desc Ty
STLCD = ...

STLCD' : Desc' ???
STLCD' = ???
	\end{code}
\end{frame}

\note{And they need to learn a new generic representation everytime they want some features that only exist in another generic library, the syntax they are working on must be redefined. This leads us to te third problem, interoperability. It would be hard to use two or more generic libraries at once.}

% \begin{frame}[fragile]{Problems with Syntax Universes: Interoperability}
% \begin{columns}[T]
% 	\begin{column}{0.4\textwidth}
% 		\begin{code}
% f : Γ ⊢ A → ℕ
% f t = {! | !}
% 		\end{code}
% Ctrl + C $\downarrow$
% 	\pause
% 		\begin{code}
% f : Γ ⊢ A → ℕ
% f (‵ x)    =  {!    !}
% f (ƛ N)    =  {!    !}
% f (L · M)  =  {! |  !}
% 		\end{code}
% 	\end{column}
% 	\pause
% 	\begin{column}{0.4\textwidth}
% 	\begin{code}
% f : Tm d τ Γ → ℕ
% f t = {! | !}
% 	\end{code}
% Ctrl + C $\downarrow$
% 	\begin{code}
% ???
% 	\end{code}
% 	\end{column}
% \end{columns}
% \end{frame}
% 
% \note{The interoperability problem also exists with existing tools, for example, because every typing rule corresponds to one constructor, we can utilize the case-spliting mechanism provided by Agda's editor mode, by placing te cursor in th hole of f, and press Ctrl and C in the Emacs or VS Code editor, we can easily see how many clauses we should define for a function that takes a natural term. We can't benefit from these tools or existing IDE supports when using generic universes, case spliting on Tm would work, but it will look like a mess.}

\section{Elaborator Reflection to the Rescue}

\note{Therefore, we want the best from both worlds, we want programmers and researchers to use native definitions whenever possible, while generic programs can still be invoked. We acheive this by elaborator reflection. Elaborator reflection is the metaprogramming mechanism provided by Agda, it allows us to read and define datatype and function definitions.}

\begin{frame}[fragile]{Elaborator Reflection to the Rescue}
	``Datatype-Generic Programming Meets Elaborator Reflection'' by Josh Ko, Liang-Ting Chen, and Tzu-Chi Lin
	at 15:50, Tuesday.

	\pause

	Syntax-generic operations \emph{are} Datatype-generic programs with constraints.
\end{frame}

\note{I would like to shamelessly promote the other work we are presenting at ICFP, Datatype-Generic Programming Meets Elaborator Reflection. My advisor Josh will present it on Tuesday. We have demostrated in that work that we can define programs on a family of datatypes with our program description, while using elaborator reflection to reify such programs as natural function definitions defined on native datatypes. What does this have to do with syntax-generic libraries that we spent so much time intorducing? It turns out, syntax-generic programs sometimes datatype-generic programs. We can constrain a subset of all datatypes such that datatypes in this subset are also describable bya generic universe, in this case Allais their library.}

\begin{frame}[fragile]{The process}
	\begin{enumerate}
		\item The programmer defines a native datatype $T$.
		\pause
		\item A metaprogram generates the description $D$ of $T$.
		\pause
		\item The programmer chooses a description $P$ from a set of pre-defined generic programs.
		\pause
		\item A metaprogram takes $D$ and $P$, generates a native function accordingly.
	\end{enumerate}
\end{frame}

\note{Now let us skip the introduction of datatype-generic programming and metaprograms. To get the whole picture, let's do a rundown of our alternative process for a programmer to invoke generic programs. Firstly they define a native datatype T that we know to be a syntax, instead of relying on any generic description. Then by metaprograms in our datatype-generic library, they get the datatype description D of T. Then the programmer can choose a generic program P to reify. This generic program is pre-defined by the geneic library. Lastly, another metaprogram takes $D$ and $P$, and gives the programmer a native, reifed funtion definition that works on $S$, as if everything is defined by hands.}

\begin{frame}[fragile]{The process}
	\begin{enumerate}
		\item The programmer defines a native datatype $T$.
		\item A metaprogram generates the description $D$ of $T$.
		\item {\color{red} The programmer provides a proof $S$ of $D$ that says $T$ is indeed a syntax.}
		\item The programmer chooses a description $P$ from a set of pre-defined generic programs.
		\item A metaprogram takes $D$, {\color{red} $S$}, and $P$, generates a native function accordingly.
	\end{enumerate}
\end{frame}

\note{But this process is actually not sufficient, how does the generic library know S is a syntax? To pre-define a datatype-generic program that work specifically on a family of syntax, we must also pre-define a predicate that says a datatype is indeed a syntax. So the geneic library should also provide predicates that constrain general datatypes, saying they are syntaxes. And the programmer must provide a proof of this predicate when choosing a generic program to reify. So the process we just showed actually requires an extra step, that is the programmer providing a proof of the datatype $T$ being a syntax.}

\begin{frame}[fragile]{Flow Chart}
\includegraphics[width=\columnwidth]{Diagram1.pdf}
\end{frame}

\note{Let's do a rundown again, but with our actual definitions. We have three worlds here, the user's own world, the syntax-datatype-generic library, and metaprograms. Say the user defines a language called Lam, indexed by the type and context of a term.}

\begin{frame}[fragile]{Flow Chart}
\includegraphics[width=\columnwidth]{Diagram2.pdf}
\end{frame}

\note{They can invoke a metaprogram genDataD, which generates a datatype description of type DataD, we call it LamD.}

\begin{frame}[fragile]{Flow Chart}
\includegraphics[width=\columnwidth]{Diagram3.pdf}
\end{frame}

\note{Then to use the generic library, the user must provide a proof that the description we just generated is syntax. Here Syntax is the predicate, and we call the proof LamSyn.}

\begin{frame}[fragile]{Flow Chart}
\includegraphics[width=\columnwidth]{Diagram4.pdf}
\end{frame}

\note{Then it's the job for the generic library. Renaming here is a function that generates syntax-generic programs. Syntax-generic programs are represented as Semantics.}

\begin{frame}[fragile]{Flow Chart}
\includegraphics[width=\columnwidth]{Diagram5.pdf}
\end{frame}

\note{But our metaprograms that generates native functions are for datatype-generic programs. so we need another translation in the generic library that is from syntax-generic programs to datatype-generic programs. SemP is this translation and FoldP is the type of datatype-generic fold programs.}

\begin{frame}[fragile]{Flow Chart}
\includegraphics[width=\columnwidth]{Diagram6.pdf}
\end{frame}

\note{Finally, defineFold is a metaprogram that generates actual function definitions. So the user doesn't need to understand the detailed definitions in the generic libary, they can write native datatype and get native function definitions if they know what metaprograms and functions to call.}

\begin{frame}[fragile]{Some of Our Contributions}
In ``Datatype-generic Programming Meets Elaborator Reflection'':
	\begin{itemize}
		\item \mi{DataD}
		\item \mi{FoldP} for folds (and \mi{IndP} for inductions)
		\item metaprogram \mi{genDataD}
		\item metaprogram \mi{defineFold}
	\end{itemize}
\pause
In this work:
	\begin{itemize}
		\item predicate \mi{Syntax} on \mi{DataD} that captures \mi{Desc}.
		\item function \mi{SemP} that generates \mi{FoldP} from \mi{Syntax} proofs.
	\end{itemize}
\end{frame}

\note{The datatype and program descriptions are provided by our other work we mentioned, so are the metaprograms. In this work we provide the Syntax predicate and the translations built arount it.}


\begin{frame}[fragile]{The \mi{Syntax} Predicate}
	\begin{code}
Syntax : Set ℓ → DataD → Setω
	\end{code}
\mi{Desc} are captured by \mi{Syntax} as each:
	\pause
	\begin{itemize}
		\item has a variable rule,
		\pause
		\item is not universe polymorphic,
		\pause
		\item has two indices, $I$ and $\mi{List}\ I$, and
		\pause
		\item supports context extensions.
	\end{itemize}
\end{frame}

\note{Unfortunately our time is limited, we can't go into the details of the Syntax predicate.}


\begin{frame}[fragile]{The \mi{Syntax} Predicate}
\begin{columns}[T]
	\begin{column}{0.5\textwidth}
Does \mi{PCF} satisfies \mi{Syntax}?
	\begin{code}
data PCF : Ty → Context → Set where
  ‵var   : Var σ Γ → PCF σ Γ
  ‵app   : PCF (σ ⇒ τ) Γ → PCF σ Γ → PCF τ Γ
  ‵lam   : PCF τ (σ ∷ Γ)  → PCF (σ ⇒ τ) Γ
  ‵zero  : PCF ‵ℕ Γ
  ‵suc_  : PCF ‵ℕ Γ → PCF ‵ℕ Γ
	\end{code}
	\end{column}
	\pause
	\begin{column}{0.5\textwidth}
	Proof of PCF being Syntax:
		\begin{code}
SyntaxPCF : Syntax Ty (genDataD PCF)
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
	\end{column}
\end{columns}
\end{frame}

\note{We were worried that the Syntax proof might be too complicated, because if it's too complicated it would not save any efforts and nobody would want to use it. Fortunately in this case it's pretty straightforward. Suppose we define a language PCF, which has five constructors. For this PCF datatype to be a syntax, a lot of things has to be considered, like the datatype's universe level, numbers of parameters and indices, and constraints on each field of each constructor. In this case the parameters must be empty and there must be exactly two indices, a type and a list of type. It turns out most of these are equality proofs, and if the datatype truely is a syntax, these can be proved by simply using the refl constructor. Proofs of any datatypes being syntaxes look pretty much the same, so it is possible to write yet another metaprogram for generating such proofs. Which is a future work we haven't done yet.}

% \begin{frame}[fragile]{Translation from Semantics to natural looking functions}
% \end{frame}

\section{Discussion}

\begin{frame}[fragile]{Towards Datatype-generic Libraries for Syntaxes?}
		% \item Expressiveness is limited by Agda datatypes as well as the generic universe, a \mi{Syntax} predicate must be defined.
		% \pause
		% \item Even if we can define \mi{Syntax}, the proof could be more complicated, even require programmers to understand the generic universe.
		% \pause
		% \item Obstacles of using multiple generic libraries at once.
		% \pause
		% \item Are folds and inductions enough?
		Do we really need syntax-generic libraries?
\end{frame}

\note{As you can see, our work has a lot to be done. Since we are running out of time, I would like to address one issue that's probably the elephant in the room. What if people actually don't want syntax-generic operations at all? Maybe they only define a language once in a while, and it's not worth the time looking up what libraries they can use. Or, since researchers define languages with new features all the time, maybe it's common for them to come up something no generic universes can cover. Our framework could still be help in that case, maybe our metaprograms can analyse the constructors in a datatype and determine which of them fit in a universe, and generate functions that are partially defined, then leave the uncertain parts to the programmer. So what do you think about it? Please share with us your conerns or what you think this framework can be going. Thank you all for listening.}

\end{document}

