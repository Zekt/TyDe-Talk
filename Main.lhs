\documentclass[10pt,xcolor=svgnames,aspectratio=169,notes]{beamer} %Beamer
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

\note{Hello everyone, my name is Tzu-Chi, I am a research assistant from Academia Sinica in Taiwan.
Today I will be talking about the joint work of my advisor's am mine, it's "Syntax-generic Operations, Reflectively Reified".}

\begin{frame}[fragile]{Outline}
\setbeamertemplate{section in toc}[sections numbered] %This is numbering the sections
\tableofcontents[hideallsubsections] %You can comment this line if you want to show the subsections in the table of contents
\end{frame}

\note{Firstly, I will introduce some backgrounds and our motivations, including the existing work we base on. In general, we apply the techniques we introduced in our another work, "Datatype-Generic Programming Meets Elaborator Reflection", which Josh will present on Tuesday. We apply the techniques in that work on a common problem for depentely typed programmers. I will show you a demo if we have time, and most importantly, we want to know your opinions on it.}

\section{Introduction}

\note{Let's start!}

\begin{frame}[fragile]{Motivation}
\emph{Intrinsic typing} is common for $\uplambda$-calculus with De Bruijn indices.
	\aha{%
		\begin{code}
data _⊢_ : Context → Type → Set where
  ‵_     : Γ ∋ A → Γ ⊢ A
  ƛ_     : Γ , A ⊢ B → Γ ⊢ A ⇒ B
  _·_    : Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
  ‵zero  : Γ ⊢ ‵ℕ
  ‵suc_  : Γ ⊢ ‵ℕ → Γ ⊢ ‵ℕ
  case   : Γ ⊢ ‵ℕ → Γ ⊢ A → Γ , ‵ℕ ⊢ A → Γ ⊢ A
  μ_     : Γ , A ⊢ A → Γ ⊢ A
		\end{code}
	}{%
		\begin{code}
data Type : Set where
  α    : Type
  _⇒_  : Type → Type → Type

data _⊢_ : Context → Type → Set where
  ‵_     : Γ ∋ A → Γ ⊢ A
  ƛ_     : Γ , A ⊢ B → Γ ⊢ A ⇒ B
  _·_    : Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
		\end{code}
	}
\end{frame}

\note{Here is an example of a language defined in Agda. It's simply-typed lambda calculus, and with the help of intrinsic typing, the syntax definition is very concise. Here \mi{Context} is List of Type. There are three constructors, each corresponding to the variable, abstraction, and application rule.}

\begin{frame}[fragile]{Motivation}
\emph{Intrinsic typing} is common for $\uplambda$-calculus with De Bruijn indices.
	\parl{
	\begin{code}
data _⊢_ : Context → Type → Set where
  ‵_     : Γ ∋ A → Γ ⊢ A
  ƛ_     : Γ , A ⊢ B → Γ ⊢ A ⇒ B
  _·_    : Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
  ‵zero  : Γ ⊢ ‵ℕ
  ‵suc_  : Γ ⊢ ‵ℕ → Γ ⊢ ‵ℕ
  case   : Γ ⊢ ‵ℕ → Γ ⊢ A → Γ , ‵ℕ ⊢ A → Γ ⊢ A
  μ_     : Γ , A ⊢ A → Γ ⊢ A
	\end{code}
	}
\end{frame}

\note{Let's extend the example, we might want natural number primitives in our language, so we extend the Type datatype, we also add rules for branching and recursion.}

\begin{frame}[fragile]{Motivation}
Scope-safe syntax operations:
		\begin{code}
rename : ∀ {Γ Δ}  → (∀ {A} → Γ ∋  A → Δ ∋  A)
                  → (∀ {A} → Γ ⊢  A → Δ ⊢  A)
rename ρ (‵ x)          =  ‵ (ρ x)
rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)
rename ρ (‵zero)        =  ‵zero
rename ρ (‵suc M)       =  ‵suc (rename ρ M)
rename ρ (case L M N)   =  case  (rename ρ L)
                                 (rename ρ M)
                                 (rename (ext ρ) N)
rename ρ (μ N)          =  μ (rename (ext ρ) N)
		\end{code}
\end{frame}

\note{There are some common operations for this kind of language, for example, \mi{rename} is common for languages with De Bruijn indices. \mi{rename} says that if there's a mapping from every element in a context $\varGamma$ to the other $\varDelta$, we can always find a mapping from every term that is typed in $\varGamma$ to a term typed in $\varDelta$.}

\begin{frame}[fragile]{Motivation}
We may change/extend the object language:
		\begin{code}
data _⊢_ : Context → Type → Set where
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

\note{What if we extend the language even further? Here we add even more rules to the language we just defined.}

\begin{frame}[fragile]{Motivation}
Redefine/extend syntax operations:
		\begin{code}
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

\note{The \mi{rename} function must be extended or redefined everytime we make some changes to the object language. Here we can start to notice the pattern of \mi{rename}. For every subterm in a term we call \mi{rename} recursively, and modify the mapping function with \mi{ext} if there are context extensions. The result subterms are then constructed by the same constructor they are pattern matched from. We see here a pattern of fold operation. We probaly would want to apply generic programming here to avoid defining such operations every time.}

\begin{frame}[fragile]{Motivation}
Other repeating operations:
		\begin{code}
subst : ∀ {Γ Δ}  → (∀ {A} → Γ ∋  A → Δ ⊢ A)
                 → (∀ {A} → Γ ⊢  A → Δ ⊢ A)


print : Γ ⊢ A → String


...
		\end{code}
\end{frame}

\note{There are other repeating operations that must be redefined for every change in the object language, if you have already defined a language with multiple such operations, you probaly would wish for some kind of automations.}

\begin{frame}[fragile]{Existing work}
  There are generic libraries for a family/families of syntaxes with binders~\footcite{Allais-generic-syntax}\footcite{Ahrens-typed-abstract-syntax}.

We improve upon Allais et al.'s approach\footnotemark[1] published at ICFP '18.
\end{frame}

\note{There have been some generic libraries aiming for eliminating such repetitions, but they are not widely adopted. We introduce a work by Allais et al. and illustrate what we think is limiting in their and others' generic libraries, so later we can show how we can improve upon their work and others alike.}

\begin{frame}[fragile]{Existing work by Allais et al.}
	Allais et al.'s \mi{Desc}:
	\begin{code}
data Desc (I : Set) : Set₁ where
	‵σ  : (A : Set) → (A → Desc I) → Desc I
	‵X  : List I → I → Desc I → Desc I
	‵▪  : I → Desc I
	\end{code}
\end{frame}

\note{Allais et al. provides a universe that describes a certain kind of syntax. It's worth mentioning that all such universes are limiting in natural, because we don't know what kind of syntax the researchers would define, we can only presume. In this case, they have presumed that the syntax to be described must have a type and a context, while allowing binders to extend the context. This restriction is necessary and important, we will come back to it later.}

\begin{frame}[fragile]{Existing work by Allais et al.}
\begin{columns}[T]
\begin{column}{0.5\textwidth}
Simply typed $\uplambda$-calculus
	\begin{code}
data STLC : Type → Context → Set where
  ‵var  : Var σ Γ
        → STLC σ Γ

  ‵app  : STLC (σ ⇒ τ) Γ → STLC σ Γ
        → STLC τ Γ

  ‵lam  : STLC τ (σ ∷ Γ)
        → STLC (σ ⇒ τ) Γ
	\end{code}
\end{column}
\begin{column}{0.5\textwidth}
	\pause
encoded in \mi{Desc}:
	\begin{code}
data ‵STLC : Set where
  App Lam : Type → Type → ‵STLC

STLCD : Desc Type
STLCD = ‵σ ‵STLC λ where
  (App  i j) →
    ‵X [] (i ⇒ j) (‵X [] i (▪ j))
  (Lam  i j) →
    ‵X (i ∷ []) j (▪ (i ⇒ j))

STLC' = Tm STLCD
	\end{code}
\end{column}
\end{columns}
\pause
$$\mi{STLC} \cong \mi{STLC'}$$
\end{frame}

\note{In most such generic libraries, programmers are required to encode their syntax in the given description. For example, a simply-typed lambda calculus here, \mi{Tm} is a type constructor that takes the fixpoint of the functor of a description. We may prove that a syntax defined as a isolated datatype is isomorphic to the fixpoint of some functor, but the programmer shall never use the isolated datatype definition again, what happens in the generic universe stays in that generic universe. }

% \begin{frame}[fragile]{Existing work by Allais et al.}
% 	\begin{code}
% STLC : Desc Type
% STLC = σ ‵STLC λ where
%   (App  i j) → ‵X [] (i ⇒ j) (‵X [] i (▪ j))
%   (Lam  i j) → ‵X (i ∷ []) j (▪ (i ⇒ j))
% 	\end{code}
% \end{frame}

\begin{frame}[fragile]{Existing work by Allais et al.}
	Generic programs are \mi{Semantics} records.

	Functions are realized on fixpoints \mi{Tm} via \mi{semantics}.
	\begin{code}
Renaming : ∀ {d : Desc I} → Semantics d Var (Tm d)

rename : ∀ {d : Desc I} → (∀ {i}  → Var i Γ‘ → Var i Δ)
                                  → Tm d j Γ → Tm d j Δ
rename = semantics Renaming
	\end{code}
\mi{rename} can be applied to fixpoints of any description (e.g. $\mi{Tm}\ \mi{STLC}$).
\end{frame}

\note{Likewise, generic functions in these libraries require specific descriptions, such that we can define functions that work for a whole family of syntaxes. In this case, the sementics function with lower case S is used to interpret the semantics description with upper case S, and we can obtain a rename function that is very similar to what we have defined previously. You can see it is generic as it works on Tm d for every d.}

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
% data _⊢_ : Context → Type → Set where
%   ‵_     : Γ ∋ A → Γ ⊢ A
%   ƛ_     : Γ , A ⊢ B → Γ ⊢ A ⇒ B
%   _·_    : Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
% 		\end{code}
% 	\begin{code}
% STLC : Desc Type
% STLC = σ ‵STLC λ where
%   (App  i j) → ‵X [] (i ⇒ j) (‵X [] i (▪ j))
%   (Lam  i j) → ‵X (i ∷ []) j (▪ (i ⇒ j))
% 	\end{code}
% 	}
% \end{frame}

\begin{frame}[fragile]{Motivation cont.}
	\begin{columns}[T]
		\begin{column}{0.5\textwidth}
		``Natural'' function:
		\begin{code}
rename : ∀ {Γ Δ}
       → (∀ {A} → Γ ∋  A → Δ ∋  A)
       → (∀ {A} → Γ ⊢  A → Δ ⊢  A)
rename ρ (‵ x)          =  ‵ (ρ x)
rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)
		\end{code}
		\end{column}

		\begin{column}{0.5\textwidth}
		Generic function:
		\begin{code}
Renaming : Semantics Var Lam
Renaming = record
  { th^V  = th^Var
  ; var   = ‘var
  ; app   = ‘app
  ; lam   = λ b → ‘lam (b weaken z) }
rename = semantics Renaming
		\end{code}
		\end{column}
	\end{columns}
\end{frame}

\note{We conclude that one of the reasons these generic libraries are not widely adopted is because the definitions are not intuitive. Here is a comparison, we think function definitions on the left is more popular and have better properties for programming language researchers. }

\begin{frame}[fragile]{Motivation cont.}
	Problems with using syntax universes:
	\pause
	\begin{enumerate}
		\item Readability
		\pause
		\item Extra work for programmers
		\pause
		\item Interoperability with existing tools/IDEs
		\pause
		\item Interoperability with existing libraries
	\end{enumerate}
\end{frame}

\note{The downsides of generic libraries can be summarized as such: First of all, readability. One merit of intrinsic typing is that types of constructors closely resemble typing rules, as we can see previously, typing rules are less obvious for syntaxes defined in generic universes. Secondly, to utilize such generic libraries, programmers are required to understand the generic universe instead of just defining syntaxes the way they want, and they need to learn a new generic construction or representation everytime they want some features only exist in another generic library, even though they are working on the same syntax. This leads us to te third problem, interoperability. It's not only hard to use two or more generic libraries at once, it's also very difficult to use any libaries that was applicable to natural definitions. The interoperability with existing tools also suffer, for example, it was clear that for every typing rule their is a clause for the rename function, because every typing rule corresponds to one constructor. Here we can utilize the case-spliting mechanism provided by Agda's editor mode, and we can easily see how many clauses we should define for a rename function. We can't benefit from these tools or existing IDE supports when using generic universes, for there's no such correspondence.}

\section{Elaborator Reflection to the Rescue}

\note{Therefore, we want the best from both worlds, we want programmers and researchers to use native definitions whenever possible, while generic programs can still be invoked. We acheive this by elaborator reflection. Elaborator reflection is the metaprogramming mechanism provided by Agda, it allows us to read and define datatype and function definitions.}

\begin{frame}[fragile]{Elaborator Reflection to the Rescue}
	``Datatype-Generic Programming Meets Elaborator Reflection'' at 15:50, Tuesday.

	\pause

	Syntax-generic operations \emph{are} Datatype-generic programs with constraints.
\end{frame}

\note{I would like to shamelessly promote the other work we are publishing, Datatype-Generic Programming Meets Elaborator Reflection. Josh will present it on Tuesday at the main conference. Josh, my advisor, Liang-Ting, my co-worker, and I, we have demostrated in that work on how to mix elaborator reflection with datatype-generic programming, such  we can define programs that work for a family of datatypes, while using elaborator reflection to reify such programs as natural function definitions defined on native datatypes. What does this have to do with syntax-generic libraries that we spent so much time intorducing? It turns out, syntax-generic programs can sometimes be seem as a subset of datatype-generic programs. In this case, we can constrain a subset of all datatypes such that datatypes in this subset are also describable by Allais et al.'s library.}

\begin{frame}[fragile]{The ideal process}
	\begin{enumerate}
		\item The programmer defines a native datatype $T$.
		\pause
		\item A metaprogram generates the description $D$ of $T$.
		\pause
		\item The programmer provides a proof $S$ of $D$ that says $T$ is indeed a syntax.
		\pause
		\item The programmer choose one description $P$ from a set of pre-defined generic programs.
		\pause
		\item A metaprogram takes $D$, $S$, and $P$, generates a native function accordingly.
	\end{enumerate}
\end{frame}

\note{By introducing datatype-generic programming and metaprograms, let's see what we think is the better process here for a programmer? Firstly they define a native datatype that we know to be a syntax, instead of relying on any generic description. Then by metaprograms in our datatype-generic library, they get the datatype description of that datatype. The programmer then proves the datatype to be a syntax by providing a proof of our pre-defined predicate. Then they can choose a generic program to reify. This generic program is pre-defined by the ``geneic library programmers'', who has defined what generic programs exist for what subsets, here the chosen programs must work on datatypes constrained by $S$ which are syntaxes. Lastly, another metaprogram takes all these things, $D$, $S$, $P$, and gives the programmer a native, reifed funtion definition, as if everything is defined by hands.}

\begin{frame}[fragile]{Flow Chart}
\includegraphics[width=\columnwidth]{Diagram1.pdf}
\end{frame}

\note{Let's do a quick rundown with our actual definitions. We have three worlds, the user's own world, the syntax-datatype-generic library, and metaprograms. Say the user defines a language called Lam, indexed by the type and context of a term.}

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

\note{But our metaprograms that generates functions are for datatype-generic programs. so we need another translation in the generic library that is from syntax-generic programs to datatype-generic programs. SemP is this translation and FoldP is the type of datatype-generic fold programs.}

\begin{frame}[fragile]{Flow Chart}
\includegraphics[width=\columnwidth]{Diagram6.pdf}
\end{frame}

\note{Finally, defineFold is a metaprogram that generates actual function definitions. So the user doesn't need to understand the detailed definitions in the generic libary, they can write native datatype and get native function definitions if they know what metaprograms and functions to call.}

\begin{frame}[fragile]{Provided by our datatype-generic library}
	\begin{itemize}
		\item \mi{DataD}
		\pause
		\item \mi{FoldP} for folds (and \mi{IndP} for inductions)
		\pause
		\item metaprogram \mi{genDataD}
		\pause
		\item metaprogram \mi{defineFold}
	\end{itemize}
\end{frame}

\note{These are provided by our work DGP+Reflection}

\begin{frame}[fragile]{Our Work}
	\begin{itemize}
		\item a predicate \mi{Syntax} on \mi{DataD} that captures \mi{Desc}.
		\item a function \mi{SemP} that generates \mi{FoldP} from \mi{Syntax} proofs.
	\end{itemize}
\end{frame}

\note{These are our contribution in this work}


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

\note{We don't have time for these}

\begin{frame}[fragile]{The \mi{Syntax} Predicate}
Does \mi{PCF} satisfies \mi{Syntax}?
	\begin{code}
data PCF : Type → Context → Set where
  ‵var   : Var σ Γ → PCF σ Γ
  ‵app   : PCF (σ ⇒ τ) Γ → PCF σ Γ → PCF τ Γ
  ‵lam   : PCF τ (σ ∷ Γ)  → PCF (σ ⇒ τ) Γ
  ‵zero  : PCF ‵ℕ Γ
  ‵suc_  : PCF ‵ℕ Γ → PCF ‵ℕ Γ
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
        , (_ , _ , _ , refl , (λ _ → refl))
        , (_ , _ , _ , refl , (λ _ → refl))
        , (_ , _ , _ , refl , (λ _ → refl))
        , (_ , _ , _ , refl , (λ _ → refl))
        , tt
		\end{code}
	\end{exampleblock}
\end{frame}

\note{Let's see an example of the syntax proof}

% \begin{frame}[fragile]{Translation from Semantics to natural looking functions}
% \end{frame}

\section{Demo}

\section{Discussion: towards datatype-generic libraries for syntaxes?}

\begin{frame}[fragile]{Future Works \& Issues}
	\begin{itemize}
		\item \mi{Syntax} proof automation
		\item User interface
		\item Port more generic libraries:
		\pause
			\begin{itemize}
				% \item Expressiveness is limited by Agda datatypes as well as the generic universe, a \mi{Syntax} predicate must be defined.
				% \pause
				% \item Even if we can define \mi{Syntax}, the proof could be more complicated, even require programmers to understand the generic universe.
				% \pause
				% \item Obstacles of using multiple generic libraries at once.
				% \pause
				% \item Are folds and inductions enough?
				\item Expressiveness
				\pause
				\item Complexity of \mi{Syntax}
				\pause
				\item Interoperability
				\pause
				\item Are folds and inductions enough?
			\end{itemize}
	\pause
	\end{itemize}
\end{frame}

\section{Q \& A}

\end{document}

