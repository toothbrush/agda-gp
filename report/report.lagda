\documentclass[a4paper]{article}

\def\textmu{}

\RequirePackage{xcolor}
\newcommand{\ty}[1]{{\color{orange}\mathsf{#1}}}
\newcommand{\con}[1]{{\color{blue}\mathsf{#1}}}
\newcommand{\consymop}[1]{{\color{blue}\mathsf{#1}}}
\newcommand{\consym}[1]{{\color{blue}\mathsf{#1}}}
\newcommand{\id}[1]{{\color{blue}\mathsf{#1}}}



%\newcommand{\ty}[1]{{\color{orange}\mathsf{#1}}}
\colorlet{darkgreen}{green!30!black}
%include report.fmt

\usepackage{url}
\usepackage{hyperref}
\title{Isomorphism between Regular and Spine in Agda}
\date{\today}
\author{Justin Paston-Cooper\footnote{\url{paston.cooper@@gmail.com}} \and Marcelo Sousa\footnote{\url{dipython@@gmail.com}} \and Paul van der Walt\footnote{\url{paul@@denknerd.org}}}
\begin{document}

\maketitle

\begin{abstract}
    This report details our efforts in embedding Spine and Regular (two Haskell generic programming
    libraries with different generic views) into Agda, a dependently typed programming language. There is also
    an automatic conversion function between representations in the two views, and a partial isomorphism.
    Furthermore, LIGD (another GP library) is looked at, and an attempt is made to embed it in Agda, and pointers
    for further research are given.
\end{abstract}

\section{Introduction}


\section{Aim}
The aim of the project was to show an embedding relation between
algebraic datatype representation systems such as LIGD, Regular and
Spine. Below there are presented embeddings of the respective
universes for each of the listed systems.

To show an embedding of a system A into a system B, one must define a
conversion of the codes in A into the codes in B, showing that this
conversion is injective. That can be done by creating a left-inverse
of the initial conversion function. Datatypes in Spine are represented
by lists of signatures, where a signature consists of one of the
type's constructors, along with an indication of the order and type of
the parameters thereof. Lists of signatures intuitively represent a
sum of products view where elements of the list represent the
summands, and the parameters of a signature represent terms of
products.

This fact suggests the existence of an embedding relation including
the spine and sum of products views, where LIGD was the original
choice for the sum of products view. We attempted to convert from
Spine to LIGD and also from LIGD to Spine, where in both cases we ran
into problems which are detailed later.

%% We have found that any Regular representation can be translated into a
%% Spine representation, but not all Spine representations can be
%% translated into Regular (in particular existential types pose a
%% problem in Regular).

\section{The Universes}

\subsection{LIGD}

\begin{code}
data LCode : Set where
  runit : LCode
  rnat : LCode
  rsum : LCode → LCode → LCode
  rprod : LCode → LCode → LCode
  rtype : (A : Set) → (A → LCode) → (LCode → A) → LCode

L⟦_⟧ : LCode → Set
L⟦ runit ⟧ = ⊤
L⟦ rnat ⟧ = ℕ
L⟦ rsum r₁ r₂ ⟧ = L⟦ r₁ ⟧ ⊎ L⟦ r₂ ⟧
L⟦ rprod r₁ r₂ ⟧ = L⟦ r₁ ⟧ × L⟦ r₂ ⟧
L⟦ rtype t _ _ ⟧ = t

\end{code}

\subsection{Regular}
\begin{code}
data Code : Set where
  U : Code
  K : Set → Code
  I : Code
  _⊕_ : Code → Code → Code
  _⊗_ : Code → Code → Code

⟦_⟧_ : Code → Set → Set
⟦ U ⟧       r = ⊤
⟦ K a ⟧     r = a
⟦ I ⟧       r = r
⟦ c1 ⊕ c2 ⟧ r = ⟦ c1 ⟧ r ⊎ ⟦ c2 ⟧ r
⟦ c1 ⊗ c2 ⟧ r = ⟦ c1 ⟧ r × ⟦ c2 ⟧ r

data μ_ (c : Code) : Set where
  <_> : ⟦ c ⟧ (μ c) → μ c

\end{code}

\subsection{Spine}
\begin{code}
data Type : Set -> Set where
  bool : Type Bool
  nat  : Type ℕ
  list : {a : Set} -> Type a -> Type (List a)

data Spine : Set -> Set where
  Con : ∀ {a} -> a -> Spine a
  _:<>:_ : ∀ {a b} -> Spine (a -> b) -> Typed a -> Spine b

data Type? : Set where
  con : Type?
  rec : Type?

data Signature a : Set where
  Sig : a -> Signature a
  _·_ : {b : Set} → Signature (b → a) → Type? × Type b → Signature a

sigList : {a : Set} -> Type a -> List⁺ (Signature a)
sigList bool = Sig true ∷ [ Sig false ]
sigList nat  = Sig zero ∷ [ (Sig suc · rec , nat) ]
sigList (list a) = Sig [] ∷ [ (Sig (_∷_) · con , a · rec , (list a)) ]

\end{code}

\section{Initial Attempt: Spine to LIGD}
Taking a representation in LIGD of a given datatype, the datatype is
explicitly referred to in the recursive position. Consider the LIGD
representation of the usual [a] datatype for a given type a

\begin{code}
rList : LCode → LCode
rList RA = rsum runit (rprod RA (rList RA))
\end{code}

Note here that the recursive call is equal to the left hand side of
the definition. Because of this, we ran into termination
problems. Firstly the defined function does not terminate, something
that wouldn't have been a problem in Haskell. This can be disabled,
but for later defining conversion of values, we needed the code
conversion functions in type signatures, and in those, all expressions
must terminate.

We instead chose to implement a conversion from Spine to Regular,
since in Regular, recursion is modeled by an extra parameter. This
allowed all functions to be terminating. In Regular one models the
pattern functor, then applies the least fixed-point operator |μ| which
results in a representation which is isomorphic to the represented
type.
\section{Regular in Agda}
\begin{code}

-- Code for Regular
data Code : Set where
  U : Code
  K : Set → Code
  I : Code
  _⊕_ : Code → Code → Code
  _⊗_ : Code → Code → Code

-- Interpretation function for Regular Code
⟦_⟧_ : Code → Set → Set
⟦ U ⟧       r = ⊤
⟦ K a ⟧     r = a
⟦ I ⟧       r = r
⟦ c1 ⊕ c2 ⟧ r = ⟦ c1 ⟧ r ⊎ ⟦ c2 ⟧ r
⟦ c1 ⊗ c2 ⟧ r = ⟦ c1 ⟧ r × ⟦ c2 ⟧ r

-- Least fixed point of Codes
data μ_ (c : Code) : Set where
  <_> : ⟦ c ⟧ (μ c) → μ c

\end{code}
\section{Spine in Agda}


\section{The embedding}

Spine has support for existential types, since it allows arbitrary parameters to be used in its Signature type. Therefore, it's not possible to translate
all Spine representations into Regular. We can, however, translate a subset of Spine into Regular, as is done in the following code example.
\end{document}
