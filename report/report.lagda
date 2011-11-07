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

LIGD is a Haskell datatype generic programming library based on the familiar sum-of-products
view, which we have modeled in Agda. It relies on explicit recursion, and the universe (which includes
the interpretation function to convert a code into a real Agda type) is presented below.

\begin{code}
data LCode : Set where
  runit     :                                             LCode
  rnat      :                                             LCode
  rsum      : LCode → LCode                             → LCode
  rprod     : LCode → LCode                             → LCode
  rtype     : (A : Set) → (A → LCode) → (LCode → A)     → LCode

L⟦_⟧ : LCode → Set
L⟦ runit ⟧          = ⊤
L⟦ rnat ⟧           = ℕ
L⟦ rsum r₁ r₂ ⟧     = L⟦ r₁ ⟧ ⊎ L⟦ r₂ ⟧
L⟦ rprod r₁ r₂ ⟧    = L⟦ r₁ ⟧ × L⟦ r₂ ⟧
L⟦ rtype t _ _ ⟧    = t
\end{code}

Note that the |rtype| constructor is useful for embedding any user-defined Agda type into
the LIGD universe, but that this does make for example decidable equality functions tricky.

\subsection{Regular}

As we will explain later on, problems were encountered as a result of the deep recursion which
LIGD uses, along with the termination checking property of Agda. As a result of this, it was decided
to switch to an embedding of the Regular library in Agda, since it makes use of shallow recursion, along
with $\mu$, the fixed-point operator.

Regular is quite similar to LIGD, except for the addition of the |I| constructor, which marks a recursive
position of a constructor. The interpretation function |⟦_⟧_| is unsurprising.

\begin{code}
data Code : Set where
  U     : Code
  K     : Set → Code
  I     : Code
  _⊕_   : Code → Code → Code
  _⊗_   : Code → Code → Code

⟦_⟧_ : Code → Set → Set
⟦ U ⟧           r = ⊤
⟦ K a ⟧         r = a
⟦ I ⟧           r = r
⟦ c1 ⊕ c2 ⟧     r = ⟦ c1 ⟧ r ⊎ ⟦ c2 ⟧ r
⟦ c1 ⊗ c2 ⟧     r = ⟦ c1 ⟧ r × ⟦ c2 ⟧ r

data μ_ (c : Code) : Set where
  ⟨_⟩  : ⟦ c ⟧ (μ c) → μ c

\end{code}

Since $\mu$ isn't included inside the universe, Regular cannot have more than
one recursive position, whereas Spine can. This is something we take for
granted, since we're modelling a limited version of Spine, such that the
universes of Spine and Regular (or at least our restricted versions of them)
have some structural similarity relation.



\subsection{Spine}

Here we present the universe of Spine as we have embedded it in Agda. Notice that
the |Type| datatype represents the types which are representable in Spine, which implies that the spine universe
is closed. The |Type?| datatype is an extension we've had to make to Spine, to tag arguments as being
parameters or recursive positions, because we weren't able to define a function for decidable equality
on types.

\begin{code}
data Type : Set -> Set where
  bool  : Type Bool
  nat   : Type ℕ
  list  : {a : Set} -> Type a -> Type (List a)

data Spine : Set -> Set where
  Con       : ∀ {a} -> a -> Spine a
  _:<>:_    : ∀ {a b} -> Spine (a -> b) -> Typed a -> Spine b

data Type? : Set where
  par : Type?
  rec : Type?

data Signature a : Set where
  Sig : a -> Signature a
  _·_ : {b : Set} → Signature (b → a) → Type? × Type b → Signature a

\end{code}

The way to represent a datatype using Spine is to provide a list of |Signature|s, where
a |Signature| corresponds to one of the datatype's constructors. A |Signature|, as can be seen
above, consists of the constructor itself, along with representations for each of it's parameters,
separated by the |_·_| operator. See for example the representation of the well-known |List| data type
in Spine.

\begin{code}
listRep-S : {a : Set} -> Type a -> List (Signature a)
listRep-S a = Sig [] ∷ [ Sig (_∷_) · (par , a) · (rec , (listRep-S a)) ]
\end{code}

Finally, the |sigList| function is a function which the user of the library should
provide, giving the list of signatures for each supported type in the Spine universe. This is
a convenient and uniform method of storing the representations as presented above.

\begin{code}
sigList : {a : Set} -> Type a -> List⁺ (Signature a)
sigList bool = Sig true ∷ [ Sig false ]
sigList nat  = Sig zero ∷ [ Sig suc · (rec , nat) ]
sigList (list a) = Sig [] ∷ [ Sig (_∷_) · (par , a) · (rec , list a) ]
\end{code}


\section{Initial Attempt: Spine to LIGD}
Taking a representation in LIGD of a given datatype, the datatype is
explicitly referred to in the recursive position. Consider the LIGD
representation of the usual |[ a ]| datatype for a given type |a|.

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

\section{Spine in Agda}


\section{The embedding}

Spine has support for existential types, since it allows arbitrary parameters to be used in its |Signature| type. Therefore, it's not possible to translate
all Spine representations into Regular. We can, however, translate a subset of Spine into Regular, as is done in the following code example.
\end{document}
