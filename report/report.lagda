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

Datatype generic programming is a technique which can save a lot of effort
when defining functions on data, the idea being that you define a function once,
to work on values in a common representation format, then define functions which
translate specific datatypes from and to this intermediate format. The problem is,
even though many libraries use similar representation types (such as the sum-of-products view),
not much work has been done to make these representations interchangeable. This project aims
to discover similarities between representation types and explore the possibilities of
formalising these structural similarities, and possibly even exploiting them to create automatic
value and datatype representation conversion.

This way, once a user has defined a function using the representation of one generic programming library,
the option might exist to use automatic translation functions to be able to run
this function on other generic values possibly defined using some other generic programming library's
generic view.


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

\section{The Universes}

Initially we decided to explore the similarity between LIGD (which uses the sum-of-products view \dots) %TODO: insert reference
and the spine view, which consists of lists of signatures. Consider for example the representation of the common
Haskell-like |List| data structure in both libraries. In Spine:

\begin{code}
listRep-S : {a : Set} -> Type a -> List (Signature a)
listRep-S a = Sig [] ∷ [ Sig (_∷_) · (par , a) · (rec , (listRep-S a)) ]
\end{code}

\dots and in LIGD:

\begin{code}
listRep-L : LCode → LCode
listRep-L a = U ⊎ (a × (listRep-L a))
\end{code}

One can easily see that the products in the sum-of-products view correspond to
the parameters of each constructor, which are chained together using the |_·_| operator
in Spine, and that sums correspond to alternatives of a datatype, which are modelled using
elements of the signature list in the Spine view. Informally, one could replace list concatenation with
sums, and the  |_·_| operator with products to obtain an LIGD representation of a datatype, from a Spine
representation.

The first step to exploring the similarities between these representational styles is of course to embed
them into Agda. This embedding is discussed in the following section.

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
must terminate (since Agda evaluates all the functions in the type signature
to normal form, to decide if a function type checks).

We instead chose to implement a conversion from Spine to Regular,
since in Regular, recursion is modeled by an extra parameter. This
allowed all functions to be terminating. In Regular one models the
pattern functor, then applies the least fixed-point operator |μ| which
results in a representation which is isomorphic to the represented
type.

\section{The embedding and conversion functions}

Spine has support for existential types, since it allows arbitrary parameters to be used in its |Signature| type. Therefore, it's not possible to translate
all Spine representations into Regular. We can, however, translate a subset of Spine into Regular, as is done in the following code example.


\section{Related work}


\section{Our contribution}

\section{Discussion}

\section{Conclusion}

In summary, this project has resulted in an injective embedding of Spine into Regular. Functions for
converting representations from one viewe to another have been provided, and a number of suggestions for future
work have been done. While the functions aren't as generic as could be desired, the project has clearly
demonstrated a concrete relationship between the Spine and Regular worlds. Most likely it would be worthwhile
to do further research and possibly abstract away from the Spine universe and allow conversion of Regular
representations into Spine representations. It should also be possible to formalise the given relationships
using Agda's power as a proof assistant.


    \begin{thebibliography}{9}

        \bibitem{loh}
            L{\"o}h, A. and Magalh{\~a}es, J.P.,
            \emph{Formally comparing approaches to datatype-generic programming, using Agda} (talk).
            2011.
    \end{thebibliography}

\end{document}
