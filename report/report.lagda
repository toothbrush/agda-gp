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
\usepackage{graphicx}
\title{Isomorphism between Regular and Spine in Agda}
\date{\today}
\author{Justin Paston-Cooper\footnote{\url{paston.cooper@@gmail.com}} \and Marcelo Sousa\footnote{\url{dipython@@gmail.com}} \and Paul van der Walt\footnote{\url{paul@@denknerd.org}}}
\begin{document}

\maketitle

\begin{abstract}
    This report details our efforts in embedding generic datatype
    systems into Agda. We present a conversion function between representations
    in different views and we show a structural relation between Spine and
    Regular.
\end{abstract}

\section{Introduction}

The idea of datatype geeneric programming is that to define a function, a user defines a function once
over a set of building blocks of a system, and then the function works for all types which are representable
in that system. The system provides methods of converting to and from a normal value, say in Agda, to this representation, at
which point, the defined function can be applied.
Even though many libraries use similar representation types (such as the sum-of-products view),
not much work has been done to make these representations interchangeable. The aim of the project was
to discover similarities between generic datatype systems, to formally describe them and to create generic
value and datatype representation conversions.

In this way, once a user has defined a function using the representation of one generic programming library,
the option may exist to use automatic translation functions for running
this function on other values defined using another generic programming library's
generic view.

The full source code belonging to the presented work can be downloaded from the repository. \cite{source}

\section{Aim}
The aim of the project was to show an embedding relation between
algebraic datatype representation systems such as LIGD, Regular and
Spine. Below are presented embeddings of the respective
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

As stated, we initially decided to explore the similarity between LIGD, which uses the sum-of-products view,
and the spine view, which consists of lists of signatures, where a single signature contains a constructor
along with the types of its parameters. Consider for example the representation of the common
Haskell-like |List a| data structure in both libraries. In Spine:

\begin{code}
listRep-S : {a : Set} → Type a → List (Signature a)
listRep-S a = Sig [] ∷ [ Sig (_∷_) · (par , a) · (rec , (listRep-S a)) ]
\end{code}

\dots and in LIGD:

\begin{code}
listRep-L : LCode → LCode
listRep-L a = U ⊎ (a × (listRep-L a))
\end{code}

It is intuitive that the terms of a single product in the sum-of-products view correspond to
the parameters of a constructor, which are chained together using the |_·_| operator
in Spine. It is also intuitive that the terms in sums correspond to the alternatives of a datatype, which are modelled using
elements of the signature list in the Spine view. In other words, one can replace list concatenation with
sums, and the  |_·_| operator with products to obtain an LIGD representation of a datatype, from a Spine
representation.

The first step in exploring the similarities between these representational styles is to embed
them into Agda. This embedding is detailed in the following section.

\subsection{LIGD}

LIGD is a Haskell datatype generic programming library encorporating the sum-of-products
view, which we have modelled in Agda. It relies on explicit recursion and a universe which includes
an interpretation function to convert a code, representing a type, into an Agda type.

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

The |rtype| constructor is useful for embedding a user-defined Agda type into
the LIGD universe. This can make decideable equality functions tricky.

\subsection{Regular}

As detailed later, problems were encountered as a result of the deep recursion which
LIGD uses, along with the termination checking property of Agda. As a result of this, it was decided
to switch to an embedding of the Regular library in Agda, since it makes use of shallow recursion, along
with |μ|, the fixed-point operator.

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

Since $μ$ isn't included inside the universe, Regular cannot have more than
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
data Type : Set → Set where
  bool  : Type Bool
  nat   : Type ℕ
  list  : {a : Set} → Type a → Type (List a)

data Spine : Set → Set where
  Con       : ∀ {a} → a → Spine a
  _:<>:_    : ∀ {a b} → Spine (a → b) → Typed a → Spine b

data Type? : Set where
  par : Type?
  rec : Type?

data Signature a : Set where
  Sig : a → Signature a
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
sigList : {a : Set} → Type a → List⁺ (Signature a)
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
that wouldn't have been a problem in Haskell. Termination checking can be disabled.
However, for later defining a function for value conversion, we needed the code
conversion functions in type signatures of that function, and all expressions
in a signature must terminate.

We later chose to implement a conversion from Spine to Regular.
Regular is similar to LIGD in its sum-of-products approach, but there is an extra parameter to every code for
implicit representation of recursion. The extra parameter is filled on application of the least fixed-point operator |μ|.
Using regular allowed the conversion functions we defined later, to terminate.

\section{Spine to Regular}

After running into the problems mentioned above, we decided to switch to Regular for our sum-of-products view.


\section{Related work}

\begin{figure}[h]
    \begin{center}
        \includegraphics[width=\textwidth]{conversions}
    \end{center}
    \caption{Relation of embeddings of various libraries.}
    \label{fig:conversions}
\end{figure}

\section{Our contribution}
We have claimed an injective embedding of the Spine system into the
Regular System. Our embedding is carried out by \texttt{convert},
which takes a Spine type representation and gives the corresponding
regular representation based on the signature list, and by the value
conversion functions |S→R| and |R→S|.

The injectivity of this embedding can be seen as follows. The function
|S→R| is of type |{a : Set} → (tyA : Type a) → Spine a → μ
(convert tyA)|. The function |R→S| is of type |{a : Set} → (tyA :
Type a) → μ (convert tyA) → Spine a|. For a single |Type a|,
|S→R| and |R→S| are inverses of each other, thus showing them both
to be bijections. However, the union of all codomains of |S→R| over
all |Type a|, the set of all Regular representations of Spine values,
is only a proper subset of the whole Regular value universe. We
therefore see that |S→R| as an injective embedding of the Spine value
universe into that of Regular, with |R→S| being its left-inverse.



\section{Critical Analysis}

\subsection{An Addition to the Original Spine System}
We made an addition the previously standing definition of Signature in
Spine. In our version, type parameters are tagged with a value of
|Type?|, indicating whether or not that position in the signature is a
parameter or recursive. Below is given a comparison between the
previous version of the signature list for (list a), and our current
version.

\begin{code}
sigList (list a) [] = Sig [] ∷ (Sig (∷) · a · list a) ∷ []
\end{code}

\begin{code}
sigList (list a) [] = Sig [] ∷ (Sig (∷) · (par , a) · (rec , list a)) ∷ []
\end{code}
This tagging is required in the making of the product type
corresponding to a single signature, which is implemented by the
function |makeProd|. Given a |(par , a)|, it gives a |K| code and
given a |(rec , list a)|, it gives an |I| code. 

We had previously tried to define a |makeProd| function with the type
|{a : Set} → Type a → Signature a → Code|. In deconstructing the
given signature, any type matching the given |Type a| value would be
seen as the recursive position, and any other type would be seen as a
parameter. In trying to define |makeProd| in this way, we ran into
problems in checking equalities of the Spine type representations, and
we had many more issues with the Agda type checker. We were not able
to complete such a definition in the time provided, but it may be
possible with further work.


\subsection{Further Genericity of |from| and |to|}
The |convert| function is generic in the sense that its definition is
not dependent the currently defined Spine universe of types, which
could be extended to include further algebraic datatypes. For any
future extension of the type universe, with an appropriate extension
of |sigList|, it would continue to work. However, the |from| and |to|
functions are not generic in this sense. Their pattern matching
depends on knowledge of the currently defined type universe, and if a
user were to make an extension to the universe, the |from| and |to|
functions would also need to be changed.

In fact, all the information which |from| and |to| should need is in
the signature lists. We made an attempt to define the functions to
depend only on the signature lists, but again we ran into problems
with the Agda type checker. Below is presented a mock of how we would
like to define the |to| function.

\begin{spec}
applyParams : {a : Set} → (sig : Signature a) → ⟦ makeProd sig ⟧ a → a
\end{spec}   
\begin{spec}
chooseSig : {a : Set} → List⁺ (Signature a) → μ (convert tyA) → A
chooseSig (sig ∷ rest)          < inj₁ val > = applyParams sig val
chooseSig [single]              < inj₂ val > = applyParams single val
chooseSig (_ ∷ rest)            < inj₂ val > = chooseSig rest val
\end{spec}   
\begin{spec}
to : {a : Set} → (tyA : Type a) → μ (convert tyA) → A
to tyA val with (sigList tyA)
... | [single]     = applyParams single val
... | multiple     = chooseSig multiple val
\end{spec}
The |to| function calls |chooseSig| when |convert tyA| would have
returned a proper sum, which is exactly when there is more than one
signature in the signature list. Otherwise it directly calls
|applyParams| with the given value.

The function |chooseSig| finds the signature that corresponds to the
type of the given value, which corresponds to one of the terms in the
sum given by |convert tyA|. If a value is found inside an |inj₁|, then
by definition of |convert|, the value should correspond to the first
signature in the list. The only case in which a value may correspond
to a signature in a one-element list is when it is found inside an
|inj₂|, which is reflected by the second pattern matching. When there
are at least two signatures and an |inj₂|, then |chooseSig| must call
itself again with the rest of the signatures, as reflected by the
third pattern matching.

The function |chooseSig| works by going through the list of signatures
until it reaches either a value inside an |inj₁|, at which point the
first signature in the list corresponds to the value, or when only one
element in the list is left and it finds the value inside an
|inj₂|. This value is by definition of type |⟦ makeProd sig ⟧ a|, and
this is reflected in the type signature of |applyParams|. A working
definition of |applyParams| would deconstruct the given product, and
give the terms as arguments to the constructor found inside the given
signature.


\section{Conclusion}


    \begin{thebibliography}{9}

        \bibitem{loh}
            L{\"o}h, A. and Magalh{\~a}es, J.P.,
            \emph{Formally comparing approaches to datatype-generic programming, using Agda} (talk).
            2011.
        \bibitem{source}
            Marcelo Sousa, Justin Paston-Cooper, Paul van der Walt,
            \emph{Project source code},
            \url{https://github.com/toothbrush/agda-gp/tree/master/src},
            2011.
    \end{thebibliography}




\end{document}
