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
\title{Embedding Datatype-Generic Views in Agda}
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

The idea of datatype generic programming is that a user defines a
function once over a set of building blocks of a system, and then the
function works for all types which are representable by those building
blocks. The system provides methods of converting to and from a normal
value, for example in Agda, to a representation. Once it has been
converted, the defined function can be applied. Even though many
libraries represent datatypes similarly (such as the sum-of-products
view), we believe believe that there are still similarities to be
explored. The aim of the project was to discover similarities between
Spine and a sum-of-products view such as LIGD and Regular.

The full source code of the presented work can be downloaded from the
repository. \cite{source}

\section{Goal} 
The goal of the project was to show an embedding
relation between algebraic datatype representation systems such as
LIGD, Regular and Spine. Below are presented embeddings of the
respective universes for each of the listed systems.

To show an embedding of a system A into a system B, one must define a
conversion of the codes in A to the codes in B, showing that this
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

As stated, we initially decided to explore the similarity between
LIGD, which uses the sum-of-products view, and the spine view, which
consists of lists of signatures, where a single signature contains a
constructor along with the types of its parameters. Consider for
example the representation of the common Haskell-like |List a| data
structure in both libraries. In Spine:

\begin{code}
listRep-S : {a : Set} → Type a → List (Signature a)
listRep-S a = Sig [] ∷ [ Sig (_∷_) · (par , a) · (rec , (listRep-S a)) ]
\end{code}

\dots and in LIGD:

\begin{code}
listRep-L : LCode → LCode
listRep-L a = U ⊎ (a × (listRep-L a))
\end{code}

It is intuitive that the terms of a single product in the
sum-of-products view correspond to the parameters of a constructor,
which are chained together using the |_·_| operator in Spine. It is
also intuitive that the terms in sums correspond to the alternatives
of a datatype, which are modelled using elements of the signature list
in the Spine view. In other words, one can replace list concatenation
with sums, and the |_·_| operator with products to obtain an LIGD
representation of a datatype, from a Spine representation.

The first step in exploring the similarities between these
representational styles is to embed them into Agda. This embedding is
detailed in the following section.

\subsection{LIGD}

LIGD is a Haskell datatype generic programming library encorporating
the sum-of-products view, which we have modelled in Agda. It relies on
shallow recursion and a universe which includes an interpretation
function to convert a code, representing a type, into an Agda type.

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

As detailed later, problems were encountered as a result of the
shallow recursion which LIGD uses, along with the termination checking
property of Agda. As a result of this, we decided to switch to an
embedding of the Regular library in Agda, since it makes use of
explicit recursion in its codes with |I|.

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

\subsection{Spine}

Here we present the universe of Spine embedded in Agda. Notice that
the |Type| datatype represents the types which are representable in
Spine, which implies that the spine universe is closed. The |Type?|
datatype is an extension to Spine to tag arguments as parameters or
recursive positions for type decideability in Agda.

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

Types are represented in Spine by providing a list of |Signature|s,
where a |Signature| corresponds to one constructor of a datatype. A
|Signature|, as can be seen above, consists of the constructor itself,
along with type representations for each of it's parameters, separated
by the |_·_| operator. See for example the representation of the
well-known |List a| data type in Spine.

The |sigList| function is a function which the user of the library should
provide, giving the list of signatures for each supported type in the Spine universe. This is
a convenient and uniform method of storing the representations as presented above.

\begin{code}
sigList : {a : Set} → Type a → List⁺ (Signature a)
sigList bool = Sig true ∷ [ Sig false ]
sigList nat  = Sig zero ∷ [ Sig suc · (rec , nat) ]
sigList (list a) = Sig [] ∷ [ Sig (_∷_) · (par , a) · (rec , list a) ]
\end{code}

Finally, we can easily define the functions |fromSpine| and |toSpine|
that respectively decode and encode a |Spine| value.

\begin{code}
fromSpine : {a : Set} -> Spine a -> a
fromSpine (Con c) = c
fromSpine (f :<>: (x :> _)) = (fromSpine f) x

toSpine : {a : Set} -> Type a -> a -> Spine a
toSpine nat zero  = Con zero
toSpine nat (suc n) = Con suc :<>: (n :> nat)
toSpine bool b = Con b
toSpine (list a) [] = Con []
toSpine (list a) (_∷_ x xs) = Con _∷_ :<>: (x :> a) :<>: (xs :> list a) 
\end{code}

\section{Initial Attempt: Spine to LIGD} Taking a representation in
LIGD of a given datatype, the datatype is explicitly referred to in
the recursive position. Consider the LIGD representation of the usual
|[ a ]| datatype for a given type |a|.

\begin{code}
rList : LCode → LCode
rList RA = rsum runit (rprod RA (rList RA))
\end{code}

Because the argument of the recursive call is not structurely smaller 
the function will not be valid for the termination checker in Agda. 
However since the termination checker can be disabled, 
the real problem is that because later we need to define a function for value
conversion and the code conversion function will be in the type signature
of that function. In Agda all expressions in a signature must terminate.

We later chose to implement a conversion from Spine to Regular.
Regular is similar to LIGD in its sum-of-products approach, but there is an extra parameter to every code for
explicit representation of recursion.
Using regular allowed the conversion functions we defined later, to terminate.

\section{Spine to Regular}

We start by defining the function |convert| that converts a |Spine| type into a |Regular| representation of that |Spine| type by using the list of |Signature|s:

\begin{code}
convert : {A : Set} → Type A → Code
convert tyA = makeSum (sigList tyA)
\end{code}
The function |convert| uses the function |makeSum| which implements the conversion method described in Section 3. 
\begin{code}
makeSum : {A : Set} → List⁺ (Signature A) → Code
makeSum [ x ] = makeProd x
makeSum (x ∷ xs) = makeProd x ⊕ makeSum xs
\end{code}
Given an non-empty list of |Signature| A, every |Signature| corresponds to a product of the sum.
\begin{code}
makeProd : {B : Set} → Signature B → Code
makeProd (Sig _) = U
makeProd (Sig _ · (con , t)) = K $ decodeType t
makeProd (Sig _ · (rec , t)) = I
makeProd (s · (con , t)) = makeProd s ⊗ K (decodeType t)
makeProd (s · (rec , t)) = makeProd s ⊗ I
\end{code}

The function |makeProd| translates a |Signature| to a |Regular| code
by pattern matching on the |Signature|. If the constructor does not
have arguments we produce |U|.  In the case that the constructor has
one argument, we pattern match on the pair |Type? × Type b|: A
parameter is tagged with |con| and a recursive position with |rec|
respectively corresponding to |K| and |I| in |Regular|. Since |_·_| is
left associative, if the constructor has more than one argument then
we pattern match on the pair to identify whether it is a parameter or
a recursive position and construct the product by recursively calling
|makeProd| on the left arguments.

Now that we have a generic function to convert a list of signatures
representing a |Spine| type into a |Regular| representation we define
functions that, given a |Spine| type and a |Spine| value, convert that
value to its |Regular| value.

\begin{code}
S→R : {A : Set} → (tyA : Type A) → Spine A → μ (convert tyA)
S→R tyA s = from tyA (fromSpine s) 
\end{code}
and also the inverse:
\begin{code}
R→S : {A : Set} → (tyA : Type A) → μ (convert tyA) → Spine A
R→S tyA r = toSpine tyA (to tyA r)
\end{code}

Since we have the |fromSpine| and |toSpine| functions that
respectively decode and encode a |Spine| value, we define the
functions |from| and |to|.

\begin{code}
from : {A : Set} → (tyA : Type A) → A → μ (convert tyA)
from bool true = < inj₁ tt >
from bool false = < inj₂ tt >
from nat zero = < inj₁ tt >
from nat (suc n) = < inj₂ (from nat n) >
from (list a) [] = < inj₁ tt >
from (list a) (x ∷ xs) with decodeType a | decodeType a ≡A | from (list a) xs
... | p | refl | z = < inj₂ (x , z) >
\end{code}

The function |from| encodes a |Regular| value representing a |Spine|
value that was decoded to an Agda value by |fromSpine|. In the case of
|list a| we construct a proof that the type parameter |a| of |list a|
is the same as the one we are trying to encode. The proof is
constructed by the function |decodeType_≡A|:

\begin{code}
decodeType_≡A : {A : Set} -> (ty : Type A) → decodeType ty ≡ A
decodeType nat ≡A  = refl
decodeType bool ≡A = refl
decodeType (list a) ≡A with decodeType a | decodeType a ≡A
... | x | refl = refl
\end{code}

The proof is trivial except for the |list a| case where we also need
to construct a proof for the parameter |a|. 

The function |to| decodes a |Regular| value from a |Regular| code that
was produced by |convert|, i.e. a |Regular| value for which we know
that there is a correspondent |Spine| value.

\begin{code}
to : {A : Set} → (tyA : Type A) → μ (convert tyA) → A
to nat  < inj₁ tt > = zero 
to nat  < inj₂ n >  = suc $ to nat n
to bool < inj₁ tt > = true
to bool < inj₂ tt > = false
to (list a) < inj₁ tt > = []
to (list a) < inj₂ (x , xs) > with decodeType a | decodeType a ≡A | to (list a) xs
... | p | refl | z = x ∷ z 
\end{code}

\section{Related work}

Related work has been carried out regarding exploring and formalising
relations between different generic datatype views in Agda (L\"oh and
Magalh\~aes, \cite{loh}), where injections from Regular to other
libraries such as PolyP, Multirec, Indexed and Instant Generics have
been presented.

\section{Our contribution}
As one can see in Figure \ref{fig:conversions}, the contribution of
this project fits nicely with that of L\"oh and Magalh\~aes.  Namely,
we provide an injection from Spine into Regular, which in turn already
has injections to other libraries. Note that we have investigated the
Spine view, as opposed to the more common sum-of-products view, on
which all the libraries investigated by L\"oh and Magalh\~aes are
based.

\begin{figure}[h]
    \begin{center}
        \includegraphics[width=\textwidth]{conversions}
    \end{center}
    \caption{Relation of embeddings of various libraries. The dotted line indicates previous work. \cite{loh}}
    \label{fig:conversions}
\end{figure}

We have claimed an injective embedding of the Spine system into the
Regular System. Our embedding is carried out by |convert|, which takes
a Spine type representation and gives the corresponding regular
representation based on the signature list, and by the value
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

We had previously tried to define a |makeProd| function with the type
|{a : Set} → Type a → Signature a → Code|. In deconstructing the given
signature, any type matching the given |Type a| value would be seen as
the recursive position, and any other type would be seen as a
parameter. Trying to define |makeProd| in this way, we ran into
problems in checking equalities of the Spine type representations, and
we had many more issues with the Agda type checker. We were not able
to complete such a definition in the time provided, but it may be
possible with further work.


\subsection{Further Genericity of |from| and |to|}
The |convert| function is generic in the sense that its definition is
not dependent on the currently defined Spine universe of types, which
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

\section{Conclusion} We have shown an injective embedding of Spine
into Regular. We have provided functions for converting
representations from one generic system to the other, and we have
presented several suggestions for future work. While the value
conversion functions are not as generic as desired, the project has
demonstrated a concrete relationship between the Spine and Regular
universes. Further work on defining a conversion of Regular into Spine
would be worthwhile. As a final remark, we believe that it is possible
to further formalise the given relationships using Agda's power as a
proof assistant.


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