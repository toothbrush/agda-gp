\def\textmu{}

\RequirePackage{xcolor}
\newcommand{\ty}[1]{{\color{orange}\mathsf{#1}}}
\newcommand{\con}[1]{{\color{blue}\mathsf{#1}}}
\newcommand{\consymop}[1]{{\color{blue}\mathsf{#1}}}
\newcommand{\consym}[1]{{\color{blue}\mathsf{#1}}}
\newcommand{\id}[1]{{\color{blue}\mathsf{#1}}}


\newcommand{\ppause}{\pause \vspace{-3em}}

%\newcommand{\ty}[1]{{\color{orange}\mathsf{#1}}}
\colorlet{darkgreen}{green!30!black}
%\newcommand{\con}[1]{{\color{darkgreen}\mathsf{#1}}}
%%\newcommand{\consym}[1]{\mathord{\color{darkgreen}{\mathord{#1}}}}
%\newcommand{\consym}[1]{\mathrel{\color{darkgreen}{\mathord{\!#1\!}}}}
%\newcommand{\consymop}[1]{\mathrel{\color{darkgreen}{\mathsf{\_\!\!#1\!\!\_}}}}
%%\newcommand{\id}[1]{{\color{blue}\Varid{#1}}}
%\newcommand{\id}[1]{\Varid{#1}}
%\newcommand{\goal}[1]{{\color{red}\mathsf{#1}}}
%\newcommand{\keyw}[1]{\mathbf{#1}}
%\definecolor{lightgray}{gray}{0.50}
%\definecolor{darkgray}{gray}{0.45}

%include agda-gp-talk.fmt

% kill another warning:
\usepackage{textcomp}
\usepackage{verbatim}
\usepackage{graphicx}
\usepackage{latexsym}
\usepackage{amsfonts}
\usepackage{tikz}
\usepackage{dsfont}
\usepackage{listings}
\usepackage{amsmath}

\newcommand{\nt}[1]{\note{\ensuremath{\circ} ~ ~ ~#1 \\ }}
% get rid of LaTeX-beamer warning:
\let\Tiny=\tiny
% hm a bit ugly but ok:
\usepackage[T1]{fontenc}

\usetheme{Madrid}


\title[Generics in Agda]{Embedding Generic Datatype Views in Agda}
\date{\today}
\author[MABS, JPC, PvdW]{Marcelo Sousa, Justin Paston-Cooper, Paul van der Walt}
\institute[UU]{Utrecht University}
\setcounter{tocdepth}{1}

\begin{document}
\maketitle
\begin{frame}{Motivation}
\begin{itemize}
\item Spine : List of signatures
\item LIGD : Sum of products
\item Spine and LIGD have a noticeable similarity
\item Signatures of constructors correspond to products
\item List of signatures corresponds to sum
\end{itemize}
\end{frame}

\begin{frame}
    Similarity:

\begin{spec}
NatRep : Code
NatRep = U ⊎ I

datatype : {a : Set} -> Type a -> List (Signature a)
datatype NatR  = (Sig zero) ∷ ((Sig suc · NatR) ∷ [])
\end{spec}\nt{we modified this, though}

\end{frame}


\begin{frame}{Problem}
\begin{itemize}
\item Explore the extent of the similarity
\item If possible, prove a concrete structural relation (isomorphism, injection, $\dotsc$)
\nt{Wanted to see how far the universe could be extended keeping a relation}
\item Possible (generic) conversion of codes and values between LIGD and Spine
\end{itemize}
\end{frame}
\begin{frame}{Method}
\begin{itemize}
\item Embed Spine and LIGD in Agda
\end{itemize}
\begin{spec}
data Type : Set -> Set where
  bool : Type Bool
  nat  : Type ℕ
  list : {a : Set} -> Type a -> Type (List a)

data Type? : Set where
  con : Type?
  rec : Type?

data Typed (a : Set) : Set where
  _:>_ : a -> Type a -> Typed a
\end{spec}\nt{type? is for pattern matching on type representations, we ran into problems proving equality of types. (in makeproduct. the recursive case needs to be identified, but this wasn't possible, so we marked it)}
\end{frame}
\begin{frame}
\begin{spec}
data Spine : Set -> Set where
  Con : ∀ {a} -> a -> Spine a
  _:<>:_ : ∀ {a b} -> Spine (a -> b) -> Typed a -> Spine b

data Signature a : Set where
  Sig : a -> Signature a
  _·_ : {b : Set}   → Signature (b → a) 
                    → Type? × Type b → Signature a

fromSpine : {a : Set} -> Spine a -> a
fromSpine (Con c) = c
fromSpine (f :<>: (x :> _)) = (fromSpine f) x
\end{spec}
\end{frame}
\begin{frame}
\begin{spec}
data LCode : Set where
  runit : LCode
  rnat : LCode
  rsum : LCode → LCode → LCode
  rprod : LCode → LCode → LCode
  rtype : (A : Set) → (A → LCode) → (LCode → A) → LCode

L⟦_⟧ : LCode → Set
L⟦ runit ⟧ = ⊤
L⟦ rnat ⟧ = ℕ
L⟦ rsum r₁ r₂ ⟧ = L⟦ r₁ ⟧ + L⟦ r₂ ⟧
L⟦ rprod r₁ r₂ ⟧ = L⟦ r₁ ⟧ × L⟦ r₂ ⟧
L⟦ rtype t _ _ ⟧ = t
\end{spec}
\end{frame}
\begin{frame}{Problem with LIGD}
\begin{itemize}
\item Wanted function of type |convert : Type a → LCode|
\item Ran into difficulties regarding recursion representation in LIGD
\end{itemize}
\begin{spec}
rList : ∀ {A} → Rep A → Rep (List A)
rList ra = RType isoList (RSum RUnit (RProd ra (rList ra)))

makeProdRep : {a : Set} -> (b : Signature a) -> Rep (makeProd b)
makeProdRep (Sig _ · (ListR y)) with makeRep y
... | ra = {!!}
\end{spec}
\begin{itemize}
    \item In retrospect might be solvable
    \item Switched to Regular and Spine as a result
\end{itemize}
\end{frame}

\begin{frame}{Regular}
Our Regular universe

\begin{spec}
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
\end{spec}
\end{frame}

\begin{frame}
Now we want functions
\begin{spec}
S→R : {A : Set} → (tyA : Type A) → Spine A → μ (convert tyA)

R→S : {A : Set} → (tyA : Type A) → μ (convert tyA) → Spine A
\end{spec}

To start with, convert representations.
\end{frame}

\begin{frame}
\begin{spec}
-- Convert a signature to a code
makeProd : {B : Set} → Signature B → Code
makeProd (Sig _) = U
makeProd (Sig _ · con , t) = K $ interpretSTRep t
makeProd (Sig _ · rec , t) = I
makeProd (s · con , t) = makeProd s ⊗ K (interpretSTRep t)
makeProd (s · rec , t) = makeProd s ⊗ I

-- Convert a list of signatures to a code
makeSum : {A : Set} → List⁺ (Signature A) → Code
makeSum [ x ] = makeProd x
makeSum (x ∷ xs) = makeProd x ⊕ makeSum xs

-- Convert a Spine Type to a Code in Regular
convert : {A : Set} → Type A → Code
convert tyA = makeSum (sigList tyA)
\end{spec}
\end{frame}
\begin{frame}{Lists of signatures}
\begin{itemize}
\item User defined spine representation of datatypes
\item They are needed for producing a complete sum
\end{itemize}
\begin{spec}
sigList : {a : Set} -> Type a -> List⁺ (Signature a)
sigList bool = Sig true ∷ [ Sig false ]
sigList nat  = Sig zero ∷ [ (Sig suc · rec , nat) ]
sigList (list a) = Sig [] ∷ [ (Sig (_∷_) · con , a · rec , (list a)) ]
\end{spec}
\nt{This is provided by the user}
\end{frame}
%% from : {A : Set} → (tyA : Type A) → A → μ (convert tyA)
%% from (list a) < inj₁ tt > = []
%% from (list a) < inj₂ (x , xs) > with decodeType a | decodeType a ≡A | from (list a) xs
%% ... | p | refl | z = x ∷ z 
\begin{frame}
\begin{spec}
S→R : {A : Set} → (tyA : Type A) → Spine A → μ (convert tyA)
S→R tyA s = from tyA (fromSpine s) 

R→S : {A : Set} → (tyA : Type A) → μ (convert tyA) → Spine A
R→S tyA r = toSpine tyA (to tyA r)

to : {A : Set} → (tyA : Type A) → μ (convert tyA) → A
to (list a) [] = < inj₁ tt >
to (list a) (x ∷ xs) with decodeType a | decodeType a ≡A | to (list a) xs
... | p | refl | z = < inj₂ (x , z) >

toSpine : {a : Set} -> Type a -> a -> Spine a
toSpine (list a) [] = Con []
toSpine (list a) (_∷_ x xs) = Con _∷_ :<>: (x :> a) :<>: (xs :> list a) 

interpretSTRep_≡A : {A : Set} -> (ty : Type A) → interpretSTRep ty ≡ A
interpretSTRep (list a) ≡A with interpretSTRep a | interpretSTRep a ≡A
... | x | refl = refl
\end{spec}
\nt{@convert@ gives a spine injection into Regular}
\nt{Mention that only case for list is given}
\nt{interpretSTRep is the interpretation function}
\end{frame}
\begin{frame}{Contribution}
\begin{itemize}
\item We have shown an injective embedding of Spine into Regular
\item Automatic conversion of representations 
\end{itemize}
\end{frame}
\begin{frame}{Related Work}
\end{frame}
\begin{frame}{Critical Analysis}
\end{frame}
\end{document}
