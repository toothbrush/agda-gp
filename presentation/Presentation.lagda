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

\newenvironment{changemargin}[2]{%
  \begin{list}{}{%
    \setlength{\topsep}{0pt}%
    \setlength{\leftmargin}{#1}%
    \setlength{\rightmargin}{#2}%
    \setlength{\listparindent}{\parindent}%
    \setlength{\itemindent}{\parindent}%
    \setlength{\parsep}{\parskip}%
  }%
  \item[]}{\end{list}}


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
\begin{frame}
    \tableofcontents
\end{frame}
\section{Motivation}
\begin{frame}{Motivation}
\begin{itemize}
\item Spine : List of signatures
\item LIGD : Sum of products
\item Spine and LIGD have a noticeable similarity
\end{itemize}
\end{frame}

\begin{frame}{Similarity}

\begin{itemize}
    \item Signatures of constructors correspond to products
    \item List of signatures corresponds to sum
\end{itemize}
Representation of list in LIGD vs. Spine

\begin{spec}
sigList : {a : Set} → Type a → List (Signature a)
sigList (list a) = Sig [] ∷ (Sig (_∷_) · a · (list a)) ∷ []

ListRep : LCode → LCode
ListRep a = U ⊎ (a × (ListRep a))
\end{spec}
\nt{we modified this, though (the rec/con construction)}
\nt{Point out how NatR is the recursive position}
\end{frame}

\section{The Problem}
\begin{frame}{Problem}
\begin{itemize}
\item Explore the extent of the similarity
\item If possible, prove a concrete structural relation (isomorphism, injection, $\dotsc$)
\nt{Wanted to see how far the universe could be extended keeping a relation}
\item Possible (generic) conversion of codes and values between LIGD and Spine
\end{itemize}
\end{frame}
\section{Method}
\begin{frame}{Method}
\begin{itemize}
\item Embed Spine and LIGD in Agda
\end{itemize}
\begin{spec}
data Type : Set → Set where
  bool : Type Bool
  nat  : Type ℕ
  list : {a : Set} → Type a → Type (List a)

data Type? : Set where
  par : Type?
  rec : Type?

data Typed (a : Set) : Set where
  _▹_ : a → Type a → Typed a
\end{spec}\nt{type? is for pattern matching on type representations, we ran into problems proving equality of types. (in makeproduct. the recursive case needs to be identified, but this wasn't possible, so we marked it)}
\end{frame}
\begin{frame}{Spine Universe}
\begin{spec}
data Spine : Set → Set where
  Con : ∀ {a} → a → Spine a
  _◆_ : ∀ {a b} → Spine (a → b) → Typed a → Spine b

data Signature a : Set where
  Sig : a → Signature a
  _·_ : {b : Set}   → Signature (a → b) 
                    → Type? × Type a → Signature b

fromSpine : {a : Set} → Spine a → a
fromSpine (Con c) = c
fromSpine (f ◆ (x ▹ _)) = (fromSpine f) x
\end{spec}
\begin{spec}
sigList : {a : Set} → Type a → List⁺ (Signature a)
sigList bool = Sig true ∷ [ Sig false ]
sigList nat  = Sig zero ∷ [ Sig suc · (rec , nat) ]
sigList (list a) = Sig [] ∷ [ (Sig (_∷_) · (par , a) · (rec , list a)) ]
\end{spec}
\end{frame}
\begin{frame}{LIGD Universe}
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
rList : LCode → LCode
rList ra = rtype isoList (rsum runit (rprod ra (rList ra)))

makeProdRep : {a : Set} → (b : Signature a) → LCode
makeProdRep (Sig _ · (list y)) with makeRep y
... | ra = {!rList !}
\end{spec}
\begin{itemize}
    \item Might be possible
    \item Switched to Regular and Spine as a result
\end{itemize}
\end{frame}

\begin{frame}{Regular}
    Our Regular universe\nt{Marcelo's bit starts here, he'll talk about conversion of representations.}

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

\begin{frame}{Injection of Spine in Regular}
Now we want functions
\begin{spec}
S→R : {A : Set} → (tyA : Type A) → Spine A → μ (convert tyA)

R→S : {A : Set} → (tyA : Type A) → μ (convert tyA) → Spine A
\end{spec}

To start with, convert representations.
\end{frame}

\begin{frame}{Convert representations}
\begin{spec}
makeProd : {B : Set} → Signature B → Code
makeProd (Sig _) = U
makeProd (Sig _ · (par , t)) = K ( decodeType t )
makeProd (Sig _ · (rec , t)) = I
makeProd (s · (par , t)) = makeProd s ⊗ K (decodeType t)
makeProd (s · (rec , t)) = makeProd s ⊗ I

makeSum : {A : Set} → List⁺ (Signature A) → Code
makeSum [ x ] = makeProd x
makeSum (x ∷ xs) = makeProd x ⊕ makeSum xs

convert : {A : Set} → Type A → Code
convert tyA = makeSum (sigList tyA)
\end{spec}
\nt{|_._| is left-associative}
\nt{conversion of signature to a code}
\nt{conversion of list of signatures to code}
\nt{Conversion of Spine Type into Regular}
\end{frame}
%% \begin{frame}{Lists of signatures}
%% \begin{itemize}
%% \item User defined spine representation of datatypes
%% \item They are needed for producing a sum containing all constructors
%% \end{itemize}
%% \begin{spec}
%% sigList : {a : Set} → Type a → List⁺ (Signature a)
%% sigList bool = Sig true ∷ [ Sig false ]
%% sigList nat  = Sig zero ∷ [ Sig suc · (rec , nat) ]
%% sigList (list a) = Sig [] ∷ [ (Sig (_∷_) · (par , a) · (rec , list a)) ]
%% \end{spec}
%% \nt{This is provided by the user}
%% \end{frame}
%% %% from : {A : Set} → (tyA : Type A) → A → μ (convert tyA)
%% from (list a) < inj₁ tt > = []
%% from (list a) < inj₂ (x , xs) > with decodeType a | decodeType a ≡A | from (list a) xs
%% ... | p | refl | z = x ∷ z 
\begin{frame}{Showing injection}
\begin{spec}
from : {A : Set} → (tyA : Type A) → A → μ (convert tyA)

to : {A : Set} → (tyA : Type A) → μ (convert tyA) → A
to (list a) [] = < inj₁ tt >
to (list a) (x ∷ y) with decodeType a | decodeType a ≡A | to (list a) y
... | _ | refl | z = < inj₂ (x , z) >

decodeType_≡A : {A : Set} → (ty : Type A) → decodeType ty ≡ A
decodeType (list a) ≡A with decodeType a | decodeType a ≡A
... | _ | refl = refl
\end{spec}
\nt{@convert@ gives a spine injection into Regular}
\nt{Mention that only case for list is given}
\nt{decodeType is the interpretation function}
\end{frame}



\begin{frame}{Showing injection}
    \begin{spec}
S→R : {A : Set} → (tyA : Type A) → Spine A → μ (convert tyA)
S→R tyA s = from tyA (fromSpine s) 

R→S : {A : Set} → (tyA : Type A) → μ (convert tyA) → Spine A
R→S tyA r = toSpine tyA (to tyA r)
    \end{spec}
    \nt{Justin's bit starts here}
\end{frame}
\section{Related work}
\begin{frame}{Related Work}
\begin{itemize}
    \item Formally comparing approaches to datatype-generic programming, using Agda  (Jos\'{e} Pedro Magalh\~aes, Andres L\"oh)\cite{loh}
\end{itemize}
\begin{figure}[h]
    \begin{center}
        \includegraphics[width=\textwidth]{conversions}
    \end{center}
    \label{fig:conversions}
\end{figure}
\end{frame}
\section{Contribution}
\begin{frame}{Contribution}
\begin{itemize}
\item We have shown an injective embedding of Spine into Regular
\item Automatic conversion of representations
\end{itemize}
\end{frame}
\section{Critical Analysis}
\begin{frame}{Critical Analysis}
    \begin{itemize}
        \item We have shown an embedding of the Spine universe inside that of Regular 
        \item This was done by converting Spine codes to Regular codes
        \item With the from and to functions, we then converted between Regular
              representations of spine values and concrete Agda values
        \item |R→S| can be seen to be a left-inverse of |S→R| ($\Rightarrow$ |S→R| is injective)
    \end{itemize}
\end{frame}
\begin{frame}{Further development}
    \begin{itemize}
        \item Make |to| and |from| generic w.r.t. values.\nt{when converting from regular, }

    \end{itemize}
\begin{spec}
applyParams : {a : Set}     → (sig : Signature a) 
                            → ⟦ makeProd sig ⟧ a → a

 \end{spec}   
 \begin{spec}
chooseSig : {a : Set} → List⁺ (Signature a) → μ (convert tyA) → A
chooseSig (sig ∷ rest) < inj₁ val > = applyParams sig val
chooseSig (_ ∷ rest)   < inj₂ val > = chooseSig rest val
 \end{spec}   
 \begin{spec}

to : {a : Set} → (tyA : Type a) → μ (convert tyA) → A
to tyA val with (sigList tyA)
... | [singleSig] = applyParams singleSig val
... | multiple = chooseSig multiple val
               
 \end{spec}   
\end{frame}
\begin{frame}
    \begin{thebibliography}{9}

        \bibitem{loh}
            L{\"o}h, A. and Magalh{\~a}es, J.P.,
            \emph{Formally comparing approaches to datatype-generic programming, using Agda} (talk).
            2011.
    \end{thebibliography}
\end{frame}
\end{document}
