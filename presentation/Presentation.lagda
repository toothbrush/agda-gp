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

\usetheme{madrid}


\title{Embedding Generic Datatype Views in Agda}
\date{\today}
\author{Us}
\institute[UU]{Utrecht University}
\setcounter{tocdepth}{1}

\begin{document}
\begin{frame}{Motivation}
\begin{itemize}
\item Spine : List of signatures
\item LIGD : Sum of products
\item Spine and LIGD have a noticeable similarity
\item Signatures of constructors correspond to products
\item List of signatures corresponds to sum
\end{itemize}
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
\end{spec}
\end{frame}
\begin{frame}
\begin{spec}
data Spine : Set -> Set where
  Con : ∀ {a} -> a -> Spine a
  _:<>:_ : ∀ {a b} -> Spine (a -> b) -> Typed a -> Spine b

data Signature a : Set where
  Sig : a -> Signature a
  _·_ : {b : Set} → Signature (b → a) → Type? × Type b → Signature a

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
\end{itemize}
\begin{spec}
makeProdRep : {a : Set} -> (b : Signature a) -> Rep (makeProd b)
makeProdRep (Sig _ · (ListR y)) with makeRep y
... | ra = {!!} 

\end{spec}
\end{frame}
\begin{frame}{Contribution}
\end{frame}
\begin{frame}{Related Work}
\end{frame}
\begin{frame}{Critical Analysis}
\end{frame}
\maketitle
\end{document}
