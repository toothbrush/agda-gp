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

The aim of this project was to embed LIGD and Spine in Agda, a dependently typed programming language,
and then to define a (partial) isomorphism between the two styles of generic views.

As a result of some implementational difficulties (LIGD proved impractical to implement in Agda) we switched from
LIGD to Regular. The details of how and why can be found in the following sections.

As it turns out, any Regular representation can be translated into a Spine representation, but not all Spine representations
can be translated into Regular (in particular existential types pose a problem in Regular).

\section{LIGD in Agda}

We will now present our embedding of LIGD in Agda. It is unsurprising, but the problem we ran
into was that (most likely) infinite recursion was being done when Agda was type-checking our definitions.
The reason for this would be the explicit recursion that LIGD relies on.

The workaround was eventually to implement a mapping between Regular and Spine instead, since in Regular recursion is modeled
by an extra parameter. This allowed all functions to be terminating. In Regular one models the pattern functor, then applies the least fixed-point
operator which results in a representation which is isomorphic to the to-be-represented type.



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
