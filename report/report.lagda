%input report.fmt
\documentclass[a4paper]{article}

\title{Isomorphism between Regular and Spine in Agda}
\date{\today}
\begin{document}

\maketitle

\begin{abstract}
    
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



\section{Spine in Agda}


\section{The embedding}

Spine has support for existential types, since it allows arbitrary parameters to be used in its Signature type. Therefore, it's not possible to translate
all Spine representations into Regular. We can, however, translate a subset of Spine into Regular, as is done in the following code example.


\end{document}
