\begin{tikzpicture}[%
  scale=1.0,
  lib/.style={rectangle,draw=uuyblue!70!black,fill=uuyblue!20!white,thick,minimum width=2.6cm,minimum height=1.5cm,text centered,text width=2.6cm},
  embeds/.style={ ->,very thick}
]%
\node (regular)     at ( 0, 2) [lib] {Regular\\\small |I1|\ \,|⊕|\,\ \,|⊗|};
\node (polyp)       at ( 3.3, 0) [lib] {PolyP\\\small |I1|\ |P'1|\ \,|⊕|\,\ \,|⊗|\,\ \,|⊚|};
\node (coinductive) at ( 0,-4) [lib] {InstantGenerics\\\small |R'| \,|⊕|\,\ \,|⊗|};
\node (multirec)    at (-3.3, 0) [lib] {Multirec\\\small |In|\ \,|⊕|\,\ \,|⊗|};
\node (indexed)     at ( 0,-2) [lib] {Indexed\\\small |In|\ |P'n| \,|⊕|\,\ \,|⊗|\,\ \,|⊚|\,\ |Fix|};
\draw [embeds] (regular)  -- (polyp);
%\draw [embeds] (regular)  -- (coinductive);
%\draw [embeds] (polyp)    -- (coinductive);
\draw [embeds] (indexed)  -- (coinductive);
\draw [embeds] (multirec) -- (indexed);
\draw [embeds] (regular)  -- (multirec);
\draw [embeds] (polyp)    -- (indexed);
\end{tikzpicture}
