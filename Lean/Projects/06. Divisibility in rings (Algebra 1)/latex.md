\documentclass{article}
\usepackage{amsmath, amssymb}

\title{Teilbarkeit}
\author{Elias und Petr\\
Proseminar über computergestützte Mathematik,\\
Heidelberg, Sommersemester 2024}
\date{}

\begin{document}

\maketitle

\section*{Einleitung}
In diesem Projektsketch definieren wir irreduzible und prime Elemente eines kommutativen Rings. Das Ziel ist es, faktorisierbare Ringe zu definieren und zu zeigen, dass in einem faktorisierbaren Ring jedes irreduzible Element prim ist.

\section*{Grundlagen}
\begin{itemize}
    \item Sei \( R \) ein kommutativer Ring.
    \item Wir sagen, dass ein Element \( x \in R \) \( y \in R \) teilt, wenn und nur wenn \( y \) ein Vielfaches von \( x \) ist. Formal: \( x \mid y \) wenn es ein \( a \in R \) gibt, so dass \( y = a \cdot x \).
    \item Wenn Null \( x \) teilt, dann muss \( x \) Null sein.
    \item Wenn \( x \) ein nicht-null Element \( y \) teilt, dann ist \( x \) nicht-null.
    \item Zwei Elemente \( x \) und \( y \) heißen assoziiert, wenn und nur wenn \( x \) und \( y \) bis auf eine Einheit übereinstimmen. Formal: \( x \) und \( y \) sind assoziiert, wenn es eine Einheit \( a \in R \) gibt, so dass \( y = a \cdot x \).
    \item Ein Element \( x \in R \) ist nicht-trivial, wenn es weder Null noch eine Einheit ist.
    \item Ein Element \( x \in R \) ist irreduzibel, wenn es nicht-trivial ist und immer wenn \( x = a \cdot b \), dann ist entweder \( a \) eine Einheit oder \( b \) eine Einheit.
    \item Ein Element \( x \in R \) ist prim, wenn es nicht-trivial ist und immer wenn \( x \mid a \cdot b \), es einen der Faktoren teilt.
\end{itemize}

\section*{Hauptergebnisse}
\begin{enumerate}
    \item In einem Integritätsbereich ist jedes prime Element irreduzibel.
    
    \textbf{Beweis:}
    \begin{proof}
    Sei \( R \) ein Integritätsbereich und \( x \in R \) ein primes Element. Sei \( x \) prim und angenommen \( x = a \cdot b \). Da \( x \) prim ist, folgt, dass \( x \mid a \cdot b \). Nach Definition von Prim folgt, dass \( x \mid a \) oder \( x \mid b \). Angenommen \( x \mid a \), dann gibt es ein \( c \in R \) so dass \( a = c \cdot x \). Somit ist \( x = c \cdot x \cdot b \). Da \( R \) ein Integritätsbereich ist und \( x \neq 0 \), folgt \( c \cdot b = 1 \), also ist \( c \) eine Einheit. Analog ist \( b \) eine Einheit, wenn \( x \mid b \). Daher ist \( x \) irreduzibel.
    \end{proof}
    
    \item Definiere faktorisierbare Ringe (auch genannt eindeutige Faktorisierungsdomänen) und zeige, dass in jedem faktorisierbaren Ring jedes irreduzible Element prim ist.
    
    \textbf{Definition:}
    \begin{definition}
    Ein Ring \( R \) ist faktorisierbar, wenn jedes nicht-null und nicht-einheitliche Element als Produkt von irreduziblen Elementen geschrieben werden kann und diese Zerlegung bis auf die Reihenfolge und Assoziiertheit eindeutig ist.
    \end{definition}
    
    \textbf{Beweis:}
    \begin{proof}
    Sei \( R \) ein faktorisierbarer Ring und \( x \in R \) irreduzibel. Angenommen \( x \mid a \cdot b \). Da \( x \) irreduzibel ist, gibt es keine nicht-trivialen Zerlegungen von \( x \). Somit, wenn \( x = a \cdot b \), muss entweder \( a \) oder \( b \) eine Einheit sein, da \( x \) sonst als Produkt nicht-einheitlicher Elemente zerlegt werden könnte, was der Irreduzibilität widerspricht. Daher teilt \( x \) entweder \( a \) oder \( b \), was zeigt, dass \( x \) prim ist.
    \end{proof}
\end{enumerate}

\section*{Beweisdetails aus dem Lean-Code}
\begin{enumerate}
    \item \textbf{Lemma:} Wenn Null \( x \) teilt, dann ist \( x \) Null.
    
    \textbf{Beweis:}
    \begin{proof}
    Sei \( 0 \mid x \). Dann gibt es ein \( a \in R \) so dass \( x = a \cdot 0 \). Da \( a \cdot 0 = 0 \), folgt \( x = 0 \).
    \end{proof}

    \item \textbf{Lemma:} Wenn \( x \) ein nicht-null Element \( y \) teilt, dann ist \( x \) nicht-null.
    
    \textbf{Beweis:}
    \begin{proof}
    Sei \( x \mid y \) und \( y \neq 0 \). Angenommen \( x = 0 \). Dann gibt es ein \( a \in R \) so dass \( y = a \cdot x = a \cdot 0 = 0 \), was im Widerspruch zu \( y \neq 0 \) steht. Daher muss \( x \neq 0 \) sein.
    \end{proof}

    \item \textbf{Lemma:} Zwei Elemente \( x \) und \( y \) sind assoziiert, wenn und nur wenn sie sich gegenseitig teilen.
    
    \textbf{Beweis:}
    \begin{proof}
    Sei \( x \) und \( y \) assoziiert. Dann gibt es eine Einheit \( a \in R \) so dass \( y = a \cdot x \). Somit teilt \( x \) \( y \) und \( y \) \( x \), da \( a \) eine Einheit ist und es eine \( b = a^{-1} \) gibt, so dass \( x = b \cdot y \).
    
    Umgekehrt, wenn \( x \mid y \) und \( y \mid x \), dann gibt es \( a, b \in R \) so dass \( y = a \cdot x \) und \( x = b \cdot y \). Somit \( x = b \cdot a \cdot x \). Da \( R \) ein Integritätsbereich ist und \( x \neq 0 \), folgt \( b \cdot a = 1 \), also ist \( a \) eine Einheit und \( x \) und \( y \) sind assoziiert.
    \end{proof}

    \item \textbf{Theorem:} In einem faktorisierbaren Ring ist jedes irreduzible Element prim.
    
    \textbf{Beweis:}
    \begin{proof}
    Sei \( R \) ein faktorisierbarer Ring und \( x \) irreduzibel. Angenommen \( x \mid a \cdot b \). Da \( x \) irreduzibel ist, folgt, dass wenn \( x = a \cdot b \), dann ist entweder \( a \) oder \( b \) eine Einheit. Angenommen \( x \mid a \cdot b \), aber \( x \mid a \) nicht und \( x \mid b \) nicht. Dann wäre \( x \) keine Einheit und es gäbe keine Einheit \( u \), so dass \( x = u \cdot a \) oder \( x = u \cdot b \). Dies steht im Widerspruch zur Irreduzibilität von \( x \). Daher muss \( x \mid a \) oder \( x \mid b \). Also ist \( x \) prim.
    \end{proof}
\end{enumerate}

\end{document}