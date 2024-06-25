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
    \item Wir sagen, dass ein Element \( x \in R \) ein Element \( y \in R \) teilt, wenn und nur wenn \( y \) ein Vielfaches von \( x \) ist. Formal: \( x \mid y \), wenn es ein \( a \in R \) gibt, so dass \( y = a \cdot x \).
    \item Wenn Null \( x \) teilt, dann muss \( x \) Null sein.
    \item Wenn \( x \) ein nicht-null Element \( y \) teilt, dann ist \( x \) nicht-null.
    \item Zwei Elemente \( x \) und \( y \) heißen assoziiert, wenn und nur wenn \( x \) und \( y \) bis auf eine Einheit übereinstimmen. Formal: \( x \) und \( y \) sind assoziiert, wenn es eine Einheit \( a \in R \) gibt, so dass \( y = a \cdot x \). Eine Einheit ist ein Element, das ein multiplikatives Inverses hat.
    \item Ein Element \( x \in R \) ist nicht-trivial, wenn es weder Null noch eine Einheit ist.
    \item Ein Element \( x \in R \) ist irreduzibel, wenn es nicht-trivial ist und immer wenn \( x = a \cdot b \), dann ist entweder \( a \) eine Einheit oder \( b \) eine Einheit.
    \item Ein Element \( x \in R \) ist prim, wenn es nicht-trivial ist und immer wenn \( x \mid a \cdot b \), es einen der Faktoren teilt.
\end{itemize}

\section*{Hauptergebnisse}
\begin{enumerate}
    \item In einem Integritätsbereich ist jedes prime Element irreduzibel.
    
    \textbf{Beweis:}
    \begin{proof}
    Sei \( R \) ein Integritätsbereich und \( x \in R \) ein primes Element. Wir zeigen, dass \( x \) irreduzibel ist:
    \begin{enumerate}
        \item Sei \( x = a \cdot b \) für \( a, b \in R \).
        \item Da \( x \) prim ist, folgt aus \( x \mid a \cdot b \), dass \( x \mid a \) oder \( x \mid b \).
        \item Angenommen \( x \mid a \). Dann existiert ein \( c \in R \) mit \( a = c \cdot x \).
        \item Setze \( x = a \cdot b = (c \cdot x) \cdot b = c \cdot (x \cdot b) \).
        \item Da \( R \) ein Integritätsbereich ist und \( x \neq 0 \), folgt \( c \cdot b = 1 \). Somit ist \( c \) eine Einheit.
        \item Analog ist \( b \) eine Einheit, wenn \( x \mid b \).
        \item Daher ist \( x \) irreduzibel.
    \end{enumerate}
    \end{proof}
    
    \textbf{Beispiel:} 
    Betrachten wir den Ring der ganzen Zahlen \(\mathbb{Z}\). Das Element 2 ist prim, weil 2 nicht null und keine Einheit ist und wenn 2 ein Produkt teilt, teilt es einen der Faktoren. Wenn \(2 = a \cdot b\), dann muss einer der Faktoren eine Einheit sein (1 oder -1). Daher ist 2 irreduzibel.

    \item Definiere faktorisierbare Ringe (auch genannt eindeutige Faktorisierungsdomänen) und zeige, dass in jedem faktorisierbaren Ring jedes irreduzible Element prim ist.
    
    \textbf{Definition:}
    \begin{definition}
    Ein Ring \( R \) ist faktorisierbar, wenn jedes nicht-null und nicht-einheitliche Element als Produkt von irreduziblen Elementen geschrieben werden kann und diese Zerlegung bis auf die Reihenfolge und Assoziiertheit eindeutig ist.
    \end{definition}
    
    \textbf{Beweis:}
    \begin{proof}
    Sei \( R \) ein faktorisierbarer Ring und \( x \in R \) irreduzibel. Wir zeigen, dass \( x \) prim ist:
    \begin{enumerate}
        \item Angenommen, \( x \mid a \cdot b \). Dann gibt es ein \( c \in R \), so dass \( a \cdot b = c \cdot x \).
        \item Da \( x \) irreduzibel ist, kann \( x \) nicht weiter zerlegt werden, außer \( x = a \cdot b \) mit einer Einheit \( a \) oder \( b \).
        \item Angenommen \( x \mid a \cdot b \), aber \( x \mid a \) nicht und \( x \mid b \) nicht.
        \item Dann wäre \( x \) keine Einheit und es gäbe keine Einheit \( u \), so dass \( x = u \cdot a \) oder \( x = u \cdot b \).
        \item Dies steht im Widerspruch zur Irreduzibilität von \( x \).
        \item Daher muss \( x \mid a \) oder \( x \mid b \).
        \item Also ist \( x \) prim.
    \end{enumerate}
    \end{proof}
    
    \textbf{Beispiel:} 
    Betrachten wir den Ring der ganzen Zahlen \(\mathbb{Z}\). In \(\mathbb{Z}\) ist jede ganze Zahl entweder eine Einheit, null oder kann als Produkt von Primzahlen (die irreduzibel sind) dargestellt werden. Wenn eine irreduzible Zahl wie 3 ein Produkt \(a \cdot b\) teilt, dann teilt sie entweder \(a\) oder \(b\). Somit ist 3 auch prim.
    
\end{enumerate}

\section*{Beweisdetails aus dem Lean-Code}
\begin{enumerate}
    \item \textbf{Lemma:} Wenn Null \( x \) teilt, dann ist \( x \) Null.
    
    \textbf{Beweis:}
    \begin{proof}
    Sei \( 0 \mid x \). Dann gibt es ein \( a \in R \), so dass
    \[
    x = a \cdot 0.
    \]
    Da \( a \cdot 0 = 0 \), folgt
    \[
    x = 0.
    \]
    \end{proof}
    
    \textbf{Beispiel:} 
    Betrachten wir den Ring der ganzen Zahlen \(\mathbb{Z}\). Wenn 0 eine ganze Zahl \(x\) teilt, dann ist \(x\) zwangsläufig 0, da jedes Element mal 0 wieder 0 ergibt.
    

    \item \textbf{Lemma:} Wenn \( x \) ein nicht-null Element \( y \) teilt, dann ist \( x \) nicht-null.
    
    \textbf{Beweis:}
    \begin{proof}
    Sei \( x \mid y \) und \( y \neq 0 \). Angenommen, \( x = 0 \). Dann gibt es ein \( a \in R \), so dass
    \[
    y = a \cdot x = a \cdot 0 = 0,
    \]
    was im Widerspruch zu \( y \neq 0 \) steht. Daher muss
    \[
    x \neq 0.
    \]
    \end{proof}
    
    \textbf{Beispiel:} 
    Betrachten wir den Ring der ganzen Zahlen \(\mathbb{Z}\). Wenn eine Zahl \(x\) eine nicht-null Zahl \(y\) teilt, dann kann \(x\) nicht null sein, da das Produkt einer nicht-null Zahl mit 0 null ist.
    
\end{enumerate}

\end{document}
