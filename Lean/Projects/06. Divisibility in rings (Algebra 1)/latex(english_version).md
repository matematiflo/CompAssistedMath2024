\documentclass{article}
\usepackage{amsmath, amssymb}

\title{Divisibility}
\author{Elias and Petr\\
Proseminar on Computer-Aided Mathematics,\\
Heidelberg, Summer Semester 2024}
\date{}

\begin{document}

\maketitle

\section*{Introduction}
In this project sketch, we define irreducible and prime elements of a commutative ring. The goal is to define factorable rings and show that in a factorable ring every irreducible element is prime.

\section*{Basics}
\begin{itemize}
    \item Let \( R \) be a commutative ring.
    \item We say that an element \( x \in R \) divides an element \( y \in R \) if and only if \( y \) is a multiple of \( x \). Formally: \( x \mid y \) if there exists \( a \in R \) such that \( y = a \cdot x \).
    \item If zero divides \( x \), then \( x \) must be zero.
    \item If \( x \) divides a non-zero element \( y \), then \( x \) is non-zero.
    \item Two elements \( x \) and \( y \) are called associated if and only if \( x \) and \( y \) differ by a unit. Formally: \( x \) and \( y \) are associated if there exists a unit \( a \in R \) such that \( y = a \cdot x \). A unit is an element that has a multiplicative inverse.
    \item An element \( x \in R \) is non-trivial if it is neither zero nor a unit.
    \item An element \( x \in R \) is irreducible if it is non-trivial and whenever \( x = a \cdot b \), either \( a \) or \( b \) is a unit.
    \item An element \( x \in R \) is prime if it is non-trivial and whenever \( x \mid a \cdot b \), it divides one of the factors.
\end{itemize}

\section*{Main Results}
\begin{enumerate}
    \item In an integral domain, every prime element is irreducible.
    
    \textbf{Proof:}
    \begin{proof}
    Let \( R \) be an integral domain and \( x \in R \) a prime element. We show that \( x \) is irreducible:
    \begin{enumerate}
        \item Let \( x = a \cdot b \) for \( a, b \in R \).
        \item Since \( x \) is prime, from \( x \mid a \cdot b \), it follows that \( x \mid a \) or \( x \mid b \).
        \item Assume \( x \mid a \). Then there exists \( c \in R \) with \( a = c \cdot x \).
        \item Set \( x = a \cdot b = (c \cdot x) \cdot b = c \cdot (x \cdot b) \).
        \item Since \( R \) is an integral domain and \( x \neq 0 \), it follows \( c \cdot b = 1 \). Thus, \( c \) is a unit.
        \item Similarly, \( b \) is a unit if \( x \mid b \).
        \item Therefore, \( x \) is irreducible.
    \end{enumerate}
    \end{proof}
    
    \textbf{Example:} 
    Consider the ring of integers \(\mathbb{Z}\). The element 2 is prime because 2 is neither zero nor a unit, and if 2 divides a product, it divides one of the factors. If \(2 = a \cdot b\), then one of the factors must be a unit (1 or -1). Therefore, 2 is irreducible.

    \item Define factorable rings (also called unique factorization domains) and show that in any factorable ring, every irreducible element is prime.
    
    \textbf{Definition:}
    \begin{definition}
    A ring \( R \) is factorable if every non-zero and non-unit element can be written as a product of irreducible elements, and this factorization is unique up to order and association.
    \end{definition}
    
    \textbf{Proof:}
    \begin{proof}
    Let \( R \) be a factorable ring and \( x \in R \) irreducible. We show that \( x \) is prime:
    \begin{enumerate}
        \item Assume \( x \mid a \cdot b \). Then there exists \( c \in R \) such that \( a \cdot b = c \cdot x \).
        \item Since \( x \) is irreducible, \( x \) cannot be further factored, except \( x = a \cdot b \) with a unit \( a \) or \( b \).
        \item Assume \( x \mid a \cdot b \), but \( x \mid a \) not and \( x \mid b \) not.
        \item Then \( x \) would not be a unit and there would be no unit \( u \) such that \( x = u \cdot a \) or \( x = u \cdot b \).
        \item This contradicts the irreducibility of \( x \).
        \item Therefore, \( x \mid a \) or \( x \mid b \).
        \item Hence, \( x \) is prime.
    \end{enumerate}
    \end{proof}
    
    \textbf{Example:} 
    Consider the ring of integers \(\mathbb{Z}\). In \(\mathbb{Z}\), every integer is either a unit, zero, or can be represented as a product of prime numbers (which are irreducible). If an irreducible number like 3 divides a product \(a \cdot b\), then it divides either \(a\) or \(b\). Thus, 3 is also prime.
    
\end{enumerate}

\section*{Proof Details from Lean Code}
\begin{enumerate}
    \item \textbf{Lemma:} If zero divides \( x \), then \( x \) is zero.
    
    \textbf{Proof:}
    \begin{proof}
    Let \( 0 \mid x \). Then there exists \( a \in R \) such that
    \[
    x = a \cdot 0.
    \]
    Since \( a \cdot 0 = 0 \), it follows
    \[
    x = 0.
    \]
    \end{proof}
    
    \textbf{Example:} 
    Consider the ring of integers \(\mathbb{Z}\). If 0 divides an integer \(x\), then \(x\) must be 0, since any number multiplied by 0 is again 0.
    

    \item \textbf{Lemma:} If \( x \) divides a non-zero element \( y \), then \( x \) is non-zero.
    
    \textbf{Proof:}
    \begin{proof}
    Let \( x \mid y \) and \( y \neq 0 \). Assume \( x = 0 \). Then there exists \( a \in R \) such that
    \[
    y = a \cdot x = a \cdot 0 = 0,
    \]
    which contradicts \( y \neq 0 \). Therefore,
    \[
    x \neq 0.
    \]
    \end{proof}
    
    \textbf{Example:} 
    Consider the ring of integers \(\mathbb{Z}\). If a number \(x\) divides a non-zero number \(y\), then \(x\) cannot be zero, since the product of a non-zero number with 0 is zero.
    
\end{enumerate}

\end{document}
