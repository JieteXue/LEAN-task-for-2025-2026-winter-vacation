**Question 3**
- $\neg (1\land 2)$:
    We suppose there exists $N∈ \N$ such that for any $n ≥ N$,$a_n =a_N$ and there exists $I\subseteq \N$ s.t. $(a_n)_{n\in I}$ is strictly decreasing. 
Let $J=I\cap \{n\in \N | n\geqslant N\}$.
Then $\forall n\in J,a_n=a_N$.
But $J\subseteq I$, which implies $(a_n)_{n\in J}$ is strictly decreasing,contradioction.

- $1 \vee 2$:
  We suppose $\neg 1$,namely $\forall N\in \N$,$\exist m> N$ s.t $a_m\neq a_N$. 
  Since $(a_n)_{n\in \N}$,$a_m<a_N$.($*$)
  We can construct a subsequence by induction.
  Let $n_0=0$.
  We suppose $n_0,n_1,\cdots,n_k$ are chosen.
  By $(*)$,$\exist m_k>k,$ s.t. $a_{m_k}< a_k$.Let $n_{k+1}=m_k$.
  Let $\{n_0,n_1,n_2\cdots \}=I$.Then $(a_n)_{n\in I}$ is strictly decreasing.