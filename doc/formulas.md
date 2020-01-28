
## Formulas.

Face eliminator:  $s=\rho_1+\cdots +\rho_r$ where $\rho_i\leq c$,
$r$ is the Face Rank.  $A_{ij}:\mathbb{M}_{c\times r_j}(K)$.

So 
$$
\begin{bmatrix}
    A_{11} & \cdots & A_{1r}\\
    \vdots & \ddots & \vdots \\
    A_{r1} & \cdots & A_{rr}\\
\end{bmatrix}
$$

Compute the LUP-decomposition ($L$ invertible)
$$
[A_{11},\cdots,A_{1r}] = L_1 U_1 P_1
$$
Then compute LUP-decompostion of 
$$
[A_{22},\cdots,A_{2r}]-A_{21}U_1 P_1 = L_2U_2 P_2
$$
Then 
$$
[A_{33},\cdots,A_{3r}]-A_{32}U_2P_2 -A_{31}U_1 P_1 = L_3U_3 P_3
$$
and in general
$$
[A_{ii},\cdots,A_{ir}]-\sum_{j=1}^{i-1}A_{ij}U_j P_j = L_i U_i P_i.
$$


**Total Work**
There are $r$ rounds of LUP's on at most $(c\times (s-\sum_j \rho_j))$-matrices.
$$
2c^2 s+2c^2 (s-\rho_1)+\cdots +2c^2 (\rho_r)
=2c^2 \sum_{i=1}^r\sum_{j=1}^{i} \rho_j \leq c^2 sr.
$$
Plus we must work with the subtractions to get
$$
O(c^2 s r^2).
$$
Generically $r(A)\approx s/c+o(1)$.
$$
O(s^3)
$$
Note: we control $s$ and can subsample for example if looking to see if a solution exists.  Perhaps even to guess the solutions.  E.g. keep $s\in O(\sqrt{d})$ for $d$ the bulk dimension.  That would give $O(d^2)$ heuristic, and worst case $O(d^3)$.

At this point we have
$$
T_1=
\begin{bmatrix}
I_c & 0 & &  0\\ 
-A_{21}  & I_c & & 0\\
\vdots & & \ddots & \\
-A_{r1} & 0 & & I_c
\end{bmatrix}
\begin{bmatrix}
L_1^{-1} \\ 
& I_c & \\
 & & \ddots \\
 & & & I_c
\end{bmatrix}
$$
$$
T_2=
\begin{bmatrix}
I_c &  & &  \\ 
 & I_c  & & 0\\
 & -A_{32} & \ddots & \\
 & \vdots &0 & I_c
\end{bmatrix}
\begin{bmatrix}
I_c &  & &  \\ 
 & L_2^{-1}  & &\\
 &  & I_c\\
 &  & & \ddots
\end{bmatrix}
$$
and so on.  It follows that
$$
T_r \cdots T_1 A = 
\begin{bmatrix}
U_1 & \cdots \\
0 & U_2 & \cdots \\
0 & 0 & \ddots
\end{bmatrix}
$$
This is not yet upper triangular.  Need to permute the rows up
$$
\Sigma_1 T_r\cdots T_1 A= \begin{bmatrix} T_0 \\ 0 \end{bmatrix}.
$$
with $T_0$ upper triangular.  We don't create this matrix we just think of this formula and write down $T_0$.



---
