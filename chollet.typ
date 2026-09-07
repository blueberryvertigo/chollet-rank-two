// Chollet's permanent inequality for matrices of rank two
#set page(paper: "a4", margin: (x: 1.1in, y: 1.0in), numbering: "1")
#set text(size: 11pt)
#set par(justify: true, leading: 0.62em, first-line-indent: 1.2em)
#set heading(numbering: "1.")
#show heading: it => { v(0.6em); it; v(0.3em) }
#set math.equation(numbering: "(1)")
#show ref: it => {
  let el = it.element
  if el != none and el.func() == math.equation {
    link(el.location(), numbering(el.numbering, ..counter(math.equation).at(el.location())))
  } else { it }
}

#let per = math.op("per")
#let Imm = math.op("Imm")
#let tr = math.op("tr")
#let un(body) = [#set math.equation(numbering: none); #body]

#let thm(kind, num, name: none, body) = block(width: 100%, above: 1.1em, below: 1.1em)[
  *#kind #num*#if name != none [ (#name)]. #emph(body)
]
#let rem(kind, num, name: none, body) = block(width: 100%, above: 1.1em, below: 1.1em)[
  *#kind #num*#if name != none [ (#name)]. #body
]
#let proof(body) = block(width: 100%, above: 0.8em, below: 1.1em)[_Proof._ #body #h(1fr) $square$]

#align(center)[
  #text(size: 17pt, weight: "bold")[Chollet's permanent inequality when one factor has rank two]
  #v(0.6em)
  #text(size: 12pt)[liqsweep]
  #v(0.2em)
  #text(size: 10pt)[X: \@liqsweep]
  #v(0.2em)
  #text(size: 10pt)[September 2026]
]
#v(0.6em)

#block(inset: (x: 2.2em))[
  #set par(first-line-indent: 0em)
  *Abstract.* Chollet conjectured in 1982 that $per(A compose B) <= per(A) per(B)$ for all complex Hermitian positive semidefinite matrices $A, B$ of the same order, where $compose$ is the entrywise product. The conjecture is open; it is known for order at most four. We prove it whenever $A$ has rank at most two, with no restriction on $B$, in every order. For order at least five we obtain the strictly smaller constant $577\/690$. The proof decomposes $per(A compose B)$ over the irreducible representations of the symmetric group. When $A$ has rank two the sum is supported on partitions with at most two rows, where the immanant dominance theorem of James and Liebeck applies to $B$; a trace inequality then reduces the problem to a lower bound for $per(A)$, which we obtain from a Gaussian integral representation and, in order five, from an exact computation on the Bloch sphere.
]
#v(0.4em)

= Introduction

For an $n times n$ complex matrix $X = (x_(i j))$ write $per(X) = sum_(g in S_n) product_(i=1)^n x_(i, g(i))$ and $h(X) = product_i x_(i i)$, and let $A compose B$ denote the entrywise product. Let $cal(H)_n$ be the set of $n times n$ complex Hermitian positive semidefinite matrices. In 1982 Chollet @Cho82 asked whether the permanent obeys the analogue of Oppenheim's determinant inequality:

#thm("Conjecture", "1.1", name: "Chollet")[
  For all $A, B in cal(H)_n$, $quad per(A compose B) <= per(A) per(B)$.
]

The conjecture is listed as Conjecture 5 in Wanless's survey @Wan22, where it is one of the few in its family still standing: the stronger conjectures of Soules, Bapat and Sunder, and Beasley that would have implied it have all been refuted. It is known for $n <= 3$ by James and Liebeck @JL87 and for $n = 4$ by Rodtes @Rod24, and for structured classes such as certain graph Laplacians @PS26. Chollet observed that the case $B = A$ suffices, and Zhang @Zha12 studied the matrices maximizing $per(A compose X)$. The general case is open.

This paper proves the conjecture under a rank hypothesis on one factor only.

#thm("Theorem", "1.2")[
  Let $A, B in cal(H)_n$ with $"rank"(A) <= 2$. Then
  $ per(A compose B) <= per(A) per(B) . $ <eq:main>
  If $n >= 5$, then moreover
  $ per(A compose B) <= 577/690 thin per(A) per(B) . $ <eq:const>
]

No rank restriction is placed on $B$, and $n$ is arbitrary. The constant $577\/690 = 0.8362 dots$ is not optimal; see Remark 6.2.

*Method.* Let $m_X (g) = product_i x_(i, g(i))$, so that $per(A compose B) = sum_g m_A (g) m_B (g)$. For each partition $lambda$ of $n$ fix an irreducible representation $rho_lambda$ of degree $d_lambda$ and set $F_lambda (X) = sum_g m_X (g) rho_lambda (g)$. These matrices are positive semidefinite for $X in cal(H)_n$, their traces are the immanants of $X$, and Fourier inversion gives
$ per(A compose B) = 1/n! sum_lambda d_lambda tr (F_lambda (A) F_lambda (overline(B))) . $ <eq:fourier>
If $A$ has rank at most two its Gram vectors lie in $bb(C)^2$, so by Schur–Weyl duality $F_lambda (A) = 0$ unless $lambda$ has at most two rows. On those $lambda$ the immanant dominance theorem of James and Liebeck bounds $Imm_lambda (B)$ by $d_lambda per(B)$, and the elementary inequality $tr(U V) <= tr(U) tr(V)$ for positive semidefinite $U, V$ converts @eq:fourier into
$ per(A compose B) <= per(B) [d_n h(A) - (d_n - 1) per(A) \/ n!] , $ <eq:transfer0>
where $d_n$ is the largest degree of a nontrivial two-row irreducible representation. For a correlation matrix this says that $per(A) >= d_n$ already implies Chollet's inequality. The remaining work is to prove such a lower bound for permanents of rank-two correlation matrices. A Gaussian integral representation and Jensen's inequality give $per(A) >= (n+1)! e^(-n)$, which beats $d_n$ for $n >= 6$; order five needs an exact computation, carried out in Section 4 on the Bloch sphere, and orders at most four are covered by Rodtes's theorem.

*External inputs.* Two published permanent theorems are used as stated and are not reproved: the immanant dominance theorem of James and Liebeck @JL87 for partitions with at most two rows, and Rodtes's theorem @Rod24 for order four. Everything else is proved here.

= The Fourier decomposition

Throughout, $N = n!$ and $m_X (g) = product_(i=1)^n x_(i, g(i))$ for $g in S_n$. Fix for each partition $lambda tack.r n$ a unitary irreducible representation $rho_lambda$ of $S_n$ of degree $d_lambda$, with character $chi_lambda$, and set
$ F_lambda (X) = sum_(g in S_n) m_X (g) rho_lambda (g), quad quad Imm_lambda (X) = sum_(g in S_n) chi_lambda (g) m_X (g) . $ <eq:Flam>
The characters of $S_n$ are real-valued and integral, so $Imm_lambda (overline(X)) = overline(Imm_lambda (X))$.

#thm("Lemma", "2.1")[
  Let $X in cal(H)_n$. Then
  + $F_lambda (X) succ.eq 0$ for every $lambda$, and $tr F_lambda (X) = Imm_lambda (X) >= 0$;
  + $sum_lambda d_lambda Imm_lambda (X) = N thin h(X)$, and $Imm_((n))(X) = per(X)$;
  + if $"rank"(X) <= 2$ then $F_lambda (X) = 0$ for every $lambda$ with more than two rows.
]

#proof[
  Write $X = (⟨ v_i, v_j ⟩)$ with $v_1, dots, v_n in bb(C)^r$, $r = "rank"(X)$, and let $Pi(X)$ be the Schur power matrix, $Pi(X)_(sigma, tau) = product_i x_(sigma(i), tau(i))$. Putting $psi = v_1 ⊗ dots.c ⊗ v_n$ and letting $U_sigma$ permute tensor factors, $Pi(X)_(sigma, tau) = ⟨ U_sigma psi, U_tau psi ⟩$, so $Pi(X) succ.eq 0$. Substituting $j = sigma(i)$ gives $Pi(X)_(sigma, tau) = m_X (tau sigma^(-1))$, so $Pi(X)$ is the matrix of the element $a = sum_g m_X (g) g$ of the group algebra acting in the regular representation. By Wedderburn the regular representation is $⊕_lambda rho_lambda^(⊕ d_lambda)$, so $Pi(X)$ is unitarily equivalent to $⊕_lambda F_lambda (X)^T ⊗ I_(d_lambda)$; positivity of $Pi(X)$ therefore gives $F_lambda (X) succ.eq 0$, and the trace formula is immediate from @eq:Flam. This proves (1).

  For (2), $sum_lambda d_lambda chi_lambda (g) = N dot bold(1)_(g = e)$ is the character of the regular representation, and $m_X (e) = h(X)$. The trivial partition has $chi_((n)) equiv 1$.

  For (3), the vectors $U_sigma psi$ lie in $(bb(C)^r)^(⊗ n)$. By Schur–Weyl duality the $S_n$-module $(bb(C)^r)^(⊗ n)$ contains no irreducible constituent whose partition has more than $r$ rows: antisymmetrizing $r+1$ tensor slots of vectors in $bb(C)^r$ gives zero. Hence the isotypic component of $Pi(X)$ for such a $lambda$ vanishes, so $F_lambda (X) = 0$. With $r <= 2$ this is (3).
]

#thm("Lemma", "2.2")[
  For all $A, B in cal(H)_n$,
  $ per(A compose B) = 1/N sum_lambda d_lambda tr (F_lambda (A) F_lambda (overline(B))) . $ <eq:fourier2>
]

#proof[
  Expanding the right side and using $tr rho_lambda (g) rho_lambda (h) = chi_lambda (g h)$,
  #un[$ 1/N sum_(g, h) m_A (g) thin m_(overline(B))(h) sum_lambda d_lambda chi_lambda (g h) = sum_g m_A (g) thin m_(overline(B))(g^(-1)) . $]
  Since $B$ is Hermitian, $m_(overline(B))(g^(-1)) = product_i overline(b)_(i, g^(-1)(i)) = product_j overline(b)_(g(j), j) = product_j b_(j, g(j)) = m_B (g)$. The left side is $sum_g m_A (g) m_B (g) = per(A compose B)$ by the definition of the entrywise product.
]

= The transfer inequality

For $n >= 2$ let
$ d_n = max_(1 <= k <= floor(n\/2)) [binom(n, k) - binom(n, k-1)] $ <eq:dn>
be the largest degree of an irreducible representation of $S_n$ indexed by a two-row partition other than $(n)$; the degree of $(n-k, k)$ is $binom(n,k) - binom(n,k-1)$ by the hook length formula. The first values are
#align(center)[
  #table(columns: 12, align: center, stroke: none, inset: 4pt,
    [$n$], [2], [3], [4], [5], [6], [7], [8], [9], [10], [11], [12],
    [$d_n$], [1], [2], [3], [5], [9], [14], [28], [48], [90], [165], [297])
]

#thm("Lemma", "3.1")[
  If $U, V succ.eq 0$ are of the same size then $tr(U V) <= tr(U) tr(V)$.
]

#proof[
  $V prec.eq (tr V) I$, so $tr(U V) = tr(U^(1\/2) V U^(1\/2)) <= (tr V) tr(U)$.
]

We use the following theorem of James and Liebeck @JL87[Theorem 1]: for every $X in cal(H)_n$ and every partition $lambda$ of $n$ with at most two rows,
$ Imm_lambda (X) <= d_lambda per(X) . $ <eq:JL>

#thm("Proposition", "3.2", name: "transfer inequality")[
  Let $A, B in cal(H)_n$ with $"rank"(A) <= 2$. Then
  $ per(A compose B) <= per(B) [ d_n h(A) - (d_n - 1) per(A)/N ] . $ <eq:transfer>
  In particular, if $A$ is a correlation matrix then
  $ (per(A compose B))/(per(A) per(B)) <= d_n/(per(A)) - (d_n - 1)/N , $ <eq:ratio>
  and $per(A) >= d_n$ implies Chollet's inequality for the pair $(A, B)$.
]

#proof[
  By Lemma 2.1(3) only partitions with at most two rows contribute to @eq:fourier2. For those, Lemma 3.1 and Lemma 2.1(1) give $tr(F_lambda (A) F_lambda (overline(B))) <= Imm_lambda (A) Imm_lambda (overline(B))$, and $Imm_lambda (overline(B)) = overline(Imm_lambda (B)) = Imm_lambda (B)$ since immanants of Hermitian matrices are real. Hence by @eq:JL,
  #un[$ per(A compose B) <= 1/N sum_(lambda: thin <= 2 "rows") d_lambda thin Imm_lambda (A) thin d_lambda per(B) = (per(B))/N sum_(lambda: thin <= 2 "rows") d_lambda^2 thin Imm_lambda (A) . $]
  All $Imm_lambda (A)$ are nonnegative. Separating $lambda = (n)$, whose degree is one and whose immanant is $per(A)$, and bounding $d_lambda <= d_n$ on the remaining two-row partitions,
  #un[$ sum_(lambda: thin <= 2 "rows") d_lambda^2 Imm_lambda (A) <= per(A) + d_n sum_(lambda != (n)) d_lambda Imm_lambda (A) = per(A) + d_n (N h(A) - per(A)) , $]
  where the last step is Lemma 2.1(2) together with Lemma 2.1(3), which makes the partitions with more than two rows contribute nothing to the total mass. Dividing by $N$ gives @eq:transfer; @eq:ratio is the case $h(A) = 1$.
]

Note that @eq:transfer is a comparison of traces. It is not the assertion $F_lambda (A) prec.eq per(A) I$, which is the permanent-on-top property and is false for complex matrices of rank two @Tra21.

= Lower bounds for rank-two permanents

Throughout this section $A in cal(H)_n$ is a correlation matrix of rank at most two, so $A = (⟨ v_i, v_j ⟩)$ with unit vectors $v_i in bb(C)^2$.

#thm("Lemma", "4.1", name: "Gaussian representation")[
  Let $g$ be a standard circular complex Gaussian vector in $bb(C)^2$, that is $bb(E)[g overline(g)^T] = I$. Then
  $ per(A) = bb(E) product_(i=1)^n abs(⟨ v_i, g ⟩)^2 . $ <eq:gauss>
]

#proof[
  Expanding the product and using the Wick formula for circular complex Gaussians, $bb(E)[product_i ⟨ v_i, g ⟩ overline(⟨ v_j, g ⟩)]$ equals the sum over bijections between the two index sets of the products of the pairwise covariances $bb(E)[⟨ v_i, g ⟩ overline(⟨ v_j, g ⟩)] = ⟨ v_j, v_i ⟩$. That sum is $per(A)$.
]

#thm("Proposition", "4.2")[
  For every correlation matrix $A$ of rank at most two,
  $ per(A) >= L_n := (n+1)! thin e^(-n) . $ <eq:jensen>
]

#proof[
  Write $g = R u$ where $R = norm(g)$ and $u = g \/ norm(g)$; these are independent, $u$ is uniform on the unit sphere of $bb(C)^2$, and $R^2$ has density $t e^(-t)$ on $(0, oo)$, so $bb(E) R^(2n) = integral_0^oo t^n dot t e^(-t) dif t = (n+1)!$. For a unit vector $v in bb(C)^2$ the random variable $abs(⟨ v, u ⟩)^2$ is uniform on $[0, 1]$: rotating $v$ to the first coordinate, it becomes $abs(g_1)^2 \/ (abs(g_1)^2 + abs(g_2)^2)$, a ratio of an exponential variable to the sum of two independent ones. Hence
  #un[$ bb(E) log abs(⟨ v_i, u ⟩)^2 = integral_0^1 log x dif x = -1 $]
  for each $i$; no independence between different $i$ is needed, and each logarithm is integrable. By @eq:gauss and Jensen's inequality applied to the exponential,
  #un[$ per(A) = (n+1)! thin bb(E) exp(sum_(i=1)^n log abs(⟨ v_i, u ⟩)^2) >= (n+1)! exp(-n) . $]
]

The bound @eq:jensen exceeds $d_n$ from order six onwards but not at order five, where $L_5 = 4.85 dots < 5 = d_5$. Order five is settled exactly.

#thm("Proposition", "4.3")[
  For every correlation matrix $A$ of rank at most two and order five,
  $ per(A) >= 23/4 . $ <eq:n5>
]

#proof[
  Write the rank-one projector onto $v_i$ in Bloch form, $v_i v_i^* = (I + r_i dot sigma) \/ 2$ with $r_i in bb(R)^3$ a unit vector and $sigma$ the Pauli matrices, and let $x$ be the Bloch vector of $u$, uniform on the sphere $S^2$. Then $abs(⟨ v_i, u ⟩)^2 = (1 + r_i dot x) \/ 2$, so by the proof of Proposition 4.2 with $n = 5$,
  $ per(A) = 720/32 thin bb(E) product_(i=1)^5 (1 + r_i dot x) . $ <eq:bloch>
  Odd moments of $x$ vanish, and $bb(E) x_a x_b = delta_(a b) \/ 3$ and $bb(E) x_a x_b x_c x_d = (delta_(a b) delta_(c d) + delta_(a c) delta_(b d) + delta_(a d) delta_(b c)) \/ 15$. Expanding the product, the degree-two term contributes $S \/ 3$ with $S = sum_(i < j) r_i dot r_j$, and the degree-four term contributes $D \/ 15$, where $D$ is the sum of $(r_i dot r_j)(r_k dot r_l)$ over the fifteen unordered pairs of disjoint edges of $K_5$; each four-element index set yields exactly the three pairings. Hence
  $ per(A) = 720/32 [1 + S/3 + D/15] . $ <eq:bloch2>
  Put $R = sum_i r_i$, $s = norm(R)^2$ and $M = sum_i r_i r_i^T$, and write $w_e = r_i dot r_j$ for the edge $e = {i, j}$. Since $norm(r_i) = 1$ one has $s = 5 + 2 S$, that is $S = (s-5)\/2$. Expanding $S^2 = (sum_e w_e)^2$ and sorting the ordered pairs of edges into equal, adjacent and disjoint ones,
  #un[$ S^2 = sum_e w_e^2 + 2 sum_(e, f "adjacent") w_e w_f + 2 D , $]
  the last sum being over unordered pairs of distinct edges meeting in one vertex. Since each edge ${i,j}$ occurs at $i$ and at $j$, and each adjacent pair meets in exactly one vertex,
  #un[$ sum_i (sum_(j != i) w_(i j))^2 = 2 sum_e w_e^2 + 2 sum_(e, f "adjacent") w_e w_f . $]
  Eliminating the adjacent sum gives $2 D = S^2 + sum_e w_e^2 - sum_i (sum_(j != i) w_(i j))^2$. Now $sum_e w_e^2 = (tr(M^2) - 5)\/2$, because $tr(M^2) = sum_(i,j)(r_i dot r_j)^2 = 5 + 2 sum_e w_e^2$; and $sum_(j != i) w_(i j) = r_i dot R - 1$, so
  #un[$ sum_i (sum_(j != i) w_(i j))^2 = sum_i (r_i dot R)^2 - 2 sum_i r_i dot R + 5 = R^T M R - 2 s + 5 . $]
  Substituting these and $S = (s-5)\/2$ yields
  $ D = s^2/8 - s/4 - 5/8 + (tr(M^2))/4 - (R^T M R)/2 . $ <eq:D>
  Substituting @eq:D and $S = (s-5)\/2$ into @eq:bloch2 and simplifying,
  $ per(A) = 3/16 [s^2 + 18 s + 15 + 2 tr(M^2) - 4 R^T M R] . $ <eq:per5>
  Now $M succ.eq 0$ with $tr M = 5$, so $tr(M^2) >= (tr M)^2 \/ 3 = 25\/3$ by Cauchy–Schwarz on the eigenvalues, and $M prec.eq (tr M) I = 5 I$ gives $R^T M R <= 5 s$. Therefore
  #un[$ per(A) >= 3/16 [s^2 + 18 s + 15 + 50/3 - 20 s] = 3/16 (s-1)^2 + 23/4 >= 23/4 . $]
]

= Proof of Theorem 1.2

If $A$ or $B$ has a zero diagonal entry, then positivity forces the whole corresponding row and column to vanish, and both sides of @eq:main are zero; so assume all diagonal entries are positive. Conjugating $A$ by a positive diagonal matrix multiplies $per(A compose B)$ and $per(A)$ by the same factor $h(A)$ and changes neither $per(B)$ nor the rank of $A$, so we may assume $A$ is a correlation matrix. The permanent of a positive definite correlation matrix is positive, for instance by @eq:gauss.

*Orders at most four.* Rodtes's theorem @Rod24 gives $per(X compose overline(X)) <= per(X)^2$ for all $X in cal(H)_m$ with $m <= 4$; padding with identity blocks reduces $m < 4$ to $m = 4$, and the theorem has no rank restriction, so the padding is harmless. Cauchy–Schwarz applied to $per(A compose B) = sum_g m_A (g) m_B (g)$ gives
#un[$ per(A compose B) <= (sum_g abs(m_A (g))^2)^(1\/2) (sum_g abs(m_B (g))^2)^(1\/2) = per(A compose overline(A))^(1\/2) per(B compose overline(B))^(1\/2) <= per(A) per(B) . $]

*Order five.* Here $d_5 = 5$ and $per(A) >= 23\/4$ by Proposition 4.3, so @eq:ratio gives
$ (per(A compose B))/(per(A) per(B)) <= 5/(23\/4) - 4/120 = 20/23 - 1/30 = 577/690 < 1 . $ <eq:577>

*Orders at least six.* We claim $d_n \/ L_n <= d_6 \/ L_6$ for all $n >= 6$. By the branching rule, the restriction of the irreducible representation of $S_(n+1)$ indexed by $(n+1-k, k)$ to $S_n$ is the sum of those indexed by $(n-k, k)$ and $(n+1-k, k-1)$, both with at most two rows; hence $d_(n+1) <= 2 d_n$. Meanwhile $L_(n+1) \/ L_n = (n+2) \/ e > 2$ for $n >= 6$, since $n + 2 >= 8 > 2 e$. Therefore $d_(n+1) \/ L_(n+1) < d_n \/ L_n$, proving the claim by induction. Discarding the negative term in @eq:ratio and using Proposition 4.2,
$ (per(A compose B))/(per(A) per(B)) <= d_n/(per(A)) <= d_n/L_n <= d_6/L_6 = (9 e^6)/5040 . $ <eq:tail>
Finally $e < 11\/4$, because $e - 5\/2 = sum_(j >= 3) 1\/j! < (1\/6) sum_(i >= 0) 3^(-i) = 1\/4$. Hence
$ 690 dot 9 e^6 < 6210 (11/4)^6 = 11001394410/4096 < 2685692 < 2908080 = 577 dot 5040 , $ <eq:rational>
so $9 e^6 \/ 5040 < 577\/690$. Together with @eq:577 this proves @eq:const for all $n >= 5$, and with the case $n <= 4$ it proves @eq:main in every order. $square$

= Remarks

#rem("Remark", "6.1", name: "where the rank enters")[
  Rank two is used exactly once, in Lemma 2.1(3), to restrict the Fourier support to two-row partitions, which is the range in which James–Liebeck dominance is available. For rank three the same argument would need immanant dominance for three-row partitions, which is known for $n <= 13$ by the work of Pate and others @Wan22 but not in general; and $d_n$ would be replaced by the largest degree among partitions with at most three rows, which grows too fast for the lower bound of Proposition 4.2 to compensate. So the argument does not extend to rank three by these two changes alone.
]

#rem("Remark", "6.2", name: "the constant")[
  Numerical minimization of $per(A)$ over rank-two correlation matrices of order five suggests that the true minimum is $6$, attained in the limit of a configuration of Bloch vectors concentrated at antipodes, rather than the value $23\/4 = 5.75$ proved in Proposition 4.3. Replacing $23\/4$ by $6$ in @eq:577 would give the constant $5\/6 - 1\/30 = 4\/5$. We have not proved the sharp bound. Likewise $9 e^6 \/ 5040 = 0.7204 dots$ is the true value of $d_6 \/ L_6$, and the ratio $d_n \/ L_n$ tends to zero rapidly, so the constant in @eq:const is governed entirely by order five.
]

#rem("Remark", "6.3", name: "relation to stronger conjectures")[
  Chollet's inequality is implied by the permanent-on-top conjecture, which is false @Shc16 @Tra21, and by the Bapat–Sunder inequality $per(A compose B) <= per(A) h(B)$, which is also false @Dru17. Theorem 1.2 asserts nothing about those two statements for complex rank-two $A$; indeed permanent-on-top fails for such matrices, by Tran's order-five example. The point of Proposition 3.2 is that a trace comparison survives where the corresponding operator inequality does not.
]

= Computational confirmation

The Fourier identity @eq:fourier2, the trace mass identity of Lemma 2.1(2), the vanishing in Lemma 2.1(3), and the James–Liebeck bound were verified by exact and floating-point computation for $n <= 5$; the transfer inequality @eq:transfer and Theorem 1.2 were checked on random pairs with $"rank"(A) <= 2$ and $B$ of every rank for $n <= 6$; the values of $d_n$, the identity in @eq:577 and the rational comparison @eq:rational were verified exactly; and Propositions 4.2 and 4.3 were tested by direct minimization. These computations played no role in the proof.

#v(1em)
*Acknowledgments.* The exposition was prepared with the assistance of GPT-6 Astra.

#v(0.5em)
#bibliography("refs.yml", title: "References", style: "ieee")
