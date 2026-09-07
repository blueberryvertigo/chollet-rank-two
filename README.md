# Chollet's permanent inequality when one factor has rank two

Chollet conjectured in 1982 that for all complex Hermitian positive semidefinite
matrices A, B of the same order,

    per(A ∘ B) ≤ per(A) · per(B),

where ∘ is the entrywise product. The conjecture is **open**. It is known for order
at most four (James–Liebeck 1987 for n ≤ 3, Rodtes 2024 for n = 4).

**Theorem.** If rank(A) ≤ 2, the inequality holds in every order, with no rank
restriction on B. For order at least five the constant improves to 577/690.

Method: decompose per(A∘B) over the irreducible representations of S_n. When A has
rank two the sum is supported on partitions with at most two rows, where the immanant
dominance theorem of James and Liebeck applies to B; the trace inequality
tr(UV) ≤ tr(U)tr(V) then reduces the problem to a lower bound for per(A), obtained
from a Gaussian integral representation and, in order five, from an exact
computation on the Bloch sphere.

This is a restricted case. Chollet's conjecture remains open in general.

- `chollet_rank_two.pdf` — the paper
- `chollet.typ`, `refs.yml` — Typst source; build with `typst compile chollet.typ`
