# quadratic-producer-rank

Lean 4 + Mathlib proofs about **how many products a quadratic law needs**.

A *bilinear producer* computes $(g^\top x)(u^\top x)$ and a *square producer* computes
$c\,(a^\top x)^2$. A layer that sums $m$ bilinear producers,
$f(x)=\sum_j d_j(g_j^\top x)(u_j^\top x)$, is the quadratic form of the symmetric matrix
$M=\tfrac12\sum_j d_j(g_ju_j^\top+u_jg_j^\top)$.

Every statement is labelled **[L]**: proved by the Lean kernel with no `sorry`, no warnings, and
only the standard axioms `propext`, `Classical.choice` and `Quot.sound`. All of them are in
[`QuadraticProducerRank.lean`](QuadraticProducerRank.lean).

| Statement | Lean name |
|-----------|-----------|
| A symmetric matrix whose quadratic form vanishes identically is zero (polarization) | `eq_zero_of_quadratic_eq_zero` |
| The quadratic form of $A\,\mathrm{diag}(c)\,A^\top$ is $\sum_k c_k(a_k^\top x)^2$ | `quadratic_of_factored` |
| **Lower bound.** If $x^\top Mx=\sum_{k<r}c_k(a_k^\top x)^2$ for all $x$, then $M=A\,\mathrm{diag}(c)\,A^\top$ and $\operatorname{rank}M\le r$. No rewriting of the layer with fewer than $\operatorname{rank}M$ square producers exists | `rank_le_of_squares` |
| **Two squares per bilinear producer**: $(g^\top x)(u^\top x)=\tfrac14((g+u)^\top x)^2-\tfrac14((g-u)^\top x)^2$, so $2m$ squares always suffice | `bilinear_eq_squares` |
| **Joint elimination beats the producer count**: $(x_0+x_1)x_0+(-x_1)x_0=x_0^2$, one product instead of two | `joint_elimination_example` |
| **Refutation**: $x_0^2+x_1^2$ is not a single square $c(a^\top x)^2$ (its matrix has rank 2) | `no_single_square` |
| **Upper bound (spectral theorem)**: a real symmetric $M$ is a sum of exactly $\operatorname{rank}M$ weighted squares | `exists_rank_squares` |
| **Exact producer count**: the minimal number of weighted squares realizing $x^\top Mx$ is $\operatorname{rank}M$ | `min_squares_eq_rank` |

## Why it matters

The quantity that governs how many products a layer needs is the **rank of its joint quadratic
law**, not the number of producers it is written with. Rank is a certified floor that no
rewriting can go below, and when the joint rank is below $m$, producers can be eliminated
outright. The floor is exact: $\operatorname{rank}M$ squares always suffice
(`min_squares_eq_rank`).

## Verify

```bash
lake exe cache get
scripts/audit.sh            # compiles each file and checks sorry, warnings and axioms
```

Pin: `leanprover/lean4:v4.33.1`, Mathlib `0df444a` (v4.33.1).
