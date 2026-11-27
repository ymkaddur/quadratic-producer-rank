import Mathlib

/-!
# How many products does a quadratic law need?

A *bilinear producer* computes `(gᵀx)(uᵀx)`; a *square producer* computes `c (aᵀx)²`. A layer
that sums `m` bilinear producers, `f(x) = Σ_j d_j (g_jᵀx)(u_jᵀx)`, is the quadratic form of the
symmetric matrix `M = ½ Σ_j d_j (g_j u_jᵀ + u_j g_jᵀ)`. Every claim is labelled:

* **[L] lower bound (no realization below the rank)**: if `xᵀMx = Σ_{k<r} c_k (a_kᵀx)²` for all
  `x` and `M` is symmetric, then `M = A·diag(c)·Aᵀ` and `rank M ≤ r` (`rank_le_of_squares`).
  This certifies that **no** rewriting of the layer with fewer than `rank M` square producers
  exists;
* **[L] polarization (two squares per bilinear producer)**:
  `(gᵀx)(uᵀx) = ¼((g+u)ᵀx)² − ¼((g−u)ᵀx)²` (`bilinear_eq_squares`), so `2m` squares always
  suffice;
* **[L] joint elimination can beat the producer count**: two bilinear producers whose joint
  law is `x₀²` need a single square (`joint_elimination_example`);
* **[L] refutation of a too-small realization**: `x₀² + x₁²` is not `c (aᵀx)²` for any `c`, `a`
  (`no_single_square`), because its matrix has rank `2`.
-/

namespace QuadraticProducerRank

open Matrix Finset

variable {n r : ℕ}

/-- **Polarization for symmetric matrices**: a symmetric matrix whose quadratic form vanishes
identically is zero. -/
theorem eq_zero_of_quadratic_eq_zero (S : Matrix (Fin n) (Fin n) ℝ) (hS : Sᵀ = S)
    (h : ∀ x : Fin n → ℝ, x ⬝ᵥ (S *ᵥ x) = 0) : S = 0 := by
  have hdiag : ∀ i, S i i = 0 := by
    intro i
    have := h (Pi.single i 1)
    simpa [mulVec, dotProduct, Pi.single_apply] using this
  have hsym : ∀ i j, S j i = S i j := fun i j => by
    have := congrFun (congrFun hS i) j
    simpa [transpose_apply] using this
  ext i j
  have hij := h (Pi.single i 1 + Pi.single j 1)
  have key : (Pi.single i 1 + Pi.single j 1 : Fin n → ℝ) ⬝ᵥ
      (S *ᵥ (Pi.single i 1 + Pi.single j 1)) = S i i + S i j + S j i + S j j := by
    simp only [mulVec_add, dotProduct_add, add_dotProduct]
    simp [mulVec, dotProduct, Pi.single_apply]
    ring
  rw [key, hdiag i, hdiag j, hsym i j] at hij
  simp only [Matrix.zero_apply]
  linarith

/-- Matrix whose columns are the vectors `a k`. -/
def cols (a : Fin r → Fin n → ℝ) : Matrix (Fin n) (Fin r) ℝ := Matrix.of fun i k => a k i

/-- The quadratic form of `A·diag(c)·Aᵀ` is `Σ_k c_k (a_kᵀx)²`. -/
theorem quadratic_of_factored (a : Fin r → Fin n → ℝ) (c : Fin r → ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ ((cols a * diagonal c * (cols a)ᵀ) *ᵥ x) = ∑ k, c k * (a k ⬝ᵥ x) ^ 2 := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
  have hy : (cols a)ᵀ *ᵥ x = fun k => a k ⬝ᵥ x := by
    ext k
    simp [cols, mulVec, dotProduct, transpose_apply]
  rw [hy]
  simp only [dotProduct, mulVec_diagonal]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem factored_symm (a : Fin r → Fin n → ℝ) (c : Fin r → ℝ) :
    (cols a * diagonal c * (cols a)ᵀ)ᵀ = cols a * diagonal c * (cols a)ᵀ := by
  rw [transpose_mul, transpose_mul, transpose_transpose, diagonal_transpose, Matrix.mul_assoc]

/-- **[L] Lower bound.** If a symmetric `M` has quadratic form `Σ_{k<r} c_k (a_kᵀx)²`, then
`M = A·diag(c)·Aᵀ` and `rank M ≤ r`. -/
theorem rank_le_of_squares (M : Matrix (Fin n) (Fin n) ℝ) (hM : Mᵀ = M) (a : Fin r → Fin n → ℝ)
    (c : Fin r → ℝ) (h : ∀ x, x ⬝ᵥ (M *ᵥ x) = ∑ k, c k * (a k ⬝ᵥ x) ^ 2) :
    M = cols a * diagonal c * (cols a)ᵀ ∧ M.rank ≤ r := by
  have hEq : M = cols a * diagonal c * (cols a)ᵀ := by
    have hz := eq_zero_of_quadratic_eq_zero (M - cols a * diagonal c * (cols a)ᵀ)
      (by rw [transpose_sub, hM, factored_symm])
      (fun x => by rw [sub_mulVec, dotProduct_sub, h x, quadratic_of_factored, sub_self])
    exact sub_eq_zero.1 hz
  refine ⟨hEq, ?_⟩
  rw [hEq]
  calc (cols a * diagonal c * (cols a)ᵀ).rank ≤ ((cols a)ᵀ).rank := rank_mul_le_right _ _
    _ ≤ Fintype.card (Fin r) := rank_le_card_height _
    _ = r := Fintype.card_fin r

/-- **[L] Polarization**: one bilinear producer is a difference of two squares. -/
theorem bilinear_eq_squares (g u x : Fin n → ℝ) :
    (g ⬝ᵥ x) * (u ⬝ᵥ x) = (1 / 4) * ((g + u) ⬝ᵥ x) ^ 2 - (1 / 4) * ((g - u) ⬝ᵥ x) ^ 2 := by
  rw [add_dotProduct, sub_dotProduct]
  ring

/-- **[L] Joint elimination.** The two bilinear producers `(x₀ + x₁)·x₀` and `(−x₁)·x₀` add up
to the single square `x₀²`: one product instead of two. -/
theorem joint_elimination_example (x : Fin 2 → ℝ) :
    (x 0 + x 1) * x 0 + (-x 1) * x 0 = 1 * (![1, 0] ⬝ᵥ x) ^ 2 := by
  simp [dotProduct, Fin.sum_univ_two]
  ring

/-- **[L] Refutation.** `x₀² + x₁²` is not a single square `c (aᵀx)²`: its matrix is the
identity, of rank `2 > 1`. -/
theorem no_single_square :
    ¬ ∃ (c : ℝ) (a : Fin 2 → ℝ), ∀ x : Fin 2 → ℝ, x 0 ^ 2 + x 1 ^ 2 = c * (a ⬝ᵥ x) ^ 2 := by
  rintro ⟨c, a, h⟩
  have hq : ∀ x : Fin 2 → ℝ, x ⬝ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ x) =
      ∑ k : Fin 1, (fun _ => c) k * ((fun _ => a) k ⬝ᵥ x) ^ 2 := by
    intro x
    rw [one_mulVec, Fin.sum_univ_one, ← h x]
    simp [dotProduct, Fin.sum_univ_two, sq]
  have hr := (rank_le_of_squares 1 transpose_one (fun _ => a) (fun _ => c) hq).2
  rw [rank_one, Fintype.card_fin] at hr
  omega

end QuadraticProducerRank
