import Mathlib

/-!
# Square producers shared by several protected readers

A layer read by several protected readers `ℓ` has one joint quadratic law per reader,
`x ↦ xᵀ M_ℓ x` (symmetric `M_ℓ`). A **shared realization with `s` producers** is a family of
linear forms `a_1, …, a_s` with reader-specific weights `c_{ℓk}` such that
`xᵀ M_ℓ x = Σ_k c_{ℓk} (a_kᵀ x)²` for every reader and every `x`. Results, with their class:

* **[L] span lower bound**: every shared realization has `s ≥ dim span{M_ℓ}`
  (`shared_lower_bound`), in addition to `s ≥ rank M_ℓ` for each reader (`shared_rank_bound`);
* **refuted: the largest individual rank does not suffice**: the three rank-one laws `x₀²`, `x₁²`,
  `(x₀ + x₁)²` on `ℝ²` admit no shared realization with two producers (`three_laws_need_three`),
  because their span has dimension `3`;
* **[L] identical readers share everything**: `N` readers with the same law are served by the
  producers of one reader (`identical_readers`), so the shared count does not grow with `N`.
-/

namespace SharedProducers

open Matrix Finset

variable {n s : ℕ}

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

/-- The matrix `Σ_k c_k a_k a_kᵀ`. -/
def sumSquares (a : Fin s → Fin n → ℝ) (c : Fin s → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  ∑ k, c k • vecMulVec (a k) (a k)

theorem quad_vecMulVec (a x : Fin n → ℝ) : x ⬝ᵥ (vecMulVec a a *ᵥ x) = (a ⬝ᵥ x) ^ 2 := by
  simp only [dotProduct, mulVec, vecMulVec_apply, sq, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem quadratic_sumSquares (a : Fin s → Fin n → ℝ) (c : Fin s → ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ (sumSquares a c *ᵥ x) = ∑ k, c k * (a k ⬝ᵥ x) ^ 2 := by
  simp only [sumSquares, Matrix.sum_mulVec, Matrix.smul_mulVec, dotProduct_sum, dotProduct_smul,
    smul_eq_mul]
  exact Finset.sum_congr rfl fun k _ => by rw [quad_vecMulVec]

/-- Matrix whose columns are the vectors `a k`. -/
def cols (a : Fin s → Fin n → ℝ) : Matrix (Fin n) (Fin s) ℝ := Matrix.of fun i k => a k i

theorem sumSquares_eq_factored (a : Fin s → Fin n → ℝ) (c : Fin s → ℝ) :
    sumSquares a c = cols a * diagonal c * (cols a)ᵀ := by
  ext i j
  simp only [sumSquares, Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul,
    Matrix.mul_apply, cols, Matrix.of_apply, diagonal_apply, transpose_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem sumSquares_symm (a : Fin s → Fin n → ℝ) (c : Fin s → ℝ) :
    (sumSquares a c)ᵀ = sumSquares a c := by
  simp only [sumSquares, transpose_sum, transpose_smul, transpose_vecMulVec]

/-- A symmetric law realized by squares **is** the matrix of those squares. -/
theorem eq_sumSquares (M : Matrix (Fin n) (Fin n) ℝ) (hM : Mᵀ = M) (a : Fin s → Fin n → ℝ)
    (c : Fin s → ℝ) (h : ∀ x, x ⬝ᵥ (M *ᵥ x) = ∑ k, c k * (a k ⬝ᵥ x) ^ 2) :
    M = sumSquares a c := by
  have hz := eq_zero_of_quadratic_eq_zero (M - sumSquares a c)
    (by rw [transpose_sub, hM, sumSquares_symm])
    (fun x => by rw [sub_mulVec, dotProduct_sub, h x, quadratic_sumSquares, sub_self])
  exact sub_eq_zero.1 hz

/-- **[L] Span lower bound**: a shared realization of the laws `M_ℓ` with `s` producers has
`dim span{M_ℓ} ≤ s`. -/
theorem shared_lower_bound {ι : Type*} (M : ι → Matrix (Fin n) (Fin n) ℝ) (hM : ∀ l, (M l)ᵀ = M l)
    (a : Fin s → Fin n → ℝ) (c : ι → Fin s → ℝ)
    (h : ∀ l x, x ⬝ᵥ (M l *ᵥ x) = ∑ k, c l k * (a k ⬝ᵥ x) ^ 2) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range M)) ≤ s := by
  have hmem : ∀ l, M l ∈ Submodule.span ℝ (Set.range fun k => vecMulVec (a k) (a k)) := by
    intro l
    rw [eq_sumSquares (M l) (hM l) a (c l) (h l), sumSquares]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  calc Module.finrank ℝ (Submodule.span ℝ (Set.range M))
      ≤ Module.finrank ℝ (Submodule.span ℝ (Set.range fun k => vecMulVec (a k) (a k))) :=
        Submodule.finrank_mono (Submodule.span_le.2 (by rintro _ ⟨l, rfl⟩; exact hmem l))
    _ ≤ Fintype.card (Fin s) := finrank_range_le_card _
    _ = s := Fintype.card_fin s

/-- **[L] Per-reader rank bound** inside a shared realization: `rank M_ℓ ≤ s`. -/
theorem shared_rank_bound {ι : Type*} (M : ι → Matrix (Fin n) (Fin n) ℝ) (hM : ∀ l, (M l)ᵀ = M l)
    (a : Fin s → Fin n → ℝ) (c : ι → Fin s → ℝ)
    (h : ∀ l x, x ⬝ᵥ (M l *ᵥ x) = ∑ k, c l k * (a k ⬝ᵥ x) ^ 2) (l : ι) : (M l).rank ≤ s := by
  rw [eq_sumSquares (M l) (hM l) a (c l) (h l), sumSquares_eq_factored]
  calc (cols a * diagonal (c l) * (cols a)ᵀ).rank ≤ ((cols a)ᵀ).rank := rank_mul_le_right _ _
    _ ≤ Fintype.card (Fin s) := rank_le_card_height _
    _ = s := Fintype.card_fin s

/-- The three rank-one laws `x₀²`, `x₁²`, `(x₀ + x₁)²`. -/
def threeLaws : Fin 3 → Matrix (Fin 2) (Fin 2) ℝ := ![!![1, 0; 0, 0], !![0, 0; 0, 1], !![1, 1; 1, 1]]

theorem threeLaws_independent : LinearIndependent ℝ threeLaws := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h00 := congrFun (congrFun hg 0) 0
  have h11 := congrFun (congrFun hg 1) 1
  have h01 := congrFun (congrFun hg 0) 1
  simp [Fin.sum_univ_three, threeLaws] at h00 h11 h01
  intro i
  fin_cases i <;> simp <;> linarith

/-- **Refuted: the largest individual rank does not suffice.** Each of `x₀²`, `x₁²`, `(x₀+x₁)²`
has rank one, but no two shared producers realize all three. -/
theorem three_laws_need_three :
    ¬ ∃ (a : Fin 2 → Fin 2 → ℝ) (c : Fin 3 → Fin 2 → ℝ),
      ∀ l x, x ⬝ᵥ (threeLaws l *ᵥ x) = ∑ k, c l k * (a k ⬝ᵥ x) ^ 2 := by
  rintro ⟨a, c, h⟩
  have hsymm : ∀ l, (threeLaws l)ᵀ = threeLaws l := by
    intro l; fin_cases l <;> ext i j <;> fin_cases i <;> fin_cases j <;> rfl
  have hb := shared_lower_bound threeLaws hsymm a c h
  rw [finrank_span_eq_card threeLaws_independent, Fintype.card_fin] at hb
  omega

/-- **[L] Identical readers share everything**: if every reader has the law of one reader, the
producers of that reader serve them all. -/
theorem identical_readers {ι : Type*} (M : Matrix (Fin n) (Fin n) ℝ) (a : Fin s → Fin n → ℝ)
    (c : Fin s → ℝ) (h : ∀ x, x ⬝ᵥ (M *ᵥ x) = ∑ k, c k * (a k ⬝ᵥ x) ^ 2) :
    ∀ (_l : ι) x, x ⬝ᵥ ((fun _ : ι => M) _l *ᵥ x) = ∑ k, (fun _ : ι => c) _l k * (a k ⬝ᵥ x) ^ 2 :=
  fun _ x => h x

end SharedProducers
