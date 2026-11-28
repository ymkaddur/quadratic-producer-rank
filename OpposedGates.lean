import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.LinearCombination

namespace OpposedGates

noncomputable def sigmoid (x : ℝ) : ℝ := 1/(1+Real.exp (-x))
noncomputable def silu (x : ℝ) : ℝ := x*sigmoid x

theorem complements (x : ℝ) : sigmoid x + sigmoid (-x) = 1 := by
  have h : 0 < Real.exp x := Real.exp_pos _
  simp only [sigmoid, neg_neg, Real.exp_neg]
  field_simp
  ring

/-- A square and a product may be produced jointly without evaluating either sigmoid. -/
theorem odd_part (x : ℝ) : silu x - silu (-x) = x := by
  calc
    _ = x*(sigmoid x+sigmoid (-x)) := by unfold silu; ring
    _ = _ := by rw [complements,mul_one]

/-- Different routing coefficients expose the nonlinear residual that must still be paid. -/
theorem unequal_routes (x u d p q : ℝ) :
    p*d*u*silu x - q*d*u*silu (-x) =
      p*d*u*x + (p-q)*d*u*silu (-x) := by
  linear_combination p*d*u*(odd_part x)

theorem equal_routes (x u d p : ℝ) :
    p*d*u*silu x - p*d*u*silu (-x) = p*d*u*x := by
  rw [unequal_routes]
  ring

theorem unmatched_is_visible : silu (-1) ≠ 0 := by
  unfold silu sigmoid
  exact mul_ne_zero (by norm_num) (div_ne_zero one_ne_zero (by positivity))

end OpposedGates
