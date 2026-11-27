import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! A binary pencil whose simultaneous square rank strictly exceeds both elementary bounds. -/
namespace BinaryPencil

def pencil (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a, b; b, -a]

theorem det_pencil (a b : ℝ) : (pencil a b).det = -(a ^ 2 + b ^ 2) := by
  rw [Matrix.det_fin_two]
  simp [pencil]
  ring

theorem rank_pencil {a b : ℝ} (h : a ≠ 0 ∨ b ≠ 0) : (pencil a b).rank = 2 := by
  have hd : (pencil a b).det ≠ 0 := by
    rw [det_pencil]
    rcases h with h | h <;> nlinarith [sq_pos_of_ne_zero h, sq_nonneg a, sq_nonneg b]
  simpa using Matrix.rank_of_isUnit (pencil a b)
    ((Matrix.isUnit_iff_isUnit_det (pencil a b)).mpr (isUnit_iff_ne_zero.mpr hd))

def readers : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ := ![pencil 1 0, pencil 0 1]

theorem readers_independent : LinearIndependent ℝ readers := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h₁ := congrFun (congrFun hg 0) 0
  have h₂ := congrFun (congrFun hg 0) 1
  simp [Fin.sum_univ_two, readers, pencil] at h₁ h₂
  intro i
  fin_cases i <;> assumption

theorem dim_readers : Module.finrank ℝ (Submodule.span ℝ (Set.range readers)) = 2 := by
  rw [finrank_span_eq_card readers_independent, Fintype.card_fin]

/-- The two outputs use fixed real linear combinations of the same two squared linear forms. -/
def TwoSquares : Prop := ∃ a b c d r s t u : ℝ, ∀ x y : ℝ,
  r * (a*x+b*y)^2 + s * (c*x+d*y)^2 = x^2-y^2 ∧
  t * (a*x+b*y)^2 + u * (c*x+d*y)^2 = 2*x*y

theorem no_two_squares : ¬ TwoSquares := by
  rintro ⟨a,b,c,d,r,s,t,u,h⟩
  have h₀ := h 1 0
  have h₁ := h 0 1
  have h₂ := h 1 1
  norm_num at h₀ h₁ h₂
  have hdet : r*u-s*t ≠ 0 := by
    intro Hz
    have he : (r*a^2+s*c^2)*(t*(a+b)^2+u*(c+d)^2) -
        (r*(a+b)^2+s*(c+d)^2)*(t*a^2+u*c^2) =
        (r*u-s*t)*(a^2*(c+d)^2-c^2*(a+b)^2) := by ring
    rw [h₀.1, h₀.2, h₂.1, h₂.2, Hz] at he
    norm_num at he
  have htrace₁ : r*(a^2+b^2)+s*(c^2+d^2)=0 := by linarith [h₀.1,h₁.1]
  have htrace₂ : t*(a^2+b^2)+u*(c^2+d^2)=0 := by linarith [h₀.2,h₁.2]
  have hp : (r*u-s*t)*(a^2+b^2)=0 := by linear_combination u*htrace₁-s*htrace₂
  have hq : (r*u-s*t)*(c^2+d^2)=0 := by linear_combination r*htrace₂-t*htrace₁
  have hp' := (mul_eq_zero.mp hp).resolve_left hdet
  have hq' := (mul_eq_zero.mp hq).resolve_left hdet
  have ha : a=0 := by nlinarith [sq_nonneg b]
  have hc : c=0 := by nlinarith [sq_nonneg d]
  simp [ha,hc] at h₀

theorem three_squares (x y : ℝ) :
    x^2-y^2 = x^2-y^2 ∧ 2*x*y = (x+y)^2-x^2-y^2 := by
  exact ⟨rfl, by ring⟩

def Realizes (n : ℕ) : Prop :=
  ∃ a b r t : Fin n → ℝ, ∀ x y : ℝ,
    (∑ i, r i * (a i*x+b i*y)^2) = x^2-y^2 ∧
    (∑ i, t i * (a i*x+b i*y)^2) = 2*x*y

theorem minimum_three : Realizes 3 ∧ ∀ n, Realizes n → 3 ≤ n := by
  constructor
  · refine ⟨![1,0,1], ![0,1,1], ![1,-1,0], ![-1,-1,1], ?_⟩
    intro x y
    simp [Fin.sum_univ_three]
    constructor <;> ring
  · intro n hn
    by_contra h
    have cases : n=0 ∨ n=1 ∨ n=2 := by omega
    rcases cases with h₀ | h₁ | h₂
    · subst n
      obtain ⟨a,b,r,t,e⟩ := hn
      have he := (e 1 0).1
      norm_num at he
    · subst n
      obtain ⟨a,b,r,t,e⟩ := hn
      apply no_two_squares
      refine ⟨a 0,b 0,0,0,r 0,0,t 0,0,?_⟩
      intro x y
      simpa using e x y
    · subst n
      obtain ⟨a,b,r,t,e⟩ := hn
      exact no_two_squares ⟨a 0,b 0,a 1,b 1,r 0,r 1,t 0,t 1,
        fun x y => by simpa [Fin.sum_univ_two] using e x y⟩

/-- Enlarging the primitive to products of two linear forms gives two independent outputs. -/
theorem two_products (x y : ℝ) : x^2-y^2 = (x-y)*(x+y) ∧ 2*x*y = (2*x)*y :=
  ⟨by ring, rfl⟩

end BinaryPencil
