import BinaryPencil
import OpposedGates

namespace ProducerPins

/-- Two-dimensional vector language, shared hidden layer and unrestricted signed readout. -/
def Supports (n : ℕ) : Prop :=
  ∃ v : Fin n → ℝ × ℝ, ∃ w : Fin n → ℝ × ℝ, ∀ p : ℝ × ℝ,
    ((∑ i, (w i).1 * ((v i).1*p.1 + (v i).2*p.2)^2),
     (∑ i, (w i).2 * ((v i).1*p.1 + (v i).2*p.2)^2)) =
      (p.1^2-p.2^2, 2*p.1*p.2)

theorem square_contract (n : ℕ) : Supports n ↔ BinaryPencil.Realizes n := by
  constructor
  · rintro ⟨v,w,h⟩
    exact ⟨fun i => (v i).1, fun i => (v i).2, fun i => (w i).1, fun i => (w i).2,
      fun x y => ⟨congrArg Prod.fst (h (x,y)), congrArg Prod.snd (h (x,y))⟩⟩
  · rintro ⟨a,b,r,t,h⟩
    exact ⟨fun i => (a i,b i), fun i => (r i,t i),
      fun p => Prod.ext (h p.1 p.2).1 (h p.1 p.2).2⟩

theorem least_width : IsLeast {n : ℕ | Supports n} 3 :=
  ⟨(square_contract 3).mpr BinaryPencil.minimum_three.1,
   fun n hn => BinaryPencil.minimum_three.2 n ((square_contract n).mp hn)⟩

/-- Raw exponential specification, with effective outer weights given separately. -/
theorem sigmoid_pair_contract (x u d p q : ℝ) :
    p*d*u*(x*(1/(1+Real.exp (-x)))) - q*d*u*((-x)*(1/(1+Real.exp x))) =
      p*d*u*x+(p-q)*d*u*((-x)*(1/(1+Real.exp x))) := by
  simpa only [OpposedGates.silu, OpposedGates.sigmoid, neg_neg] using
    OpposedGates.unequal_routes x u d p q

end ProducerPins
