import Mathlib

/-!
# Linear broadcast with side information

A secret `w` lies in a finite-dimensional space `V` over a field `K`. Receiver `i` already knows
the values on `w` of the linear forms in a subspace `L i` of the dual space, and wants the values
of the forms in a subspace `D i`. The sender broadcasts the values of the forms in a subspace `B`.
Results, with their class:

* **[L-known] decoding criterion**: a receiver computes its demand from what it knows and hears,
  with any decoder, linear or not, iff `D ≤ L ⊔ B` (`decodes_iff`). So for a linear broadcast,
  nonlinear decoders never help;
* **[L-known] single-receiver bound**: then `dim (L ⊔ D) ≤ dim L + dim B` (`finrank_le_of_le_sup`);
* **[L] identical side information gives no coding gain**: if every receiver knows the same `L`,
  the least broadcast dimension is `dim (L ⊔ ⨆ i, D i) - dim L`, the cost of one receiver that
  wants all the demands (`identical_lower`, `identical_attained`);
* **[L] nested side information, exact optimum**: for two receivers with `L₁ ≤ L₂`, the least
  broadcast dimension is `dim (L₂ ⊔ D₁ ⊔ D₂) - dim L₂ + dim (L₁ ⊔ (L₁ ⊔ D₁) ⊓ L₂) - dim L₁`
  (`nested_lower`, `nested_attained`);
* **example, a joint broadcast beats separate messages**: two receivers that each know the value
  the other wants are served by one broadcast form, while separate messages need one form each
  (`xor_serves`, `xor_separate`);
* **[L-known] response signatures**: linear queries `Q` over a field with `q` elements take exactly
  `q ^ rank Q` response vectors, so any message from which the responses can be recomputed takes
  at least `q ^ rank Q` values (`card_responses`, `message_lower_bound`); a bilinear query `yᵀ W x`
  is the linear query `vec (y xᵀ)` on the entries of `W` (`bilinear_query`);
* **[L] example, coding across instances halves the broadcast**: three receivers see `w₀`, `w₁`
  and `w₀ + w₁` of a secret `w ∈ F₂²` and want all of it. One instance needs a message with at
  least `4` values, for every code, linear or not (`scalar_needs_four`). Two instances are served
  by one linear 2-bit message (`two_instances_two_bits`), and no code for `t` instances uses fewer
  than `2 ^ t` messages (`rate_lower_bound`).
-/

namespace LinearBroadcast

open Module Submodule

section General

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The values on `w` of the forms in `S`. -/
def obs (S : Submodule K (Dual K V)) (w : V) : S → K := fun φ => (φ : Dual K V) w

/-- A receiver that knows the forms in `L` and hears the forms in `B` computes the forms in `D`
with some decoder `g`, which need not be linear. -/
def Decodes (L B D : Submodule K (Dual K V)) : Prop :=
  ∃ g : (L → K) × (B → K) → (D → K), ∀ w, g (obs L w, obs B w) = obs D w

/-- A map factors through `F` iff it is constant on the fibres of `F`. -/
theorem factor_iff {α β γ : Type*} [Nonempty γ] (F : α → β) (G : α → γ) :
    (∃ g : β → γ, ∀ a, g (F a) = G a) ↔ ∀ a a', F a = F a' → G a = G a' := by
  classical
  constructor
  · rintro ⟨g, hg⟩ a a' h
    rw [← hg a, ← hg a', h]
  · intro h
    refine ⟨fun b => if hb : ∃ a, F a = b then G hb.choose else Classical.arbitrary γ,
      fun a => ?_⟩
    have hb : ∃ a', F a' = F a := ⟨a, rfl⟩
    simp only [dif_pos hb]
    exact h _ _ hb.choose_spec

theorem decodes_iff_fibers (L B D : Submodule K (Dual K V)) :
    Decodes L B D ↔
      ∀ w w', obs L w = obs L w' → obs B w = obs B w' → obs D w = obs D w' := by
  unfold Decodes
  rw [factor_iff (fun w => (obs L w, obs B w)) (obs D)]
  constructor
  · intro h w w' h1 h2
    exact h w w' (Prod.ext h1 h2)
  · intro h w w' hw
    exact h w w' (congrArg Prod.fst hw) (congrArg Prod.snd hw)

/-- **Decoding criterion.** With any decoder, linear or not, the receiver computes the forms in
`D` iff `D ≤ L ⊔ B`. -/
theorem decodes_iff [FiniteDimensional K V] (L B D : Submodule K (Dual K V)) :
    Decodes L B D ↔ D ≤ L ⊔ B := by
  rw [decodes_iff_fibers]
  constructor
  · intro h
    have key : (L ⊔ B).dualCoannihilator ≤ D.dualCoannihilator := by
      intro v hv
      rw [mem_dualCoannihilator] at hv ⊢
      have hL : obs L v = obs L 0 := by
        funext φ
        simp only [obs, map_zero]
        exact hv φ.1 (mem_sup_left φ.2)
      have hB : obs B v = obs B 0 := by
        funext φ
        simp only [obs, map_zero]
        exact hv φ.1 (mem_sup_right φ.2)
      intro d hd
      have := congrFun (h v 0 hL hB) ⟨d, hd⟩
      simpa [obs] using this
    have h2 := le_dualAnnihilator_iff_le_dualCoannihilator.2 key
    rwa [Subspace.dualCoannihilator_dualAnnihilator_eq] at h2
  · intro hD w w' hL hB
    funext d
    obtain ⟨l, hl, b, hb, hlb⟩ := mem_sup.1 (hD d.2)
    have e1 := congrFun hL ⟨l, hl⟩
    have e2 := congrFun hB ⟨b, hb⟩
    simp only [obs] at e1 e2 ⊢
    rw [← hlb, LinearMap.add_apply, LinearMap.add_apply, e1, e2]

/-- **Single-receiver bound.** A broadcast that completes `D` over `L` has
`dim (L ⊔ D) ≤ dim L + dim B`. -/
theorem finrank_le_of_le_sup [FiniteDimensional K V] {L B D : Submodule K (Dual K V)}
    (h : D ≤ L ⊔ B) : finrank K ↥(L ⊔ D) ≤ finrank K L + finrank K B :=
  (Submodule.finrank_mono (sup_le le_sup_left h)).trans
    (Submodule.finrank_add_le_finrank_add_finrank L B)

/-- A demand outside the side information forces a nonzero broadcast. -/
theorem finrank_pos_of_not_le [FiniteDimensional K V] {L B D : Submodule K (Dual K V)}
    (hD : ¬ D ≤ L) (h : D ≤ L ⊔ B) : 0 < finrank K B := by
  rcases Nat.eq_zero_or_pos (finrank K B) with h0 | h0
  · rw [Submodule.finrank_eq_zero.1 h0, sup_bot_eq] at h
    exact absurd h hD
  · exact h0

/-- The broadcast `B` serves every receiver `i`, with side information `L i` and demand `D i`. -/
def Serves {ι : Type*} (L D : ι → Submodule K (Dual K V)) (B : Submodule K (Dual K V)) : Prop :=
  ∀ i, D i ≤ L i ⊔ B

theorem serves_iff_decodes [FiniteDimensional K V] {ι : Type*}
    (L D : ι → Submodule K (Dual K V)) (B : Submodule K (Dual K V)) :
    Serves L D B ↔ ∀ i, Decodes (L i) B (D i) := by
  simp only [Serves, decodes_iff]

/-- A relative complement: inside `T ≥ P` there is `C` with `P ⊔ C = T`, `P ⊓ C = ⊥`. -/
theorem exists_rel_compl {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {P T : Submodule K W} (h : P ≤ T) :
    ∃ C, C ≤ T ∧ P ⊔ C = T ∧ P ⊓ C = ⊥ ∧ finrank K P + finrank K C = finrank K T := by
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl P
  have hsup : P ⊔ q ⊓ T = T := by
    rw [← sup_inf_assoc_of_le q h, hq.sup_eq_top, top_inf_eq]
  have hinf : P ⊓ (q ⊓ T) = ⊥ :=
    eq_bot_iff.2 ((inf_le_inf_left P inf_le_left).trans hq.inf_eq_bot.le)
  refine ⟨q ⊓ T, inf_le_right, hsup, hinf, ?_⟩
  have := Submodule.finrank_sup_add_finrank_inf_eq P (q ⊓ T)
  rw [hsup, hinf, finrank_bot, add_zero] at this
  exact this.symm

/-- **Identical side information, lower bound.** Receivers that all know `L` need
`dim (L ⊔ ⨆ i, D i) ≤ dim L + dim B`. -/
theorem identical_lower [FiniteDimensional K V] {ι : Type*} (L : Submodule K (Dual K V))
    (D : ι → Submodule K (Dual K V)) (B : Submodule K (Dual K V))
    (h : Serves (fun _ => L) D B) :
    finrank K ↥(L ⊔ ⨆ i, D i) ≤ finrank K L + finrank K B :=
  finrank_le_of_le_sup (iSup_le fun i => h i)

/-- **Identical side information, attained.** Some broadcast of dimension
`dim (L ⊔ ⨆ i, D i) - dim L` serves all receivers that know `L`: there is no coding gain beyond
one receiver that wants every demand. -/
theorem identical_attained [FiniteDimensional K V] {ι : Type*} (L : Submodule K (Dual K V))
    (D : ι → Submodule K (Dual K V)) :
    ∃ B, Serves (fun _ => L) D B ∧
      finrank K L + finrank K B = finrank K ↥(L ⊔ ⨆ i, D i) := by
  obtain ⟨C, -, hsup, -, hdim⟩ := exists_rel_compl (le_sup_left : L ≤ L ⊔ ⨆ i, D i)
  refine ⟨C, fun i => ?_, hdim⟩
  show D i ≤ L ⊔ C
  rw [hsup]
  exact le_sup_of_le_right (le_iSup D i)

/-- **Nested side information, lower bound.** Two receivers with `L₁ ≤ L₂`. -/
theorem nested_lower [FiniteDimensional K V] {L₁ L₂ D₁ D₂ B : Submodule K (Dual K V)}
    (hL : L₁ ≤ L₂) (h₁ : D₁ ≤ L₁ ⊔ B) (h₂ : D₂ ≤ L₂ ⊔ B) :
    finrank K ↥(L₂ ⊔ (D₁ ⊔ D₂)) + finrank K ↥(L₁ ⊔ (L₁ ⊔ D₁) ⊓ L₂) ≤
      finrank K L₁ + finrank K L₂ + finrank K B := by
  have hT : L₂ ⊔ (D₁ ⊔ D₂) ≤ L₂ ⊔ B :=
    sup_le le_sup_left (sup_le (h₁.trans (sup_le_sup_right hL B)) h₂)
  have hA1 : L₁ ⊔ D₁ ≤ L₁ ⊔ B := sup_le le_sup_left h₁
  have hA : L₁ ⊔ (L₁ ⊔ D₁) ⊓ L₂ ≤ L₁ ⊔ B ⊓ L₂ := by
    rw [← sup_inf_assoc_of_le B hL]
    exact sup_le (le_inf (le_sup_left : L₁ ≤ L₁ ⊔ B) hL) (inf_le_inf_right L₂ hA1)
  have e1 := Submodule.finrank_mono hT
  have e2 := Submodule.finrank_mono hA
  have e3 := Submodule.finrank_add_le_finrank_add_finrank L₁ (B ⊓ L₂)
  have e4 := Submodule.finrank_sup_add_finrank_inf_eq L₂ B
  rw [inf_comm] at e4
  omega

/-- **Nested side information, attained.** The bound of `nested_lower` is reached. -/
theorem nested_attained [FiniteDimensional K V] {L₁ L₂ : Submodule K (Dual K V)}
    (hL : L₁ ≤ L₂) (D₁ D₂ : Submodule K (Dual K V)) :
    ∃ B, D₁ ≤ L₁ ⊔ B ∧ D₂ ≤ L₂ ⊔ B ∧
      finrank K L₁ + finrank K L₂ + finrank K B =
        finrank K ↥(L₂ ⊔ (D₁ ⊔ D₂)) + finrank K ↥(L₁ ⊔ (L₁ ⊔ D₁) ⊓ L₂) := by
  -- `C₀`: the part of the first demand that the second receiver already knows
  obtain ⟨C₀, -, hsup₀, -, hdim₀⟩ :=
    exists_rel_compl (le_sup_left : L₁ ≤ L₁ ⊔ (L₁ ⊔ D₁) ⊓ L₂)
  -- `C₁`: the part of the first demand outside `L₂`
  obtain ⟨C₁, hC₁, hsup₁, hinf₁, -⟩ :=
    exists_rel_compl (inf_le_left : (L₁ ⊔ D₁) ⊓ L₂ ≤ L₁ ⊔ D₁)
  have hAT : L₁ ⊔ D₁ ≤ L₂ ⊔ (D₁ ⊔ D₂) :=
    sup_le (hL.trans le_sup_left) ((le_sup_left : D₁ ≤ D₁ ⊔ D₂).trans le_sup_right)
  have hdisj : L₂ ⊓ C₁ = ⊥ := by
    rw [eq_bot_iff, ← hinf₁]
    exact le_inf (le_inf (inf_le_right.trans hC₁) inf_le_left) inf_le_right
  have hdimL₂C₁ := Submodule.finrank_sup_add_finrank_inf_eq L₂ C₁
  rw [hdisj, finrank_bot, add_zero] at hdimL₂C₁
  -- `C₂`: completes `L₂ ⊔ C₁` to everything the second receiver must reach
  obtain ⟨C₂, -, hsup₂, -, hdim₂⟩ :=
    exists_rel_compl (sup_le le_sup_left (hC₁.trans hAT) : L₂ ⊔ C₁ ≤ L₂ ⊔ (D₁ ⊔ D₂))
  have h1 : D₁ ≤ L₁ ⊔ (C₁ ⊔ C₂ ⊔ C₀) := by
    calc D₁ ≤ L₁ ⊔ D₁ := le_sup_right
      _ = (L₁ ⊔ D₁) ⊓ L₂ ⊔ C₁ := hsup₁.symm
      _ ≤ L₁ ⊔ (C₁ ⊔ C₂ ⊔ C₀) := by
        refine sup_le ?_ (le_sup_of_le_right (le_sup_left.trans le_sup_left))
        calc (L₁ ⊔ D₁) ⊓ L₂ ≤ L₁ ⊔ (L₁ ⊔ D₁) ⊓ L₂ := le_sup_right
          _ = L₁ ⊔ C₀ := hsup₀.symm
          _ ≤ L₁ ⊔ (C₁ ⊔ C₂ ⊔ C₀) := sup_le_sup_left le_sup_right L₁
  have h2 : D₂ ≤ L₂ ⊔ (C₁ ⊔ C₂ ⊔ C₀) := by
    calc D₂ ≤ L₂ ⊔ (D₁ ⊔ D₂) := (le_sup_right : D₂ ≤ D₁ ⊔ D₂).trans le_sup_right
      _ = L₂ ⊔ C₁ ⊔ C₂ := hsup₂.symm
      _ ≤ L₂ ⊔ (C₁ ⊔ C₂ ⊔ C₀) := by
        rw [sup_assoc]
        exact sup_le_sup_left le_sup_left L₂
  refine ⟨C₁ ⊔ C₂ ⊔ C₀, h1, h2, ?_⟩
  have u1 := Submodule.finrank_add_le_finrank_add_finrank (C₁ ⊔ C₂) C₀
  have u2 := Submodule.finrank_add_le_finrank_add_finrank C₁ C₂
  have low := nested_lower hL h1 h2
  omega

end General

section Xor

variable (K : Type*) [Field K]

/-- The coordinate form `w ↦ w i` on `K²`. -/
def e (i : Fin 2) : Dual K (Fin 2 → K) := LinearMap.proj i

theorem e_apply (i : Fin 2) (w : Fin 2 → K) : e K i w = w i := rfl

theorem not_le_span (i j : Fin 2) (hij : i ≠ j) : ¬ (K ∙ e K i) ≤ (K ∙ e K j) := by
  rw [span_singleton_le_iff_mem, mem_span_singleton]
  rintro ⟨c, hc⟩
  have := LinearMap.congr_fun hc (Pi.single i 1)
  simp [e_apply, hij.symm] at this

/-- **One form serves both receivers**: receiver `0` knows `w₁` and wants `w₀`, receiver `1`
knows `w₀` and wants `w₁`, and the broadcast is `w₀ + w₁`. -/
theorem xor_serves :
    Serves ![K ∙ e K 1, K ∙ e K 0] ![K ∙ e K 0, K ∙ e K 1] (K ∙ (e K 0 + e K 1)) := by
  intro i
  fin_cases i
  · show (K ∙ e K 0) ≤ (K ∙ e K 1) ⊔ (K ∙ (e K 0 + e K 1))
    rw [span_singleton_le_iff_mem, mem_sup]
    exact ⟨-e K 1, neg_mem (mem_span_singleton_self _), e K 0 + e K 1,
      mem_span_singleton_self _, by abel⟩
  · show (K ∙ e K 1) ≤ (K ∙ e K 0) ⊔ (K ∙ (e K 0 + e K 1))
    rw [span_singleton_le_iff_mem, mem_sup]
    exact ⟨-e K 0, neg_mem (mem_span_singleton_self _), e K 0 + e K 1,
      mem_span_singleton_self _, by abel⟩

theorem xor_broadcast_dim : finrank K ↥(K ∙ (e K 0 + e K 1)) = 1 := by
  apply finrank_span_singleton
  intro h
  have := LinearMap.congr_fun h (Pi.single 0 1)
  simp [e_apply] at this

/-- **Separate messages need two forms**: each receiver needs a nonzero message of its own. -/
theorem xor_separate (B₀ B₁ : Submodule K (Dual K (Fin 2 → K)))
    (h₀ : (K ∙ e K 0) ≤ (K ∙ e K 1) ⊔ B₀) (h₁ : (K ∙ e K 1) ≤ (K ∙ e K 0) ⊔ B₁) :
    2 ≤ finrank K B₀ + finrank K B₁ := by
  have a := finrank_pos_of_not_le (not_le_span K 0 1 (by decide)) h₀
  have b := finrank_pos_of_not_le (not_le_span K 1 0 (by decide)) h₁
  omega

end Xor

section Signatures

open Matrix

/-- **Response signatures.** Linear queries `Q` take exactly `q ^ rank Q` response vectors. -/
theorem card_responses {K ι κ : Type*} [Field K] [Fintype ι] [Fintype κ] [Finite K]
    (Q : Matrix ι κ K) :
    Nat.card (LinearMap.range Q.mulVecLin) = Nat.card K ^ Q.rank :=
  Module.natCard_eq_pow_finrank

/-- **Message lower bound.** A message `m w` from which the responses `Q w` can be recomputed
takes at least `q ^ rank Q` values. -/
theorem message_lower_bound {K ι κ M : Type*} [Field K] [Fintype ι] [Fintype κ] [Finite K]
    [Finite M] (Q : Matrix ι κ K) (m : (κ → K) → M) (g : M → ι → K)
    (h : ∀ w, g (m w) = Q *ᵥ w) : Nat.card K ^ Q.rank ≤ Nat.card M := by
  rw [← card_responses]
  refine Nat.card_le_card_of_injective (fun s => m (LinearMap.mem_range.1 s.2).choose) ?_
  intro s t hst
  have hs := (LinearMap.mem_range.1 s.2).choose_spec
  have ht := (LinearMap.mem_range.1 t.2).choose_spec
  apply Subtype.ext
  rw [← hs, ← ht, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, ← h, ← h]
  exact congrArg g hst

/-- A bilinear query `yᵀ W x` is the linear query `vec (y xᵀ)` on the entries of `W`. -/
theorem bilinear_query {K m n : Type*} [CommRing K] [Fintype m] [Fintype n] (y : m → K)
    (x : n → K) (W : Matrix m n K) :
    y ⬝ᵥ (W *ᵥ x) = (fun p : m × n => y p.1 * x p.2) ⬝ᵥ (fun p => W p.1 p.2) := by
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

end Signatures

section Binary

/-- Receiver `i` sees `w₀`, `w₁` or `w₀ + w₁` of a secret `w ∈ F₂²`. -/
def view : Fin 3 → (Fin 2 → ZMod 2) → ZMod 2 :=
  ![fun w => w 0, fun w => w 1, fun w => w 0 + w 1]

/-- Any two distinct secrets look the same to some receiver. -/
theorem confusable : ∀ w w' : Fin 2 → ZMod 2, w ≠ w' → ∃ i, view i w = view i w' := by
  decide

/-- **One instance needs four messages, for every code.** If each receiver recovers the whole
secret from its view and the message `e w`, then `e` takes at least `4` values (2 bits). -/
theorem scalar_needs_four {M : Type*} [Finite M] (e : (Fin 2 → ZMod 2) → M)
    (hdec : ∀ i w w', view i w = view i w' → e w = e w' → w = w') : 4 ≤ Nat.card M := by
  have hinj : Function.Injective e := by
    intro w w' h
    by_contra hne
    obtain ⟨i, hi⟩ := confusable w w' hne
    exact hne (hdec i w w' hi h)
  have := Nat.card_le_card_of_injective e hinj
  simpa [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card] using this

/-- The 2-bit message `A + ω B ∈ F₄ = F₂[ω]/(ω² + ω + 1)` for two instances `u, v`, with
`A = (u₀, v₀)` and `B = (u₁, v₁)` in the basis `1, ω`. It is `F₂`-linear in `(u, v)`. -/
def msg (u v : Fin 2 → ZMod 2) : ZMod 2 × ZMod 2 := (u 0 + v 1, v 0 + u 1 + v 1)

/-- **Two instances, two bits.** Every receiver recovers both instances from its two views and
the 2-bit linear message. -/
theorem two_instances_two_bits : ∀ i : Fin 3, ∀ u v u' v' : Fin 2 → ZMod 2,
    view i u = view i u' → view i v = view i v' → msg u v = msg u' v' → u = u' ∧ v = v' := by
  decide

/-- **No code beats one bit per instance.** If receiver `0` recovers `t` instances from its views
and the message, the message takes at least `2 ^ t` values. -/
theorem rate_lower_bound {t : ℕ} {M : Type*} [Finite M] (e : (Fin t → Fin 2 → ZMod 2) → M)
    (hdec : ∀ w w', (∀ s, view 0 (w s) = view 0 (w' s)) → e w = e w' → w = w') :
    2 ^ t ≤ Nat.card M := by
  have hinj : Function.Injective fun b : Fin t → ZMod 2 => e fun s => ![0, b s] := by
    intro b b' h
    have hw := hdec _ _ (fun s => by simp [view]) h
    funext s
    simpa using congrFun (congrFun hw s) 1
  have := Nat.card_le_card_of_injective _ hinj
  simpa [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card] using this

end Binary

end LinearBroadcast
