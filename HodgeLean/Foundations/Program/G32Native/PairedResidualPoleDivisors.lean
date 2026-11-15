import HodgeLean.Foundations.Program.G32Native.PairedResidualPoleEnvelope

/-! # Divisors of nonzero members of the full simple-pole space -/

noncomputable section
set_option maxHeartbeats 400000
open HodgeLean.Adapters
open scoped Manifold ContDiff Topology
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- A nonzero normalized differential has a nonzero punctured coefficient germ. -/
theorem residual_normalized_form_has_finite_order
    (hE : Module.finrank ℂ E = 1) (S : Set C) (w : b4c_MeroForm E C hE)
    (hw : (w : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0)
    (ha : ∀ p ∉ S, AnalyticAt ℂ (HurwitzPrymRR_loc hE w p) 0)
    (hz : ∀ p ∈ S, ∀ u, w ⟨p, u⟩ = 0) :
    ∃ p, meromorphicOrderAt (HurwitzPrymRR_loc hE w p) 0 ≠ ⊤ := by
  classical
  by_contra h
  apply hw
  apply RiemannRochEichler_regular_zero_of_zero_germs hE w w.property.1 S ha hz
  intro p
  exact meromorphicOrderAt_eq_top_iff.mp (not_not.mp (not_exists.mp h p))

#print axioms residual_normalized_form_has_finite_order

/-- Every nonzero normalized pole form has the canonical divisor degree. -/
theorem residual_normalized_form_canonical_degree
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (S : Set C) (w : b4c_MeroForm E C hE)
    (hw : (w : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0)
    (ha : ∀ p ∉ S, AnalyticAt ℂ (HurwitzPrymRR_loc hE w p) 0)
    (hz : ∀ p ∈ S, ∀ u, w ⟨p, u⟩ = 0) :
    b4c_deg (b4c_divForm (hE := hE) w) =
      2 * (Module.finrank ℂ (b3_HolForm E C) : ℤ) - 2 :=
  b4c_deg_canonical_aux hE w hw
    (residual_normalized_form_has_finite_order hE S w hw ha hz)

#print axioms residual_normalized_form_canonical_degree

/-- The marked divisor absorbs every pole of a normalized simple-pole form. -/
theorem residual_normalized_adjusted_divisor_effective
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {n : ℕ}
    (y : Fin n → C) (hy : Function.Injective y)
    (w : b4c_MeroForm E C hE)
    (hw : (w : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0)
    (horder : ∀ p, ((-1 : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (HurwitzPrymRR_loc hE w p) 0)
    (ha : ∀ p ∉ Set.range y, AnalyticAt ℂ (HurwitzPrymRR_loc hE w p) 0)
    (hz : ∀ p ∈ Set.range y, ∀ u, w ⟨p, u⟩ = 0) :
    ∀ p, 0 ≤ (b4c_divForm (hE := hE) w + s2e_markedPoleDivisor y) p := by
  classical
  have hg := residual_normalized_form_has_finite_order hE (Set.range y) w hw ha hz
  have hcoe := RiemannRochEichler_divForm_order hE w hg
  intro p
  change (0 : ℤ) ≤ b4c_divForm (hE := hE) w p + s2e_markedPoleDivisor y p
  by_cases hp : p ∈ Set.range y
  · obtain ⟨j, rfl⟩ := hp
    rw [s2e_markedPoleDivisor_apply_of_injective y hy j]
    have ho := horder (y j)
    rw [← hcoe (y j), WithTop.coe_le_coe] at ho
    omega
  · rw [s2e_markedPoleDivisor_apply_outside y p hp, add_zero]
    have ho := (ha p hp).meromorphicOrderAt_nonneg
    rw [← hcoe p] at ho
    exact WithTop.coe_le_coe.mp ho

#print axioms residual_normalized_adjusted_divisor_effective

/-- The genus equation fixes the degree throughout the full pole space. -/
theorem residual_normalized_adjusted_divisor_degree
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {k r : ℕ}
    (y : Fin (2 * r) → C) (w : b4c_MeroForm E C hE)
    (hw : (w : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0)
    (ha : ∀ p ∉ Set.range y, AnalyticAt ℂ (HurwitzPrymRR_loc hE w p) 0)
    (hz : ∀ p ∈ Set.range y, ∀ u, w ⟨p, u⟩ = 0)
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ (b3_HolForm E C) + 2 * r) :
    b4c_deg (b4c_divForm (hE := hE) w + s2e_markedPoleDivisor y) = (2 * k : ℕ) := by
  rw [RiemannRochAna_deg_add,
    residual_normalized_form_canonical_degree hE (Set.range y) w hw ha hz,
    s2e_markedPoleDivisor_degree]
  have hg : (2 : ℤ) * (k : ℤ) + 2 =
      2 * (Module.finrank ℂ (b3_HolForm E C) : ℤ) + 2 * (r : ℤ) := by
    exact_mod_cast hgenus
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  omega

#print axioms residual_normalized_adjusted_divisor_degree

end HodgeLean.Foundations.Program.G32Native
