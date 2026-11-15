import HodgeLean.Foundations.Program.G32Native.PairedResidualProjectiveSystem
import HodgeLean.Foundations.Program.SchoenCycleDivisorInjectivity

/-! # Divisor uniqueness in normalized differential spaces -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters Filter
open scoped Manifold ContDiff Topology
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- Equal divisors in a normalized differential space determine a nonzero scalar. -/
theorem residual_normalized_divisors_proportional
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (S : Set C)
    (W : Submodule ℂ (TangentBundle 𝓘(ℂ, E) C → ℂ))
    (hW : ∀ q : W, b4c_IsMeroForm hE q.val ∧
      (∀ p ∉ S, AnalyticAt ℂ (HurwitzPrymRR_loc hE q.val p) 0) ∧
      ∀ p ∈ S, ∀ u, q.val ⟨p, u⟩ = 0)
    (u v : W) (hu : u ≠ 0) (hv : v ≠ 0)
    (hd : b4c_divForm (hE := hE) u.val = b4c_divForm (hE := hE) v.val) :
    ∃ c : ℂ, c ≠ 0 ∧ u = c • v := by
  let U : b4c_MeroForm E C hE := ⟨u.val, (hW u).1⟩
  let V : b4c_MeroForm E C hE := ⟨v.val, (hW v).1⟩
  have hU : (U : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0 := fun h => hu (Subtype.ext h)
  have hV : (V : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0 := fun h => hv (Subtype.ext h)
  have hgU := residual_normalized_form_has_finite_order hE S U hU (hW u).2.1 (hW u).2.2
  have hgV := residual_normalized_form_has_finite_order hE S V hV (hW v).2.1 (hW v).2.2
  obtain ⟨c, hc, hr⟩ := s2e_equal_divisors_ratio_nonzero_constant hE U V hU hV hgU hgV hd
  refine ⟨c, hc, sub_eq_zero.mp (Subtype.ext ?_)⟩
  apply RiemannRochEichler_regular_zero_of_zero_germs hE (u - c • v).val
    (hW (u - c • v)).1.1 S (hW (u - c • v)).2.1 (hW (u - c • v)).2.2
  intro p
  have hp := s2e_constant_formRatio_germ hE U V hgU hgV c hr p
  have he : HurwitzPrymRR_loc hE (u - c • v).val p =
      (fun z => HurwitzPrymRR_loc hE U p z - c * HurwitzPrymRR_loc hE V p z) := by
    rfl
  rw [he]
  filter_upwards [hp] with z hz
  exact sub_eq_zero.mpr hz

#print axioms residual_normalized_divisors_proportional

/-- The full normalized projective divisor assignment distinguishes its parameters. -/
theorem residualProjectiveDivisor_injective
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {n : ℕ} (y : Fin n → C)
    (W : Submodule ℂ (TangentBundle 𝓘(ℂ, E) C → ℂ))
    (hW : ∀ q : W, b4c_IsMeroForm hE q.val ∧
      (∀ p ∉ Set.range y, AnalyticAt ℂ (HurwitzPrymRR_loc hE q.val p) 0) ∧
      ∀ p ∈ Set.range y, ∀ u, q.val ⟨p, u⟩ = 0) :
    Function.Injective (residualProjectiveDivisor hE y W) := by
  intro z t h
  induction z using Projectivization.ind with
  | h u hu =>
    induction t using Projectivization.ind with
    | h v hv =>
      change b4c_divForm (hE := hE) u.val + s2e_markedPoleDivisor y =
        b4c_divForm (hE := hE) v.val + s2e_markedPoleDivisor y at h
      obtain ⟨c, _, hc⟩ := residual_normalized_divisors_proportional hE
        (Set.range y) W hW u v hu hv (add_right_cancel h)
      exact (Projectivization.mk_eq_mk_iff' ℂ u v hu hv).mpr ⟨c, hc.symm⟩

#print axioms residualProjectiveDivisor_injective

/-- The full-system divisor assignment retains the supplied paired divisors exactly. -/
theorem residualProjectiveDivisor_map_paired
    (hE : Module.finrank ℂ E = 1) {r n : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (y : Fin n → C)
    (W : Submodule ℂ (TangentBundle 𝓘(ℂ, E) C → ℂ))
    (F : (b3_HolForm E C × (Fin r → ℂ)) →ₗ[ℂ] W)
    (hF : Function.Injective F)
    (hFg : ∀ v p, HurwitzPrymRR_loc hE (F v).val p =ᶠ[𝓝[≠] 0]
      HurwitzPrymRR_loc hE (s2e_pairedDifferentialLinear hE w v) p)
    (z : Projectivization ℂ (b3_HolForm E C × (Fin r → ℂ))) :
    residualProjectiveDivisor hE y W (Projectivization.map F hF z) =
      s2e_projectiveDifferentialDivisor hE w y z := by
  induction z using Projectivization.ind with
  | h v hv =>
    change b4c_divForm (hE := hE) (F v).val + s2e_markedPoleDivisor y =
      b4c_divForm (hE := hE) (s2e_pairedDifferentialLinear hE w v) + s2e_markedPoleDivisor y
    rw [residual_divisor_eq_of_germs hE _ _ (hFg v)]

#print axioms residualProjectiveDivisor_map_paired

/-- The full-system quotient map agrees with the supplied paired divisor map. -/
theorem residualProjectiveSystemPoint_map_paired
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) {k r : ℕ}
    (w : Fin r → b4c_MeroForm E C hE) (x : Fin r → C)
    (hres : ∀ i j, b4c_res (hE := hE) (w i) (x j) = if i = j then 1 else 0)
    (y : Fin (2 * r) → C) (hy : Function.Injective y)
    (horder : ∀ i p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hE (w i) p) 0)
    (hout : ∀ i p, p ∉ Set.range y → AnalyticAt ℂ (HurwitzPrymRR_loc hE (w i) p) 0)
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ (b3_HolForm E C) + 2 * r)
    (W : Submodule ℂ (TangentBundle 𝓘(ℂ, E) C → ℂ))
    (hW : ∀ q : W, b4c_IsMeroForm hE q.val ∧
      (∀ p, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc hE q.val p) 0) ∧
      (∀ p ∉ Set.range y, AnalyticAt ℂ (HurwitzPrymRR_loc hE q.val p) 0) ∧
      ∀ p ∈ Set.range y, ∀ u, q.val ⟨p, u⟩ = 0)
    (F : (b3_HolForm E C × (Fin r → ℂ)) →ₗ[ℂ] W) (hF : Function.Injective F)
    (hFg : ∀ v p, HurwitzPrymRR_loc hE (F v).val p =ᶠ[𝓝[≠] 0]
      HurwitzPrymRR_loc hE (s2e_pairedDifferentialLinear hE w v) p)
    {Z B : Over (Spec ↧ℂ)} (γ : g3_power Z (2 * k) ⟶ B) (e : C → ComplexPoint Z)
    (z : Projectivization ℂ (b3_HolForm E C × (Fin r → ℂ))) :
    residualProjectiveSystemPoint hE y hy W hW hgenus γ e (Projectivization.map F hF z) =
      s2e_projectiveDifferentialQuotientPoint hE w x hres y hy horder hout hgenus γ e z := by
  unfold residualProjectiveSystemPoint s2e_projectiveDifferentialQuotientPoint
    s2e_projectiveDifferentialSymmetricPower
  congr 2
  apply Subtype.ext
  change s2e_divisorMultiset (residualProjectiveDivisor hE y W (Projectivization.map F hF z)) =
    s2e_divisorMultiset (s2e_projectiveDifferentialDivisor hE w y z)
  rw [residualProjectiveDivisor_map_paired hE w y W F hF hFg z]

#print axioms residualProjectiveSystemPoint_map_paired

end HodgeLean.Foundations.Program.G32Native
