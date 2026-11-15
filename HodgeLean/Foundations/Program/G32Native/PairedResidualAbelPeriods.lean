import HodgeLean.Foundations.Program.G32Native.PairedResidualRegularQuotient
import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.PrincipalPeriods

/-! # Abel periods of the full normalized differential system -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open HodgeLean.Adapters HodgeLean.Foundations.Curves.AbelAdapter
open HodgeLean.Foundations.Curves.AbelAdapter.StageFour
open Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]

/-- Every nonzero normalized member has the same Abel sum after the same marked correction. -/
theorem residual_normalized_divisor_abel_sum_eq
    (hE : Module.finrank ℂ E = 1) (S : Set C)
    (W : Submodule ℂ (TangentBundle 𝓘(ℂ, E) C → ℂ))
    (hW : ∀ q : W, b4c_IsMeroForm hE q.val ∧
      (∀ p ∉ S, AnalyticAt ℂ (HurwitzPrymRR_loc hE q.val p) 0) ∧
      ∀ p ∈ S, ∀ t, q.val ⟨p, t⟩ = 0)
    (u v : W) (hu : u ≠ 0) (hv : v ≠ 0) (p : C) (M : C →₀ ℤ) :
    weightedSum (analyticAbel (C := C) hE p)
        (b4c_divForm (hE := hE) u.val + M) =
      weightedSum (analyticAbel (C := C) hE p)
        (b4c_divForm (hE := hE) v.val + M) := by
  classical
  let U : b4c_MeroForm E C hE := ⟨u.val, (hW u).1⟩
  let V : b4c_MeroForm E C hE := ⟨v.val, (hW v).1⟩
  have hU : (U : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0 := fun h => hu (Subtype.ext h)
  have hV : (V : TangentBundle 𝓘(ℂ, E) C → ℂ) ≠ 0 := fun h => hv (Subtype.ext h)
  have hgU := residual_normalized_form_has_finite_order hE S U hU (hW u).2.1 (hW u).2.2
  have hgV := residual_normalized_form_has_finite_order hE S V hV (hW v).2.1 (hW v).2.2
  let F : b4c_MeroFun E C := ⟨b4c_formRatio (hE := hE) U V,
    b4c_formRatio_isMeroFun_aux hE U V hU hV hgU hgV⟩
  have hf : ∃ x, F x ≠ (0 : ℂ) := by
    by_contra hn
    push_neg at hn
    obtain ⟨q, hq⟩ := hgU
    apply hq
    apply meromorphicOrderAt_eq_top_iff.mpr
    have hh := s2e_constant_formRatio_germ hE U V ⟨q, hq⟩ hgV 0 hn q
    filter_upwards [hh] with z hz
    simpa only [zero_mul] using hz
  have hdiv := b4c_divForm_sub hE U V hU hV hgU hgV
  have hb := analyticPrincipalPeriods (C := C) hE p F hf
  have he : weightedSum (analyticAbel (C := C) hE p) (b4c_divForm (hE := hE) u.val) =
      weightedSum (analyticAbel (C := C) hE p) (b4c_divForm (hE := hE) v.val) := by
    apply sub_eq_zero.mp
    rw [← map_sub]
    rw [hdiv]
    exact hb
  simpa only [map_add] using congrArg
    (fun t => t + weightedSum (analyticAbel (C := C) hE p) M) he

#print axioms residual_normalized_divisor_abel_sum_eq
end HodgeLean.Foundations.Program.G32Native
