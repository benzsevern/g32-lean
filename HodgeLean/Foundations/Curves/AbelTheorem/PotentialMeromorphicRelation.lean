import HodgeLean.Foundations.Curves.AbelTheorem.ComplexPotentialPairing
import HodgeLean.Foundations.Curves.AbelTheorem.ComplexWeightedResidueStokes
import HodgeLean.Foundations.Curves.AbelTheorem.ResiduePoleSupport
import HodgeLean.Foundations.Curves.AbelTheorem.HolomorphicProjectedForms

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold MeasureTheory
open scoped Topology ContDiff BigOperators
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C]
  [MeasurableSpace E] [BorelSpace E]
attribute [local instance] b3Forms_isManifold_real

/-- Source: Farkas–Kra, Riemann Surfaces, III.6, meromorphic reciprocity by a dual potential. -/
theorem potential_meromorphic_relation (h : Module.finrank ℂ E = 1)
    (D : C →₀ ℤ) (w : b4c_MeroForm E C h)
    (hr : ∀ x, b4c_res (hE := h) w x = (D x : ℂ))
    (ho : ∀ x, (-1 : WithTop ℤ) ≤ meromorphicOrderAt (HurwitzPrymRR_loc h w x) 0)
    (ha : ∀ x, x ∉ D.support → AnalyticAt ℂ (HurwitzPrymRR_loc h w x) 0)
    {ι : Type} [Fintype ι] (η : ι → C → E [⋀^Fin 1]→L[ℝ] ℝ)
    (hη : ∀ s, b3Forms_IsSmooth (η s))
    (hzero : ∀ s x, x ∈ D.support → η s =ᶠ[𝓝 x] 0)
    (c : ι → ℂ) (θ : b3_HolForm E C) (G : C → ℂ)
    (hG : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ G)
    (hre : b3Forms_d (b3Forms_fun (E := E) (fun x => (G x).re)) =
      b3Forms_reForm θ + ∑ s, (c s).re • η s)
    (him : b3Forms_d (b3Forms_fun (E := E) (fun x => (G x).im)) =
      b3Forms_imForm θ + ∑ s, (c s).im • η s)
    (hhol : ∀ x ∈ D.support, ∀ᶠ y in 𝓝 x, AnalyticAt ℂ (centeredScalar h G y) 0)
    (v : ι → ℂ)
    (hpair : ∀ (P : ℂ →L[ℝ] ℝ) s, b3Forms_integral (b4c_residue_basis h)
      (b3Forms_wedgeForm (b4c_residue_realForm h (b4c_residue_normalizedForm h w) P) (η s)) = P (v s)) :
    ∑ s, c s * v s = (2 * Real.pi * Complex.I) * ∑ x ∈ D.support, (D x : ℂ) * G x := by
  classical
  have hpoles := pole_set_eq_residue_divisor_support h D w hr ha
  have he (P : ℂ →L[ℝ] ℝ) : P (∑ s, c s * v s) =
      P ((2 * Real.pi * Complex.I) * ∑ x ∈ D.support, (D x : ℂ) * G x) := by
    obtain ⟨hs, hv⟩ := complex_potential_dual_pairing h D w ha η hη hzero c θ.val θ.property.2 G
      (by rwa [(holomorphic_projected_forms h θ).1])
      (by rwa [(holomorphic_projected_forms h θ).2]) v hpair P
    have hw := complex_weighted_residue_stokes h w ho G hG
      (fun x hx => hhol x (hpoles ▸ (b4c_residue_poles_finite h w).mem_toFinset.mpr hx)) P hs
    rw [hv, hpoles] at hw
    apply neg_inj.mp
    rw [hw]
    congr 1
    rw [Finset.mul_sum, _root_.map_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [hr]
    congr 1
    ring
  exact Complex.ext (he Complex.reCLM) (he Complex.imCLM)

end HodgeLean.Foundations.Curves.AbelTheorem
