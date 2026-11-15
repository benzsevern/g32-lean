import HodgeLean.Foundations.Curves.AbelTheorem.PrincipalIntegration

noncomputable section
open HodgeLean.Foundations.Program
open HodgeLean.Foundations.Curves.AbelAdapter
open HodgeLean.Foundations.Curves.AbelAdapter.StageFour
open Manifold
open scoped ContDiff BigOperators
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C] [ConnectedSpace C]

/-- Source: Miranda, Algebraic Curves and Riemann Surfaces, VIII.2, base point independence in degree zero. -/
theorem abel_divisor_sum_base_independent (h : Module.finrank ℂ E = 1)
    (p q : C) (D : C →₀ ℤ) (hdeg : b4c_deg D = 0) :
    weightedSum (analyticAbel h q) D = weightedSum (analyticAbel h p) D := by
  have hA := (b3_exists_abelJacobi (E := E) (C := C) h p).choose_spec
  have hreb : b3_IsAbelJacobi E C q (fun x => analyticAbel h p x - analyticAbel h p q) := by
    refine ⟨sub_self _, ?_⟩
    intro γ hγ
    obtain ⟨v, hv, he⟩ := hA.2 γ hγ
    exact ⟨v, hv, (sub_sub_sub_cancel_right _ _ _).trans he⟩
  have ht := b3_abelJacobi_unique h q (analyticAbel h q) _
    (b3_exists_abelJacobi (E := E) (C := C) h q).choose_spec hreb
  rw [ht]
  change (∑ x ∈ D.support, D x • (analyticAbel h p x - analyticAbel h p q)) =
    ∑ x ∈ D.support, D x • analyticAbel h p x
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
  change _ - b4c_deg D • analyticAbel h p q = _
  rw [hdeg, zero_smul, sub_zero]

end HodgeLean.Foundations.Curves.AbelTheorem
