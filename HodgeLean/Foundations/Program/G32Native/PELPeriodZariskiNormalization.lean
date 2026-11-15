import HodgeLean.Foundations.Program.G32Native.PELPeriodGeneratedSubgroup
import HodgeLean.Foundations.HodgeGroupAlgebraicDescent

noncomputable section
set_option maxHeartbeats 400000
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program.GeneralTypeIII

/-- The real identity component normalizes the abstract period-generated
subgroup. The topology here is the ordinary real matrix topology. -/
theorem pelRealIsometries_mem_period_normalizer (R : PELSplitReference)
    (g : pelRealIsometries R) (hg : g ∈ connectedComponent (1 : pelRealIsometries R)) :
    Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) g.val ∈
      Subgroup.normalizer (pelPeriodGeneratedSubgroup R : Set (Matrix.GeneralLinearGroup (Fin 12) ℂ)) := by
  rw [Subgroup.mem_normalizer_iff'']
  intro x
  constructor
  · exact pelPeriodGeneratedSubgroup_conjugate R g hg x
  · intro hx
    have hi : g⁻¹ ∈ connectedComponent (1 : pelRealIsometries R) := by
      simpa only [inv_one] using continuous_inv.mapsTo_connectedComponent
        (1 : pelRealIsometries R) hg
    have hh := pelPeriodGeneratedSubgroup_conjugate R g⁻¹ hi _ hx
    simpa only [Subgroup.coe_inv, map_inv, inv_inv, mul_assoc,
      mul_inv_cancel_left, inv_mul_cancel_left, mul_inv_cancel, mul_one] using hh

/-- Real identity-component conjugation preserves the complex Zariski hull
of the period-generated subgroup. Complex Zariski closure is explicit, so
it does not alter the ordinary real topology in the hypothesis.
Source: Borel, Linear Algebraic Groups, second edition, §§1.3, 2.2. -/
theorem pelPeriodZariskiHull_conjugate (R : PELSplitReference)
    (g : pelRealIsometries R) (hg : g ∈ connectedComponent (1 : pelRealIsometries R))
    (x : Matrix.GeneralLinearGroup (Fin 12) ℂ)
    (hx : x ∈ @closure _ (g1_zariski ℂ 12)
      (pelPeriodGeneratedSubgroup R : Set (Matrix.GeneralLinearGroup (Fin 12) ℂ))) :
    (Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) g.val)⁻¹ * x *
      Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) g.val ∈
      @closure _ (g1_zariski ℂ 12)
        (pelPeriodGeneratedSubgroup R : Set (Matrix.GeneralLinearGroup (Fin 12) ℂ)) := by
  letI : TopologicalSpace (Matrix.GeneralLinearGroup (Fin 12) ℂ) := g1_zariski ℂ 12
  let c := Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) g.val
  have hc : Continuous (fun y : Matrix.GeneralLinearGroup (Fin 12) ℂ => c⁻¹ * y * c) :=
    (g2h_continuous_mul_right c).comp (g1_continuous_mul_left c⁻¹)
  have hh := image_closure_subset_closure_image hc ⟨x, hx, rfl⟩
  apply closure_mono _ hh
  rintro _ ⟨y, hy, rfl⟩
  exact pelPeriodGeneratedSubgroup_conjugate R g hg y hy

#print axioms pelRealIsometries_mem_period_normalizer
#print axioms pelPeriodZariskiHull_conjugate
end HodgeLean.Foundations.Program.GeneralTypeIII
