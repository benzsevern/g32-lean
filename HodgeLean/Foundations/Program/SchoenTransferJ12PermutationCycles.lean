import HodgeLean.Foundations.Program.SchoenSymmetricPowerAction
import HodgeLean.Foundations.Program.CycleFoundationsDefs
import HodgeLean.Foundations.Program.CompensationAssemblyPullback

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 2000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The unsigned geometric permutation average preserves actual algebraic curve-power classes.
Source: Fulton, Intersection Theory, §16.1; Schoen (1988), Remark 1.4. -/
theorem s4_selected_unsigned_average_cycles
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (n k : ℕ) [IsIntegral (g3_power Y n).left]
    [Smooth (g3_power Y n).hom] [IsProjective (g3_power Y n).hom]
    (x : HQ (g3_power Y n) (2 * k)) (hx : x ∈ cfd_cycleSpan (g3_power Y n) k) :
    (Nat.factorial n : ℚ)⁻¹ •
      ∑ σ : Equiv.Perm (Fin n), homPullback (s2_permute Y n σ) (2 * k) x ∈
      cfd_cycleSpan (g3_power Y n) k := by
  classical
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro σ _
  letI : IsIso (s2_permute Y n σ) := (s2_permuteIso Y n σ).isIso_hom
  letI : IsIso (s2_permute Y n σ).left :=
    ((Over.forget (Spec ↧ℂ)).mapIso (s2_permuteIso Y n σ)).isIso_hom
  exact cq_smooth_pullback_span_core (s2_permute Y n σ) k
    (Submodule.mem_map_of_mem hx)

#print axioms s4_selected_unsigned_average_cycles

end HodgeLean.Foundations.Program
