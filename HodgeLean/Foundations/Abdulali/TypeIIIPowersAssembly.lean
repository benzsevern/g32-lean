import HodgeLean.Foundations.Abdulali.SplitPowerQuadratics
import HodgeLean.Foundations.Abdulali.SplitPowerVolumes
import HodgeLean.Foundations.Abdulali.OrthogonalTensorAlgebraicity
import HodgeLean.Foundations.Abdulali.PowerDegreeBounds

noncomputable section
set_option maxHeartbeats 200000
set_option Elab.async false
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct Quaternion
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Program.TypeIIIPaper
namespace HodgeLean.Foundations.Abdulali
open HodgeLean.Foundations.WeilPower HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf algebraicCycleClassSpan

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
local instance : Module.Finite ℚ (HQ A 1) := (torusCohomology_cupProductOf A).finite
variable
  (W : letI := (torusCohomology_cupProductOf A).finite
    HodgeBlocks.WeilAction
      (abelianVarietyCohomologyOf (finiteBetti_abelian A)
        (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
        (torusCohomology_cupProductOf A)).weight1 3)
  (pol : HQ A 2)
  (hM : IsMemberOfM (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
    (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W pol)
/-- The type-III powers implication for arbitrary geometric biproduct powers,
retaining the selected rational quaternionic degree-six space.
Source: Abdulali, Annals of Mathematics 155 (2002), Remark 4.2 and proof of
Theorem 4.1, p. 924; Weyl, The Classical Groups, II.9 and II.17. -/
theorem typeIII_powers_assembly :
    ∀ (P : GeneralPELMember A W pol hM),
      (∀ x : HQ A (2*3), x ∈ quaternionicSpan A (weilSix A W pol hM) →
        x ∈ algebraicCycleClassSpan A 3) →
      ∀ (Y : Over (Spec ↧ℂ)) [GrpObj Y] [IsCommMonObj Y]
        [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
        (r : ℕ), 0 < r → AbelianPowerData A Y r →
        ∀ p : ℕ, Hdg^p(Y; ℚ) ≤ algebraicCycleClassSpan Y p := by
  intro P hQ Y _ _ _ _ _ r hr power p
  by_cases hp : p = 0
  · subst p
    exact power_hodge_degree_zero (Y := Y)
  by_cases hd : r * TopologicalSpace.dim A.left < p
  · exact power_hodge_above_dimension A power p hd
  obtain ⟨s, a, e, B, hs, ha, hI, hsym, hB, hJ, he, hform, hc⟩ :=
    typeIII_skew_centralizer_normal_form A W pol hM P
  apply (Submodule.baseChange_le_iff (A := ℂ)).mp
  intro z hz
  let E := (exteriorEquiv (2*p) (splitPowerH1Equiv power e)).trans (complexCupEquiv Y (2*p))
  let w := E.symm z
  have hEz : complexCupEquiv Y (2*p)
      (exteriorPower.map (2*p) (splitPowerH1Equiv power e).toLinearMap w) = z :=
    E.apply_symm_apply z
  have hw : w ∈ (m1b_fixed (m1b_copies (r*2) ''
      {u ∈ m1b_isometries B | u.det = 1}) (2*p)).map
        (InvariantsExterior.wedgeQuotient (2*p)) := by
    apply (split_power_hodge_iff A e B hB hsym hc power p w).mp
    rw [hEz]
    exact hz
  obtain ⟨t, ht, htw⟩ := Submodule.mem_map.mp hw
  have halg := orthogonal_tensor_images_algebraic Y (r*2) B hB hsym.eq
    (splitPowerH1Equiv power e).toLinearMap
    (split_power_quadratics_algebraic A e B hB hsym hc power)
    (split_power_volumes_algebraic A W pol hM P hQ s hs a hI e he power) p t ht
  rw [htw, hEz] at halg
  exact halg

end HodgeLean.Foundations.Abdulali
