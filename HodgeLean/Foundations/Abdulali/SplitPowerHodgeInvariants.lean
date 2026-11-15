import HodgeLean.Foundations.Abdulali.PowerComplexHodge
import HodgeLean.Foundations.Abdulali.SplitExteriorInvariants
import HodgeLean.Foundations.Abdulali.TypeIIICentralizer

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct Quaternion
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.WeilPower HodgeLean.Foundations.Program
open HodgeLean.Foundations.Program.TypeIIIPaper
namespace HodgeLean.Foundations.Abdulali
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
variable {Y : Over (Spec ↧ℂ)} [GrpObj Y] [IsCommMonObj Y]
  [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom] {r : ℕ}

/-- The actual class of a split exterior vector is Hodge exactly when the vector
is an alternating image of an SO-fixed tensor.
Source: Abdulali, Annals 155 (2002), §4 and Remark 4.2; biproduct Hodge transport. -/
theorem split_power_hodge_iff
    (e : ((Fin 2 → ℂ) ⊗[ℂ] (Fin 6 → ℂ)) ≃ₗ[ℂ] (ℂ ⊗[ℚ] HQ A 1))
    (B : LinearMap.BilinForm ℂ (Fin 6 → ℂ)) (hB : B.Nondegenerate) (hs : B.IsSymm)
    (hc : ∀ X : Module.End ℂ (ℂ ⊗[ℚ] HQ A 1),
      X ∈ complexSpan (hodgeLieAlgebra (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal).toSubmodule ↔
        ∃! T : Module.End ℂ (Fin 6 → ℂ),
          (∀ x y, B (T x) y + B x (T y) = 0) ∧ e.symm.conj X = T.lTensor (Fin 2 → ℂ))
    (power : AbelianPowerData A Y r) (p : ℕ)
    (w : ⋀[ℂ]^(2*p) (Fin (r*2) → Fin 6 → ℂ)) :
    complexCupEquiv Y (2*p) (exteriorPower.map (2*p)
      (splitPowerH1Equiv power e).toLinearMap w) ∈ (Hdg^p(Y; ℚ)).baseChange ℂ ↔
    w ∈ (m1b_fixed (m1b_copies (r*2) ''
      {u ∈ m1b_isometries B | u.det = 1}) (2*p)).map (InvariantsExterior.wedgeQuotient (2*p)) := by
  let E := exteriorEquiv (2*p) (splitPowerCoordinates r e)
  have hm : exteriorPower.map (2*p) (power.h1Map.baseChange ℂ) (E.symm w) =
      exteriorPower.map (2*p) (splitPowerH1Equiv power e).toLinearMap w := by
    rw [f1575_exteriorEquiv_symm, ← LinearMap.comp_apply, ← exteriorPower.map_comp]
    rfl
  rw [← hm, power_complex_hodge_mem]
  have h := split_exterior_hodge_invariants
    (abelianWeightOneHodgeStructure A).H (abelianWeightOneHodgeStructure A).isInternal
    e B hB hs hc r (2*p) (E.symm w)
  simpa only [E, LinearEquiv.apply_symm_apply] using h

end HodgeLean.Foundations.Abdulali
