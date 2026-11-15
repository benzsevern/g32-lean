import HodgeLean.Foundations.Abdulali.SplitPowerHodgeInvariants
import HodgeLean.Foundations.Abdulali.SpecialOrthogonalGeneration
import HodgeLean.Foundations.ChowProjective

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

/-- The orthogonal quadratic generators give actual divisor classes on the
specified power through the rational Hodge transport and Lefschetz (1,1).
Source: Lefschetz (1,1), Griffiths–Harris, Chapter 1, §2; Abdulali, §4. -/
theorem split_power_quadratics_algebraic
    (e : ((Fin 2 → ℂ) ⊗[ℂ] (Fin 6 → ℂ)) ≃ₗ[ℂ] (ℂ ⊗[ℚ] HQ A 1))
    (B : LinearMap.BilinForm ℂ (Fin 6 → ℂ)) (hB : B.Nondegenerate) (hs : B.IsSymm)
    (hc : ∀ X : Module.End ℂ (ℂ ⊗[ℚ] HQ A 1),
      X ∈ complexSpan (hodgeLieAlgebra (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal).toSubmodule ↔
        ∃! T : Module.End ℂ (Fin 6 → ℂ),
          (∀ x y, B (T x) y + B x (T y) = 0) ∧ e.symm.conj X = T.lTensor (Fin 2 → ℂ))
    (power : AbelianPowerData A Y r)
    (t : ⨂[ℂ]^2 (Fin (r*2) → Fin 6 → ℂ))
    (ht : t ∈ Submodule.span ℂ (Set.range (labeledInverseForm B hB hs.eq (r*2)))) :
    complexCupEquiv Y 2 (exteriorPower.map 2 (splitPowerH1Equiv power e).toLinearMap
      (InvariantsExterior.wedgeQuotient 2 t)) ∈ (algebraicCycleClassSpan Y 1).baseChange ℂ := by
  have hO : t ∈ m1b_fixed (m1b_copies (r*2) '' m1b_isometries B) 2 := by
    rw [orthogonal_quadratics_eq_inverseForm_span B hB hs.eq (r*2)]
    exact ht
  have hSO : t ∈ m1b_fixed (m1b_copies (r*2) ''
      {u ∈ m1b_isometries B | u.det = 1}) 2 := by
    simp only [m1b_fixed, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at hO ⊢
    rintro _ ⟨u, hu, rfl⟩
    exact hO _ ⟨u, hu.1, rfl⟩
  have hHdg : complexCupEquiv Y 2 (exteriorPower.map 2
      (splitPowerH1Equiv power e).toLinearMap (InvariantsExterior.wedgeQuotient 2 t)) ∈
      (Hdg^1(Y; ℚ)).baseChange ℂ := by
    exact (split_power_hodge_iff A e B hB hs hc power 1
      (InvariantsExterior.wedgeQuotient 2 t)).mpr (Submodule.mem_map.mpr ⟨t, hSO, rfl⟩)
  exact (Submodule.baseChange_mono ℂ (chowG_lefschetzOneOne_abelian Y)) hHdg


end HodgeLean.Foundations.Abdulali
