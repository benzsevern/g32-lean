import HodgeLean.Foundations.Abdulali.TypeIIICentralizer

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct Quaternion
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Program.TypeIIIPaper

namespace HodgeLean.Foundations.Abdulali

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]

local instance : Module.Finite ℚ (HQ A 1) :=
  (torusCohomology_cupProductOf A).finite

variable
  (W : letI := (torusCohomology_cupProductOf A).finite
    HodgeBlocks.WeilAction
      (abelianVarietyCohomologyOf (finiteBetti_abelian A)
        (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
        (torusCohomology_cupProductOf A)).weight1 3)
  (pol : HQ A 2)
  (hM : IsMemberOfM (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
    (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W pol)


/-- The normal form retains the exact two distinguished Eisenstein
eigenspaces, without reselecting a quadratic action or its eigenspaces.
In the normal form the matrix `a ⟨0,1,0,0⟩` is `diag(s,-s)`; its negative
appears because the covariant quaternion action uses conjugation.
Source: Abdulali, Annals of Mathematics 155 (2002), §3.2 and §4;
van Geemen–Verra, Quaternionic Pryms and Hodge Classes, §4.6. -/
theorem typeIII_selected_eigenspaces (P : GeneralPELMember A W pol hM)
    (a : ℍ[ℂ, -3, 0, (P.b : ℂ)] ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ)
    (e : ((Fin 2 → ℂ) ⊗[ℂ] (Fin 6 → ℂ)) ≃ₗ[ℂ] (ℂ ⊗[ℚ] HQ A 1))
    (he : ∀ q z, quaternionComplexAction P.b (typeIIIQuaternionAction A W pol hM P) q (e z) =
      e ((Matrix.toLin' (a q)).rTensor (Fin 6 → ℂ) z))
    (z : (Fin 2 → ℂ) ⊗[ℂ] (Fin 6 → ℂ)) :
    (e z ∈ W.Vs ↔
      -((Matrix.toLin' (a ⟨0, 1, 0, 0⟩)).rTensor (Fin 6 → ℂ) z) =
        HodgeBlocks.WeilAction.omegaC 3 • z) ∧
    (e z ∈ W.Vsbar ↔
      -((Matrix.toLin' (a ⟨0, 1, 0, 0⟩)).rTensor (Fin 6 → ℂ) z) =
        -HodgeBlocks.WeilAction.omegaC 3 • z) := by
  have hinc : quaternionRationalInclusion P.b (⟨0, 1, 0, 0⟩ : ℍ[ℚ, -3, 0, P.b]) =
      (⟨0, 1, 0, 0⟩ : ℍ[ℂ, -3, 0, (P.b : ℂ)]) := by
    ext <;> simp [quaternionRationalInclusion]
  have hh := he (quaternionRationalInclusion P.b ⟨0, 1, 0, 0⟩) z
  rw [quaternionComplexAction_rational, typeIIIQuaternionAction_eisenstein,
    LinearMap.baseChange_neg, LinearMap.neg_apply, hinc] at hh
  have hw : W.J.baseChange ℂ (e z) =
      e (-((Matrix.toLin' (a ⟨0, 1, 0, 0⟩)).rTensor (Fin 6 → ℂ) z)) := by
    have h := congrArg Neg.neg hh
    simpa only [neg_neg, ← map_neg] using h
  constructor
  · rw [HodgeBlocks.WeilAction.Vs, Module.End.mem_eigenspace_iff]
    change W.J.baseChange ℂ (e z) = HodgeBlocks.WeilAction.omegaC 3 • e z ↔ _
    rw [hw, ← map_smul, e.injective.eq_iff]
  · rw [HodgeBlocks.WeilAction.Vsbar, Module.End.mem_eigenspace_iff]
    change W.J.baseChange ℂ (e z) = -HodgeBlocks.WeilAction.omegaC 3 • e z ↔ _
    rw [hw, ← map_smul, e.injective.eq_iff]

end HodgeLean.Foundations.Abdulali
