import HodgeLean.Foundations.Abdulali.PowerVolumeAlgebraicity
import HodgeLean.Foundations.Abdulali.SplitPowerProjection
import HodgeLean.Foundations.Abdulali.TensorProductAlgebraicity

noncomputable section
set_option maxHeartbeats 200000
set_option Elab.async false
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct Quaternion
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Program.TypeIIIPaper
namespace HodgeLean.Foundations.Abdulali

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

/-- Replacing the standard ordered volume frame by any six vectors only
multiplies its alternating image by a determinant. The degree is retained for
use with the normalized tensor's dimension index.
Source: Weyl, The Classical Groups, II.9; Abdulali, Remark 4.2. -/
theorem typeIII_power_volume_vectors_algebraic (P : GeneralPELMember A W pol hM)
    (hQ : ∀ x : HQ A (2*3), x ∈ quaternionicSpan A (weilSix A W pol hM) →
      x ∈ algebraicCycleClassSpan A 3)
    (s : ℂ) (hs : s ^ 2 = -3)
    (a : ℍ[ℂ, -3, 0, (P.b : ℂ)] ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ)
    (hI : a ⟨0, 1, 0, 0⟩ = !![s, 0; 0, -s])
    (e : ((Fin 2 → ℂ) ⊗[ℂ] (Fin 6 → ℂ)) ≃ₗ[ℂ] (ℂ ⊗[ℚ] HQ A 1))
    (he : ∀ q z, quaternionComplexAction P.b (typeIIIQuaternionAction A W pol hM P) q (e z) =
      e ((Matrix.toLin' (a q)).rTensor (Fin 6 → ℂ) z))
    (power : AbelianPowerData A Y r) (n : ℕ) (hn : n = 6)
    (v : Fin n → (Fin 6 → ℂ)) (labels : Fin n → (Fin (r*2) → ℂ)) :
    complexCupEquiv Y n
      (InvariantsExterior.wedgeQuotient n
        (PiTensorProduct.map (fun i => (powerMultiplicityMap power e).flip (labels i))
          (SchurWeyl.antisymTensor ℂ (Fin 6 → ℂ) (Fin n) v))) ∈
      f1575EvenCohomologySpan (algebraicCycleClassSpan Y) n := by
  subst n
  erw [f1575EvenCohomologySpan_even (algebraicCycleClassSpan Y) 3]
  let L := (complexCupEquiv Y 6).toLinearMap.comp
    ((InvariantsExterior.wedgeQuotient 6).comp
      (PiTensorProduct.map (fun i => (powerMultiplicityMap power e).flip (labels i))))
  have hv : L (SchurWeyl.antisymTensor ℂ (Fin 6 → ℂ) (Fin 6) v) =
      (Pi.basisFun ℂ (Fin 6)).det v •
        L (SchurWeyl.antisymTensor ℂ (Fin 6 → ℂ) (Fin 6) (Pi.basisFun ℂ (Fin 6))) := by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro ell
    have h := congrArg (fun F => F v)
      ((ell.compAlternatingMap
        (L.compAlternatingMap (SchurWeyl.antisymTensor ℂ (Fin 6 → ℂ) (Fin 6)))).eq_smul_basis_det
          (Pi.basisFun ℂ (Fin 6)))
    simp only [LinearMap.compAlternatingMap_apply, AlternatingMap.smul_apply,
      smul_eq_mul] at h
    rw [map_sub, map_smul, h, smul_eq_mul, mul_comm, sub_self]
  dsimp only [L, LinearMap.comp_apply, LinearEquiv.coe_coe] at hv
  rw [hv]
  apply Submodule.smul_mem
  rw [wedge_labelled_antisymTensor]
  exact typeIII_power_volume_algebraic A W pol hM P hQ s hs a hI e he power labels

end HodgeLean.Foundations.Abdulali
