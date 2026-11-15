import HodgeLean.Foundations.Abdulali.PowerVolumeVectors
import HodgeLean.Foundations.Abdulali.TensorExteriorMap
import HodgeLean.Foundations.Abdulali.SpecialOrthogonalGeneration

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

/-- The normalized labelled tensor generators give algebraic volume classes
on the specified geometric power, with their original dimension index.
Source: Weyl, The Classical Groups, II.17; Abdulali, Annals 155 (2002), Remark 4.2. -/
theorem split_power_volumes_algebraic (P : GeneralPELMember A W pol hM)
    (hQ : ∀ x : HQ A (2*3), x ∈ quaternionicSpan A (weilSix A W pol hM) →
      x ∈ algebraicCycleClassSpan A 3)
    (s : ℂ) (hs : s ^ 2 = -3)
    (a : ℍ[ℂ, -3, 0, (P.b : ℂ)] ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ)
    (hI : a ⟨0, 1, 0, 0⟩ = !![s, 0; 0, -s])
    (e : ((Fin 2 → ℂ) ⊗[ℂ] (Fin 6 → ℂ)) ≃ₗ[ℂ] (ℂ ⊗[ℚ] HQ A 1))
    (he : ∀ q z, quaternionComplexAction P.b (typeIIIQuaternionAction A W pol hM P) q (e z) =
      e ((Matrix.toLin' (a q)).rTensor (Fin 6 → ℂ) z))
    (power : AbelianPowerData A Y r)
    (c : Fin (Module.finrank ℂ (Fin 6 → ℂ)) → Fin (r*2)) :
    complexCupEquiv Y (Module.finrank ℂ (Fin 6 → ℂ))
      (exteriorPower.map _ (splitPowerH1Equiv power e).toLinearMap
        (InvariantsExterior.wedgeQuotient _ (labeledVolume (r*2) c))) ∈
      f1575EvenCohomologySpan (algebraicCycleClassSpan Y) (Module.finrank ℂ (Fin 6 → ℂ)) := by
  unfold labeledVolume
  rw [wedgeQuotient_naturality]
  have hmap := LinearMap.congr_fun
    (PiTensorProduct.map_comp
      (f := fun i => LinearMap.single ℂ (fun _ : Fin (r*2) => Fin 6 → ℂ) (c i))
      (g := fun _ => (splitPowerH1Equiv power e).toLinearMap))
    (SchurWeyl.detTensorDual ℂ (Fin 6 → ℂ))
  simp only [LinearMap.comp_apply] at hmap
  rw [← hmap]
  have hm : (fun i => (splitPowerH1Equiv power e).toLinearMap.comp
      (LinearMap.single ℂ (fun _ : Fin (r*2) => Fin 6 → ℂ) (c i))) =
      (fun i => (powerMultiplicityMap power e).flip (Pi.single (c i) 1)) := by
    funext i
    apply LinearMap.ext
    intro u
    exact splitPowerH1Equiv_label power e (c i) u
  rw [hm, SchurWeyl.detTensorDual_eq]
  exact typeIII_power_volume_vectors_algebraic A W pol hM P hQ s hs a hI e he power
    (Module.finrank ℂ (Fin 6 → ℂ)) (by simp)
    (Module.finBasis ℂ (Fin 6 → ℂ)) (fun i => Pi.single (c i) 1)

end HodgeLean.Foundations.Abdulali
