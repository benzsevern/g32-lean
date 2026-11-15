import HodgeLean.Foundations.Abdulali.PowerCyclePullback
import HodgeLean.Foundations.Abdulali.QuaternionicDeterminantPolarization

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

/-- The actual sum-pullback span of an algebraic subspace remains algebraic on
arbitrary power data. The endomorphism algebra need not be commutative.
Source: Fulton, Intersection Theory, §1.7; Mumford, Abelian Varieties, §19. -/
theorem typeIII_power_image_span_algebraic (P : GeneralPELMember A W pol hM)
    (power : AbelianPowerData A Y r) (p : ℕ) (U : Submodule ℚ (HQ A (2*p)))
    (hU : U ≤ algebraicCycleClassSpan A p) :
    (⨆ f : Fin r → AbelianEnd A, U.map (homPullback (power.sumMap f) (2*p))) ≤
      algebraicCycleClassSpan Y p := by
  apply iSup_le
  intro f
  exact (Submodule.map_mono hU).trans (typeIII_sumMap_algebraic A W pol hM P power f p)

/-- Alternating volume generators give algebraic classes on every specified
power when the selected rational quaternionic space is algebraic.
Source: Abdulali, Annals of Mathematics 155 (2002), Remark 4.2;
van Geemen–Verra, Quaternionic Pryms and Hodge Classes, §4.6, Proposition 4.7. -/
theorem typeIII_power_volume_algebraic (P : GeneralPELMember A W pol hM)
    (hQ : ∀ x : HQ A (2*3), x ∈ quaternionicSpan A (weilSix A W pol hM) →
      x ∈ algebraicCycleClassSpan A 3)
    (s : ℂ) (hs : s ^ 2 = -3)
    (a : ℍ[ℂ, -3, 0, (P.b : ℂ)] ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ)
    (hI : a ⟨0, 1, 0, 0⟩ = !![s, 0; 0, -s])
    (e : ((Fin 2 → ℂ) ⊗[ℂ] (Fin 6 → ℂ)) ≃ₗ[ℂ] (ℂ ⊗[ℚ] HQ A 1))
    (he : ∀ q z, quaternionComplexAction P.b (typeIIIQuaternionAction A W pol hM P) q (e z) =
      e ((Matrix.toLin' (a q)).rTensor (Fin 6 → ℂ) z))
    (power : AbelianPowerData A Y r) (labels : Fin 6 → (Fin (r * 2) → ℂ)) :
    complexCupEquiv Y 6
      (∑ σ : Equiv.Perm (Fin 6), Equiv.Perm.sign σ •
        exteriorPower.ιMulti ℂ 6 (fun i =>
          powerMultiplicityMap power e (Pi.basisFun ℂ (Fin 6) (σ i)) (labels i))) ∈
      (algebraicCycleClassSpan Y 3).baseChange ℂ := by
  apply Submodule.baseChange_mono ℂ
    (typeIII_power_image_span_algebraic A W pol hM P power 3 _ hQ)
  exact quaternionic_determinant_polarization A W pol hM P s hs a hI e he power labels



#print axioms typeIII_power_image_span_algebraic
#print axioms typeIII_power_volume_algebraic
end HodgeLean.Foundations.Abdulali
