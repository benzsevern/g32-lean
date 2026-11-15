import HodgeLean.Foundations.Abdulali.PowerComplexHodge
import HodgeLean.Foundations.Abdulali.QuaternionicDeterminantPolarization

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000
set_option Elab.async false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.WeilPower HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali
attribute [local irreducible] cupProductOf algebraicCycleClassSpan
variable {A Y : Over (Spec ↧ℂ)} [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
  [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
  {r : ℕ}

/-- A coordinate vector retains its actual projection and quaternion row.
Source: biproduct cohomology and split quaternion coordinates, Abdulali, Remark 4.2. -/
theorem splitPowerH1Equiv_single (power : AbelianPowerData A Y r)
    (e : ((Fin 2 → ℂ) ⊗[ℂ] (Fin 6 → ℂ)) ≃ₗ[ℂ] (ℂ ⊗[ℚ] HQ A 1))
    (i : Fin r) (k : Fin 2) (u : Fin 6 → ℂ) :
    splitPowerH1Equiv power e (Pi.single (finProdFinEquiv (i,k)) u) =
      (homPullback (power.proj i) 1).baseChange ℂ
        (e ((Pi.single k 1 : Fin 2 → ℂ) ⊗ₜ[ℂ] u)) := by
  classical
  have hc : splitPowerCoordinates r e
      ((powerBaseChange r).symm
        (e ((Pi.single k 1 : Fin 2 → ℂ) ⊗ₜ[ℂ] u) ⊗ₜ[ℂ] (Pi.single i 1 : Fin r → ℂ))) =
      Pi.single (finProdFinEquiv (i,k)) u := by
    ext j
    obtain ⟨⟨j,l⟩, rfl⟩ := finProdFinEquiv.surjective j
    have hd (a : Fin r) (b : Fin 2) : (finProdFinEquiv (a,b)).divNat = a :=
      congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (a,b))
    have hm (a : Fin r) (b : Fin 2) : (finProdFinEquiv (a,b)).modNat = b :=
      congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (a,b))
    by_cases hj : j = i <;> by_cases hl : l = k <;>
      simp [splitPowerCoordinates, flattenSplitCopies, splitRowCoordinates,
        TensorProduct.piScalarRight, TensorProduct.piScalarRightHom,
        TensorProduct.piScalarRightHomBil, Pi.single_apply, Prod.ext_iff, hd, hm, hj, hl]
  rw [← hc]
  simp only [splitPowerH1Equiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  change power.h1Map.baseChange ℂ _ = _
  rw [powerH1Map_coordinates]
  simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]

/-- The labelled standard injection is the same multiplicity vector used by the
quaternionic determinant polarization theorem.
Source: Abdulali, Annals 155 (2002), Remark 4.2; Weyl polarization. -/
theorem splitPowerH1Equiv_label (power : AbelianPowerData A Y r)
    (e : ((Fin 2 → ℂ) ⊗[ℂ] (Fin 6 → ℂ)) ≃ₗ[ℂ] (ℂ ⊗[ℚ] HQ A 1))
    (j : Fin (r*2)) (u : Fin 6 → ℂ) :
    splitPowerH1Equiv power e (Pi.single j u) =
      powerMultiplicityMap power e u (Pi.single j 1) := by
  classical
  obtain ⟨⟨i,k⟩, rfl⟩ := finProdFinEquiv.surjective j
  rw [splitPowerH1Equiv_single]
  unfold powerMultiplicityMap
  simp only [LinearMap.mk₂_apply]
  rw [Finset.sum_eq_single i]
  · have hrow : (fun l : Fin 2 =>
        (Pi.single (finProdFinEquiv (i,k)) (1 : ℂ) : Fin (r*2) → ℂ)
          (finProdFinEquiv (i,l))) = (Pi.single k 1 : Fin 2 → ℂ) := by
      ext l
      simp [Pi.single_apply, Prod.ext_iff, eq_comm]
    rw [hrow]
  · intro j _ hji
    have hz : (fun l : Fin 2 =>
        (Pi.single (finProdFinEquiv (i,k)) (1 : ℂ) : Fin (r*2) → ℂ)
          (finProdFinEquiv (j,l))) = (0 : Fin 2 → ℂ) := by
      ext l
      simp [Pi.single_apply, Prod.ext_iff, hji, Ne.symm hji]
    rw [hz, TensorProduct.zero_tmul, map_zero, map_zero]
  · simp

end HodgeLean.Foundations.Abdulali
