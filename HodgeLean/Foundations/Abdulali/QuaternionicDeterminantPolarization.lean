import HodgeLean.Foundations.Abdulali.DeterminantPolarization
import HodgeLean.Foundations.Abdulali.QuaternionicVolumeComparison

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct Quaternion
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Program.TypeIIIPaper
namespace HodgeLean.Foundations.Abdulali

variable {A Y : Over (Spec ↧ℂ)} [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
  [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
  {r : ℕ}

/-- Insert a multiplicity vector in the fixed split model on the specified
power. Coordinates use `Fin (r*2)`, with the pair `(copy, quaternion row)`.
Source: Abdulali, Annals of Mathematics 155 (2002), §3 and Remark 4.2;
van Geemen–Verra, Quaternionic Pryms and Hodge Classes, §4.6. -/
def powerMultiplicityMap (power : AbelianPowerData A Y r)
    (e : ((Fin 2 → ℂ) ⊗[ℂ] (Fin 6 → ℂ)) ≃ₗ[ℂ] (ℂ ⊗[ℚ] HQ A 1)) :
    (Fin 6 → ℂ) →ₗ[ℂ] (Fin (r * 2) → ℂ) →ₗ[ℂ] (ℂ ⊗[ℚ] HQ Y 1) :=
  LinearMap.mk₂ ℂ (fun v b => ∑ i : Fin r,
    (homPullback (power.proj i) 1).baseChange ℂ
      (e ((fun k => b (finProdFinEquiv (i, k))) ⊗ₜ[ℂ] v)))
    (by intros; simp only [TensorProduct.tmul_add, map_add, Finset.sum_add_distrib])
    (by intros; simp only [TensorProduct.tmul_smul, map_smul, Finset.smul_sum])
    (by
      intro v x y
      change (∑ i : Fin r, (homPullback (power.proj i) 1).baseChange ℂ
        (e (((fun k => x (finProdFinEquiv (i, k))) +
          (fun k => y (finProdFinEquiv (i, k)))) ⊗ₜ[ℂ] v))) = _
      simp only [TensorProduct.add_tmul, map_add, Finset.sum_add_distrib])
    (by
      intro c v x
      change (∑ i : Fin r, (homPullback (power.proj i) 1).baseChange ℂ
        (e ((c • (fun k => x (finProdFinEquiv (i, k)) )) ⊗ₜ[ℂ] v))) = _
      simp only [← TensorProduct.smul_tmul', map_smul, Finset.smul_sum])

example (power : AbelianPowerData A Y r)
    (e : ((Fin 2 → ℂ) ⊗[ℂ] (Fin 6 → ℂ)) ≃ₗ[ℂ] (ℂ ⊗[ℚ] HQ A 1))
    (v : Fin 6 → ℂ) (b : Fin (r * 2) → ℂ) :
    powerMultiplicityMap power e v b = ∑ i : Fin r,
      (homPullback (power.proj i) 1).baseChange ℂ
        (e ((fun k => b (finProdFinEquiv (i, k))) ⊗ₜ[ℂ] v)) := rfl

variable (A)
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

/-- Under the fixed identification from the skew-centralizer normal form,
every alternating volume block on arbitrary power data belongs to the complex
span of integral sum-morphism pullbacks of the selected rational quaternionic
space. The six independent multiplicity vectors allow all mixed-copy labels.
Source: Abdulali, Annals of Mathematics 155 (2002), §3 and Remark 4.2;
van Geemen–Verra, Quaternionic Pryms and Hodge Classes, §4.6, Proposition 4.7;
Weyl, The Classical Groups, Chapter II, §9 (polarization). -/
theorem quaternionic_determinant_polarization (P : GeneralPELMember A W pol hM)
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
      (⨆ f : Fin r → AbelianEnd A,
        (quaternionicSpan A (weilSix A W pol hM)).map
          (homPullback (power.sumMap f) 6)).baseChange ℂ := by
  classical
  let j := powerMultiplicityMap power e
  let b := Pi.basisFun ℂ (Fin 6)
  let S := (⨆ f : Fin r → AbelianEnd A,
    (quaternionicSpan A (weilSix A W pol hM)).map
      (homPullback (power.sumMap f) 6)).baseChange ℂ
  have hdiag (x : Fin (r * 2) → ℂ) :
      complexCupEquiv Y 6 (exteriorPower.ιMulti ℂ 6 (fun i => j (b i) x)) ∈ S := by
    let q (i : Fin r) := a.symm !![x (finProdFinEquiv (i, 0)), 0;
      x (finProdFinEquiv (i, 1)), 0]
    let v := exteriorPower.ιMulti ℂ 6 (fun i =>
      e ((Pi.single 0 1 : Fin 2 → ℂ) ⊗ₜ[ℂ] b i))
    have hv := quaternionic_base_volume_aux A W pol hM P s hs a hI e he
    have h := quaternionic_complex_sum_pullback_aux A W pol hM P power 6
      (quaternionicSpan A (weilSix A W pol hM)) q (complexCupEquiv A 6 v) hv
    rw [LinearEquiv.symm_apply_apply, exteriorPower.map_apply_ιMulti] at h
    convert h using 1
    congr 2
    funext k
    simp only [Function.comp_apply, LinearMap.sum_apply, LinearMap.comp_apply, v]
    change j (b k) x = _
    unfold j powerMultiplicityMap
    simp only [LinearMap.mk₂_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [he, LinearMap.rTensor_tmul]
    congr 2
    congr 1
    change (fun k => x (finProdFinEquiv (i, k))) =
      Matrix.toLin' (a (q i)) (Pi.single 0 1)
    rw [show a (q i) = !![x (finProdFinEquiv (i, 0)), 0;
        x (finProdFinEquiv (i, 1)), 0] from a.apply_symm_apply _]
    ext k
    fin_cases k <;> simp [Matrix.toLin'_apply, Matrix.mulVec, Fin.sum_univ_two,
      Pi.single_apply]
  apply (Submodule.span_le.mpr ?_)
    (alternating_volume_map_mem_span_rational_diagonals j b labels
      (complexCupEquiv Y 6).toLinearMap)
  rintro _ ⟨x, rfl⟩
  exact hdiag (fun i => (x i : ℂ))

end HodgeLean.Foundations.Abdulali
