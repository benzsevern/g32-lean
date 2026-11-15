import HodgeLean.Foundations.Program.MilneDivisorsPowers
import HodgeLean.Foundations.Program.MilneExteriorPresentation
import HodgeLean.Foundations.Program.G32ContractionComplexExterior

noncomputable section
set_option maxHeartbeats 200000
open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations

namespace HodgeLean.Foundations.Program

def m2_powerExteriorEquiv {V : Type*} [AddCommGroup V] [Module ℚ V] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ V) (r n : ℕ) :
    ℂ ⊗[ℚ] (⋀[ℚ]^n (Fin r → V)) ≃ₗ[ℂ] ⋀[ℂ]^n (Fin r → ℂ ⊗[ℚ] V) :=
  (((m2_piBasis b r).exteriorPower n).baseChange ℂ).equiv
    ((m2_piBasis (b.baseChange ℂ) r).exteriorPower n) (Equiv.refl _)

theorem m2_powerExteriorEquiv_basis {V : Type*} [AddCommGroup V] [Module ℚ V] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ V) (r n : ℕ) (s : Set.powersetCard (Fin (d * r)) n) :
    m2_powerExteriorEquiv b r n ((1 : ℂ) ⊗ₜ[ℚ] (m2_piBasis b r).exteriorPower n s) =
      (m2_piBasis (b.baseChange ℂ) r).exteriorPower n s := by
  rw [← Module.Basis.baseChange_apply ℂ ((m2_piBasis b r).exteriorPower n) s]
  exact Module.Basis.equiv_apply _ _ _ _

theorem m2_piRight_basis {V : Type*} [AddCommGroup V] [Module ℚ V] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ V) (r : ℕ) (j : Fin (d * r)) :
    TensorProduct.piRight ℚ ℂ ℂ (fun _ : Fin r => V)
      ((1 : ℂ) ⊗ₜ[ℚ] m2_piBasis b r j) = m2_piBasis (b.baseChange ℂ) r j := by
  classical
  rw [m2_piBasis_apply, m2_piBasis_apply]
  simp only [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
  funext i
  by_cases h : (finProdFinEquiv.symm j).2 = i
  · subst i
    simp only [Pi.single_eq_same, Module.Basis.baseChange_apply]
  · simp only [Pi.single_eq_of_ne (Ne.symm h), TensorProduct.tmul_zero]


theorem m2_powerExteriorEquiv_eq {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] {d : ℕ} (b : Module.Basis (Fin d) ℚ V) (r n : ℕ) :
    (m2_powerExteriorEquiv b r n).toLinearMap =
      exteriorPower.map n (TensorProduct.piRight ℚ ℂ ℂ (fun _ : Fin r => V)).toLinearMap ∘ₗ
        (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv n).toLinearMap := by
  apply (((m2_piBasis b r).exteriorPower n).baseChange ℂ).ext
  intro s
  rw [Module.Basis.baseChange_apply]
  simp only [LinearEquiv.coe_coe]
  rw [m2_powerExteriorEquiv_basis]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv_tmul,
    exteriorPower.basis_apply, exteriorPower.ιMulti_family, HodgeBlocks.complexifyWedge_ιMulti,
    exteriorPower.map_apply_ιMulti]
  congr 1
  funext i
  exact (m2_piRight_basis b r _).symm


def m2_powerOneQ (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (r : ℕ) :
    (Fin r → HQ J 1) →ₗ[ℚ] HQ (g3_power J r) 1 :=
  ∑ i, homPullback (g3_proj J r i) 1 ∘ₗ LinearMap.proj i

theorem m2_powerOne_baseChange (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (r : ℕ) :
    g32p_powerOne J r ∘ₗ
      (TensorProduct.piRight ℚ ℂ ℂ (fun _ : Fin r => HQ J 1)).toLinearMap =
        (m2_powerOneQ J r).baseChange ℂ := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro c v
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.piRight_apply,
    TensorProduct.piRightHom_tmul, g32p_powerOne, m2_powerOneQ,
    LinearMap.sum_apply, LinearMap.proj_apply, LinearMap.baseChange_tmul,
    TensorProduct.tmul_sum]

def m2_powerCupQ (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (r n : ℕ) :
    (⋀[ℚ]^n (Fin r → HQ J 1)) →ₗ[ℚ] HQ (g3_power J r) n :=
  (cupProductOf (g3_power J r)).cupWedgeMap n ∘ₗ exteriorPower.map n (m2_powerOneQ J r)


theorem m2_powerClass_baseChange (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    (b : Module.Basis (Fin (Module.finrank ℚ (HQ J 1))) ℚ (HQ J 1)) (r n : ℕ) :
    g32p_powerClass J r n ∘ₗ (m2_powerExteriorEquiv b r n).toLinearMap =
      (m2_powerCupQ J r n).baseChange ℂ := by
  letI := (torusCohomology_cupProductOf J).finite
  letI := (torusCohomology_cupProductOf (g3_power J r)).finite
  rw [m2_powerExteriorEquiv_eq]
  simp only [g32p_powerClass, m2_powerCupQ, LinearMap.baseChange_comp,
    LinearMap.comp_assoc]
  have he : exteriorPower.map n (g32p_powerOne J r) ∘ₗ
      exteriorPower.map n (TensorProduct.piRight ℚ ℂ ℂ (fun _ : Fin r => HQ J 1)).toLinearMap =
        exteriorPower.map n ((m2_powerOneQ J r).baseChange ℂ) := by
    rw [← exteriorPower.map_comp, m2_powerOne_baseChange]
  rw [← LinearMap.comp_assoc
    (HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv
      (V := Fin r → HQ J 1) n).toLinearMap
    (exteriorPower.map n (TensorProduct.piRight ℚ ℂ ℂ (fun _ : Fin r => HQ J 1)).toLinearMap)
    (exteriorPower.map n (g32p_powerOne J r)), he]
  have hn := g32c_exterior_baseChange_natural n (m2_powerOneQ J r)
  rw [← hn]
  simp only [← LinearMap.comp_assoc, LinearEquiv.symm_comp, LinearMap.id_comp]


theorem m2_powerExteriorEquiv_intertwines {V : Type*} [AddCommGroup V] [Module ℚ V]
    {d : ℕ} (b : Module.Basis (Fin d) ℚ V) (r n : ℕ)
    (u : Module.End ℂ (ℂ ⊗[ℚ] V)) :
    exteriorPower.map n (m2_diagonalEnd r u) ∘ₗ (m2_powerExteriorEquiv b r n).toLinearMap =
      (m2_powerExteriorEquiv b r n).toLinearMap ∘ₗ
        Matrix.toLin (((m2_piBasis b r).exteriorPower n).baseChange ℂ)
          (((m2_piBasis b r).exteriorPower n).baseChange ℂ)
          (m2_exteriorMatrix d r n (LinearMap.toMatrix (b.baseChange ℂ) (b.baseChange ℂ) u)) := by
  have h := m2_basisEquiv_intertwines
    (((m2_piBasis b r).exteriorPower n).baseChange ℂ)
    ((m2_piBasis (b.baseChange ℂ) r).exteriorPower n)
    (LinearMap.toMatrix ((m2_piBasis (b.baseChange ℂ) r).exteriorPower n)
      ((m2_piBasis (b.baseChange ℂ) r).exteriorPower n)
        (exteriorPower.map n (m2_diagonalEnd r u)))
  rw [Matrix.toLin_toMatrix, m2_exteriorEnd_matrix] at h
  exact h.symm


end HodgeLean.Foundations.Program
