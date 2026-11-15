import HodgeLean.Foundations.Program.MilnePowerForms
import HodgeLean.Foundations.Program.MilnePowerAction

noncomputable section
set_option maxHeartbeats 200000
open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open HodgeLean.Foundations.Symplectic
namespace HodgeLean.Foundations.Program

def m2_powerFormQ (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol)) (r : ℕ) :
    LinearMap.BilinForm ℚ (HQ (g3_power J r) 1) :=
  ∑ i, (polarizationForm (torusCohomology_cupProductOf J) hη).comp
    (homPullback (g3_incl J r i) 1) (homPullback (g3_incl J r i) 1)

theorem m2_powerForm_baseChange (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol)) (r : ℕ) :
    (m2_powerFormQ J pol hη r).baseChange ℂ =
      ∑ i, (m0_form J pol hη).comp
        ((homPullback (g3_incl J r i) 1).baseChange ℂ)
        ((homPullback (g3_incl J r i) 1).baseChange ℂ) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro a x
  apply TensorProduct.AlgebraTensorModule.ext
  intro b y
  simp only [LinearMap.BilinForm.baseChange_tmul, m2_powerFormQ, LinearMap.sum_apply,
    Finset.sum_smul, LinearMap.BilinForm.comp_apply, LinearMap.baseChange_tmul, m0_form,
    LinearMap.BilinForm.baseChange_tmul]


theorem m2_powerForm_nondegenerate (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol)) (r : ℕ) :
    ((m2_powerFormQ J pol hη r).baseChange ℂ).Nondegenerate := by
  have hE := m0_form_nondegenerate J pol hη
  have hi : Function.Injective (m2_powerOneInv J r) := (m2_powerOneEquiv J r).symm.injective
  constructor
  · intro x hx
    apply hi
    funext i
    change (homPullback (g3_incl J r i) 1).baseChange ℂ x = 0
    apply hE.1
    intro y
    have h := hx ((homPullback (g3_proj J r i) 1).baseChange ℂ y)
    rw [m2_powerForm_baseChange] at h
    simp only [LinearMap.sum_apply, LinearMap.BilinForm.comp_apply] at h
    have hd (j : Fin r) : (homPullback (g3_incl J r j) 1).baseChange ℂ
        ((homPullback (g3_proj J r i) 1).baseChange ℂ y) = if j = i then y else 0 := by
      have hh := LinearMap.congr_fun (m2_power_incl_proj J r j i) y
      split_ifs at hh ⊢ <;> exact hh
    simpa only [hd, apply_ite, ite_apply, map_zero, LinearMap.zero_apply, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using h
  · intro x hx
    apply hi
    funext i
    change (homPullback (g3_incl J r i) 1).baseChange ℂ x = 0
    apply hE.2
    intro y
    have h := hx ((homPullback (g3_proj J r i) 1).baseChange ℂ y)
    rw [m2_powerForm_baseChange] at h
    simp only [LinearMap.sum_apply, LinearMap.BilinForm.comp_apply] at h
    have hd (j : Fin r) : (homPullback (g3_incl J r j) 1).baseChange ℂ
        ((homPullback (g3_proj J r i) 1).baseChange ℂ y) = if j = i then y else 0 := by
      have hh := LinearMap.congr_fun (m2_power_incl_proj J r j i) y
      split_ifs at hh ⊢ <;> exact hh
    have hs (j : Fin r) : m0_form J pol hη
        ((homPullback (g3_incl J r j) 1).baseChange ℂ
          ((homPullback (g3_proj J r i) 1).baseChange ℂ y))
        ((homPullback (g3_incl J r j) 1).baseChange ℂ x) =
        if j = i then m0_form J pol hη y
          ((homPullback (g3_incl J r i) 1).baseChange ℂ x) else 0 := by
      rw [hd]
      split_ifs with hj
      · subst j; rfl
      · rw [map_zero, LinearMap.zero_apply]
    simpa only [hs, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using h

theorem m2_powerForm_preserved (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol)) (r : ℕ)
    (u : Module.End ℂ (ℂ ⊗[ℚ] HQ J 1)) (hu : u ∈ g32p_lefschetz J pol) :
    ∀ x y, (m2_powerFormQ J pol hη r).baseChange ℂ (m2_powerAction J r u x)
      (m2_powerAction J r u y) = (m2_powerFormQ J pol hη r).baseChange ℂ x y := by
  intro x y
  simp only [m2_powerForm_baseChange, LinearMap.sum_apply, LinearMap.BilinForm.comp_apply, m2_powerAction_incl]
  apply Finset.sum_congr rfl
  intro i _
  exact ((m0_mem_lefschetz_iff J pol hη u).1 hu).2.2 _ _


theorem m2_powerForm_grading_skew (J : Over (Spec ↧ℂ)) [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom] (pol : HQ J 2)
    (hη : IsNondegenerate (polarizationVec (torusCohomology_cupProductOf J) pol))
    (hpos : PolarizationPositive (finiteBetti_abelian J) (spec_bettiDeRhamIso_abelian J)
      (hodgeDecomposition_of_abelian J) (torusCohomology_cupProductOf J) hη) (r : ℕ) :
    ∀ x y, (m2_powerFormQ J pol hη r).baseChange ℂ
      (m2_hodgeGrading (g3_power J r) x) y =
      -(m2_powerFormQ J pol hη r).baseChange ℂ x (m2_hodgeGrading (g3_power J r) y) := by
  have hc : m2_hodgeGrading J ∈ g32p_lefschetz J pol :=
    m2_grading_mem_lefschetz J pol hη hpos
  have he := m2_powerForm_preserved J pol hη r (m2_hodgeGrading J) hc
  rw [m2_powerAction_grading] at he
  intro x y
  have h := he x (m2_hodgeGrading (g3_power J r) y)
  rw [m2_hodgeGrading_square, map_neg] at h
  exact neg_eq_iff_eq_neg.mp h


end HodgeLean.Foundations.Program
