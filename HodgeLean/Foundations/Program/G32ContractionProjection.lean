import HodgeLean.Foundations.Program.G32ContractionComplexExterior
import HodgeLean.Foundations.Program.G32ContractionTwoDefs
import HodgeLean.Foundations.Program.G32Contraction

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 4000
set_option Elab.async false
open scoped TensorProduct CategoryTheory.MonObj
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations

namespace HodgeLean.Foundations.Program

theorem g32c_cupC_pullback {Y B : Over (Spec ↧ℂ)}
    [GrpObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [GrpObj B] [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (f : B ⟶ Y) (n : ℕ) :
    letI := (torusCohomology_cupProductOf Y).finite
    letI := (torusCohomology_cupProductOf B).finite
    ∀ w : ⋀[ℂ]^n (ℂ ⊗[ℚ] HQ Y 1),
      (homPullback f n).baseChange ℂ
        (((cupProductOf Y).cupWedgeMap n).baseChange ℂ
          ((HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv n).symm w)) =
      ((cupProductOf B).cupWedgeMap n).baseChange ℂ
        ((HodgeBlocks.WeilAction.exteriorPowerBaseChangeEquiv n).symm
          (exteriorPower.map n ((homPullback f 1).baseChange ℂ) w)) := by
  intro w
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
    spec_homPullback_cupWedgeMap, LinearMap.baseChange_comp, LinearMap.comp_apply,
    g32c_exterior_baseChange_symm_natural]

variable {A : g32t_Sixfold}

theorem g32c_proj_one (X : g32p_Cover A) {r : ℕ} (S : Fin r → g32p_Supplier)
    (hS : ∀ j, g32p_Admissible X.aut (S j)) :
    (homPullback (g32c_proj X S hS) 1).baseChange ℂ ∘ₗ g32c_oneC X S hS =
      g32p_powerOne X.J (r + 1) ∘ₗ g32c_lowerOne X S hS := by
  have hR := g32c_realization X S hS
  have h0 : (homPullback (g32c_proj X S hS) 1).baseChange ℂ ∘ₗ
      (homPullback (fst A.X (g32c_B X S hS)) 1).baseChange ℂ =
      (homPullback (g3_proj X.J (r + 1) 0) 1).baseChange ℂ ∘ₗ
        (homPullback (X.projA ≫ 𝟙 A.X ^ (g32c_N X S hS / X.NA)) 1).baseChange ℂ := by
    simp only [← LinearMap.baseChange_comp, ← spec_homPullback_comp, hR.2.2.2.2.1]
  have hj (j : Fin r) : (homPullback (g32c_proj X S hS) 1).baseChange ℂ ∘ₗ
      (homPullback (snd A.X (g32c_B X S hS) ≫ cfd_proj r (g32c_parts X S hS) j) 1).baseChange ℂ =
      (homPullback (g3_proj X.J (r + 1) j.succ) 1).baseChange ℂ ∘ₗ
        (homPullback ((X.part (S j) (hS j)).proj ≫
          𝟙 (g32c_parts X S hS j) ^ (g32c_N X S hS / (X.part (S j) (hS j)).N)) 1).baseChange ℂ := by
    simp only [← LinearMap.baseChange_comp, ← spec_homPullback_comp, hR.2.2.2.2.2 j]
  apply LinearMap.ext
  intro v
  simp only [LinearMap.comp_apply, g32c_oneC, g32p_powerOne, LinearMap.add_apply,
    LinearMap.sum_apply, LinearMap.comp_apply, map_add, map_sum, Fin.sum_univ_succ,
    g32c_lowerOne, LinearMap.pi_apply, Fin.cases_zero, Fin.cases_succ,
    LinearMap.fst_apply, LinearMap.snd_apply, LinearMap.proj_apply]
  congr 1
  · exact LinearMap.congr_fun h0 v.1
  · apply Finset.sum_congr rfl
    intro j _
    exact LinearMap.congr_fun (hj j) (v.2 j)

end HodgeLean.Foundations.Program
