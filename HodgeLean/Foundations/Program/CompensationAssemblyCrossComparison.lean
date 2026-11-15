import HodgeLean.Foundations.Program.CompensationAssemblyContraction

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open AlgebraicTopology.Singular
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.Program

theorem cq_cross_singular_product (A Y : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (i j : ℕ) (a : HQ A i) (b : HQ Y j) :
    cohomologyHomeomorphEquiv (HodgeLean.Foundations.complexPointProdHomeomorph A Y) (i + j)
      (cupComparison (A ⊗ Y) (i + j) (cq_cross A Y i j a b)) =
      cup (TopCat.of (ComplexPoint A × ComplexPoint Y)) rfl
        (cohomologyMap ℚ i (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) (cupComparison A i a))
        (cohomologyMap ℚ j (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩) (cupComparison Y j b)) := by
  let h := HodgeLean.Foundations.complexPointProdHomeomorph A Y
  let g : TopCat.of (ComplexPoint A × ComplexPoint Y) ⟶ TopCat.of (ComplexPoint (A ⊗ Y)) :=
    TopCat.ofHom ⟨h.symm, h.symm.continuous⟩
  have hgA : g ≫ TopCat.ofHom (Point.continuousMap (fst A Y)) =
      TopCat.ofHom ⟨Prod.fst, continuous_fst⟩ := by
    apply ConcreteCategory.hom_ext
    intro p
    exact congrArg Prod.fst (h.apply_symm_apply p)
  have hgY : g ≫ TopCat.ofHom (Point.continuousMap (snd A Y)) =
      TopCat.ofHom ⟨Prod.snd, continuous_snd⟩ := by
    apply ConcreteCategory.hom_ext
    intro p
    exact congrArg Prod.snd (h.apply_symm_apply p)
  have hpA : cohomologyMap ℚ i g
      (cupComparison (A ⊗ Y) i (homPullback (fst A Y) i a)) =
      cohomologyMap ℚ i (TopCat.ofHom ⟨Prod.fst, continuous_fst⟩) (cupComparison A i a) := by
    change cohomologyMap ℚ i g ((cupComparison (A ⊗ Y) i)
      ((cupComparison (A ⊗ Y) i).symm
        (cohomologyMap ℚ i (TopCat.ofHom (Point.continuousMap (fst A Y))) (cupComparison A i a)))) = _
    rw [LinearEquiv.apply_symm_apply]
    change (cohomologyMap ℚ i g ∘ₗ
      cohomologyMap ℚ i (TopCat.ofHom (Point.continuousMap (fst A Y)))) (cupComparison A i a) = _
    rw [← cohomologyMap_comp, hgA]
  have hpY : cohomologyMap ℚ j g
      (cupComparison (A ⊗ Y) j (homPullback (snd A Y) j b)) =
      cohomologyMap ℚ j (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩) (cupComparison Y j b) := by
    change cohomologyMap ℚ j g ((cupComparison (A ⊗ Y) j)
      ((cupComparison (A ⊗ Y) j).symm
        (cohomologyMap ℚ j (TopCat.ofHom (Point.continuousMap (snd A Y))) (cupComparison Y j b)))) = _
    rw [LinearEquiv.apply_symm_apply]
    change (cohomologyMap ℚ j g ∘ₗ
      cohomologyMap ℚ j (TopCat.ofHom (Point.continuousMap (snd A Y)))) (cupComparison Y j b) = _
    rw [← cohomologyMap_comp, hgY]
  change cohomologyMap ℚ (i + j) g
    (cupComparison (A ⊗ Y) (i + j)
      ((cupProductOf (A ⊗ Y)).cup rfl (homPullback (fst A Y) i a) (homPullback (snd A Y) j b))) = _
  rw [cupComparison_cup, cohomologyMap_cup, hpA, hpY]

end HodgeLean.Foundations.Program
