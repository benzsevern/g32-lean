import HodgeLean.Foundations.Program.G32SelectedRealizationSupplierHodge
import HodgeLean.Foundations.Program.G32SelectedRealizationRangeSplit
import HodgeLean.Foundations.Program.G32SelectedRealizationRangeBaseChange

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
open scoped TensorProduct CategoryTheory.MonObj
namespace HodgeLean.Foundations.Program

theorem g32y_abelian_range_hodge_complement
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsIntegral A.left] [Smooth A.hom]
    [IsProjective A.hom] {I : Type*} [Fintype I]
    (f : I → AbelianEnd A) (u : I → ℚ)
    (V : Submodule ℚ (HQ A 1))
    (hR : LinearMap.range (∑ i, u i • homPullback (f i).hom 1) = V) :
    IsCompl ((cohomologyHodgePiece A 1 (1, 0)).comap (V.subtype.baseChange ℂ))
      ((cohomologyHodgePiece A 1 (0, 1)).comap (V.subtype.baseChange ℂ)) := by
  classical
  let T : Module.End ℚ (HQ A 1) := ∑ i, u i • homPullback (f i).hom 1
  have hTC : LinearMap.range (T.baseChange ℂ) =
      LinearMap.range (V.subtype.baseChange ℂ) := by
    rw [g32y_baseChange_range, show LinearMap.range T = V from hR]
  have hfull : IsCompl (cohomologyHodgePiece A 1 (1, 0))
      (cohomologyHodgePiece A 1 (0, 1)) := by
    rw [spec_g4_cohomologyHodgePiece_one_eq]
    simp only [latticeHodgePieces, ↓reduceIte, Prod.mk.injEq, one_ne_zero, false_and]
    exact ⟨(spec_complexH1_split A).2, codisjoint_iff.mpr (spec_complexH1_split A).1⟩
  have hp (pq : ℤ × ℤ) : (cohomologyHodgePiece A 1 pq).map (T.baseChange ℂ) ≤
      cohomologyHodgePiece A 1 pq := by
    rintro _ ⟨x, hx, rfl⟩
    have he : T.baseChange ℂ = ∑ i, u i • (homPullback (f i).hom 1).baseChange ℂ := by
      exact map_sum (LinearMap.baseChangeHom ℚ ℂ _ _) _ _ |>.trans
        (Finset.sum_congr rfl (fun i _ ↦ LinearMap.baseChange_smul (u i) (homPullback (f i).hom 1)))
    rw [he, LinearMap.sum_apply]
    apply Submodule.sum_mem
    intro i _
    exact (cohomologyHodgePiece A 1 pq).restrictScalars ℚ |>.smul_mem (u i)
      (spec_homPullback_hodgePiece_one (f i).hom pq ⟨x, hx, rfl⟩)
  exact g32y_range_complement (V.subtype.baseChange ℂ)
    (Module.Flat.lTensor_preserves_injective_linearMap V.subtype Subtype.val_injective)
    (T.baseChange ℂ) hTC _ _ hfull (hp _) (hp _)

end HodgeLean.Foundations.Program
