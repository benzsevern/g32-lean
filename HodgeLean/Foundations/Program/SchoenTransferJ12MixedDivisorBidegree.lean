import HodgeLean.Foundations.Program.SchoenTransferJ12CrossMap
import HodgeLean.Foundations.Program.SchoenTransferJ12CurveMixedContraction

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MonoidalCategory
open scoped TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- Every actual mixed divisor has only the degree-one external bidegree.
Source: the exterior presentation of abelian cohomology and the mixed divisor cup formula. -/
theorem s4_selected_mixed_divisor_bidegree
    (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : Y ⟶ A) (pol : HQ A 2) :
    s4_selected_curve_mixed_divisor A Y f pol ∈
      LinearMap.range (s4_selected_cross_map A Y 1 1 2 rfl) := by
  let E := (cupProductOf A).cupWedgeMap 2
  let M := s4_selected_curve_mixed_linear A Y f
  let S := (LinearMap.range (s4_selected_cross_map A Y 1 1 2 rfl)).comap (M.comp E)
  have hs : ⊤ ≤ S := by
    rw [← exteriorPower.ιMulti_span ℚ 2 (HQ A 1)]
    apply Submodule.span_le.mpr
    rintro _ ⟨v, rfl⟩
    change M (E (exteriorPower.ιMulti ℚ 2 v)) ∈
      LinearMap.range (s4_selected_cross_map A Y 1 1 2 rfl)
    have hE : E (exteriorPower.ιMulti ℚ 2 v) =
        (cupProductOf A).cup rfl (v 0) (v 1) := by
      dsimp only [E]
      rw [CupProduct.cupWedgeMap_ιMulti, CupProduct.cupMulti_succ _ 1 rfl,
        CupProduct.cupMulti_succ _ 0 rfl, CupProduct.cupMulti_zero, CupProduct.cup_one]
      rfl
    rw [hE]
    change s4_selected_curve_mixed_divisor A Y f _ ∈ _
    rw [s4_selected_curve_mixed_divisor_cup]
    exact Submodule.sub_mem _
      (LinearMap.mem_range.mpr ⟨v 0 ⊗ₜ[ℚ] homPullback f 1 (v 1), rfl⟩)
      (LinearMap.mem_range.mpr ⟨v 1 ⊗ₜ[ℚ] homPullback f 1 (v 0), rfl⟩)
  obtain ⟨x, rfl⟩ := ((torusCohomology_cupProductOf A).cupWedgeEquiv 2).surjective pol
  exact hs (Submodule.mem_top : x ∈ ⊤)

#print axioms s4_selected_mixed_divisor_bidegree
end HodgeLean.Foundations.Program
