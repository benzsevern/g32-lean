import HodgeLean.Foundations.Program.SchoenTransferJ12CurveJordanOperatorCups

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- The actual fibre-integral Jordan operation induces the symmetrized composition on all divisor classes. -/
theorem s4_selected_curve_jordan_operator
    (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : Y ⟶ A) (I : HQ Y 2 ≃ₗ[ℚ] ℚ) (p q : HQ A 2) :
    let D := s4_selected_curve_divisor_operator A Y f I
    D (s4_selected_curve_jordan A Y f I p q) =
      (2 : ℚ)⁻¹ • ((D p).comp (D q) + (D q).comp (D p)) := by
  let D := s4_selected_curve_divisor_operator A Y f I
  let E := (cupProductOf A).cupWedgeMap 2
  let H := (s4_selected_curve_jordan_linear A Y f I).compr₂ D
  let B := (LinearMap.llcomp ℚ (HQ A 1) (HQ A 1) (HQ A 1)).compl₁₂ D D
  have hE (v : Fin 2 → HQ A 1) : E (exteriorPower.ιMulti ℚ 2 v) =
      (cupProductOf A).cup rfl (v 0) (v 1) := by
    dsimp only [E]
    rw [CupProduct.cupWedgeMap_ιMulti, CupProduct.cupMulti_succ _ 1 rfl,
      CupProduct.cupMulti_succ _ 0 rfl, CupProduct.cupMulti_zero, CupProduct.cup_one]
    rfl
  have hEq : H.compl₁₂ E E = ((2 : ℚ)⁻¹ • (B + B.flip)).compl₁₂ E E := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro w
    change H (E (exteriorPower.ιMulti ℚ 2 v)) (E (exteriorPower.ιMulti ℚ 2 w)) =
      ((2 : ℚ)⁻¹ • (B + B.flip)) (E (exteriorPower.ιMulti ℚ 2 v))
        (E (exteriorPower.ιMulti ℚ 2 w))
    rw [hE v, hE w]
    exact s4_selected_curve_jordan_operator_cups A Y f I (v 0) (v 1) (w 0) (w 1)
  obtain ⟨u, rfl⟩ := ((torusCohomology_cupProductOf A).cupWedgeEquiv 2).surjective p
  obtain ⟨v, rfl⟩ := ((torusCohomology_cupProductOf A).cupWedgeEquiv 2).surjective q
  exact LinearMap.congr_fun (LinearMap.congr_fun hEq u) v

#print axioms s4_selected_curve_jordan_operator
end HodgeLean.Foundations.Program
