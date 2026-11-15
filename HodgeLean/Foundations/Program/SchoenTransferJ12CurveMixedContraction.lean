import HodgeLean.Foundations.Program.SchoenTransferJ12CurveMixedAction
import HodgeLean.Foundations.Symplectic

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback s4_selected_projection

/-- The mixed divisor construction is rational linear in its degree-two input. -/
def s4_selected_curve_mixed_linear
    (A Y : Over (Spec ↧ℂ)) [GrpObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : Y ⟶ A) : HQ A 2 →ₗ[ℚ] HQ (A ⊗ Y) 2 :=
  homPullback (s4_selected_curve_add_map A Y f) 2 -
    homPullback (CategoryTheory.CartesianMonoidalCategory.fst A Y) 2 -
      (homPullback (CategoryTheory.CartesianMonoidalCategory.snd A Y) 2).comp
        (homPullback f 2)

/-- The action of a mixed divisor is contraction of its exterior two-vector by the curve pairing. -/
theorem s4_selected_curve_mixed_action_contract
    (A Y : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : Y ⟶ A) (I : HQ Y 2 ≃ₗ[ℚ] ℚ)
    (ω : ⋀[ℚ]^2 (HQ A 1)) (u : HQ Y 1) :
    s4_selected_corr_action A Y 1 I 1 1 1 (by norm_num)
      (s4_selected_curve_mixed_divisor A Y f ((cupProductOf A).cupWedgeMap 2 ω)) u =
      -Symplectic.contract ω
        (((((cupProductOf Y).cup (show 1 + 1 = 2 from rfl)).compr₂ I.toLinearMap).flip u).comp
          (homPullback f 1)) := by
  let P := ((cupProductOf Y).cup (show 1 + 1 = 2 from rfl)).compr₂ I.toLinearMap
  let C : HQ Y 1 →ₗ[ℚ] Module.Dual ℚ (HQ A 1) :=
    (homPullback f 1).dualMap.comp P.flip
  let F := (s4_selected_kernel_linear_map A Y 1 I 1 1 1 (by norm_num)).comp
    ((s4_selected_curve_mixed_linear A Y f).comp ((cupProductOf A).cupWedgeMap 2))
  let G : (⋀[ℚ]^2 (HQ A 1)) →ₗ[ℚ] (HQ Y 1 →ₗ[ℚ] HQ A 1) :=
    { toFun := fun w => -((Symplectic.contract w).comp C)
      map_add' := by intro x y; ext z; simp only [map_add, LinearMap.neg_apply,
        LinearMap.comp_apply, LinearMap.add_apply, neg_add_rev]; abel
      map_smul' := by intro c x; ext z; simp only [map_smul, LinearMap.neg_apply,
        LinearMap.comp_apply, LinearMap.smul_apply, RingHom.id_apply, smul_neg] }
  have hFG : F = G := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    apply LinearMap.ext
    intro z
    change s4_selected_corr_action A Y 1 I 1 1 1 _
      (s4_selected_curve_mixed_divisor A Y f
        ((cupProductOf A).cupWedgeMap 2 (exteriorPower.ιMulti ℚ 2 v))) z =
      -Symplectic.contract (exteriorPower.ιMulti ℚ 2 v) (C z)
    rw [CupProduct.cupWedgeMap_ιMulti, CupProduct.cupMulti_succ _ 1 rfl,
      CupProduct.cupMulti_succ _ 0 rfl, CupProduct.cupMulti_zero, CupProduct.cup_one]
    simp only [Fin.tail]
    rw [s4_selected_curve_mixed_divisor_action, Symplectic.contract_ιMulti]
    change I ((cupProductOf Y).cup rfl (homPullback f 1 (v 1)) z) • v 0 -
      I ((cupProductOf Y).cup rfl (homPullback f 1 (v 0)) z) • v 1 =
      -(I ((cupProductOf Y).cup rfl (homPullback f 1 (v 0)) z) • v 1 -
        I ((cupProductOf Y).cup rfl (homPullback f 1 (v 1)) z) • v 0)
    abel
  exact congrArg (fun H => H ω u) hFG

#print axioms s4_selected_curve_mixed_action_contract
end HodgeLean.Foundations.Program
