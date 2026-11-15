import HodgeLean.Foundations.Program.SchoenTowerL1bKummerAction

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Pullback by inverse symmetries acts on the actual generic stalk field. -/
@[instance_reducible]
def s2v_l1b_functionFieldAction
    (X : Scheme.{0}) [IsIntegral X] (G : Type) [Group G]
    (ρ : G →* Aut X) : MulSemiringAction G X.functionField where
  smul g z := s2v_l1b_functionFieldPullback (ρ g⁻¹).asIso.hom z
  one_smul z := by
    have h : (ρ (1 : G)⁻¹).asIso.hom = 𝟙 X := by simp
    change s2v_l1b_functionFieldPullback (ρ (1 : G)⁻¹).asIso.hom z = z
    simp only [h, s2v_l1b_functionFieldPullback_id]
    rfl
  mul_smul g k z := by
    have h : (ρ (g * k)⁻¹).asIso.hom =
        (ρ g⁻¹).asIso.hom ≫ (ρ k⁻¹).asIso.hom := by
      rw [mul_inv_rev, map_mul]
      rfl
    change s2v_l1b_functionFieldPullback (ρ (g * k)⁻¹).asIso.hom z =
      s2v_l1b_functionFieldPullback (ρ g⁻¹).asIso.hom
        (s2v_l1b_functionFieldPullback (ρ k⁻¹).asIso.hom z)
    simp only [h, s2v_l1b_functionFieldPullback_comp]
    rfl
  smul_zero g := map_zero _
  smul_add g := map_add _
  smul_one g := map_one _
  smul_mul g := map_mul _

/-- Symmetries over a base fix its actual function-field image. -/
theorem s2v_l1b_functionFieldAction_fixes_base
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (β : X ⟶ Y) [IsDominant β] (G : Type) [Group G]
    (ρ : G →* Aut X) (hρ : ∀ g, (ρ g).asIso.hom ≫ β = β)
    (g : G) (z : Y.functionField) :
    letI := s2v_l1b_functionFieldAction X G ρ
    g • s2v_l1b_functionFieldPullback β z = s2v_l1b_functionFieldPullback β z := by
  exact congrArg (fun f : Y.functionField ⟶ X.functionField => f z)
    (s2v_l1b_functionFieldPullback_over_base β (ρ g⁻¹).asIso.hom (hρ g⁻¹))

/-- Faithful symmetries over a separated base act faithfully on the actual generic field. -/
theorem s2v_l1b_functionFieldAction_faithful
    {X T : Scheme.{0}} [IsIntegral X]
    (s : X ⟶ T) [IsSeparated s] (G : Type) [Group G]
    (ρ : G →* Aut X) (hinj : Function.Injective ρ)
    (hρ : ∀ g, (ρ g).asIso.hom ≫ s = s) :
    letI := s2v_l1b_functionFieldAction X G ρ
    FaithfulSMul G X.functionField := by
  letI := s2v_l1b_functionFieldAction X G ρ
  refine ⟨?_⟩
  intro g k h
  apply inv_injective
  apply hinj
  apply Aut.ext
  apply Iso.ext
  apply s2v_l1b_functionFieldPullback_faithful s
    (ρ g⁻¹).asIso.hom (ρ k⁻¹).asIso.hom ((hρ g⁻¹).trans (hρ k⁻¹).symm)
  exact ConcreteCategory.hom_ext _ _ h

end HodgeLean.Foundations.Program
