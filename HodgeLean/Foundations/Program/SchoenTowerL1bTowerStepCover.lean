import HodgeLean.Foundations.Program.SchoenTowerL1bRetainedCoordinateCover
import HodgeLean.Foundations.Program.SchoenTowerL1bEtaleBranchStep
import HodgeLean.Foundations.Program.SchoenTowerL1bStrictTransformChart

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Every branch outside a coordinate centre has its actual transform equation
on both retained blowup charts, simultaneously for an arbitrary label family. -/
theorem s2v_l1b_tower_step_coordinate_cover
    (B X : Over (Spec ↧ℂ)) (p : X ⟶ B) (I : B.left.IdealSheafData)
    (hcartier : ∀ x : X.left, ∃ V : X.left.affineOpens, x ∈ V.1 ∧
      Nonempty (((I.comap p.left).ideal V) ≃ₗ[Γ(X.left, V)] Γ(X.left, V)))
    (hblowup : ∀ (T : Over (Spec ↧ℂ)) (g : T ⟶ B),
      (∀ x : T.left, ∃ V : T.left.affineOpens, x ∈ V.1 ∧
        Nonempty (((I.comap g.left).ideal V) ≃ₗ[Γ(T.left, V)] Γ(T.left, V))) →
      ∃! u : T ⟶ X, u ≫ p = g)
    (U : B.left.affineOpens) {σ J : Type} [DecidableEq σ]
    (z : σ → Γ(B.left, U))
    (het : (MvPolynomial.eval₂Hom (B.hom.appLE ⊤ U.1 le_top).hom z).Etale)
    (a b : σ) (hab : a ≠ b) (hI : I.ideal U = Ideal.span {z a, z b})
    (D : J → B.left.IdealSheafData) (f : J → σ)
    (hfa : ∀ t, f t ≠ a) (hfb : ∀ t, f t ≠ b)
    (hD : ∀ t, (D t).ideal U = Ideal.span {z (f t)}) :
    ∃ (V₁ V₂ : X.left.affineOpens)
      (h₁ : V₁.1 ≤ p.left ⁻¹ᵁ U.1) (h₂ : V₂.1 ≤ p.left ⁻¹ᵁ U.1)
      (w₁ : σ → Γ(X.left, V₁)) (w₂ : σ → Γ(X.left, V₂)),
      V₁.1 ⊔ V₂.1 = p.left ⁻¹ᵁ U.1 ∧
      (MvPolynomial.eval₂Hom (X.hom.appLE ⊤ V₁.1 le_top).hom w₁).Etale ∧
      (MvPolynomial.eval₂Hom (X.hom.appLE ⊤ V₂.1 le_top).hom w₂).Etale ∧
      (∀ t, (s2c_strictTransform p.left (D t) I).ideal V₁ = Ideal.span {w₁ (f t)}) ∧
      (∀ t, (s2c_strictTransform p.left (D t) I).ideal V₂ = Ideal.span {w₂ (f t)}) := by
  obtain ⟨V₁, V₂, h₁, h₂, w₁, w₂, hcover, he₁, he₂, hz₁, hz₂⟩ :=
    s2v_l1b_retained_coordinate_cover B X p I hcartier hblowup U
      (B.hom.appLE ⊤ U.1 le_top).hom z het a b hab hI
  have hc (V : X.left.affineOpens) (hV : V.1 ≤ p.left ⁻¹ᵁ U.1) :
      (p.left.appLE U.1 V.1 hV).hom.comp (B.hom.appLE ⊤ U.1 le_top).hom =
        (X.hom.appLE ⊤ V.1 le_top).hom := by
    change ((B.hom.appLE ⊤ U.1 le_top) ≫ p.left.appLE U.1 V.1 hV).hom = _
    rw [Scheme.Hom.appLE_comp_appLE]
    rw [Over.w p]
  rw [hc] at he₁ he₂
  have ha : z a ∈ I.ideal U := by
    rw [hI]
    exact Ideal.subset_span (Set.mem_insert _ _)
  have hb : z b ∈ I.ideal U := by
    rw [hI]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  refine ⟨V₁, V₂, h₁, h₂, w₁, w₂, hcover, he₁, he₂, ?_, ?_⟩
  · intro t
    exact s2v_l1b_etale_chart_branch_step p.left (D t) I U V₁ h₁
      (X.hom.appLE ⊤ V₁.1 le_top).hom z w₁ he₁ a b (f t) hab
      (hfa t) (hfb t) hz₁ (hD t) hb
  · intro t
    exact s2v_l1b_etale_chart_branch_step p.left (D t) I U V₂ h₂
      (X.hom.appLE ⊤ V₂.1 le_top).hom z w₂ he₂ b a (f t) hab.symm
      (hfb t) (hfa t) hz₂ (hD t) ha

/-- A branch absent on the base affine open stays absent on every affine chart
above that open, including charts meeting the exceptional divisor. -/
theorem s2v_l1b_tower_step_absent_branch
    {X Y : Scheme} (p : X ⟶ Y) (D I : Y.IdealSheafData)
    (U : Y.affineOpens) (V : X.affineOpens) (hV : V.1 ≤ p ⁻¹ᵁ U.1)
    (hD : D.ideal U = ⊤) :
    (s2c_strictTransform p D I).ideal V = ⊤ := by
  apply s2v_l1b_strictTransform_unit_chart
  rw [s2v_l1b_comap_ideal_affine_charts p D U V hV, hD, Ideal.map_top]

end HodgeLean.Foundations.Program
