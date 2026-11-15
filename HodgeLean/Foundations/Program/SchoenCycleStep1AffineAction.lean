import HodgeLean.Foundations.Program.SchoenCycleStep1InvariantSections

/-! # Scalar structures and evaluation on invariant affine charts -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- The scalar structure on a ring of sections is induced by the scheme structure map.
Source: Hartshorne, Algebraic Geometry, II.2--II.3 (schemes over a field). -/
@[instance_reducible] def s2e_step1_sectionAlgebra (X : Over (Spec ↧ℂ)) (W : X.left.Opens) :
    Algebra ℂ Γ(X.left, W) :=
  ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.hom.appLE ⊤ W le_top).hom.toAlgebra

/-- Evaluation at a complex point respects the scalar structure on sections.
Source: Hartshorne, Algebraic Geometry, II.2--II.3 (evaluation of regular functions). -/
def s2e_step1_pointEvaluation (X : Over (Spec ↧ℂ)) (W : X.left.Opens)
    (x : ComplexPoint X) (hx : ⊤ ≤ x.left ⁻¹ᵁ W) :
    letI := s2e_step1_sectionAlgebra X W
    Γ(X.left, W) →ₐ[ℂ] ℂ := by
  letI := s2e_step1_sectionAlgebra X W
  refine ⟨(x.left.appLE W ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom, ?_⟩
  intro c
  have he : (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ X.hom.appLE ⊤ W le_top ≫
      x.left.appLE W ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom = 𝟙 _ := by
    rw [← Category.assoc (X.hom.appLE _ _ _), Scheme.Hom.appLE_comp_appLE]
    have hc : (x.left ≫ X.hom).appLE ⊤ ⊤ (by simp) = (𝟙 (Spec ↧ℂ) : Spec ↧ℂ ⟶ Spec ↧ℂ).appLE ⊤ ⊤ le_top := by
      congr 1
      exact Over.w x
    have hi : (𝟙 (Spec ↧ℂ) : Spec ↧ℂ ⟶ Spec ↧ℂ).appLE ⊤ ⊤ le_top =
        𝟙 Γ(Spec ↧ℂ, ⊤) := by
      change (𝟙 Γ(Spec ↧ℂ, ⊤)) ≫ (Spec ↧ℂ).presheaf.map (𝟙 (Opposite.op ⊤)) = _
      rw [(Spec ↧ℂ).presheaf.map_id, Category.id_comp]
    rw [hc, hi, Category.id_comp, Iso.inv_hom_id]
  exact congrArg (fun t : CommRingCat.of ℂ ⟶ CommRingCat.of ℂ => t.hom c) he

/-- Equality of evaluations on an affine chart determines the complex point. -/
theorem s2e_step1_point_ext_on_affine (X : Over (Spec ↧ℂ))
    (W : X.left.Opens) (hW : IsAffineOpen W) (x y : ComplexPoint X)
    (hx : ⊤ ≤ x.left ⁻¹ᵁ W) (hy : ⊤ ≤ y.left ⁻¹ᵁ W)
    (he : s2e_step1_pointEvaluation X W x hx = s2e_step1_pointEvaluation X W y hy) : x = y := by
  letI := s2e_step1_sectionAlgebra X W
  have ha : x.left.appLE W ⊤ hx = y.left.appLE W ⊤ hy := by
    rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom]
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom he
  have hb := congrArg (fun t => Spec.map t ≫ hW.fromSpec) ha
  rw [hW.SpecMap_appLE_fromSpec x.left (isAffineOpen_top _) hx,
    hW.SpecMap_appLE_fromSpec y.left (isAffineOpen_top _) hy] at hb
  ext1
  exact (cancel_epi (isAffineOpen_top (Spec ↧ℂ)).fromSpec).mp hb

end HodgeLean.Foundations.Program
