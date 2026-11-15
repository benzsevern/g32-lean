import HodgeLean.Foundations.Program.SchoenCycleStep1SectionAction

/-! # Point evaluations and invariant inverse-image charts -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- Containment of the distinguished point gives containment of a field-valued point map. -/
theorem s2e_step1_point_preimage (X : Over (Spec ↧ℂ))
    (x : ComplexPoint X) (W : X.left.Opens)
    (hx : x.left (IsLocalRing.closedPoint ℂ) ∈ W) : ⊤ ≤ x.left ⁻¹ᵁ W := by
  change ∀ z : PrimeSpectrum ℂ, _
  intro z _
  have hz : z = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
  change x.left z ∈ W
  rw [hz]
  exact hx

/-- Pullback of a section agrees with evaluation at the mapped point. -/
theorem s2e_step1_pointEvaluation_map (X : Over (Spec ↧ℂ))
    (W : X.left.Opens) (u : X ⟶ X) (hW : W ≤ u.left ⁻¹ᵁ W)
    (x : ComplexPoint X) (hx : ⊤ ≤ x.left ⁻¹ᵁ W)
    (hux : ⊤ ≤ (Point.map u x).left ⁻¹ᵁ W) (r : Γ(X.left, W)) :
    s2e_step1_pointEvaluation X W (Point.map u x) hux r =
      s2e_step1_pointEvaluation X W x hx ((u.left.appLE W W hW).hom r) := by
  have he : u.left.appLE W W hW ≫ x.left.appLE W ⊤ hx =
      (Point.map u x).left.appLE W ⊤ hux :=
    Scheme.Hom.appLE_comp_appLE x.left u.left W W ⊤ hW hx
  exact (congrArg (fun t : Γ(X.left, W) ⟶ Γ(Spec ↧ℂ, ⊤) =>
    (t ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom r) he).symm

/-- Points over the same base point agree on pulled-back base sections. -/
theorem s2e_step1_pointEvaluation_base (X Y : Over (Spec ↧ℂ))
    (q : X ⟶ Y) (U : Y.left.Opens) (x y : ComplexPoint X)
    (hx : ⊤ ≤ x.left ⁻¹ᵁ (q.left ⁻¹ᵁ U))
    (hy : ⊤ ≤ y.left ⁻¹ᵁ (q.left ⁻¹ᵁ U))
    (hxy : Point.map q x = Point.map q y) (c : Γ(Y.left, U)) :
    s2e_step1_pointEvaluation X (q.left ⁻¹ᵁ U) x hx ((q.left.app U).hom c) =
      s2e_step1_pointEvaluation X (q.left ⁻¹ᵁ U) y hy ((q.left.app U).hom c) := by
  have he : q.left.app U ≫ x.left.appLE (q.left ⁻¹ᵁ U) ⊤ hx =
      q.left.app U ≫ y.left.appLE (q.left ⁻¹ᵁ U) ⊤ hy := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.appLE_comp_appLE]
    congr 1
    exact congrArg Over.Hom.left hxy
  exact congrArg (fun t : Γ(Y.left, U) ⟶ Γ(Spec ↧ℂ, ⊤) =>
    (t ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).hom c) he

end HodgeLean.Foundations.Program
