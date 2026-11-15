import HodgeLean.Foundations.Program.SchoenCycleIdentifiedSubalgebraPointEvaluation
import HodgeLean.Foundations.Program.SchoenCycleAffineOpenPointsExt
import HodgeLean.Foundations.Program.SchoenCycleComplexSectionPullback

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual localized subalgebra point maps to the original base point whenever the geometric map retains the original base section evaluations.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_localized_subalgebra_base_point
    (X B : Over (Spec ↧ℂ)) (γ : X ⟶ B) (U : B.left.Opens)
    (hU : IsAffineOpen U) (hW : IsAffineOpen (γ.left ⁻¹ᵁ U))
    (x : ComplexPoint X) (hx : ⊤ ≤ x.left ⁻¹ᵁ (γ.left ⁻¹ᵁ U)) :
    letI := s2e_step1_sectionAlgebra B U
    letI := s2e_step1_sectionAlgebra X (γ.left ⁻¹ᵁ U)
    ∀ (S : Subalgebra ℂ Γ(X.left, γ.left ⁻¹ᵁ U))
      (F : Γ(B.left, U) →ₐ[ℂ] S)
      (hF : ∀ a, (F a).val = (γ.left.app U).hom a)
      (z : ComplexPoint (Over.mk (ComplexPoint.affineSpecStructureMap S)))
      (hz : z.underlying.asIdeal = ((hW.primeIdealOf ⟨x.underlying, hx trivial⟩).asIdeal).under S)
      (g : S)
      (w : ComplexPoint (Over.mk (ComplexPoint.affineSpecStructureMap (Localization.Away g))))
      (hw : ComplexPoint.affineSpecComplexPointMap
        (IsScalarTower.toAlgHom ℂ S (Localization.Away g)) w = z)
      (f : Over.mk (ComplexPoint.affineSpecStructureMap (Localization.Away g)) ⟶ B)
      (hv : ∀ a : Γ(B.left, U), Point.evaluate U a (Point.map f w) =
        ComplexPoint.affineSpecEquiv (Localization.Away g) w (algebraMap S (Localization.Away g) (F a))),
      Point.map f w = Point.map γ x := by
  letI := s2e_step1_sectionAlgebra B U
  letI := s2e_step1_sectionAlgebra X (γ.left ⁻¹ᵁ U)
  intro S F hF z hz g w hw f hv
  have hwv (s : S) : ComplexPoint.affineSpecEquiv (Localization.Away g) w
      (algebraMap S (Localization.Away g) s) = ComplexPoint.affineSpecEquiv S z s := by
    have he := congrArg (fun k : S →ₐ[ℂ] ℂ => k s)
      (ComplexPoint.affineSpecEquiv_affineSpecComplexPointMap
        (IsScalarTower.toAlgHom ℂ S (Localization.Away g)) w)
    rw [hw] at he
    exact he.symm
  have ha (a : Γ(B.left, U)) : Point.evaluate U a (Point.map f w) = Point.evaluate U a (Point.map γ x) := by
    calc
      Point.evaluate U a (Point.map f w) = ComplexPoint.affineSpecEquiv S z (F a) := (hv a).trans (hwv (F a))
      _ = Point.evaluate (γ.left ⁻¹ᵁ U) (F a).val x :=
        s2e_identified_subalgebra_point_evaluation X _ hW x hx S z hz (F a)
      _ = Point.evaluate U a (Point.map γ x) := by
        rw [hF a]
        exact (Point.evaluate_map γ U a x).symm
  have hxU : Point.map γ x ∈ Point.overOpen U := hx trivial
  have hwU : Point.map f w ∈ Point.overOpen U := by
    by_contra h
    have he := ha 1
    have h' : ¬ (Point.map f w).underlying ∈ U := h
    have hxU' : (Point.map γ x).underlying ∈ U := hxU
    simp only [Point.evaluate, dif_neg h', dif_pos hxU', map_one] at he
    exact zero_ne_one he
  exact s2e_affine_open_points_ext B U hU _ _ hwU hxU ha

#print axioms s2e_localized_subalgebra_base_point
end HodgeLean.Foundations.Program
