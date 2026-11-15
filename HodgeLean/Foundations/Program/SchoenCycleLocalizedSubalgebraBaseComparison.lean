import HodgeLean.Foundations.Program.SchoenCycleAffineOpenPointsExt
import HodgeLean.Foundations.Program.SchoenCycleComplexSectionPullback

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Exact original section evaluations identify the entire geometric upstairs-to-base comparison on complex points after localization of a section subalgebra.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_localized_subalgebra_base_comparison
    (X B Y : Over (Spec ↧ℂ)) (γ : X ⟶ B) (U : B.left.Opens) (hU : IsAffineOpen U)
    (η : Y ⟶ X) (hη : ∀ q : ComplexPoint Y, Point.map η q ∈ Point.overOpen (γ.left ⁻¹ᵁ U)) :
    letI := s2e_step1_sectionAlgebra B U
    letI := s2e_step1_sectionAlgebra X (γ.left ⁻¹ᵁ U)
    ∀ (S : Subalgebra ℂ Γ(X.left, γ.left ⁻¹ᵁ U))
      (F : Γ(B.left, U) →ₐ[ℂ] S) (hF : ∀ a, (F a).val = (γ.left.app U).hom a)
      (g : S)
      (u : Y ⟶ Over.mk (ComplexPoint.affineSpecStructureMap (Localization.Away g)))
      (hu : ∀ (q : ComplexPoint Y) (s : S),
        ComplexPoint.affineSpecEquiv (Localization.Away g) (Point.map u q)
          (algebraMap S (Localization.Away g) s) = Point.evaluate (γ.left ⁻¹ᵁ U) s.val (Point.map η q))
      (f : Over.mk (ComplexPoint.affineSpecStructureMap (Localization.Away g)) ⟶ B)
      (hf : ∀ (q : ComplexPoint (Over.mk (ComplexPoint.affineSpecStructureMap (Localization.Away g))))
        (a : Γ(B.left, U)), Point.evaluate U a (Point.map f q) =
          ComplexPoint.affineSpecEquiv (Localization.Away g) q (algebraMap S (Localization.Away g) (F a))),
      ∀ q : ComplexPoint Y, Point.map f (Point.map u q) = Point.map γ (Point.map η q) := by
  letI := s2e_step1_sectionAlgebra B U
  letI := s2e_step1_sectionAlgebra X (γ.left ⁻¹ᵁ U)
  intro S F hF g u hu f hf q
  have ha (a : Γ(B.left, U)) : Point.evaluate U a (Point.map f (Point.map u q)) =
      Point.evaluate U a (Point.map γ (Point.map η q)) := by
    calc
      Point.evaluate U a (Point.map f (Point.map u q)) =
          Point.evaluate (γ.left ⁻¹ᵁ U) (F a).val (Point.map η q) :=
        (hf (Point.map u q) a).trans (hu q (F a))
      _ = _ := by rw [hF a]; exact (Point.evaluate_map γ U a (Point.map η q)).symm
  have hx : Point.map γ (Point.map η q) ∈ Point.overOpen U := hη q
  have hy : Point.map f (Point.map u q) ∈ Point.overOpen U := by
    by_contra h
    have he := ha 1
    have h' : ¬ (Point.map f (Point.map u q)).underlying ∈ U := h
    have hx' : (Point.map γ (Point.map η q)).underlying ∈ U := hx
    simp only [Point.evaluate, dif_neg h', dif_pos hx', map_one] at he
    exact zero_ne_one he
  exact s2e_affine_open_points_ext B U hU _ _ hy hx ha

#print axioms s2e_localized_subalgebra_base_comparison
end HodgeLean.Foundations.Program
