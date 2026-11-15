import HodgeLean.Foundations.Program.SchoenCycleOpenTopSectionEquiv

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Transporting an ambient section to its actual open scheme retains its evaluation at every actual complex point.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_complex_open_top_section_evaluate
    (X : Over (Spec ↧ℂ)) (V : X.left.Opens) :
    let Y := ComplexPoint.openScheme X V
    letI := s2e_step1_sectionAlgebra X V
    letI := s2e_step1_sectionAlgebra Y ⊤
    ∀ (s : Γ(X.left, V)) (z : ComplexPoint Y),
      Point.evaluate ⊤ (s2e_complex_open_top_section_equiv X V s) z =
        Point.evaluate V s (Point.map (ComplexPoint.openInclusion X V) z) := by
  dsimp only
  let Y := ComplexPoint.openScheme X V
  letI := s2e_step1_sectionAlgebra X V
  letI := s2e_step1_sectionAlgebra Y ⊤
  intro s z
  let f := ComplexPoint.openInclusion X V
  have h : (⊤ : Y.left.Opens) ≤ f.left ⁻¹ᵁ V := by
    intro y hy
    exact y.property
  have hf : f.left.appLE V ⊤ h = V.topIso.inv := by
    change V.ι.appLE V ⊤ h = _
    rw [Scheme.Opens.ι_appLE]
    rfl
  calc
    Point.evaluate ⊤ (s2e_complex_open_top_section_equiv X V s) z =
        Point.evaluate ⊤ ((f.left.appLE V ⊤ h).hom s) z := by rw [hf]; rfl
    _ = Point.evaluate (f.left ⁻¹ᵁ V) (f.left.app V s) z :=
      (Point.evaluate_res h (f.left.app V s) z (by trivial)).symm
    _ = Point.evaluate V s (Point.map f z) := (Point.evaluate_map f V s z).symm

#print axioms s2e_complex_open_top_section_evaluate
end HodgeLean.Foundations.Program
