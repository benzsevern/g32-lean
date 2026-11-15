import HodgeLean.Foundations.Program.SchoenProjectiveActionQuotientProjectivity
import HodgeLean.Foundations.Program.SchoenQuotientOverDescent
import HodgeLean.Foundations.Program.SchoenQuotientNormality
import HodgeLean.Foundations.Program.SchoenQuotientProper
import HodgeLean.Foundations.Program.SchoenQuotientIntegrality
import HodgeLean.Foundations.Program.SchoenQuotientRationalPoints
import HodgeLean.Foundations.Program.SchoenCycleGeometryDefs

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A finite action on an integral projective complex scheme has its actual finite projective categorical quotient with complex-point orbit fibres. -/
theorem s2_finiteAction_projectiveQuotient (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [IsProjective X.hom]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X) :
    ∃ (W : Over (Spec ↧ℂ)) (q : X ⟶ W),
      IsIntegral W.left ∧ IsProjective W.hom ∧ IsFinite q.left ∧
      Function.Surjective (Point.map q) ∧
      (∀ g : G, (ρ g).asIso.hom ≫ q = q) ∧
      (∀ x y : ComplexPoint X, Point.map q x = Point.map q y ↔
        ∃ g : G, Point.map (ρ g).asIso.hom x = y) ∧
      (∀ (T : Over (Spec ↧ℂ)) (f : X ⟶ T),
        (∀ g : G, (ρ g).asIso.hom ≫ f = f) →
        ∃! d : W ⟶ T, q ≫ d = f) ∧
      (Smooth X.hom → zmtiso_IsNormal W.left) := by
  haveI : IsAffine (terminal (Scheme.{0})) :=
    IsAffine.of_isIso (specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal).inv
  haveI : IsSeparated (terminal.from X.left) := by
    rw [← terminal.comp_from X.hom]
    infer_instance
  let ρs := ((Over.forget (Spec ↧ℂ)).mapAut X).comp ρ
  have hover (g : G) : (ρs g).asIso.hom ≫ X.hom = X.hom := Over.w (ρ g).asIso.hom
  have hcover := s2_projective_invariantAffineIndex_cover ℂ X.left X.hom G ρs
  let W := s2_gluedQuotientOver X G ρs hover hcover
  let q : X ⟶ W := s2_gluedQuotientOverMap X G ρs hover hcover
  have hW : IsIntegral W.left := s2_invariantAffineGlued_isIntegral X.left G ρs hcover
  have hproper : IsProjective W.hom := s2_projectiveAction_gluedQuotient_projective X G ρ hcover hover
  have hfinite : IsFinite q.left := s2_gluedQuotientMap_finite_over X.hom G ρs hover hcover
  refine ⟨W, q, hW, hproper, hfinite, ?_, ?_, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨x, hx, hxy⟩ := s2_gluedQuotientMap_rational_surjective X.left X.hom
      G ρs hover hcover y.left (Over.w y)
    refine ⟨Over.homMk x hx, ?_⟩
    apply Over.OverMorphism.ext
    exact hxy
  · intro g
    apply Over.OverMorphism.ext
    exact s2_gluedQuotientMap_invariant X.left G ρs hcover g
  · intro x y
    have H := s2_gluedQuotientMap_rational_fibres X.left X.hom G ρs hover hcover
      x.left y.left (Over.w x) (Over.w y)
    constructor
    · intro hxy
      obtain ⟨g, hg⟩ := H.mp (congrArg (fun z : ComplexPoint W => z.left) hxy)
      refine ⟨g, ?_⟩
      apply Over.OverMorphism.ext
      exact hg
    · rintro ⟨g, hg⟩
      apply Over.OverMorphism.ext
      exact H.mpr ⟨g, congrArg (fun z : ComplexPoint X => z.left) hg⟩
  · intro T f hf
    apply s2_gluedQuotientOverDesc_arbitrary X G ρs hover hcover T f
    intro g
    exact congrArg (fun k : X ⟶ T => k.left) (hf g)

  · intro hs
    letI := hs
    exact s2_invariantAffineGlued_normal_of_smooth X.left X.hom G ρs

end HodgeLean.Foundations.Program
