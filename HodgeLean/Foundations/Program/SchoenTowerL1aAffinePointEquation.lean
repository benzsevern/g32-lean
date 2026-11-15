import HodgeLean.Foundations.Program.SchoenTowerL1aEtalePointSupport
import HodgeLean.Foundations.Program.SchoenTowerL1aOpenSectionLocalization
import HodgeLean.Foundations.Program.SchoenTowerL1aPointSections
import HodgeLean.Foundations.Program.SchoenTowerCurveCoordinateAssembly

/-! # Point equations on actual principal curve neighborhoods

Implication from an etale section separating a distinguished rational point
to its actual ideal equation after a restriction retaining finite support.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program
attribute [local instance] overSpecAlgebra

/-- An actual etale section generates the distinguished point ideal on one
principal open retaining every specified rational point.
Source: Stacks Project, tag 02FM; Hartshorne, Algebraic Geometry, II.2 and II.5. -/
theorem s2v_l1a_affine_point_equation
    (X : Over (Spec ↧ℂ)) [IsAffine X.left] [LocallyOfFiniteType X.hom]
    {ι : Type} [Finite ι] (p : ι → ComplexPoint X) (hp : Function.Injective p)
    (i₀ : ι) (g : Γ(X.left, ⊤))
    (hEt : (Polynomial.aeval (R := ℂ) g).toRingHom.Etale)
    (hg0 : Point.evaluate ⊤ g (p i₀) = 0)
    (hg : ∀ i, i ≠ i₀ → Point.evaluate ⊤ g (p i) ≠ 0) :
    ∃ d : Γ(X.left, ⊤), (∀ i, Point.evaluate ⊤ d (p i) = 1) ∧
      let O := X.left.basicOpen d
      letI : IsAffine O.toScheme := (isAffineOpen_top X.left).basicOpen d
      (((p i₀).left.ker).comap O.ι).ideal ⟨⊤, isAffineOpen_top _⟩ =
        Ideal.span {O.ι.appTop.hom g} := by
  let A := Γ(X.left, ⊤)
  letI : Algebra.FiniteType ℂ A := s2t_globalSections_finiteType X
  let φ (i : ι) := s2t_affinePointAlgHom X (p i)
  have hinj : Function.Injective φ := (s2t_affinePointAlgHom_injective X).comp hp
  obtain ⟨d, hd, hI⟩ := s2v_l1a_etale_parameter_point_support φ hinj i₀ g hEt
    (by rw [s2t_affinePointAlgHom_apply]; exact hg0)
    (fun i hi => by rw [s2t_affinePointAlgHom_apply]; exact hg i hi)
  refine ⟨d, ?_, ?_⟩
  · intro i
    rw [← s2t_affinePointAlgHom_apply]
    exact hd i
  · let O := X.left.basicOpen d
    let B := Γ(O.toScheme, ⊤)
    letI : IsAffine O.toScheme := (isAffineOpen_top X.left).basicOpen d
    letI : Algebra A B := O.ι.appTop.hom.toAlgebra
    letI : IsLocalization.Away d B := s2v_l1a_openScheme_sections_localization X.left d
    let e : Localization.Away d ≃ₐ[A] B :=
      IsLocalization.algEquiv (Submonoid.powers d) (Localization.Away d) B
    have heq : O.ι.appTop.hom = e.toRingHom.comp (algebraMap A (Localization.Away d)) := by
      ext a
      exact (e.commutes a).symm
    have hker : RingHom.ker (φ i₀).toRingHom =
        (p i₀).left.ker.ideal ⟨⊤, isAffineOpen_top _⟩ := by
      rw [← s2v_l1a_pointSectionEvaluation_kernel]
      congr 1
      ext s
      rw [s2v_l1a_pointSectionEvaluation_apply]
      exact s2t_affinePointAlgHom_apply X (p i₀) s
    change (((p i₀).left.ker).comap O.ι).ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {O.ι.appTop.hom g}
    rw [s2v_l1a_affine_ideal_pullback, ← hker, heq, ← Ideal.map_map, hI,
      Ideal.map_span, Set.image_singleton]
    rfl

end HodgeLean.Foundations.Program
