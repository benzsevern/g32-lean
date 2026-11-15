import HodgeLean.Foundations.Program.SchoenTowerL1aFiniteEtaleCurve

/-! # Etale curve sections with prescribed finite values

Implication from smoothness of the actual affine curve to a section with any
specified finite values and an etale principal neighborhood of that support.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program
attribute [local instance] overSpecAlgebra

/-- Prescribed values on distinct actual curve points extend to an etale polynomial parameter after one principal restriction retaining those points.
Source: Stacks Project, tag 054L; Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 1.10. -/
theorem s2v_l1a_affine_curve_prescribed_etale_section
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsAffine X.left] [Smooth X.hom]
    [SmoothOfRelativeDimension 1 X.hom]
    {ι : Type} [Finite ι] [Nonempty ι]
    (p : ι → ComplexPoint X) (hp : Function.Injective p) (c : ι → ℂ) :
    ∃ g r : Γ(X.left, ⊤),
      (∀ i, Point.evaluate ⊤ g (p i) = c i) ∧
      (∀ i, Point.evaluate ⊤ r (p i) = 1) ∧
      letI := (Polynomial.aeval (R := ℂ) g).toRingHom.toAlgebra
      Algebra.Etale (Polynomial ℂ) (Localization.Away r) := by
  letI : Algebra.FiniteType ℂ Γ(X.left, ⊤) := s2t_globalSections_finiteType X
  let φ (i : ι) := s2t_affinePointAlgHom X (p i)
  have hinj : Function.Injective φ := (s2t_affinePointAlgHom_injective X).comp hp
  letI (i : ι) : (RingHom.ker (φ i).toRingHom).IsPrime := RingHom.ker_isPrime _
  choose t hne ht using fun i => s2t_curve_affine_local_differential_generator X (p i)
  letI (i : ι) : Nontrivial
      (KaehlerDifferential ℂ (Localization.AtPrime (RingHom.ker (φ i).toRingHom))) :=
    nontrivial_of_ne _ _ (hne i)
  obtain ⟨g, r, hg, hr, hEt⟩ :=
    s2t_etale_coordinate_of_local_differential_generators φ hinj t ht c
  refine ⟨g, r, ?_, ?_, hEt⟩
  · intro i
    rw [← s2t_affinePointAlgHom_apply]
    exact hg i
  · intro i
    rw [← s2t_affinePointAlgHom_apply]
    exact hr i

end HodgeLean.Foundations.Program
