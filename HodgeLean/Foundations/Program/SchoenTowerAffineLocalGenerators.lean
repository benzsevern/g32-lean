import HodgeLean.Foundations.Program.SchoenTowerAffineComplexPoints

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint

namespace HodgeLean.Foundations.Program
attribute [local instance] overSpecAlgebra s2t_complexStalkAlgebra

/-- Localizing the affine section ring of a smooth complex curve at a rational point gives a
nonzero differential generator.
Source: Stacks Project, Tag 054L; `IsLocalization.algEquiv`. -/
theorem s2t_curve_affine_local_differential_generator (X : Over (Spec ↧ℂ))
    [IsAffine X.left] [SmoothOfRelativeDimension 1 X.hom] (p : ComplexPoint X) :
    letI : (RingHom.ker (s2t_affinePointAlgHom X p).toRingHom).IsPrime :=
      RingHom.ker_isPrime _
    let B := Localization.AtPrime (RingHom.ker (s2t_affinePointAlgHom X p).toRingHom)
    ∃ t : B, KaehlerDifferential.D ℂ B t ≠ 0 ∧
      Submodule.span B {KaehlerDifferential.D ℂ B t} = ⊤ := by
  let A := Γ(X.left, ⊤)
  let S := X.left.presheaf.stalk p.underlying
  let q := RingHom.ker (s2t_affinePointAlgHom X p).toRingHom
  letI : q.IsPrime := RingHom.ker_isPrime _
  let B := Localization.AtPrime q
  letI : Algebra A S := X.left.presheaf.algebra_section_stalk ⟨p.underlying, show p.underlying ∈ ⊤ from trivial⟩
  letI : IsScalarTower ℂ A S := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsLocalization.AtPrime S q := s2t_affinePoint_stalk_isLocalization X p
  let e := IsLocalization.algEquiv q.primeCompl S B
  obtain ⟨f, hf⟩ := s2t_curve_stalk_polynomial_coordinates X p.underlying
  let fB := (e.restrictScalars ℂ).toAlgHom.comp f
  letI : Algebra (Polynomial ℂ) S := f.toRingHom.toAlgebra
  letI : Algebra (Polynomial ℂ) B := fB.toRingHom.toAlgebra
  let ep : S ≃ₐ[Polynomial ℂ] B :=
    { e.toRingEquiv with commutes' := fun _ => rfl }
  letI : Algebra.FormallyEtale (Polynomial ℂ) S := hf
  letI : Algebra.FormallyEtale (Polynomial ℂ) B := Algebra.FormallyEtale.of_equiv ep
  letI : IsScalarTower ℂ (Polynomial ℂ) B :=
    IsScalarTower.of_algebraMap_eq' fB.comp_algebraMap.symm
  exact ⟨algebraMap (Polynomial ℂ) B Polynomial.X,
    s2t_polynomial_coordinate_differential_ne_zero,
    s2t_polynomial_coordinate_differential_spans⟩

end HodgeLean.Foundations.Program
