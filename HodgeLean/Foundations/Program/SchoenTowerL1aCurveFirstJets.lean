import HodgeLean.Foundations.Program.SchoenTowerL1aLocalCurveCoordinate
import HodgeLean.Foundations.Program.SchoenTowerL1aEtaleFirstJet

/-! # Actual first-order classes on local curve charts

The etale curve coordinate gives a nonzero first-order class at each actual
complex point of its affine chart. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
/-- The actual affine coordinate chart of a smooth complex curve supplies a nonzero first-order point class.
Source: Hartshorne, Algebraic Geometry, II.8 and III.10, tangent vectors in etale coordinates. -/
theorem s2v_l1a_curve_chart_first_jet
    {Z : Over (Spec ↧ℂ)} [SmoothOfRelativeDimension 1 Z.hom] {x : Z.left}
    (D : LocalEtaleCoordinates Z 1 x)
    (y : ComplexPoint (ComplexPoint.openScheme Z D.neighborhood)) :
    letI : Algebra ℂ Γ(D.neighborhood.toScheme, ⊤) :=
      (D.coordinateRingHomOnOpen.comp MvPolynomial.C).toAlgebra
    ∃ u : Γ(D.neighborhood.toScheme, ⊤),
      u ∈ RingHom.ker (D.pointAlgHomHomeomorph y).toRingHom ∧
      u ∉ RingHom.ker (D.pointAlgHomHomeomorph y).toRingHom ^ 2 := by
  letI : Algebra ℂ Γ(D.neighborhood.toScheme, ⊤) :=
    (D.coordinateRingHomOnOpen.comp MvPolynomial.C).toAlgebra
  let g : MvPolynomial (Fin 1) ℂ →ₐ[ℂ] Γ(D.neighborhood.toScheme, ⊤) :=
    { D.coordinateRingHomOnOpen with commutes' := fun _ => rfl }
  let ev := D.pointAlgHomHomeomorph y
  exact ⟨g (MvPolynomial.X 0) - algebraMap ℂ _ (ev (g (MvPolynomial.X 0))),
    s2v_l1a_etale_coordinate_first_jet g D.coordinateRingHomOnOpen_etale ev⟩

set_option backward.isDefEq.respectTransparency false in
/-- The nonzero first-order coordinate class lies in the actual point ideal and outside its square.
Source: Hartshorne, Algebraic Geometry, II.8 and III.10, point ideal sheaves and etale coordinates. -/
theorem s2v_l1a_curve_chart_point_ideal_first_jet
    {Z : Over (Spec ↧ℂ)} [SmoothOfRelativeDimension 1 Z.hom] {x : Z.left}
    (D : LocalEtaleCoordinates Z 1 x)
    (y : ComplexPoint (ComplexPoint.openScheme Z D.neighborhood)) :
    ∃ (hA : IsAffine D.neighborhood.toScheme) (u : Γ(D.neighborhood.toScheme, ⊤)),
      u ∈ (y.left.ker).ideal ⟨⊤, @isAffineOpen_top _ hA⟩ ∧
      u ∉ ((y.left.ker).ideal ⟨⊤, @isAffineOpen_top _ hA⟩) ^ 2 := by
  letI : IsAffine D.neighborhood.toScheme := D.isAffine
  letI : IsAffine (ComplexPoint.openScheme Z D.neighborhood).left := D.isAffine
  letI : Algebra ℂ Γ(D.neighborhood.toScheme, ⊤) :=
    (D.coordinateRingHomOnOpen.comp MvPolynomial.C).toAlgebra
  obtain ⟨u, hu, hnu⟩ := s2v_l1a_curve_chart_first_jet D y
  have hker : RingHom.ker (D.pointAlgHomHomeomorph y).toRingHom =
      (y.left.ker).ideal ⟨⊤, isAffineOpen_top _⟩ := by
    rw [Scheme.Hom.ker_apply]
    apply Ideal.ext
    intro s
    change D.pointAlgHomHomeomorph y s = 0 ↔ y.left.appTop.hom s = 0
    rw [D.pointAlgHomHomeomorph_apply, ComplexPoint.evaluate_top_eq_appTop]
    exact (Scheme.ΓSpecIso (CommRingCat.of ℂ)).commRingCatIsoToRingEquiv.map_eq_zero_iff
  exact ⟨inferInstance, u, hker ▸ hu, by simpa only [← hker] using hnu⟩

end HodgeLean.Foundations.Program
