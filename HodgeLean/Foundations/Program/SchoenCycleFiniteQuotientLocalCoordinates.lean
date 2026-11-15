module

public import HodgeLean.Foundations.Program.FiniteGroupCoordinateAction
public import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AnalyticMap

/-! # Analytic coordinates for fixed scheme symmetries
The coordinate expression is obtained from the actual scheme morphism.
HC no distance; AV milestone no distance.
-/
public section
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- An actual morphism fixing the marked complex point is analytic in centered
algebraic coordinates.
Source: HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AnalyticMap,
`analyticAt_localChart_symm_map`; Takamura, Linearization of Quotient Families,
J. Math. Sci. Univ. Tokyo 26 (2019), p. 381. -/
theorem s2e_fixed_morphism_centered_coordinates_analytic
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (f : X ⟶ X) (x₀ : ComplexPoint X) (hfix : Point.map f x₀ = x₀) :
    let C := localChart X d x₀
    AnalyticAt ℂ (fun z : Fin d → ℂ =>
      C (Point.map f (C.symm (z + C x₀))) - C x₀) 0 := by
  let C := localChart X d x₀
  have hx : x₀ ∈ C.source := mem_localChart_source X d x₀
  have ht : C x₀ ∈ C.target := C.map_source hx
  have hm : Point.map f (C.symm (C x₀)) ∈
      (localChart X d (Point.map f x₀)).source := by
    rw [C.left_inv hx]
    exact mem_localChart_source X d (Point.map f x₀)
  have h := analyticAt_localChart_symm_map X X f d d x₀ ht hm
  rw [hfix] at h
  change AnalyticAt ℂ (fun w => C (Point.map f (C.symm w))) (C x₀) at h
  have hshift : AnalyticAt ℂ (fun z : Fin d → ℂ => z + C x₀) 0 :=
    analyticAt_id.add analyticAt_const
  exact (h.comp_of_eq hshift (zero_add (C x₀))).sub analyticAt_const

/-- The actual algebraic coordinate chart translated to put the marked point at zero.
Source: Takamura, Linearization of Quotient Families, J. Math. Sci. Univ.
Tokyo 26 (2019), p. 381, coordinate chart centered at the fixed point. -/
def s2e_centeredLocalChart
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (x₀ : ComplexPoint X) : OpenPartialHomeomorph (ComplexPoint X) (Fin d → ℂ) :=
  (localChart X d x₀).trans
    (Homeomorph.subRight (localChart X d x₀ x₀)).toOpenPartialHomeomorph

example (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (x₀ : ComplexPoint X) : s2e_centeredLocalChart X d x₀ x₀ = 0 := by
  change localChart X d x₀ x₀ - localChart X d x₀ x₀ = 0
  exact sub_self _

/-- Centering does not change the coordinate domain.
Source: Takamura, Linearization of Quotient Families, J. Math. Sci. Univ.
Tokyo 26 (2019), p. 381, translation of the coordinate chart. -/
theorem s2e_centeredLocalChart_source
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (x₀ : ComplexPoint X) :
    (s2e_centeredLocalChart X d x₀).source = (localChart X d x₀).source := by
  rw [s2e_centeredLocalChart, OpenPartialHomeomorph.trans_source]
  change (localChart X d x₀).source ∩ (localChart X d x₀) ⁻¹' Set.univ = _
  rw [Set.preimage_univ, Set.inter_univ]

/-- The centered actual chart contains the marked point, takes it to zero,
and makes every morphism fixing it complex analytic.
Source: HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AnalyticMap,
`analyticAt_localChart_symm_map`; Takamura, Linearization of Quotient Families,
J. Math. Sci. Univ. Tokyo 26 (2019), p. 381. -/
theorem s2e_centeredLocalChart_properties
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (x₀ : ComplexPoint X) :
    let C := s2e_centeredLocalChart X d x₀
    x₀ ∈ C.source ∧ C x₀ = 0 ∧
      ∀ f : X ⟶ X, Point.map f x₀ = x₀ →
        AnalyticAt ℂ (fun z => C (Point.map f (C.symm z))) 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [s2e_centeredLocalChart_source]
    exact mem_localChart_source X d x₀
  · change localChart X d x₀ x₀ - localChart X d x₀ x₀ = 0
    exact sub_self _
  · intro f hf
    change AnalyticAt ℂ (fun z : Fin d → ℂ =>
      localChart X d x₀ (Point.map f
        ((localChart X d x₀).symm (z + localChart X d x₀ x₀))) - localChart X d x₀ x₀) 0
    exact s2e_fixed_morphism_centered_coordinates_analytic X d f x₀ hf

end HodgeLean.Foundations.Program
