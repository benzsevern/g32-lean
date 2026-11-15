import HodgeLean.Foundations.QuotientDuality.LocalOpenHolomorphicCharts
import HodgeLean.Foundations.QuotientDuality.LocalChartDimension
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Locus
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Equidimensional

/-! Smooth-locus charts in the degree selected by a local orientation. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

theorem exists_holomorphic_chart_of_mem_smoothLocus
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (d : ℕ) (o : LocalRationalOrientation (TopCat.of (ComplexPoint X)) (2 * d))
    (x : ComplexPoint X) (hx : x ∈ Point.overOpen X.hom.smoothLocus) :
    ∃ (E : OpenPartialHomeomorph (ComplexPoint X) (Fin d → ℂ)),
      x ∈ E.source ∧
      ∀ i, (f4_analytification X).IsHolFun (fun y : E.source => E y i) := by
  letI : T2Space (ComplexPoint X) := f4_t2Space X
  let U := X.hom.smoothLocus
  let Y := openScheme X U
  letI : Nonempty U := ⟨⟨x.underlying, hx⟩⟩
  letI : Nonempty Y.left := inferInstanceAs (Nonempty U)
  letI : IsIntegral Y.left := isIntegral_of_isOpenImmersion U.ι
  letI : Smooth Y.hom := X.hom.smooth_restrict_smoothLocus
  let k := TopologicalSpace.dim Y.left
  let z := asOpenPoint X U x hx
  let E := (localChart Y k z).lift_openEmbedding (isOpenEmbedding_map_open X U)
  have hz : Point.map (openInclusion X U) z = x :=
    congrArg Subtype.val ((openHomeomorph X U).apply_symm_apply ⟨x, hx⟩)
  have hE : x ∈ E.source := ⟨z, mem_localChart_source Y k z, hz⟩
  have hdim : d = k := by
    have he := localOrientation_degree_eq_chart_dimension (TopCat.of (ComplexPoint X))
      (2 * d) o k E x hE
    omega
  subst d
  exact ⟨E, hE, open_localChart_coordinates_holomorphic X U k z⟩

#print axioms exists_holomorphic_chart_of_mem_smoothLocus
end HodgeLean.Foundations.QuotientDuality
