import HodgeLean.Foundations.QuotientDuality.ProperCycleReducedStratumDimension
import HodgeLean.Foundations.QuotientDuality.ProperCycleReducedMaps
import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.Basis
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Manifold

/-! # Actual complex charts on reduced remainders at their smooth-stratum points -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Topology
namespace HodgeLean.Foundations.QuotientDuality

/-- Actual bounded-dimensional affine stratum charts extend over the open smooth locus in the corresponding reduced remainder.
Source: EGA IV, 17.11.1; Gunning and Rossi, Analytic Functions of Several Complex Variables,
chapter I, holomorphic inverse function theorem.
HC no distance; AV milestone no distance. -/
lemma properCycle_reduced_stratum_chart_on_remainder
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    (S : Closeds X.left) (d : ℕ) (hdim : topologicalKrullDim S ≤ d) (k : ℕ)
    (z : ComplexPoint (Over.mk
      (reducedClosedSmoothPieceι X.hom (reducedSmoothClosedFiltration X.hom S k) ≫ X.hom))) :
    ∃ m : ℕ, m ≤ d ∧ ∃ φ : OpenPartialHomeomorph
      (ComplexPoint (Over.mk
        (reducedClosedStructureMap X.hom (reducedSmoothClosedFiltration X.hom S k)))) (Fin m → ℂ),
      Point.map (properCycle_reduced_smooth_open_map X (reducedSmoothClosedFiltration X.hom S k)) z ∈ φ.source := by
  let T := reducedSmoothClosedFiltration X.hom S k
  let Y := Over.mk (reducedClosedSmoothPieceι X.hom T ≫ X.hom)
  obtain ⟨U, hU, hzU, m, hm, hsm⟩ :=
    properCycle_reduced_stratum_affine_relativeDimension_le X S d hdim k z.underlying
  let UY := openScheme Y U
  let j := openInclusion Y U
  let zU : ComplexPoint UY := (openHomeomorph Y U).symm ⟨z, hzU⟩
  have hzmap : Point.map j zU = z := by
    change ((openHomeomorph Y U) zU).val = z
    exact congrArg Subtype.val ((openHomeomorph Y U).apply_symm_apply ⟨z, hzU⟩)
  letI : SmoothOfRelativeDimension m UY.hom := hsm
  let φ := localChart UY m zU
  letI : IsOpenImmersion j.left := by
    change IsOpenImmersion U.ι
    infer_instance
  let jC := j ≫ properCycle_reduced_smooth_open_map X T
  have hjC : IsOpenImmersion jC.left := by
    change IsOpenImmersion (j.left ≫ (properCycle_reduced_smooth_open_map X T).left)
    infer_instance
  letI := hjC
  let ψ := φ.lift_openEmbedding
    (HodgeLean.Foundations.ComplexTopology.openImmersion_points jC)
  refine ⟨m, hm, ψ, zU, mem_localChart_source UY m zU, ?_⟩
  change Point.map jC zU = _
  rw [Point.map_comp_apply, hzmap]

end HodgeLean.Foundations.QuotientDuality
