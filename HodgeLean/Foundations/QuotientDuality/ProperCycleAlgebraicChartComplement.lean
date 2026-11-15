import HodgeLean.RealDefs.Port.AlgebraicTopology.LocalHomology.ChartFundamentalClassGenerator
import HodgeLean.Foundations.QuotientDuality.ProperCycleAlgebraicOpenStratum
import HodgeLean.Foundations.QuotientDuality.ProperCycleChartLocalVanishing

/-! # Original complex charts meet complements of smaller algebraic supports -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular
open TopologicalSpace Topology
namespace HodgeLean.Foundations.QuotientDuality

/-- Every nonempty original chart-open meets the complement of an algebraic support of strictly smaller complex dimension.
Source: properCycle_algebraic_support_open_stratum_chart; properCycle_neighborhood_embedding_local_homology_iso; properCycle_chart_local_homology_vanishes.
HC no distance; AV milestone no distance. -/
theorem properCycle_chart_open_meets_algebraic_complement
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] [NoetherianSpace X.left]
    [T2Space (ComplexPoint X)] (S : Closeds X.left) (b : ℕ)
    (hdim : topologicalKrullDim S ≤ b) (d : ℕ) (hbd : b < d)
    (e : OpenPartialHomeomorph (ComplexPoint X) (Fin d → ℂ))
    (P : Opens (ComplexPoint X)) (hP : (P : Set (ComplexPoint X)).Nonempty)
    (hPe : (P : Set (ComplexPoint X)) ⊆ e.source) :
    ∃ x : ComplexPoint X, x ∈ P ∧ x.underlying ∉ S := by
  classical
  by_contra hn
  have hPS : ∀ x ∈ P, x.underlying ∈ S := by
    intro x hx
    by_contra hs
    exact hn ⟨x, hx, hs⟩
  obtain ⟨k, m, hm, ψ, z, hz, hzP, hnb⟩ :=
    properCycle_algebraic_support_open_stratum_chart X S b hdim P hP hPS
  let T := reducedSmoothClosedFiltration X.hom S k
  let R := Over.mk (reducedClosedStructureMap X.hom T)
  let i := properCycle_reduced_closed_map X T
  letI : T1Space (ComplexPoint R) := (isEmbedding_map_of_closedImmersion i).t1Space
  let H := properCycle_neighborhood_embedding_local_homology_iso
    (TopCat.of (ComplexPoint R)) (TopCat.of (ComplexPoint X)) (Point.map i)
    (isEmbedding_map_of_closedImmersion i) z hnb (2*m)
  letI : Subsingleton (orientationGroup (TopCat.of (ComplexPoint X)) (2*m) (Point.map i z)) :=
    properCycle_chart_local_homology_vanishes (TopCat.of (ComplexPoint X)) d e
      (Point.map i z) (hPe hzP) (2*m) (by omega)
  have hzero : H.hom (localClassOfChart m ψ z hz) = 0 := Subsingleton.elim _ _
  apply localClassOfChart_ne_zero m ψ z hz
  apply H.toLinearEquiv.injective
  change H.hom (localClassOfChart m ψ z hz) = H.hom 0
  rw [map_zero]
  exact hzero

end HodgeLean.Foundations.QuotientDuality
