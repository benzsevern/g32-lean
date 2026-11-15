import HodgeLean.Foundations.QuotientDuality.ProperCycleReducedClosedChart
import HodgeLean.Foundations.QuotientDuality.ProperCycleReducedStratumCover
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ClosedImmersion

/-! # Actual bounded-dimensional charts on finite algebraic remainder marks -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Topology
namespace HodgeLean.Foundations.QuotientDuality

/-- Every original support point has a bounded complex chart on one of the actual finite reduced closed remainder images.
Source: EGA IV, 17.11.1 and Noetherian induction;
Gunning and Rossi, Analytic Functions of Several Complex Variables, chapter I.
HC no distance; AV milestone no distance. -/
lemma properCycle_reduced_mark_chart_cover
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] [NoetherianSpace X.left]
    (S : Closeds X.left) (d : ℕ) (hdim : topologicalKrullDim S ≤ d)
    (x : ComplexPoint X) (hx : x.underlying ∈ S) :
    ∃ k < (reducedSmoothStratification X.hom S).length, ∃ m : ℕ, m ≤ d ∧
      ∃ φ : OpenPartialHomeomorph
        (Set.range (Point.map (properCycle_reduced_closed_map X
          (reducedSmoothClosedFiltration X.hom S k)))) (Fin m → ℂ),
        ∃ hxS : x ∈ Set.range (Point.map (properCycle_reduced_closed_map X
          (reducedSmoothClosedFiltration X.hom S k))), (⟨x, hxS⟩ : Set.range _) ∈ φ.source := by
  obtain ⟨k, hk, z, hz⟩ := properCycle_reduced_stratum_complex_cover X S x hx
  obtain ⟨m, hm, ψ, hψ⟩ := properCycle_reduced_stratum_chart_on_remainder X S d hdim k z
  let T := reducedSmoothClosedFiltration X.hom S k
  let i := properCycle_reduced_closed_map X T
  let j := properCycle_reduced_smooth_open_map X T
  let zR := Point.map j z
  have hxEq : Point.map i zR = x := by
    change Point.map i (Point.map j z) = x
    rw [← Point.map_comp_apply]
    have hcomp : j ≫ i = reducedClosedSmoothPieceMap X T := by
      apply Over.OverMorphism.ext
      rfl
    rw [hcomp]
    exact hz
  let e := (isEmbedding_map_of_closedImmersion i).toHomeomorph
  let φ := ψ.lift_openEmbedding e.isOpenEmbedding
  refine ⟨k, hk, m, hm, φ, ⟨zR, hxEq⟩, zR, hψ, ?_⟩
  apply Subtype.ext
  exact hxEq

end HodgeLean.Foundations.QuotientDuality
