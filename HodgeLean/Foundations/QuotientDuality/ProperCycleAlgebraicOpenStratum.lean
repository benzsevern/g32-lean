import HodgeLean.Foundations.QuotientDuality.ProperCycleReducedClosedChart
import HodgeLean.Foundations.QuotientDuality.ProperCycleReducedStratumCover
import HodgeLean.Foundations.QuotientDuality.ProperCycleNeighborhoodEmbedding

/-! # Actual smooth remainder charts inside an original open algebraic support -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Topology
namespace HodgeLean.Foundations.QuotientDuality

/-- A nonempty original open contained in a dimension-bounded algebraic support meets an actual smooth remainder chart whose image is an ambient neighborhood there.
Source: reducedSmoothClosedFiltration_length; reducedSmoothClosedFiltration_layer; properCycle_reduced_stratum_chart_on_remainder.
HC no distance; AV milestone no distance. -/
theorem properCycle_algebraic_support_open_stratum_chart
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] [NoetherianSpace X.left]
    (S : Closeds X.left) (b : ℕ) (hdim : topologicalKrullDim S ≤ b)
    (P : Opens (ComplexPoint X)) (hP : (P : Set (ComplexPoint X)).Nonempty)
    (hPS : ∀ x ∈ P, x.underlying ∈ S) :
    ∃ k m : ℕ, m ≤ b ∧
      ∃ e : OpenPartialHomeomorph
        (ComplexPoint (Over.mk (reducedClosedStructureMap X.hom
          (reducedSmoothClosedFiltration X.hom S k)))) (Fin m → ℂ),
      ∃ z : ComplexPoint (Over.mk (reducedClosedStructureMap X.hom
          (reducedSmoothClosedFiltration X.hom S k))), z ∈ e.source ∧
        Point.map (properCycle_reduced_closed_map X (reducedSmoothClosedFiltration X.hom S k)) z ∈ P ∧
        Set.range (Point.map (properCycle_reduced_closed_map X
          (reducedSmoothClosedFiltration X.hom S k))) ∈
          𝓝 (Point.map (properCycle_reduced_closed_map X (reducedSmoothClosedFiltration X.hom S k)) z) := by
  classical
  let A (k : ℕ) : Set (ComplexPoint X) :=
    {x | x.underlying ∈ reducedSmoothClosedFiltration X.hom S k}
  have hrange (k : ℕ) : Set.range (Point.map (properCycle_reduced_closed_map X
      (reducedSmoothClosedFiltration X.hom S k))) = A k := by
    rw [range_map_of_closedImmersion]
    change {x : ComplexPoint X | x.underlying ∈ Set.range
      (reducedClosedSubschemeι (reducedSmoothClosedFiltration X.hom S k))} = _
    rw [range_reducedClosedSubschemeι]
    rfl
  have hclosed (k : ℕ) : IsClosed (A k) := by
    rw [← hrange]
    exact isClosed_range_map_of_closedImmersion _
  have hzero : (P : Set (ComplexPoint X)) ⊆ A 0 := by
    intro x hx
    change x.underlying ∈ reducedSmoothClosedFiltration X.hom S 0
    rw [reducedSmoothClosedFiltration_zero]
    exact hPS x hx
  have hlast : A (reducedSmoothStratification X.hom S).length = ∅ := by
    ext x
    change (x.underlying ∈ reducedSmoothClosedFiltration X.hom S
      (reducedSmoothStratification X.hom S).length) ↔ False
    rw [reducedSmoothClosedFiltration_length]
    rfl
  have hex : ∃ k : ℕ, ¬ (P : Set (ComplexPoint X)) ⊆ A k := by
    refine ⟨(reducedSmoothStratification X.hom S).length, ?_⟩
    rw [hlast]
    intro h
    obtain ⟨x, hx⟩ := hP
    exact h hx
  have hn0 : Nat.find hex ≠ 0 := by
    intro he
    apply Nat.find_spec hex
    simpa only [he] using hzero
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hPk : (P : Set (ComplexPoint X)) ⊆ A k := by
    by_contra hn
    exact Nat.find_min hex (by omega) hn
  have hnot : ¬ (P : Set (ComplexPoint X)) ⊆ A (k+1) := by
    simpa only [hk] using Nat.find_spec hex
  obtain ⟨x, hxP, hxnot⟩ := Set.not_subset.mp hnot
  have hxk : x.underlying ∈ reducedSmoothClosedFiltration X.hom S k := hPk hxP
  have hxrange : x ∈ Set.range (Point.map (reducedClosedSmoothPieceMap X
      (reducedSmoothClosedFiltration X.hom S k))) := by
    rw [range_map_of_isImmersion X]
    change x.underlying ∈ Set.range (reducedClosedSmoothPieceι X.hom
      (reducedSmoothClosedFiltration X.hom S k))
    rw [reducedSmoothClosedFiltration_layer]
    exact ⟨hxk, hxnot⟩
  obtain ⟨z, hzx⟩ := hxrange
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
    exact hzx
  obtain ⟨m, hm, e, he⟩ := properCycle_reduced_stratum_chart_on_remainder X S b hdim k z
  let W : Opens (ComplexPoint X) := P ⊓ ⟨(A (k+1))ᶜ, (hclosed (k+1)).isOpen_compl⟩
  have hxW : x ∈ W := ⟨hxP, hxnot⟩
  have hWrange : (W : Set (ComplexPoint X)) ⊆ Set.range (Point.map i) := by
    intro y hy
    rw [hrange]
    exact hPk hy.1
  have hnb : Set.range (Point.map i) ∈ 𝓝 (Point.map i zR) := by
    rw [hxEq]
    exact Filter.mem_of_superset (W.isOpen.mem_nhds hxW) hWrange
  exact ⟨k, m, hm, e, zR, he, by rwa [hxEq], hnb⟩

end HodgeLean.Foundations.QuotientDuality
