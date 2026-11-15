import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.Support
import HodgeLean.Foundations.AnalyticDivisorAlgebraic24Proofs

/-! # Separated component points in analytic neighbourhoods

HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped Classical
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace HodgeLean.Adapters
open Set Filter Topology
namespace AlgebraicGeometry.SingularCycles

/-- Every analytic neighbourhood meeting an antichain cycle contains a point of exactly one component.
Source: Fulton, Intersection Theory, second edition, §1.5; gaga24_dense_overOpen. -/
theorem cycle_exists_separated_point_in_open
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (γ : AlgebraicCycle X.left ℚ)
    (hanti : ∀ ξ ∈ γ.support, ∀ η ∈ γ.support,
      ξ ∈ closure ({η} : Set X.left) → ξ = η)
    (V : Set (ComplexPoint X)) (hV : IsOpen V) (x : ComplexPoint X)
    (hxV : x ∈ V) (hxS : x ∈ a3b4_cycleSupport X.hom γ) :
    ∃ (ξ : X.left) (y : ComplexPoint X), ξ ∈ γ.support ∧ y ∈ V ∧
      y.underlying ∈ closure ({ξ} : Set X.left) ∧
      ∀ η ∈ γ.support, η ≠ ξ → y.underlying ∉ closure ({η} : Set X.left) := by
  haveI : CompactSpace X.left := a3b4_compactSpace X.hom
  obtain ⟨ξ, hξ, hxξ⟩ := Set.mem_iUnion₂.mp hxS
  let T : Set X.left := γ.support \ {ξ}
  let B : Set X.left := ⋃ η ∈ T, closure ({η} : Set X.left)
  have hTf : T.Finite := (a3b2_support_finite γ).subset Set.diff_subset
  have hBc : IsClosed B := hTf.isClosed_biUnion (fun _ _ => isClosed_closure)
  let O : X.left.Opens := ⟨Bᶜ, hBc.isOpen_compl⟩
  have hξO : ξ ∈ O := by
    intro h
    obtain ⟨η, hη, hcl⟩ := Set.mem_iUnion₂.mp h
    have heq := hanti ξ hξ η hη.1 hcl
    exact hη.2 (Set.mem_singleton_iff.mpr heq.symm)
  let Y := Over.mk (cycleComponentι X.left ξ ≫ X.hom)
  let i : Y ⟶ X := Over.homMk (cycleComponentι X.left ξ) rfl
  haveI : IsIntegral Y.left := inferInstanceAs (IsIntegral (cycleComponent X.left ξ))
  haveI : LocallyOfFiniteType Y.hom :=
    inferInstanceAs (LocallyOfFiniteType (cycleComponentι X.left ξ ≫ X.hom))
  haveI : IsClosedImmersion i.left := inferInstanceAs (IsClosedImmersion (cycleComponentι X.left ξ))
  have hξrange : ξ ∈ Set.range i.left := by
    change ξ ∈ Set.range (cycleComponentι X.left ξ)
    rw [range_cycleComponentι]
    exact subset_closure (Set.mem_singleton ξ)
  obtain ⟨z, hz⟩ := hξrange
  let U := i.left ⁻¹ᵁ O
  haveI : Nonempty U := ⟨⟨z, by change i.left z ∈ O; rw [hz]; exact hξO⟩⟩
  have hd := HodgeLean.Foundations.AnalyticDivisorAlgebraic24.gaga24_dense_overOpen Y U
  have hxrange : x ∈ Set.range (Point.map i) := by
    rw [ComplexPoint.range_map_of_isImmersion_of_comm X Y i]
    change x.underlying ∈ Set.range (cycleComponentι X.left ξ)
    rwa [range_cycleComponentι]
  obtain ⟨z₀, hz₀⟩ := hxrange
  have hV' : IsOpen (Point.map i ⁻¹' V) := hV.preimage (Point.continuous_map i)
  have hzV : z₀ ∈ Point.map i ⁻¹' V := by
    change Point.map i z₀ ∈ V
    rwa [hz₀]
  obtain ⟨w, hwU, hwV⟩ := hd.inter_nhds_nonempty (hV'.mem_nhds hzV)
  refine ⟨ξ, Point.map i w, hξ, hwV, ?_, ?_⟩
  · have hr : (Point.map i w).underlying ∈ Set.range (cycleComponentι X.left ξ) :=
      ⟨w.underlying, rfl⟩
    rwa [range_cycleComponentι] at hr
  · intro η hη hne hcl
    have hwo : (Point.map i w).underlying ∈ O := hwU
    apply hwo
    exact Set.mem_iUnion₂.mpr ⟨η, ⟨hη, by simpa only [Set.mem_singleton_iff] using hne⟩, hcl⟩

end AlgebraicGeometry.SingularCycles
