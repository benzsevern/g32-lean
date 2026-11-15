import HodgeLean.Adapters.NormalConeB4aClassComponentChartsLocal
import HodgeLean.Foundations.AnalyticDivisorAlgebraic24Proofs

/-! # Regular component points in analytic neighborhoods

Route: the integral reduced component has a nonempty smooth Zariski open.
Analytic density of nonempty algebraic opens gives a regular point in every
ambient analytic neighborhood meeting the component.
-/
noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry Set Topology TopologicalSpace

/-- Every analytic open meeting a component contains a smooth point of that
component, without projectivity or ambient integrality. -/
theorem a3b4a_classComponent_exists_regular_in_open
    (X : Over (Spec (CommRingCat.of ℂ))) [LocallyOfFiniteType X.hom]
    (ξ : X.left) (V : Set (ComplexPoint X)) (hV : IsOpen V)
    (x : ComplexPoint X) (hxV : x ∈ V) (hxξ : x.underlying ∈ closure ({ξ} : Set X.left)) :
    ∃ y : ComplexPoint X, y ∈ V ∧ y.underlying ∈ closure ({ξ} : Set X.left) ∧
      y.underlying ∉ reducedClosedSingularRemainder X.hom ⟨closure {ξ}, isClosed_closure⟩ := by
  let Y := Over.mk (cycleComponentι X.left ξ ≫ X.hom)
  let i : Y ⟶ X := Over.homMk (cycleComponentι X.left ξ) rfl
  letI : IsIntegral Y.left := inferInstanceAs (IsIntegral (cycleComponent X.left ξ))
  letI : LocallyOfFiniteType Y.hom :=
    inferInstanceAs (LocallyOfFiniteType (cycleComponentι X.left ξ ≫ X.hom))
  letI : IsClosedImmersion i.left := inferInstanceAs (IsClosedImmersion (cycleComponentι X.left ξ))
  have hxrange : x ∈ Set.range (Point.map i) := by
    rw [ComplexPoint.range_map_of_isImmersion_of_comm X Y i]
    change x.underlying ∈ Set.range (cycleComponentι X.left ξ)
    rwa [range_cycleComponentι]
  obtain ⟨z, hz⟩ := hxrange
  let U := Y.hom.smoothLocus
  letI : Nonempty U := ⟨⟨genericPoint Y.left, Y.hom.genericPoint_mem_smoothLocus_of_perfectField⟩⟩
  have hd := HodgeLean.Foundations.AnalyticDivisorAlgebraic24.gaga24_dense_overOpen Y U
  have hO : IsOpen (Point.map i ⁻¹' V) := hV.preimage (Point.continuous_map i)
  have hzO : z ∈ Point.map i ⁻¹' V := by
    change Point.map i z ∈ V
    rwa [hz]
  obtain ⟨w, hwU, hwV⟩ := hd.inter_nhds_nonempty (hO.mem_nhds hzO)
  refine ⟨Point.map i w, hwV, ?_, ?_⟩
  · have hr : (Point.map i w).underlying ∈ Set.range (cycleComponentι X.left ξ) :=
      ⟨w.underlying, rfl⟩
    rwa [range_cycleComponentι] at hr
  · rintro ⟨v, hv, heq⟩
    have hveq : v = w.underlying := (cycleComponentι X.left ξ).isClosedEmbedding.injective heq
    subst v
    exact hv hwU

end HodgeLean.Adapters
