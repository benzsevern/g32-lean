import HodgeLean.Adapters.NormalConeB4aClassChartTransport
import HodgeLean.Adapters.NormalConeB4aClassNormalCharts
import HodgeLean.Adapters.NormalConeB4aClassSmoothComponent
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.SmoothPair.OpenTransport

/-! # Holomorphic normal charts along a regular component

Route: lift the smooth locus as a closed immersion into its ambient open,
use its exact dimension, and transport the resulting normal chart.
-/
noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry Topology TopologicalSpace

set_option backward.isDefEq.respectTransparency false in
/-- A regular point of a component of codimension `c` has a holomorphic
flattening chart with exactly `c` normal coordinates. -/
theorem a3b4a_classComponent_exists_holomorphic_flattening
    (X : Over (Spec (CommRingCat.of ℂ))) (d c : ℕ)
    [Smooth X.hom] [SmoothOfRelativeDimension d X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom]
    (ξ : X.left) (hc : Order.coheight ξ = c)
    (y : ComplexPoint X) (hy : y.underlying ∈ closure ({ξ} : Set X.left))
    (hreg : y.underlying ∉ reducedClosedSingularRemainder X.hom
      ⟨closure {ξ}, isClosed_closure⟩) :
    ∃ e : OpenPartialHomeomorph (ComplexPoint X) ((Fin (d-c) → ℂ) × (Fin c → ℂ)),
      y ∈ e.source ∧ a3b4_IsHolChart X.hom e ∧
      ∀ x ∈ e.source, x.underlying ∈ closure ({ξ} : Set X.left) ↔ (e x).2 = 0 := by
  let S : Closeds X.left := ⟨closure {ξ}, isClosed_closure⟩
  let Y := Over.mk (reducedClosedSmoothPieceι X.hom S ≫ X.hom)
  let j : Y ⟶ X := Over.homMk (reducedClosedSmoothPieceι X.hom S) rfl
  letI : LocallyOfFiniteType Y.hom := inferInstanceAs
    (LocallyOfFiniteType (reducedClosedSmoothPieceι X.hom S ≫ X.hom))
  letI : IsImmersion j.left := inferInstanceAs (IsImmersion (reducedClosedSmoothPieceι X.hom S))
  have hyr : y ∈ Set.range (Point.map j) := by
    rw [ComplexPoint.range_map_of_isImmersion]
    change y.underlying ∈ Set.range (reducedClosedSmoothPieceι X.hom S)
    rw [reducedClosedSmoothPiece_range]
    exact ⟨hy, hreg⟩
  obtain ⟨z, rfl⟩ := hyr
  let A := (cycleComponentι X.left ξ ≫ X.hom).smoothLocus
  let C := Over.mk (cycleComponentι X.left ξ ≫ X.hom)
  letI : LocallyOfFiniteType C.hom := inferInstanceAs
    (LocallyOfFiniteType (cycleComponentι X.left ξ ≫ X.hom))
  let zC : ComplexPoint C := Point.map (ComplexPoint.openInclusion C A) z
  have hzClosed : IsClosed {zC.underlying} :=
    ((pointEquivClosedPoint C.hom) ⟨zC.left, Over.w zC⟩).2
  letI : SmoothOfRelativeDimension (d-c) Y.hom :=
    a3b4a_classComponent_smoothLocus_relativeDimension X ξ hc zC.underlying
      z.underlying.property hzClosed
  let O := closedImmersionSourceOpenTarget (cycleComponentι X.left ξ) A
  let OX := ComplexPoint.openScheme X O
  let i₀ := closedImmersionSourceOpenLift (cycleComponentι X.left ξ) A
  have hi : i₀ ≫ OX.hom = Y.hom := by
    change i₀ ≫ (O.ι ≫ X.hom) = (A.ι ≫ cycleComponentι X.left ξ) ≫ X.hom
    rw [← Category.assoc, closedImmersionSourceOpenLift_ι]
  let i : Y ⟶ OX := Over.homMk i₀ hi
  letI : IsClosedImmersion i.left :=
    closedImmersionSourceOpenLift_isClosedImmersion (cycleComponentι X.left ξ) A
  letI : SmoothOfRelativeDimension d OX.hom := by
    change SmoothOfRelativeDimension d (O.ι ≫ X.hom)
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 d O.ι X.hom
  letI : LocallyOfFiniteType OX.hom := inferInstanceAs (LocallyOfFiniteType (O.ι ≫ X.hom))
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  letI : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  letI : IsNoetherian X.left := ⟨⟩
  letI : QuasiCompact OX.hom := inferInstanceAs (QuasiCompact (O.ι ≫ X.hom))
  letI : IsSeparated OX.hom := inferInstanceAs (IsSeparated (O.ι ≫ X.hom))
  letI : Nonempty (ComplexPoint OX) := ⟨Point.map i z⟩
  have hcd : c ≤ d := by
    have h := SmoothOfRelativeDimension.coheight_le_complex (f := X.hom) (d := d) ξ
    rw [hc] at h
    exact_mod_cast h
  have hdc : d - (d-c) = c := by omega
  have hex := a3b4a_classSmoothClosedImmersion_exists_holomorphic_flattening OX Y i (d-c) d z
  rw [hdc] at hex
  obtain ⟨e, hze, he, hflat⟩ := hex
  obtain ⟨E, hE, hsource, heval⟩ :=
    a3b4a_classHolomorphicChart_openTransport X O (d-c) c e he
  let f := Point.map (ComplexPoint.openInclusion X O)
  have hpoint : f (Point.map i z) = Point.map j z := by
    apply Over.OverMorphism.ext
    change (z.left ≫ i₀) ≫ O.ι = z.left ≫ (A.ι ≫ cycleComponentι X.left ξ)
    rw [Category.assoc, closedImmersionSourceOpenLift_ι]
  have hS : f ⁻¹' (Point.underlying ⁻¹' (S : Set X.left)) = Set.range (Point.map i) := by
    rw [ComplexPoint.range_map_of_isImmersion_of_comm OX Y i]
    change _ = (Point.underlying : ComplexPoint OX → OX.left) ⁻¹' Set.range i₀
    rw [range_closedImmersionSourceOpenLift, range_cycleComponentι]
    rfl
  refine ⟨E, ?_, hE, ?_⟩
  · rw [hsource, ← hpoint]
    exact ⟨Point.map i z, hze, rfl⟩
  · intro x hx
    rw [hsource] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    rw [heval]
    change w ∈ f ⁻¹' (Point.underlying ⁻¹' (S : Set X.left)) ↔ _
    rw [hS]
    exact hflat w hw

end HodgeLean.Adapters
