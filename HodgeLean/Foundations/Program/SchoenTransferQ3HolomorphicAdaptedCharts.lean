import HodgeLean.Foundations.Program.SchoenTransferQ3ActualAdaptedCharts
import HodgeLean.Foundations.Program.SchoenTransferQ3ComponentNormalization

/-! Holomorphic support charts adapted to the actual tangential fibres. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Filter Topology
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The actual tangential map has a holomorphic support-flattening chart
retaining its canonical normal coordinates and identifying its actual fibre. -/
theorem s4_q3_actual_holomorphic_adapted_normal_chart
    (X D T : Over (Spec ↧ℂ)) (i : D ⟶ X) (h : X ⟶ T) (r d : ℕ)
    [SmoothOfRelativeDimension r D.hom] [SmoothOfRelativeDimension d X.hom]
    [SmoothOfRelativeDimension r T.hom] [IsClosedImmersion i.left]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [Etale (i ≫ h).left] (z : ComplexPoint D) :
    ∃ e : OpenPartialHomeomorph (ComplexPoint X)
        ((Fin r → ℂ) × (Fin (d - r) → ℂ)),
      Point.map i z ∈ e.source ∧ a3b4_IsHolChart X.hom e ∧
      (∀ y ∈ e.source, e y =
        (localChart T r (Point.map (i ≫ h) z) (Point.map h y),
          (closedImmersionHolomorphicFlatteningChart X D i r d z y).2)) ∧
      (∀ y ∈ e.source, y ∈ Set.range (Point.map i) ↔ (e y).2 = 0) ∧
      ∀ y ∈ e.source, Point.map h y = Point.map (i ≫ h) z ↔
        (e y).1 = localChart T r (Point.map (i ≫ h) z) (Point.map (i ≫ h) z) := by
  obtain ⟨ZX, xq, rfl⟩ := Over.mk_surjective X
  let X : Over (Spec ↧ℂ) := Over.mk xq
  let x := Point.map i z
  let t := Point.map (i ≫ h) z
  let χT := localChart T r t
  obtain ⟨e, hxe, _, he, hflat⟩ := s4_q3_actual_support_adapted_normal_chart X D T i h r d z
  let W : Set (ComplexPoint X) := Point.map h ⁻¹' χT.source
  have hW : IsOpen W := χT.open_source.preimage (Point.continuous_map h)
  have ht : t ∈ χT.source := mem_localChart_source T r t
  have hxW : x ∈ W := by
    change Point.map h (Point.map i z) ∈ χT.source
    rw [← Point.map_comp_apply]
    exact ht
  let eW := e.restrOpen W hW
  have hxeW : x ∈ eW.source := ⟨hxe, hxW⟩
  have heW : ∀ y ∈ eW.source, eW y =
      (localChart T r t (Point.map h y),
        (closedImmersionHolomorphicFlatteningChart X D i r d z y).2) :=
    fun y hy => he y hy.1
  obtain ⟨V, hV, hxV, hhol⟩ := s4_q3_holomorphic_restriction_of_chart_analytic X d r (d - r)
    eW x hxeW (s4_q3_actual_adapted_chart_analytic X D T i h r d z eW hxeW heW)
  change Set (ComplexPoint X) at V
  let ef := eW.restrOpen V hV
  refine ⟨ef, ⟨hxeW, hxV⟩, hhol, ?_, ?_, ?_⟩
  · intro y hy
    exact he y hy.1.1
  · intro y hy
    exact hflat y hy.1.1
  · intro y hy
    have hfirst := congrArg Prod.fst (he y hy.1.1)
    change (ef y).1 = χT (Point.map h y) at hfirst
    rw [hfirst]
    constructor
    · intro hh; rw [hh]
    · intro hh
      exact χT.injOn hy.1.2 ht hh

end HodgeLean.Foundations.Program
