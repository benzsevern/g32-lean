import HodgeLean.Adapters.NormalConeB4aClassChartTransport

/-! # Pulling holomorphic charts back to algebraic opens

Route: compose the chart with the open inclusion's partial homeomorphism.
Regular maps pull back F4 holomorphic functions, so all chart coordinates
remain holomorphic on the inverse-image source.
-/
noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry Set Topology TopologicalSpace
open HodgeLean.Foundations.Analytic

/-- A holomorphic chart pulls back to an algebraic open, with its source and
coordinate values given by the open inclusion. -/
theorem a3b4a_classHolomorphicChart_openPullback
    (X : Over (Spec (CommRingCat.of ℂ))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] (U : X.left.Opens)
    [LocallyOfFiniteType (ComplexPoint.openScheme X U).hom]
    [QuasiCompact (ComplexPoint.openScheme X U).hom]
    [IsSeparated (ComplexPoint.openScheme X U).hom]
    [Nonempty (ComplexPoint (ComplexPoint.openScheme X U))] (r c : ℕ)
    (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin c → ℂ)))
    (he : a3b4_IsHolChart X.hom e) :
    ∃ E : OpenPartialHomeomorph (ComplexPoint (ComplexPoint.openScheme X U))
      ((Fin r → ℂ) × (Fin c → ℂ)),
      a3b4_IsHolChart (ComplexPoint.openScheme X U).hom E ∧
      E.source = Point.map (ComplexPoint.openInclusion X U) ⁻¹' e.source ∧
      ∀ y, E y = e (Point.map (ComplexPoint.openInclusion X U) y) := by
  let Y := ComplexPoint.openScheme X U
  let f := Point.map (ComplexPoint.openInclusion X U)
  have hf : IsOpenEmbedding f := ComplexPoint.isOpenEmbedding_map_open X U
  let a := hf.toOpenPartialHomeomorph f
  let E := a.trans e
  have hsource : E.source = f ⁻¹' e.source := by
    ext y
    change (y ∈ a.source ∧ e.source (a y)) ↔ e.source (f y)
    rw [show a.source = univ from rfl]
    exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩
  have hsub : E.source ⊆ f ⁻¹' e.source := hsource.le
  have hmap := f4_map_isHom (ComplexPoint.openInclusion X U)
  refine ⟨E, ?_, hsource, fun _ => rfl⟩
  constructor
  · intro j
    exact anrem_isHolFun_restrict (f4_analytification Y) hsub
      (hmap.2 e.source e.open_source (fun y : e.source => (e y).1 j) (he.1 j))
  · intro j
    exact anrem_isHolFun_restrict (f4_analytification Y) hsub
      (hmap.2 e.source e.open_source (fun y : e.source => (e y).2 j) (he.2 j))

end HodgeLean.Adapters
