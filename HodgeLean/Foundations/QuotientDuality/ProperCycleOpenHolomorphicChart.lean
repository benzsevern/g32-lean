import HodgeLean.Adapters.NormalConeB4aClassOpenHolomorphic

/-! # Original vector charts transported from actual algebraic opens -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Set Topology
open HodgeLean.Adapters HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual open immersion transports vector-valued holomorphic chart coordinates to the ambient complex scheme, retaining the literal coordinate values and chart source.
Source: SGA 1, Expose XII, Proposition 3.1; a3b4a_classHolomorphic_of_openInclusion.
HC no distance; AV milestone no distance. -/
lemma properCycle_holomorphic_vector_chart_open_transport
    (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (U : X.left.Opens) [LocallyOfFiniteType (ComplexPoint.openScheme X U).hom]
    [QuasiCompact (ComplexPoint.openScheme X U).hom]
    [IsSeparated (ComplexPoint.openScheme X U).hom]
    [Nonempty (ComplexPoint (ComplexPoint.openScheme X U))] (d : ℕ)
    (e : OpenPartialHomeomorph (ComplexPoint (ComplexPoint.openScheme X U)) (Fin d → ℂ))
    (he : ∀ i, (f4_analytification (ComplexPoint.openScheme X U)).IsHolFun
      (fun z : e.source => e z i)) :
    ∃ E : OpenPartialHomeomorph (ComplexPoint X) (Fin d → ℂ),
      (∀ i, (f4_analytification X).IsHolFun (fun z : E.source => E z i)) ∧
      E.source = Point.map (ComplexPoint.openInclusion X U) '' e.source ∧
      ∀ y, E (Point.map (ComplexPoint.openInclusion X U) y) = e y := by
  let Y := ComplexPoint.openScheme X U
  let f := Point.map (ComplexPoint.openInclusion X U)
  have hf : IsOpenEmbedding f := ComplexPoint.isOpenEmbedding_map_open X U
  let a := hf.toOpenPartialHomeomorph f
  let E := a.symm.trans e
  have heval (y : ComplexPoint Y) : E (f y) = e y := by
    change e (a.symm (f y)) = e y
    rw [hf.toOpenPartialHomeomorph_left_inv f]
  have hsource : E.source = f '' e.source := by
    ext x
    change (x ∈ a.target ∧ a.symm x ∈ e.source) ↔ _
    rw [show a.target = Set.range f from hf.toOpenPartialHomeomorph_target f]
    constructor
    · intro hx
      exact ⟨a.symm x, hx.2, hf.toOpenPartialHomeomorph_right_inv f hx.1⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨⟨y, rfl⟩, ?_⟩
      simpa only [a, hf.toOpenPartialHomeomorph_left_inv f] using hy
  have hpre : f ⁻¹' E.source ⊆ e.source := by
    intro y hy
    rw [hsource] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    exact hf.injective hzy ▸ hz
  have hVU : E.source ⊆ Point.overOpen U := by
    intro x hx
    rw [hsource] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    change (Point.map (ComplexPoint.openInclusion X U) y).underlying ∈ U
    rw [Point.underlying_map]
    exact y.underlying.property
  refine ⟨E, ?_, hsource, heval⟩
  intro i
  apply a3b4a_classHolomorphic_of_openInclusion X U E.open_source hVU
    (fun x : E.source => E x i)
  have hp := anrem_isHolFun_restrict (f4_analytification Y) hpre (he i)
  convert hp using 1
  funext y
  exact congrArg (fun v => v i) (heval y.1)

end HodgeLean.Foundations.QuotientDuality
