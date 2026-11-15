import HodgeLean.Adapters.NormalConeB4aClassOpenHolomorphic

/-! # Transporting holomorphic charts from algebraic opens

Route: compose the source chart with the inverse partial homeomorphism of
the open inclusion. Its source is the image of the original source. The
holomorphic-function descent theorem gives the frozen coordinate predicate.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry Set Topology TopologicalSpace
open HodgeLean.Foundations.Analytic

/-- A holomorphic chart on an algebraic open transports to the original
ambient analytic space, retaining its source and all coordinate values. -/
theorem a3b4a_classHolomorphicChart_openTransport
    (X : Over (Spec (CommRingCat.of ℂ))) [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom] (U : X.left.Opens)
    [LocallyOfFiniteType (ComplexPoint.openScheme X U).hom]
    [QuasiCompact (ComplexPoint.openScheme X U).hom]
    [IsSeparated (ComplexPoint.openScheme X U).hom]
    [Nonempty (ComplexPoint (ComplexPoint.openScheme X U))] (r c : ℕ)
    (e : OpenPartialHomeomorph (ComplexPoint (ComplexPoint.openScheme X U))
      ((Fin r → ℂ) × (Fin c → ℂ)))
    (he : a3b4_IsHolChart (ComplexPoint.openScheme X U).hom e) :
    ∃ E : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin c → ℂ)),
      a3b4_IsHolChart X.hom E ∧
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
    change f y ∈ E.source at hy
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
  constructor
  · intro j
    apply a3b4a_classHolomorphic_of_openInclusion X U E.open_source hVU
      (fun x : E.source => (E x).1 j)
    have hp := anrem_isHolFun_restrict (f4_analytification Y) hpre (he.1 j)
    convert hp using 1
    funext y
    exact congrArg (fun v => v.1 j) (heval y.1)
  · intro j
    apply a3b4a_classHolomorphic_of_openInclusion X U E.open_source hVU
      (fun x : E.source => (E x).2 j)
    have hp := anrem_isHolFun_restrict (f4_analytification Y) hpre (he.2 j)
    convert hp using 1
    funext y
    exact congrArg (fun v => v.2 j) (heval y.1)


end HodgeLean.Adapters
