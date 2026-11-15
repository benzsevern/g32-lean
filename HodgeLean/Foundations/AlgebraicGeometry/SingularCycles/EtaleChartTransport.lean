import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.EtaleSectionHolomorphic
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.EtaleTopology

/-! # Holomorphic chart transport through finite étale maps

HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped Classical
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open Set Filter Topology HodgeLean.Foundations.Analytic HodgeLean.Adapters
namespace AlgebraicGeometry.SingularCycles

/-- A source holomorphic chart transports through a finite étale inverse branch with unchanged coordinates.
Source: SGA 1, Exposé XII, §1; local inverse branches and holomorphic simple roots. -/
theorem etale_chart_transport {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (f : X ⟶ Z) [IsFinite f.left] [Etale f.left] {r k : ℕ}
    (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin r → ℂ) × (Fin k → ℂ)))
    (he : a3b4_IsHolChart X.hom e) (x : ComplexPoint X) (hx : x ∈ e.source) :
    ∃ W : Set (ComplexPoint X), IsOpen W ∧ x ∈ W ∧ W ⊆ e.source ∧
      Set.InjOn (Point.map f) W ∧
      ∃ E : OpenPartialHomeomorph (ComplexPoint Z) ((Fin r → ℂ) × (Fin k → ℂ)),
        a3b4_IsHolChart Z.hom E ∧ E.source = Point.map f '' W ∧
          ∀ z ∈ W, E (Point.map f z) = e z := by
  obtain ⟨u, hxu, hu⟩ := finite_etale_local_homeomorph f x
  let W := u.source ∩ e.source
  let E := u.symm.trans e
  have hfu : ∀ z, Point.map f z = u z := congrFun hu
  have hsource : E.source = Point.map f '' W := by
    ext y
    constructor
    · intro hy
      have hyu : y ∈ u.target := hy.1
      refine ⟨u.symm y, ⟨u.map_target hyu, hy.2⟩, ?_⟩
      rw [hfu, u.right_inv hyu]
    · rintro ⟨z, hz, rfl⟩
      change Point.map f z ∈ u.target ∧ u.symm (Point.map f z) ∈ e.source
      rw [hfu, u.left_inv hz.1]
      exact ⟨u.map_source hz.1, hz.2⟩
  have hs : Continuous (fun y : E.source => u.symm y) :=
    u.continuousOn_symm.comp_continuous continuous_subtype_val (fun y => y.2.1)
  have hsection : ∀ y : E.source, Point.map f (u.symm y) = y := by
    intro y
    rw [hfu, u.right_inv y.2.1]
  have hD : ∀ y : E.source, u.symm y ∈ e.source := fun y => y.2.2
  have hE : a3b4_IsHolChart Z.hom E := by
    constructor
    · intro j
      exact etale_section_holFun f E.open_source (fun y => u.symm y) hs hsection
        (fun z : e.source => (e z).1 j) (he.1 j) hD
    · intro j
      exact etale_section_holFun f E.open_source (fun y => u.symm y) hs hsection
        (fun z : e.source => (e z).2 j) (he.2 j) hD
  refine ⟨W, u.open_source.inter e.open_source, ⟨hxu, hx⟩, Set.inter_subset_right, ?_, E,
    hE, hsource, ?_⟩
  · intro z hz z' hz' hzz'
    apply u.injOn hz.1 hz'.1
    simpa only [hfu] using hzz'
  · intro z hz
    change e (u.symm (Point.map f z)) = e z
    rw [hfu, u.left_inv hz.1]

end AlgebraicGeometry.SingularCycles
