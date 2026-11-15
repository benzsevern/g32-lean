import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Manifold

/-! # Actual zero-dimensional analytic chart domains

The source of a zero-dimensional manifold chart is an isolated point.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry Topology
namespace HodgeLean.Foundations.TubularEuler

theorem complexPoint_discreteTopology_of_smooth_zero
    (X : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 0 X.hom] :
    DiscreteTopology (ComplexPoint X) := by
  apply discreteTopology_iff_isOpen_singleton.mpr
  intro x
  let e := ComplexPoint.localChart X 0 x
  have hx : x ∈ e.source := ComplexPoint.mem_localChart_source X 0 x
  have hs : e.source = {x} := by
    apply Set.ext
    intro y
    constructor
    · intro hy
      exact Set.mem_singleton_iff.mpr (e.injOn hy hx (Subsingleton.elim _ _))
    · intro hy
      rw [Set.mem_singleton_iff.mp hy]
      exact hx
  rw [← hs]
  exact e.open_source

def isolatedPointChart {X F : Type*} [TopologicalSpace X] [TopologicalSpace F]
    [Unique F] (x : X) (hx : IsOpen ({x} : Set X)) : OpenPartialHomeomorph X F where
  toPartialEquiv := {
    toFun := fun _ => default
    invFun := fun _ => x
    source := {x}
    target := Set.univ
    map_source' := fun _ _ => Set.mem_univ _
    map_target' := fun _ _ => Set.mem_singleton x
    left_inv' := fun _ hy => (Set.mem_singleton_iff.mp hy).symm
    right_inv' := fun _ _ => Subsingleton.elim _ _ }
  open_source := hx
  open_target := isOpen_univ
  continuousOn_toFun := continuousOn_const
  continuousOn_invFun := continuousOn_const

#print axioms complexPoint_discreteTopology_of_smooth_zero
#print axioms isolatedPointChart

end HodgeLean.Foundations.TubularEuler
