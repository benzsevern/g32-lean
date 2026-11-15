import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Finite-polyhedron neighborhoods in Euclidean space.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open Filter Topology
namespace HodgeLean.Foundations.ComplexTopology
/-- A small ball meets only faces incident to its center.
Source: Łojasiewicz, Triangulation of semi-analytic sets (1964), finite-polyhedron local topology; Bredon, Sheaf Theory, 2nd ed., III.1. -/
theorem polyhedron_incident_radius (n : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hK : K.faces.Finite) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ K.space) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ K.faces,
      (convexHull ℝ (s : Set _) ∩ Metric.ball x ε).Nonempty → x ∈ convexHull ℝ (s : Set _) := by
  classical
  let A : Set (EuclideanSpace ℝ (Fin n)) :=
    ⋃ s ∈ {s ∈ K.faces | x ∉ convexHull ℝ (s : Set _)}, convexHull ℝ (s : Set _)
  have hA : IsClosed A := by
    apply Set.Finite.isClosed_biUnion (hK.subset (Set.sep_subset _ _))
    intro s hs
    exact s.finite_toSet.isClosed_convexHull ℝ
  have hxA : x ∉ A := by
    simp only [A, Set.mem_iUnion, Set.mem_ofPred_eq, not_exists]
    intro s hs
    exact hs.2
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hA.isOpen_compl.mem_nhds hxA)
  refine ⟨ε, hε, ?_⟩
  intro s hs ⟨y, hy, hyball⟩
  by_contra hxs
  exact hball hyball (Set.mem_iUnion₂.mpr ⟨s, ⟨hs, hxs⟩, hy⟩)

/-- Small polyhedral neighborhoods contract along straight segments.
Source: Łojasiewicz, Triangulation of semi-analytic sets (1964), finite-polyhedron local topology; Bredon, Sheaf Theory, 2nd ed., III.1. -/
theorem polyhedron_star_ball (n : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hK : K.faces.Finite) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ K.space) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r ≤ ε →
      StarConvex ℝ x (K.space ∩ Metric.ball x r) := by
  obtain ⟨ε, hε, hincident⟩ := polyhedron_incident_radius n K hK x hx
  refine ⟨ε, hε, ?_⟩
  intro r hr hre y hy a b ha hb hab
  obtain ⟨s, hs, hys⟩ := K.mem_space_iff.mp hy.1
  have hxs := hincident s hs ⟨y, hys, Metric.ball_subset_ball hre hy.2⟩
  exact ⟨K.mem_space_iff.mpr ⟨s, hs, (convex_convexHull ℝ _) hxs hys ha hb hab⟩,
    (convex_ball x r) (Metric.mem_ball_self hr) hy.2 ha hb hab⟩

/-- Small polyhedral ball intersections are contractible.
Source: Łojasiewicz, Triangulation of semi-analytic sets (1964), finite-polyhedron local topology; Bredon, Sheaf Theory, 2nd ed., III.1. -/
theorem polyhedron_contractible_ball (n : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hK : K.faces.Finite) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ K.space) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r ≤ ε →
      ContractibleSpace ↥(K.space ∩ Metric.ball x r) := by
  obtain ⟨ε, hε, hstar⟩ := polyhedron_star_ball n K hK x hx
  exact ⟨ε, hε, fun r hr hre =>
    (hstar r hr hre).contractibleSpace ⟨x, hx, Metric.mem_ball_self hr⟩⟩

/-- Finite polyhedra have open contractible neighborhood bases.
Source: Łojasiewicz, Triangulation of semi-analytic sets (1964), finite-polyhedron local topology; Bredon, Sheaf Theory, 2nd ed., III.1. -/
theorem polyhedron_open_basis (n : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hK : K.faces.Finite) (x : K.space) (U : Set K.space) (hU : U ∈ nhds x) :
    ∃ V : Set K.space, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ContractibleSpace V := by
  obtain ⟨ε, hε, hc⟩ := polyhedron_contractible_ball n K hK x x.property
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp hU
  let r := min ε δ
  have hr : 0 < r := lt_min hε hδ
  have := hc r hr (min_le_left _ _)
  let e : (Metric.ball x r) ≃ₜ ↥(K.space ∩ Metric.ball (x : EuclideanSpace ℝ (Fin n)) r) :=
    { toFun := fun y => ⟨y.1.1, y.1.2, y.2⟩
      invFun := fun y => ⟨⟨y.1, y.2.1⟩, y.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  exact ⟨Metric.ball x r, Metric.isOpen_ball, Metric.mem_ball_self hr,
    (Metric.ball_subset_ball (min_le_right _ _)).trans hδU,
    e.contractibleSpace_iff.mpr inferInstance⟩


end HodgeLean.Foundations.ComplexTopology
