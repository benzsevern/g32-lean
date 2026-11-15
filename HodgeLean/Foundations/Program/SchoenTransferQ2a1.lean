import HodgeLean.Foundations.Program.SchoenTransferQ2a1Proofs

/-! Implication from finite geometric simplicial data to contractible neighborhoods.
Algebraic triangulation and singular/sheaf comparison belong to later units.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators
open Filter Topology
namespace HodgeLean.Foundations.Program
/-- A small ball meets only faces incident to its center.
Source: Łojasiewicz, Triangulation of semi-analytic sets (1964), finite-polyhedron local topology; Bredon, Sheaf Theory, 2nd ed., III.1. -/
theorem s4_q2a1_incident_radius (n : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hK : K.faces.Finite) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ K.space) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ K.faces,
      (convexHull ℝ (s : Set _) ∩ Metric.ball x ε).Nonempty → x ∈ convexHull ℝ (s : Set _) :=
  s4_q2a1_incident_radius_aux n K hK x hx

example := @s4_q2a1_incident_radius

/-- Small polyhedral neighborhoods contract along straight segments.
Source: Łojasiewicz, Triangulation of semi-analytic sets (1964), finite-polyhedron local topology; Bredon, Sheaf Theory, 2nd ed., III.1. -/
theorem s4_q2a1_star_ball (n : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hK : K.faces.Finite) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ K.space) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r ≤ ε →
      StarConvex ℝ x (K.space ∩ Metric.ball x r) :=
  s4_q2a1_star_ball_aux n K hK x hx

example := @s4_q2a1_star_ball

/-- Small polyhedral ball intersections are contractible.
Source: Łojasiewicz, Triangulation of semi-analytic sets (1964), finite-polyhedron local topology; Bredon, Sheaf Theory, 2nd ed., III.1. -/
theorem s4_q2a1_contractible_ball (n : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hK : K.faces.Finite) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ K.space) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r ≤ ε →
      ContractibleSpace ↥(K.space ∩ Metric.ball x r) :=
  s4_q2a1_contractible_ball_aux n K hK x hx

example := @s4_q2a1_contractible_ball

/-- Finite polyhedra have open contractible neighborhood bases.
Source: Łojasiewicz, Triangulation of semi-analytic sets (1964), finite-polyhedron local topology; Bredon, Sheaf Theory, 2nd ed., III.1. -/
theorem s4_q2a1_open_basis (n : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hK : K.faces.Finite) (x : K.space) (U : Set K.space) (hU : U ∈ nhds x) :
    ∃ V : Set K.space, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ContractibleSpace V :=
  s4_q2a1_open_basis_aux n K hK x U hU

example := @s4_q2a1_open_basis

/-- Finite-polyhedron local contractibility supplies the topology interface.
Source: Łojasiewicz, Triangulation of semi-analytic sets (1964), finite-polyhedron local topology; Bredon, Sheaf Theory, 2nd ed., III.1. -/
theorem s4_q2a1_polyhedron (n : ℕ) (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin n)))
    (hK : K.faces.Finite) :
    StronglyLocallyContractibleSpace K.space :=
  s4_q2a1_polyhedron_aux n K hK

example := @s4_q2a1_polyhedron

end HodgeLean.Foundations.Program
