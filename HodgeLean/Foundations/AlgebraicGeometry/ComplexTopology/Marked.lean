import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.MarkedChecks
import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.MarkedProofs

/-! Designated-subset local charts, their overlap laws and finite intersections.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
namespace HodgeLean.Foundations.ComplexTopology.Marked

open CheckData

/-- Affine regular.
Source: Hartshorne, Algebraic Geometry, II.2, Proposition 2.3; II.3. -/
theorem affine_regular (X : Over (Spec ↧ℂ)) [IsAffine X.left] [LocallyOfFiniteType X.hom]
    {r : ℕ} (f : Fin r → Γ(X.left, ⊤)) :
    ∃ c : RegularChart X f, c.domain = ⊤ :=
  affine_regular_aux X f

example : MvPolynomial.eval
    (coordinate regularPlane.toChart planePoint (by trivial)).val
      (regularPlane.marked (0 : Fin 2)) = (1 : ℂ) ∧
    ¬ MvPolynomial.eval
      (coordinate regularPlane.toChart planePoint (by trivial)).val
        (regularPlane.marked (0 : Fin 2)) = (2 : ℂ) := affine_regular_falsification

/-- Local subsets.
Source: Hartshorne, Algebraic Geometry, II.3 and II.5; Bochnak–Coste–Roy, Theorem 9.2.1. -/
theorem local_subsets (X : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    {r : ℕ} (Z : Fin r → Over (Spec ↧ℂ)) (i : ∀ j, Z j ⟶ X)
    [∀ j, IsClosedImmersion (i j).left] (x : ComplexPoint X) :
    ∃ c : SubsetChart (ComplexPoint X) (fun j => Set.range (Point.map (i j))),
      x ∈ c.domain :=
  local_subsets_aux X Z i x

example : o ∈ markedNode.domain ∧
    o ∈ D (0 : Fin 2) ∩ D (1 : Fin 2) ∧ a ∈ D (1 : Fin 2) ∧
    b ∈ D (0 : Fin 2) ∧ ¬ a ∈ D (0 : Fin 2) := local_subsets_falsification

/-- Transition continuous.
Source: Munkres, Topology, §16, subspace topology. -/
theorem transition_continuous {X : Type*} [TopologicalSpace X] (c d : Chart X) :
    Continuous (transition c d) ∧ IsOpen (overlap c d) :=
  transition_continuous_aux c d

example : Continuous (transition c d) ∧ IsOpen (overlap c d) ∧
    (transition c d ⟨a, by trivial⟩).val (0 : Fin 2) = (-1 : ℂ) :=
  transition_continuous_example

/-- Transition cocycle.
Source: Munkres, Topology, §§16 and 18, composition of chart maps. -/
theorem transition_cocycle {X : Type*} [TopologicalSpace X] (c d e : Chart X)
    (x : X) (hc : x ∈ c.domain) (hd : x ∈ d.domain) (he : x ∈ e.domain) :
    transition c c ⟨coordinate c x hc, by simpa [coordinate, overlap]⟩ = coordinate c x hc ∧
    transition d e ⟨transition c d ⟨coordinate c x hc,
      by simpa [coordinate, overlap] using hd⟩,
      by simpa [transition, coordinate, overlap] using he⟩ =
    transition c e ⟨coordinate c x hc, by simpa [coordinate, overlap] using he⟩ :=
  transition_cocycle_aux c d e x hc hd he

example :
    transition c c ⟨coordinate c a (by trivial), by trivial⟩ =
      coordinate c a (by trivial) ∧
    transition d c ⟨transition c d
      ⟨coordinate c a (by trivial), by trivial⟩, by trivial⟩ =
      transition c c ⟨coordinate c a (by trivial), by trivial⟩ ∧
    (transition c d ⟨a, by trivial⟩).val (0 : Fin 2) = (-1 : ℂ) :=
  transition_cocycle_example

/-- Transition subsets.
Source: Hartshorne, Algebraic Geometry, II.5; Munkres, Topology, §16. -/
theorem transition_subsets {X : Type*} [TopologicalSpace X] {r : ℕ} {D : Fin r → Set X}
    (c d : SubsetChart X D) (z : overlap c.toChart d.toChart) (j : Fin r) :
    (∀ k, MvPolynomial.eval z.val.val (c.marked j k) = (0 : ℂ)) ↔
      ∀ k, MvPolynomial.eval (transition c.toChart d.toChart z).val (d.marked j k) = (0 : ℂ) :=
  transition_subsets_aux c d z j

example : MvPolynomial.eval (transition markedNode.toChart markedNode.toChart
      ⟨a, by trivial⟩).val (markedNode.marked (1 : Fin 2) (0 : Fin 1)) = (0 : ℂ) ∧
    ¬ MvPolynomial.eval a.val (markedNode.marked (0 : Fin 2) (0 : Fin 1)) = (0 : ℂ) := transition_subsets_falsification

/-- Finite intersections retain their incidence in the chart.
Source: Hartshorne, Algebraic Geometry, II.5; elementary set intersections. -/
theorem intersection_subsets {X : Type*} [TopologicalSpace X] {r : ℕ} {D : Fin r → Set X}
    (c : SubsetChart X D) (x : c.domain) (J : Finset (Fin r)) :
    (∀ j ∈ J, x.val ∈ D j) ↔
      ∀ j ∈ J, ∀ k, MvPolynomial.eval (c.coordinates x).val (c.marked j k) = (0 : ℂ) :=
  intersection_subsets_aux c x J

example :
    (∀ j : Fin 2, ∀ k, MvPolynomial.eval
      (coordinate markedNode.toChart o (by trivial)).val (markedNode.marked j k) = (0 : ℂ)) ∧
    ¬ (∀ j : Fin 2, ∀ k, MvPolynomial.eval
      (coordinate markedNode.toChart a (by trivial)).val (markedNode.marked j k) = (0 : ℂ)) :=
  intersection_subsets_falsification

end HodgeLean.Foundations.ComplexTopology.Marked
