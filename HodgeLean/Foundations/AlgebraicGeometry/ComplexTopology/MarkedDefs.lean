import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineSpace
import Mathlib
import HodgeConjecture.Definitions.AlgebraicGeometry.ComplexPoint.Basic
import HodgeLean.Foundations.AlgebraicGeometry.ComplexTopology.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Designated polynomial subsets and chart transitions for complex point spaces.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
namespace HodgeLean.Foundations.ComplexTopology.Marked

/-- A chart retains its open domain, polynomial carrier and actual homeomorphism.
Source: Hartshorne, Algebraic Geometry, II.2; Bochnak–Coste–Roy, §9.2. -/
structure Chart (X : Type*) [TopologicalSpace X] where
  domain : Opens X
  n : ℕ
  m : ℕ
  equations : Fin m → MvPolynomial (Fin n) ℂ
  coordinates : domain ≃ₜ zeroSet equations

/-- Coordinates of a point in the specified domain.
Source: Munkres, Topology, §16. -/
def coordinate {X : Type*} [TopologicalSpace X] (c : Chart X)
    (x : X) (hx : x ∈ c.domain) : zeroSet c.equations := c.coordinates ⟨x, hx⟩

/-- The domain of a transition in source coordinates.
Source: Munkres, Topology, §16. -/
def overlap {X : Type*} [TopologicalSpace X] (c d : Chart X) :
    Set (zeroSet c.equations) := {z | (c.coordinates.symm z).val ∈ d.domain}

/-- Transition uses the same underlying point in the two chart domains.
Source: Munkres, Topology, §16. -/
def transition {X : Type*} [TopologicalSpace X] (c d : Chart X)
    (z : overlap c d) : zeroSet d.equations :=
  d.coordinates ⟨(c.coordinates.symm z.val).val, z.property⟩

/-- Polynomial coordinates of every designated regular function, including its value.
Source: Hartshorne, Algebraic Geometry, II.2, Proposition 2.3. -/
structure RegularChart (X : Over (Spec ↧ℂ)) {r : ℕ}
    (f : Fin r → Γ(X.left, ⊤)) extends Chart (ComplexPoint X) where
  marked : Fin r → MvPolynomial (Fin n) ℂ
  evaluation : ∀ (x : domain) (j : Fin r),
    MvPolynomial.eval (coordinates x).val (marked j) = Point.evaluate ⊤ (f j) x.val

/-- Polynomial vanishing locus inside the retained carrier.
Source: Bochnak–Coste–Roy, Real Algebraic Geometry, §2.1. -/
def locus {n m : ℕ} (p : Fin m → MvPolynomial (Fin n) ℂ)
    (q : MvPolynomial (Fin n) ℂ) : Set (zeroSet p) :=
  {z | MvPolynomial.eval z.val q = (0 : ℂ)}

/-- A finite family of designated subsets retained as polynomial zero loci.
Source: Hartshorne, Algebraic Geometry, II.5 (ideal sheaves). -/
structure SubsetChart (X : Type*) [TopologicalSpace X] {r : ℕ}
    (D : Fin r → Set X) extends Chart X where
  count : Fin r → ℕ
  marked : (j : Fin r) → Fin (count j) → MvPolynomial (Fin n) ℂ
  membership : ∀ (x : domain) (j : Fin r), x.val ∈ D j ↔
    ∀ k, MvPolynomial.eval (coordinates x).val (marked j k) = (0 : ℂ)

example {X : Type*} [TopologicalSpace X] (c : Chart X) :
    SubsetChart X (fun _ : Fin 1 => Set.univ) :=
  { c with count := fun _ => (0 : ℕ), marked := fun _ => Fin.elim0,
           membership := by simp }

private abbrev nodeP : Fin 1 → MvPolynomial (Fin 2) ℂ :=
  fun _ => MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2)
private abbrev Node := zeroSet nodeP
private abbrev nodeChart : Chart Node where
  domain := ⊤
  n := (2 : ℕ)
  m := (1 : ℕ)
  equations := nodeP
  coordinates := Homeomorph.Set.univ Node
private def tip : Node := ⟨![(1 : ℂ), (0 : ℂ)], by simp [zeroSet, nodeP]⟩

example : (coordinate nodeChart tip (by trivial)).val (0 : Fin 2) = (1 : ℂ) := rfl
example : nodeChart.n = (2 : ℕ) := rfl
example : coordinate nodeChart tip (by trivial) ∈ overlap nodeChart nodeChart := by trivial
example : (transition nodeChart nodeChart
    ⟨coordinate nodeChart tip (by trivial), by trivial⟩).val (0 : Fin 2) = (1 : ℂ) := rfl
example : tip ∈ locus nodeP (MvPolynomial.X (1 : Fin 2)) := by
  simp [locus, tip]

example {X : Over (Spec ↧ℂ)} (c : Chart (ComplexPoint X)) :
    RegularChart X (fun _ : Fin 1 => (0 : Γ(X.left, ⊤))) :=
  { c with marked := fun _ => (0 : MvPolynomial (Fin c.n) ℂ), evaluation := by intros; simp [Point.evaluate] }

end HodgeLean.Foundations.ComplexTopology.Marked
