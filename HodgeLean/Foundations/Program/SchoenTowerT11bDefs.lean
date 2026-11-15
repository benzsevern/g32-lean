import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Homotopy.Contractible

/-! Concrete polynomial Boolean sets and embedded radial cones.
HC no distance; AV milestone no distance.
-/
noncomputable section
namespace HodgeLean.Foundations.Program

/-- Finite Boolean polynomial descriptions in real coordinates.
Source: Coste, An Introduction to Semialgebraic Geometry (2002), §1.1. -/
inductive s2v_t11b_Formula (n : ℕ) where
  | nonneg : MvPolynomial (Fin n) ℝ → s2v_t11b_Formula n
  | compl : s2v_t11b_Formula n → s2v_t11b_Formula n
  | inter : s2v_t11b_Formula n → s2v_t11b_Formula n → s2v_t11b_Formula n

/-- The subset described by a finite polynomial Boolean expression.
Source: Coste, An Introduction to Semialgebraic Geometry (2002), §1.1. -/
def s2v_t11b_Formula.realize {n : ℕ} : s2v_t11b_Formula n → Set (EuclideanSpace ℝ (Fin n))
  | .nonneg p => {x | 0 ≤ MvPolynomial.eval (fun i => x i) p}
  | .compl f => f.realizeᶜ
  | .inter f g => f.realize ∩ g.realize

example (n : ℕ) : (s2v_t11b_Formula.nonneg (0 : MvPolynomial (Fin n) ℝ)).realize =
    Set.univ := by ext x; simp [s2v_t11b_Formula.realize]

/-- The actual radius-r link of S at x.
Source: Coste, An Introduction to Semialgebraic Geometry (2002), Theorem 4.4. -/
def s2v_t11b_link {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) := S ∩ Metric.sphere x r

example (n : ℕ) (S : Set (EuclideanSpace ℝ (Fin n))) (x y : EuclideanSpace ℝ (Fin n))
    (r : ℝ) : y ∈ s2v_t11b_link S x r ↔ y ∈ S ∧ dist y x = r := Iff.rfl

/-- Open radial cone in displacement coordinates; its apex remains when the link is empty.
Source: Coste, An Introduction to Semialgebraic Geometry (2002), Theorem 4.4. -/
def s2v_t11b_cone {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {v | v = 0 ∨ ∃ y ∈ s2v_t11b_link S x r, ∃ t ∈ Set.Ioo (0 : ℝ) 1, v = t • (y - x)}

example (n : ℕ) (S : Set (EuclideanSpace ℝ (Fin n))) (x : EuclideanSpace ℝ (Fin n))
    (r : ℝ) : (0 : EuclideanSpace ℝ (Fin n)) ∈ s2v_t11b_cone S x r := Or.inl rfl

end HodgeLean.Foundations.Program
