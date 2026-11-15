import HodgeLean.Foundations.Program.SchoenTowerHardt2Projection

noncomputable section
namespace HodgeLean.Foundations.Program

/-- Insert a finite tuple of quantified coordinates before the parameter coordinates.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.1, iterated projection coordinates. -/
def s2v_hardt2_insert {n : ℕ} : (k : ℕ) →
    (Fin k → ℝ) → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (n + k))
  | 0, _, a => a
  | k + 1, y, a => WithLp.toLp 2 (Fin.cons (y 0)
      (fun i => s2v_hardt2_insert k (fun j => y j.succ) a i))

/-- Indices of the inserted variables.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.1, coordinate bookkeeping. -/
def s2v_hardt2_boundIndex (n : ℕ) : (k : ℕ) → Fin k → Fin (n + k)
  | 0, j => Fin.elim0 j
  | k + 1, j => Fin.cases 0 (fun i => (s2v_hardt2_boundIndex n k i).succ) j

/-- Indices of the retained variables.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.1, coordinate bookkeeping. -/
def s2v_hardt2_freeIndex (n : ℕ) : (k : ℕ) → Fin n → Fin (n + k)
  | 0, j => j
  | k + 1, j => (s2v_hardt2_freeIndex n k j).succ

/-- Inserted-variable evaluation is the original tuple evaluation.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.1, coordinate bookkeeping. -/
theorem s2v_hardt2_insert_bound {n k : ℕ} (y : Fin k → ℝ)
    (a : EuclideanSpace ℝ (Fin n)) (j : Fin k) :
    s2v_hardt2_insert k y a (s2v_hardt2_boundIndex n k j) = y j := by
  induction k with
  | zero => exact Fin.elim0 j
  | succ k ih =>
    refine Fin.cases (by rfl) (fun i => ?_) j
    exact ih (fun j => y j.succ) i

/-- Retained-variable evaluation is the original parameter evaluation.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.1, coordinate bookkeeping. -/
theorem s2v_hardt2_insert_free {n k : ℕ} (y : Fin k → ℝ)
    (a : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    s2v_hardt2_insert k y a (s2v_hardt2_freeIndex n k j) = a j := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih (fun j => y j.succ)

/-- Repeated real-coordinate projection eliminates an arbitrary finite tuple.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.1, iteration. -/
theorem s2v_hardt2_repeated_projection {n k : ℕ} (f : s2v_t11b_Formula (n + k)) :
    ∃ d : s2v_t11b_Formula n, ∀ a : EuclideanSpace ℝ (Fin n),
      a ∈ d.realize ↔ ∃ y : Fin k → ℝ, s2v_hardt2_insert k y a ∈ f.realize := by
  induction k with
  | zero =>
    exact ⟨f, fun a => ⟨fun ha => ⟨Fin.elim0, ha⟩, fun ⟨_, ha⟩ => ha⟩⟩
  | succ k ih =>
    obtain ⟨g, hg⟩ := s2v_hardt2_project_coordinate f
    obtain ⟨d, hd⟩ := ih g
    refine ⟨d, ?_⟩
    intro a
    rw [hd]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨x, hx⟩ := (hg _).mp hy
      exact ⟨Fin.cons x y, hx⟩
    · rintro ⟨y, hy⟩
      exact ⟨fun j => y j.succ, (hg _).mpr ⟨y 0, hy⟩⟩

#print axioms s2v_hardt2_repeated_projection
end HodgeLean.Foundations.Program
