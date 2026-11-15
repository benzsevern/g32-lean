import HodgeLean.Foundations.Program.SchoenTowerHardtCad5GenericRootLimits
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5ClosureProjection

/-! Generic base fibers retain ambient limits below the base dimension bound. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_generic_bounded_fiber_limit {n q : ℕ}
    (S : s2v_t11b_Formula (q + n)) (P : s2v_hardt_cad5_Partition S.realize)
    (hd : P.dimension ≤ (n : ℤ)) :
    ∃ K : Subfield ℝ, Countable K ∧
      ∀ L : Subfield ℝ, K ≤ L → ∀ a : EuclideanSpace ℝ (Fin n),
        AlgebraicIndependent L (fun i => a i) → ∀ t : EuclideanSpace ℝ (Fin q),
        WithLp.toLp 2 (Fin.append (fun i => t i) (fun i => a i)) ∈ closure S.realize →
        WithLp.toLp 2 (Fin.append (fun i => t i) (fun i => a i)) ∈ S.realize := by
  classical
  let r (i : Fin q) : Fin (n + 1) → Fin (q + n) :=
    Fin.cases (i.castAdd n) (fun v => v.natAdd q)
  choose poly hp hzero using fun i => s2v_hardt_cad5_projection_polynomial_limit S P
    (show P.dimension < ((n + 1 : ℕ) : ℤ) by omega) (r i)
  apply s2v_hardt_cad5_generic_polynomial_fiber_limit S poly hp
  intro t a ht i
  have hz := hzero i (WithLp.toLp 2 (Fin.append (fun j => t j) (fun j => a j))) (subset_closure ht)
  have heq : (fun v => Fin.append (fun j => t j) (fun j => a j) (r i v)) =
      Fin.cons (t i) (fun j => a j) := by
    funext v
    refine Fin.cases ?_ (fun j => ?_) v <;> simp [r]
  simpa only [heq] using hz

end HodgeLean.Foundations.Program
