import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPolynomialFamilyContinuity
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.Topology.Order.Lattice

/-! Monic polynomial families have uniformly bounded real roots over compact bases. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_monic_root_bound {E σ : Type*} [TopologicalSpace E]
    (C : Set E) (hC : IsCompact C) (k : E → σ → ℝ) (hk : ContinuousOn k C)
    (Q : Polynomial (MvPolynomial σ ℝ)) (hQ : Q.Monic) :
    ∃ b : ℝ, ∀ x ∈ C, ∀ t : ℝ,
      Q.eval₂ (MvPolynomial.eval (k x)) t = 0 → t ∈ Set.Icc (-b) b := by
  let B : E → NNReal := fun x =>
    (Finset.range Q.natDegree).sup (fun i => ‖MvPolynomial.eval (k x) (Q.coeff i)‖₊) + 1
  have hB : ContinuousOn B C := by
    apply ContinuousOn.add ?_ continuousOn_const
    apply ContinuousOn.finset_sup_apply
    intro i hi
    exact ((MvPolynomial.continuous_eval (Q.coeff i)).comp_continuousOn hk).nnnorm
  obtain ⟨b, hb⟩ := (hC.image_of_continuousOn hB).bddAbove
  refine ⟨b, ?_⟩
  intro x hx t ht
  let p := Q.map (MvPolynomial.eval (k x))
  have hp : p.Monic := hQ.map _
  have hr : p.IsRoot t := by simpa only [p, Polynomial.IsRoot, Polynomial.eval_map] using ht
  have hbound : ‖t‖₊ ≤ b := by
    apply (hr.norm_lt_cauchyBound hp.ne_zero).le.trans
    have heq : p.cauchyBound = B x := by
      simp only [Polynomial.cauchyBound, hp.leadingCoeff, nnnorm_one, div_one,
        p, hQ.natDegree_map, Polynomial.coeff_map, B]
    rw [heq]
    exact hb (Set.mem_image_of_mem B hx)
  have habs : |t| ≤ (b : ℝ) := by exact_mod_cast hbound
  exact abs_le.mp habs

end HodgeLean.Foundations.Program
