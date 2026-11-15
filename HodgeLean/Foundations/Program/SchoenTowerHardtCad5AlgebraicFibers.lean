import HodgeLean.Foundations.Program.SchoenTowerT11bBoundary
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Algebra.Field.Subfield.Basic

/-! Algebraic coordinates of finite Boolean fibers over a coefficient field. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_finite_line_algebraic (K : Subfield ℝ)
    (f : s2v_t11b_Formula 1)
    (hlift : ∀ p ∈ f.atoms, ∃ q : MvPolynomial (Fin 1) K,
      MvPolynomial.map K.subtype q = p)
    (hfin : f.realize.Finite) (x : EuclideanSpace ℝ (Fin 1))
    (hx : x ∈ f.realize) : IsAlgebraic K (x 0) := by
  have hxi : x ∉ interior f.realize := by
    intro h
    exact (infinite_of_mem_nhds x (mem_interior_iff_mem_nhds.mp h)) hfin
  obtain ⟨p, hp, hn, hz⟩ := s2v_t11b_boundary_active_atom f x hx hxi
  obtain ⟨q, hq⟩ := hlift p hp
  have hqn : q ≠ 0 := by
    intro h
    apply hn
    rw [← hq, h, map_zero]
  refine ⟨MvPolynomial.uniqueAlgEquiv K (Fin 1) q, ?_, ?_⟩
  · exact (map_ne_zero_iff (MvPolynomial.uniqueAlgEquiv K (Fin 1))
      (MvPolynomial.uniqueAlgEquiv K (Fin 1)).injective).mpr hqn
  · rw [Polynomial.aeval_def, MvPolynomial.eval₂_const_uniqueAlgEquiv,
      MvPolynomial.eval₂_eq_eval_map]
    change MvPolynomial.eval (fun _ : Fin 1 => x 0) (MvPolynomial.map K.subtype q) = 0
    rw [hq]
    have heq : (fun _ : Fin 1 => x 0) = (fun i => x i) := by
      funext i
      exact congrArg (fun j : Fin 1 => x j) (Subsingleton.elim 0 i)
    rw [heq]
    exact hz

theorem s2v_hardt_cad5_finite_line_algebraic_of_coeff (K : Subfield ℝ)
    (f : s2v_t11b_Formula 1)
    (hcoeff : ∀ p ∈ f.atoms, ∀ d, p.coeff d ∈ K)
    (hfin : f.realize.Finite) (x : EuclideanSpace ℝ (Fin 1))
    (hx : x ∈ f.realize) : IsAlgebraic K (x 0) := by
  apply s2v_hardt_cad5_finite_line_algebraic K f ?_ hfin x hx
  intro p hp
  apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
  intro c hc
  obtain ⟨d, _, hd⟩ := MvPolynomial.mem_coeffs_iff.mp hc
  exact ⟨⟨c, hd ▸ hcoeff p hp d⟩, rfl⟩

end HodgeLean.Foundations.Program
