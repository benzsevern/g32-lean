import HodgeLean.Foundations.Program.G32Native.PELCayleyConjugationEquations
import HodgeLean.Foundations.Program.G32Native.PELRealSubspacePolynomial

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations
open MvPolynomial MatrixCayley

/-- A polynomial equation on real Cayley conjugates near zero extends to the
complex span of the same real matrix subspace, on the invertible chart. -/
theorem pel_real_subspace_conjugation_continuation {n : ℕ}
    (L : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ))
    (A : Matrix (Fin n) (Fin n) ℂ)
    (p : MvPolynomial (Fin n × Fin n) ℂ)
    (hp : ∀ᶠ X : L in nhds 0,
      eval (fun ij : Fin n × Fin n =>
        (cayley (-(X.val.map Complex.ofReal)) * A *
          cayley (X.val.map Complex.ofReal)) ij.1 ij.2) p = 0)
    (Y : Matrix (Fin n) (Fin n) ℂ) (hR : Y.map Complex.re ∈ L)
    (hI : Y.map Complex.im ∈ L)
    (hminus : (1 - Y).det ≠ 0) (hplus : (1 + Y).det ≠ 0) :
    eval (fun ij : Fin n × Fin n =>
      (cayley (-Y) * A * cayley Y) ij.1 ij.2) p = 0 := by
  let b := Module.finBasis ℝ L
  let P := pel_real_subspace_polynomial b
  obtain ⟨z, hz⟩ := pel_real_subspace_polynomial_surjective b Y hR hI
  have hzero : (eval (fun _ => (0 : ℂ))).mapMatrix P = 0 := by
    ext i j
    simp [P, pel_real_subspace_polynomial]
  have hD0 : eval (fun _ => (0 : ℂ)) ((1 - P).det * (1 + P).det) = 1 := by
    rw [map_mul, RingHom.map_det, RingHom.map_det, map_sub, map_add,
      map_one, hzero, sub_zero, add_zero, Matrix.det_one, one_mul]
  have hc : Continuous (fun t : Fin (Module.finrank ℝ L) → ℝ =>
      eval (fun i => (t i : ℂ)) ((1 - P).det * (1 + P).det)) :=
    (MvPolynomial.continuous_eval _).comp
      (continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i))
  have hDn : ∀ᶠ t : Fin (Module.finrank ℝ L) → ℝ in nhds 0,
      eval (fun i => (t i : ℂ)) ((1 - P).det * (1 + P).det) ≠ 0 := by
    apply (hc.isOpen_preimage _ isOpen_compl_singleton).mem_nhds
    exact hD0.trans_ne one_ne_zero
  have hb : Continuous b.equivFun.symm :=
    b.equivFun.symm.toLinearMap.continuous_of_finiteDimensional
  have hb0 : Filter.Tendsto b.equivFun.symm (nhds 0) (nhds 0) := by
    simpa only [map_zero] using hb.tendsto 0
  have hpn : ∀ᶠ t : Fin (Module.finrank ℝ L) → ℝ in nhds 0,
      eval (fun ij : Fin n × Fin n =>
        (cayley (-((eval (fun i => (t i : ℂ))).mapMatrix P)) * A *
          cayley ((eval (fun i => (t i : ℂ))).mapMatrix P)) ij.1 ij.2) p = 0 := by
    filter_upwards [hb0.eventually hp] with t ht
    simpa only [P, pel_real_subspace_polynomial_eval_real] using ht
  have hdz : eval z ((1 - P).det * (1 + P).det) ≠ 0 := by
    rw [map_mul, RingHom.map_det, RingHom.map_det, map_sub, map_add, map_one, hz]
    exact mul_ne_zero hminus hplus
  have h := pel_cayley_conjugation_equation_of_real_nhds P A p 0 hDn hpn z hdz
  rwa [hz] at h

#print axioms pel_real_subspace_conjugation_continuation
end HodgeLean.Foundations
