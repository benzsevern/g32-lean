import HodgeLean.Foundations.Program.G32Native.PELRealSkewCentralizer
import HodgeLean.Foundations.Program.G32Native.PELRealSubspacePolynomial
import Mathlib.Topology.Algebra.MvPolynomial

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program.GeneralTypeIII
open HodgeLean.Foundations MatrixCayley MvPolynomial

/-- A Zariski closed subgroup containing the real identity component
contains the complex Cayley chart of the real skew-centralizer subspace. -/
theorem pel_complex_cayley_mem_of_real_component {n : ℕ}
    (E : Matrix (Fin n) (Fin n) ℝ) (S : Set (Matrix (Fin n) (Fin n) ℝ))
    (L : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ))
    (hskew : ∀ X : L, X.val.transpose * E + E * X.val = 0)
    (hcomm : ∀ X : L, ∀ T ∈ S, X.val * T = T * X.val)
    (K : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℂ))
    (hK : @IsClosed _ (g1_zariski ℂ n) (K : Set _))
    (hreal : ∀ g : pelIsometrySubgroup E S, g ∈ connectedComponent 1 →
      Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) g.val ∈ K)
    (Y : Matrix (Fin n) (Fin n) ℂ) (hR : Y.map Complex.re ∈ L)
    (hI : Y.map Complex.im ∈ L) (hdet : (1 + Y).det ≠ 0)
    (g : Matrix.GeneralLinearGroup (Fin n) ℂ) (hg : g.val = cayley Y) : g ∈ K := by
  classical
  letI : TopologicalSpace (Matrix.GeneralLinearGroup (Fin n) ℂ) := g1_zariski ℂ n
  let b := Module.finBasis ℝ L
  let P := pel_real_subspace_polynomial b
  obtain ⟨z, hz⟩ := pel_real_subspace_polynomial_surjective b Y hR hI
  have hzero : (eval (fun _ => (0 : ℂ))).mapMatrix P = 0 := by
    ext i j
    simp [P, pel_real_subspace_polynomial]
  have hD0 : eval (fun _ => (0 : ℂ)) (1 + P).det = 1 := by
    rw [RingHom.map_det, map_add, map_one, hzero, add_zero, Matrix.det_one]
  have hc : Continuous (fun t : Fin (Module.finrank ℝ L) → ℝ =>
      eval (fun i => (t i : ℂ)) (1 + P).det) :=
    (MvPolynomial.continuous_eval _).comp
      (continuous_pi fun i => Complex.continuous_ofReal.comp (continuous_apply i))
  have hDn : ∀ᶠ t : Fin (Module.finrank ℝ L) → ℝ in nhds 0,
      eval (fun i => (t i : ℂ)) (1 + P).det ≠ 0 := by
    apply (hc.isOpen_preimage _ isOpen_compl_singleton).mem_nhds
    exact hD0.trans_ne one_ne_zero
  have hb : Continuous b.equivFun.symm :=
    b.equivFun.symm.toLinearMap.continuous_of_finiteDimensional
  have hN : ∀ᶠ t : Fin (Module.finrank ℝ L) → ℝ in nhds 0,
      ∃ q : pelIsometrySubgroup E S, q ∈ connectedComponent 1 ∧
        q.val.val = cayley (b.equivFun.symm t).val := by
    have hb0 : Filter.Tendsto b.equivFun.symm (nhds 0) (nhds 0) := by
      simpa only [map_zero] using hb.tendsto 0
    exact hb0.eventually (pel_real_cayley_identity_neighborhood E S L hskew hcomm)
  obtain ⟨s, hs⟩ := (g1_isClosed_iff (k := ℂ) (n := n)
    (K : Set (Matrix.GeneralLinearGroup (Fin n) ℂ))).mp hK
  change g ∈ (K : Set _)
  rw [hs]
  intro p hp
  have hn : ∀ᶠ t : Fin (Module.finrank ℝ L) → ℝ in nhds 0,
      eval (fun ij : Fin n × Fin n =>
        cayley ((eval (fun i => (t i : ℂ))).mapMatrix P) ij.1 ij.2) p = 0 := by
    filter_upwards [hN] with t ht
    obtain ⟨q, hq, hqval⟩ := ht
    have hm : (Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) q.val).val =
        cayley ((eval (fun i => (t i : ℂ))).mapMatrix P) := by
      change q.val.val.map (algebraMap ℝ ℂ) = _
      rw [show P = pel_real_subspace_polynomial b from rfl,
        pel_real_subspace_polynomial_eval_real]
      change q.val.val.map (algebraMap ℝ ℂ) =
        cayley ((b.equivFun.symm t).val.map (algebraMap ℝ ℂ))
      rw [← MatrixCayley.map, hqval]
    have hh := hreal q hq
    change _ ∈ (K : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)) at hh
    rw [hs] at hh
    have hh' := hh p hp
    change eval (fun ij : Fin n × Fin n =>
      (Matrix.GeneralLinearGroup.map (algebraMap ℝ ℂ) q.val).val ij.1 ij.2) p = 0 at hh'
    rw [hm] at hh'
    exact hh'
  have hdz : eval z (1 + P).det ≠ 0 := by
    rw [RingHom.map_det, map_add, map_one, show (eval z).mapMatrix P = Y from hz]
    exact hdet
  have h := pel_cayley_equation_of_real_nhds P p 0 hDn hn z hdz
  rw [show (eval z).mapMatrix P = Y from hz] at h
  change eval (fun ij : Fin n × Fin n => g.val ij.1 ij.2) p = 0
  rw [hg]
  exact h

end HodgeLean.Foundations.Program.GeneralTypeIII
