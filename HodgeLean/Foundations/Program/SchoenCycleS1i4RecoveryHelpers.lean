module

public import HodgeLean.Foundations.Program.SchoenCycleS1i4MultilinearHelpers
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Analytic.Uniqueness
import all HodgeLean.Foundations.Program.SchoenCycleDivisionSeries
import all HodgeLean.Foundations.Program.SchoenCycleDivisionCoefficients
import all Mathlib.Basic.Complex.Basic

public section
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology
open scoped BigOperators NNReal ENNReal
namespace HodgeLean.Foundations.Program

@[expose] def s2e_tupleIndex {m n : ℕ} (s : Fin n → Fin m) : Fin m →₀ ℕ :=
  ∑ j, Finsupp.single (s j) 1

theorem s2e_tupleIndex_degree {m n : ℕ} (s : Fin n → Fin m) :
    (s2e_tupleIndex s).degree = n := by
  simp [s2e_tupleIndex, map_sum, Finsupp.degree_single]

theorem s2e_tupleIndex_prod {m n : ℕ} (s : Fin n → Fin m) (z : Fin m → ℂ) :
    (∏ i, z i ^ s2e_tupleIndex s i) = ∏ j, z (s j) := by
  classical
  simp only [s2e_tupleIndex, Finsupp.finsetSum_apply, ← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j hj
  simp [Finsupp.single_apply]

@[expose] def s2e_multilinearPolynomial (m n : ℕ) (p : (Fin m → ℂ) [×n]→L[ℂ] ℂ) :
    MvPolynomial (Fin m) ℂ :=
  ∑ s : Fin n → Fin m, MvPolynomial.monomial (s2e_tupleIndex s)
    (p (fun j => Pi.single (s j) 1))

theorem s2e_multilinearPolynomial_homogeneous (m n : ℕ)
    (p : (Fin m → ℂ) [×n]→L[ℂ] ℂ) :
    (s2e_multilinearPolynomial m n p).IsHomogeneous n := by
  apply (MvPolynomial.homogeneousSubmodule (Fin m) ℂ n).sum_mem
  intro s hs
  exact MvPolynomial.isHomogeneous_monomial _ (s2e_tupleIndex_degree s)

theorem s2e_multilinear_diagonal_expansion (m n : ℕ)
    (p : (Fin m → ℂ) [×n]→L[ℂ] ℂ) (z : Fin m → ℂ) :
    p (fun _ => z) = MvPolynomial.eval z (s2e_multilinearPolynomial m n p) := by
  classical
  have hz : z = ∑ i, z i • (Pi.single i 1 : Fin m → ℂ) := by
    ext i
    simp [Pi.single_apply]
  rw [show (fun _ : Fin n => z) = (fun _ => ∑ i, z i • (Pi.single i 1 : Fin m → ℂ)) from
    funext (fun _ => hz), p.map_sum]
  simp only [s2e_multilinearPolynomial, map_sum, MvPolynomial.eval_monomial,
    Finsupp.prod_pow]
  apply Finset.sum_congr rfl
  intro s hs
  rw [s2e_tupleIndex_prod]
  have h := p.map_smul_univ (fun j => z (s j)) (fun j => Pi.single (s j) 1)
  simpa only [smul_eq_mul, mul_comm] using h

theorem s2e_multilinearPolynomial_coeff_norm (m n : ℕ)
    (p : (Fin m → ℂ) [×n]→L[ℂ] ℂ) :
    (∑' a : {a : Fin m →₀ ℕ // a.degree = n},
      ‖(s2e_multilinearPolynomial m n p).coeff a.val‖) ≤ (m : ℝ) ^ n * ‖p‖ := by
  classical
  let : Fintype {a : Fin m →₀ ℕ // a.degree = n} :=
    (Finsupp.finite_of_degree_eq n).fintype
  rw [tsum_fintype]
  have hc (s : Fin n → Fin m) : ‖p (fun j => Pi.single (s j) 1)‖ ≤ ‖p‖ := by
    simpa only [Pi.norm_single, norm_one, Finset.prod_const_one, mul_one] using
      p.le_opNorm (fun j => Pi.single (s j) 1)
  calc
    _ ≤ ∑ a : {a : Fin m →₀ ℕ // a.degree = n},
        ∑ s : Fin n → Fin m, ‖(MvPolynomial.monomial (s2e_tupleIndex s)
          (p (fun j => Pi.single (s j) 1))).coeff a.val‖ := by
      apply Finset.sum_le_sum
      intro a ha
      simp only [s2e_multilinearPolynomial, MvPolynomial.coeff_sum]
      exact norm_sum_le _ _
    _ = ∑ s : Fin n → Fin m, ‖p (fun j => Pi.single (s j) 1)‖ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s hs
      simp only [MvPolynomial.coeff_monomial]
      rw [Finset.sum_eq_single (⟨s2e_tupleIndex s, s2e_tupleIndex_degree s⟩ :
        {a : Fin m →₀ ℕ // a.degree = n})]
      · simp
      · intro a ha hne
        have hne' : s2e_tupleIndex s ≠ a.val := by
          intro h
          exact hne (Subtype.ext h.symm)
        simp [hne']
      · simp
    _ ≤ ∑ _s : Fin n → Fin m, ‖p‖ := Finset.sum_le_sum (fun s _ => hc s)
    _ = _ := by simp

@[expose] def s2e_recoveredSeries (m : ℕ)
    (p : FormalMultilinearSeries ℂ (Fin m → ℂ) ℂ) : MvPowerSeries (Fin m) ℂ :=
  fun a => (s2e_multilinearPolynomial m a.degree (p a.degree)).coeff a

theorem s2e_recovered_layer_coeff (m n : ℕ)
    (p : FormalMultilinearSeries ℂ (Fin m → ℂ) ℂ) (a : Fin m →₀ ℕ) :
    (s2e_multilinearPolynomial m n (p n)).coeff a =
      if a.degree = n then MvPowerSeries.coeff a (s2e_recoveredSeries m p) else 0 := by
  classical
  by_cases h : a.degree = n
  · simp only [if_pos h, s2e_recoveredSeries, MvPowerSeries.coeff_apply]
    rw [h]
  · rw [if_neg h]
    exact (s2e_multilinearPolynomial_homogeneous m n (p n)).coeff_eq_zero h

theorem s2e_recovered_diagonal (m n : ℕ)
    (p : FormalMultilinearSeries ℂ (Fin m → ℂ) ℂ) (z : Fin m → ℂ) :
    p n (fun _ => z) = ∑' a : Fin m →₀ ℕ, if a.degree = n then
      MvPowerSeries.coeff a (s2e_recoveredSeries m p) * ∏ i, z i ^ a i else 0 := by
  classical
  rw [s2e_multilinear_diagonal_expansion, MvPolynomial.eval_eq']
  let P := s2e_multilinearPolynomial m n (p n)
  have heq (a : Fin m →₀ ℕ) : (if a.degree = n then
      MvPowerSeries.coeff a (s2e_recoveredSeries m p) * ∏ i, z i ^ a i else 0) =
        P.coeff a * ∏ i, z i ^ a i := by
    rw [s2e_recovered_layer_coeff]
    split_ifs <;> simp
  simp_rw [heq]
  exact (tsum_eq_sum (s := P.support) (fun a ha => by
    have hc : P.coeff a = 0 := by simpa using ha
    rw [hc, zero_mul])).symm

theorem s2e_recovered_summable (m : ℕ)
    (p : FormalMultilinearSeries ℂ (Fin m → ℂ) ℂ) (t : ℝ≥0)
    (ht : ((m : ℝ≥0) * t : ℝ≥0∞) < p.radius) :
    Summable (fun a : Fin m →₀ ℕ => ‖MvPowerSeries.coeff a (s2e_recoveredSeries m p)‖ *
      (t : ℝ) ^ a.degree) := by
  classical
  let F := s2e_recoveredSeries m p
  let f := fun a : Fin m →₀ ℕ => ‖MvPowerSeries.coeff a F‖ * (t : ℝ) ^ a.degree
  have hn (a) : 0 ≤ f a := mul_nonneg (norm_nonneg _) (pow_nonneg t.coe_nonneg _)
  have hfib (n : ℕ) : Summable (fun a : {a : Fin m →₀ ℕ // a.degree = n} => f a.val) := by
    let : Fintype {a : Fin m →₀ ℕ // a.degree = n} :=
      (Finsupp.finite_of_degree_eq n).fintype
    exact (hasSum_fintype _).summable
  have hb (n : ℕ) : (∑' a : {a : Fin m →₀ ℕ // a.degree = n}, f a.val) ≤
      ‖p n‖ * ((m : ℝ) * (t : ℝ)) ^ n := by
    have hc (a : {a : Fin m →₀ ℕ // a.degree = n}) :
        MvPowerSeries.coeff a.val F = (s2e_multilinearPolynomial m n (p n)).coeff a.val := by
      rw [s2e_recovered_layer_coeff, if_pos a.property]
    simp only [f, hc]
    have heq (a : {a : Fin m →₀ ℕ // a.degree = n}) : a.val.degree = n := a.property
    simp only [heq]
    rw [tsum_mul_right, mul_pow]
    calc
      _ ≤ ((m : ℝ) ^ n * ‖p n‖) * (t : ℝ) ^ n :=
        mul_le_mul_of_nonneg_right (s2e_multilinearPolynomial_coeff_norm m n (p n))
          (pow_nonneg t.coe_nonneg n)
      _ = _ := by ring
  have hs : Summable (fun n : ℕ => ∑' a : {a : Fin m →₀ ℕ // a.degree = n}, f a.val) :=
    (p.summable_norm_mul_pow (r := (m : ℝ≥0) * t) ht).of_nonneg_of_le
    (fun n => tsum_nonneg (fun a => hn a.val)) hb
  have hpart := summable_partition (f := f) hn (s := fun n : ℕ => {a : Fin m →₀ ℕ | a.degree = n})
    (fun a => ⟨a.degree, rfl, fun j hj => hj.symm⟩)
  exact hpart.mpr ⟨hfib, hs⟩

end HodgeLean.Foundations.Program
