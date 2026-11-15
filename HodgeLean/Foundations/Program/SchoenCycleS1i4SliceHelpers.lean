module

public import HodgeLean.Foundations.Program.SchoenCycleS1i4BallHelpers
import all Mathlib.RingTheory.MvPowerSeries.Basic
import all HodgeLean.Foundations.Program.SchoenCycleDivisionSeries
import all HodgeLean.Foundations.Program.SchoenCycleDivisionCoefficients

public section
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology
open scoped BigOperators
namespace HodgeLean.Foundations.Program

def s2e_sliceIndex (d j : ℕ) (a : Fin d →₀ ℕ) : Fin (d + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Fin.snoc a j)

@[simp] theorem s2e_sliceIndex_base (d j : ℕ) (a : Fin d →₀ ℕ) (i : Fin d) :
    s2e_sliceIndex d j a i.castSucc = a i := by simp [s2e_sliceIndex]

@[simp] theorem s2e_sliceIndex_last (d j : ℕ) (a : Fin d →₀ ℕ) :
    s2e_sliceIndex d j a (Fin.last d) = j := by simp [s2e_sliceIndex]

theorem s2e_sliceIndex_injective (d j : ℕ) : Function.Injective (s2e_sliceIndex d j) := by
  intro a b h
  ext i
  have := congrArg (fun x : Fin (d + 1) →₀ ℕ => x i.castSucc) h
  simpa using this

def s2e_sliceEquiv (d : ℕ) : ((Fin d →₀ ℕ) × ℕ) ≃ (Fin (d + 1) →₀ ℕ) where
  toFun p := s2e_sliceIndex d p.2 p.1
  invFun a := (Finsupp.equivFunOnFinite.symm (fun i => a i.castSucc), a (Fin.last d))
  left_inv p := by
    apply Prod.ext
    · ext i
      simp
    · simp
  right_inv a := by
    ext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem s2e_slice_prod (d j : ℕ) (a : Fin d →₀ ℕ) {K : Type*} [CommMonoid K]
    (z : Fin (d + 1) → K) :
    (∏ i, z i ^ s2e_sliceIndex d j a i) =
      (∏ i : Fin d, z i.castSucc ^ a i) * z (Fin.last d) ^ j := by
  rw [Fin.prod_univ_castSucc]
  simp

theorem s2e_slice_summable (d j : ℕ) (r : Fin (d + 1) → ℝ)
    (hr : ∀ i, 0 < r i) (B : MvPowerSeries (Fin (d + 1)) ℂ)
    (hB : Summable (fun a => ‖MvPowerSeries.coeff a B‖ * s2e_divWeight d r a)) :
    Summable (fun a : Fin d →₀ ℕ => ‖MvPowerSeries.coeff (s2e_sliceIndex d j a) B‖ *
      ∏ i : Fin d, r i.castSucc ^ a i) := by
  have hs := (hB.comp_injective (s2e_sliceIndex_injective d j)).div_const (r (Fin.last d) ^ j)
  convert hs using 1
  funext a
  simp only [Function.comp_def, s2e_divWeight, s2e_slice_prod]
  rw [← mul_assoc, mul_div_cancel_right₀ _ (pow_ne_zero _ (hr _).ne')]

theorem s2e_series_analytic_all_dimensions (m : ℕ) (r : Fin m → ℝ)
    (hr : ∀ i, 0 < r i) (F : MvPowerSeries (Fin m) ℂ)
    (hF : Summable (fun a => ‖MvPowerSeries.coeff a F‖ * ∏ i, r i ^ a i)) :
    AnalyticAt ℂ (s2e_divSeries m F) 0 := by
  cases m with
  | zero =>
    have heq : s2e_divSeries 0 F = fun _ => s2e_divSeries 0 F 0 := by
      funext z
      exact congrArg (s2e_divSeries 0 F) (Subsingleton.elim z 0)
    rw [heq]
    exact analyticAt_const
  | succ d =>
    obtain ⟨p, ρ, hp, _⟩ := s2e_monomial_ball_expansion d r hr F hF
    exact hp.analyticAt

@[expose] def s2e_coefficientSlice (d j : ℕ) (B : MvPowerSeries (Fin (d + 1)) ℂ) :
    MvPowerSeries (Fin d) ℂ := fun a => MvPowerSeries.coeff (s2e_sliceIndex d j a) B

@[simp] theorem s2e_coefficientSlice_coeff (d j : ℕ) (B : MvPowerSeries (Fin (d + 1)) ℂ)
    (a : Fin d →₀ ℕ) : MvPowerSeries.coeff a (s2e_coefficientSlice d j B) =
      MvPowerSeries.coeff (s2e_sliceIndex d j a) B := by
  rfl

theorem s2e_slice_realization_at (d k : ℕ) (r : Fin (d + 1) → ℝ)
    (hr : ∀ i, 0 < r i) (B : MvPowerSeries (Fin (d + 1)) ℂ)
    (hB : Summable (fun a => ‖MvPowerSeries.coeff a B‖ * s2e_divWeight d r a))
    (hdegree : ∀ a, k ≤ a (Fin.last d) → MvPowerSeries.coeff a B = 0)
    (z : Fin (d + 1) → ℂ) (hz : ∀ i, ‖z i‖ ≤ r i) :
    s2e_divSeries (d + 1) B z =
      ∑ j : Fin k, s2e_divSeries d (s2e_coefficientSlice d j B)
        (fun i => z i.castSucc) * z (Fin.last d) ^ (j : ℕ) := by
  classical
  let e := (Equiv.prodComm ℕ (Fin d →₀ ℕ)).trans (s2e_sliceEquiv d)
  let f := fun a : Fin (d + 1) →₀ ℕ => MvPowerSeries.coeff a B * ∏ i, z i ^ a i
  have hs : Summable f := (s2e_monomial_norm_summable d r B hB z hz).of_norm
  have he : Summable (f ∘ e) := hs.comp_injective e.injective
  change (∑' a, f a) = _
  rw [← e.tsum_eq f]
  trans ∑' j : ℕ, ∑' a : Fin d →₀ ℕ, f (e (j, a))
  · exact he.tsum_prod
  have hh (j : ℕ) : (∑' a : Fin d →₀ ℕ, f (e (j, a))) =
      s2e_divSeries d (s2e_coefficientSlice d j B)
        (fun i => z i.castSucc) * z (Fin.last d) ^ j := by
    change (∑' a : Fin d →₀ ℕ, MvPowerSeries.coeff (s2e_sliceIndex d j a) B *
      ∏ i, z i ^ s2e_sliceIndex d j a i) = _
    simp_rw [s2e_slice_prod, ← mul_assoc]
    rw [tsum_mul_right]
    rfl
  simp only [Function.comp_def] at *
  simp_rw [hh]
  rw [tsum_eq_sum (s := Finset.range k)]
  · exact (Fin.sum_univ_eq_sum_range _ k).symm
  · intro j hj
    have hj' : k ≤ j := Nat.le_of_not_lt (by simpa using hj)
    have hf0 : s2e_coefficientSlice d j B = 0 := by
      ext a
      rw [s2e_coefficientSlice_coeff]
      exact hdegree _ (by simpa using hj')
    simp [hf0, s2e_divSeries]

end HodgeLean.Foundations.Program
