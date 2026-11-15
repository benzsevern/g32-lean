import HodgeLean.Foundations.Representation.OrderedKunnethStageTwoDefs
import Mathlib.Algebra.Ring.GeomSum

/-! Finite Fourier operator identities.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.OrderedKunneth.StageTwo
/-- Source: Serre, Linear Representations of Finite Groups, §2.6, character projectors. -/
theorem fourier_eigen {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (m : ℕ) (hm : 0 < m) (ζ : K) (hζ : IsPrimitiveRoot ζ m)
    (hchar : (m : K) ≠ 0) (A : Module.End K V) (hA : A ^ m = 1) (a : Fin m) (v : V) :
    A (fourierProjector m ζ A a v) = ζ ^ a.val • fourierProjector m ζ A a v := by
  let B : Module.End K V := (ζ ^ a.val)⁻¹ • A
  have hz : ζ ≠ 0 := hζ.ne_zero hm.ne'
  have hB : B ^ m = 1 := by
    dsimp [B]
    rw [smul_pow, hA, inv_pow, ← pow_mul, Nat.mul_comm a.val m,
      pow_mul, hζ.pow_eq_one, one_pow, inv_one, one_smul]
  have hsum : B * (∑ j ∈ Finset.range m, B ^ j) = ∑ j ∈ Finset.range m, B ^ j := by
    have h := mul_geom_sum B m
    rw [hB, sub_self, sub_mul, one_mul, sub_eq_zero] at h
    exact h
  have hcoeff : (∑ j : Fin m, ((ζ ^ j.val)⁻¹ ^ a.val) • A ^ j.val) =
      ∑ j ∈ Finset.range m, B ^ j := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [B]
    rw [smul_pow, inv_pow, inv_pow, ← pow_mul, ← pow_mul, Nat.mul_comm]
  have he : A * (∑ j ∈ Finset.range m, B ^ j) =
      ζ ^ a.val • (∑ j ∈ Finset.range m, B ^ j) := by
    have h := congrArg (fun T : Module.End K V => ζ ^ a.val • T) hsum
    simpa only [B, smul_mul_assoc, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hz),
      one_smul] using h
  unfold fourierProjector
  rw [hcoeff]
  change (A * ((m : K)⁻¹ • (∑ j ∈ Finset.range m, B ^ j))) v =
    (ζ ^ a.val • ((m : K)⁻¹ • (∑ j ∈ Finset.range m, B ^ j))) v
  rw [mul_smul_comm, he, smul_comm (m : K)⁻¹]


/-- Source: Serre, Linear Representations of Finite Groups, §2.6, orthogonality of characters. -/
theorem fourier_resolution {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (m : ℕ) (hm : 0 < m) (ζ : K) (hζ : IsPrimitiveRoot ζ m)
    (hchar : (m : K) ≠ 0) (A : Module.End K V) (hA : A ^ m = 1) :
    (∑ a : Fin m, fourierProjector m ζ A a) = 1 := by
  classical
  have hz : ζ ≠ 0 := hζ.ne_zero hm.ne'
  have orth (j : Fin m) : (∑ a : Fin m, (ζ ^ j.val)⁻¹ ^ a.val) =
      if j.val = 0 then (m : K) else 0 := by
    by_cases hj : j.val = 0
    · simp only [hj, pow_zero, inv_one, one_pow, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one, ite_true]
    · rw [if_neg hj, Fin.sum_univ_eq_sum_range]
      have hn : (ζ ^ j.val)⁻¹ ≠ 1 := by
        intro h
        have he : ζ ^ j.val = ζ ^ 0 := by simpa using (inv_eq_one.mp h)
        exact hj (hζ.pow_inj j.isLt hm he)
      have hp : ((ζ ^ j.val)⁻¹) ^ m = 1 := by
        rw [inv_pow, ← pow_mul, Nat.mul_comm j.val m, pow_mul,
          hζ.pow_eq_one, one_pow, inv_one]
      have h := mul_geom_sum ((ζ ^ j.val)⁻¹) m
      rw [hp, sub_self] at h
      exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hn)
  simp only [fourierProjector]
  rw [← Finset.smul_sum, Finset.sum_comm]
  have hs : (∑ j : Fin m, ∑ a : Fin m, ((ζ ^ j.val)⁻¹ ^ a.val) • A ^ j.val) =
      (m : K) • (1 : Module.End K V) := by
    simp only [← Finset.sum_smul, orth]
    rw [Finset.sum_eq_single ⟨0, hm⟩]
    · simp only [ite_true, pow_zero]
    · intro b _ hb
      rw [if_neg (fun h => hb (Fin.ext h)), zero_smul]
    · simp
  rw [hs, smul_smul, inv_mul_cancel₀ hchar, one_smul]


end HodgeLean.Foundations.OrderedKunneth.StageTwo
