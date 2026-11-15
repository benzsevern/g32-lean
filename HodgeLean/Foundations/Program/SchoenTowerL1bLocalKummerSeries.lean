import HodgeLean.Foundations.Program.SchoenTowerL1bTameBinomialFraction
import HodgeLean.Foundations.Program.SchoenTowerL1bLocalInertiaArithmetic
import HodgeLean.Foundations.Program.SchoenTowerL1bLocalPrimitiveCharacter

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A specified primitive binomial character and two nonzero base series give
ramified root fractions with compatible inertia and rescaling characters. -/
theorem s2v_l1b_local_kummer_series
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (A B : PowerSeries K) (hA : A ≠ 0) (hB : B ≠ 0)
    (m : ℕ) (hm : m ≠ 0) (ξ : K) (hξ : IsPrimitiveRoot ξ m) :
    ∃ (e q k : ℕ) (ζ : K) (F G : PowerSeries K) (he : e ≠ 0),
      0 < q ∧ IsPrimitiveRoot ζ e ∧ m = e * q ∧ ζ ^ k = ξ ^ q ∧
      F ≠ 0 ∧ G ≠ 0 ∧
      F ^ m * PowerSeries.expand e he B =
        PowerSeries.expand e he A * G ^ m ∧
      PowerSeries.rescale ζ F * G =
        PowerSeries.C (ζ ^ k) * (F * PowerSeries.rescale ζ G) := by
  obtain ⟨e, q, n, hepos, hqpos, hme, hdn, hcop⟩ :=
    s2v_l1b_local_inertia_arithmetic m hm ((A.order.toNat : ℤ) - B.order.toNat)
  have he : e ≠ 0 := Nat.ne_of_gt hepos
  have hξq : IsPrimitiveRoot (ξ ^ q) e :=
    IsPrimitiveRoot.pow (Nat.pos_of_ne_zero hm) hξ (hme.trans (Nat.mul_comm e q))
  obtain ⟨ζ, hζ, hζn⟩ := s2v_l1b_primitive_scalar_inverse (ξ ^ q) e he hξq n hcop
  letI : NeZero e := ⟨he⟩
  obtain ⟨k, hke, hζk⟩ := hζ.eq_pow_of_pow_eq_one hξq.pow_eq_one
  have hrel : (m : ℤ) * n = (e : ℤ) * ((A.order.toNat : ℤ) - B.order.toNat) := by
    rw [hdn, hme]
    push_cast
    ring
  have horders : n.toNat * m + e * B.order.toNat =
      e * A.order.toNat + (-n).toNat * m := by
    have hn := n.toNat_sub_toNat_neg
    zify
    nlinarith
  obtain ⟨F, G, hF, hG, hbin, hchar⟩ :=
    s2v_l1b_tame_binomial_fraction A B hA hB m e n.toNat (-n).toNat hm he horders
  refine ⟨e, q, k, ζ, F, G, he, hqpos, hζ, hme, hζk, hF, hG, hbin, ?_⟩
  obtain ⟨hcharF, hcharG⟩ := hchar ζ hζ.pow_eq_one
  have hζ0 : ζ ≠ 0 := hζ.ne_zero he
  have hscalar : ζ ^ n.toNat = ζ ^ k * ζ ^ (-n).toNat := by
    apply (div_eq_iff (pow_ne_zero _ hζ0)).mp
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hζ0,
      n.toNat_sub_toNat_neg, hζn, hζk]
  rw [hcharF, hcharG, hscalar, map_mul]
  ring

end HodgeLean.Foundations.Program
