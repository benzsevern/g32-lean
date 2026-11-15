import HodgeLean.Foundations.Program.SchoenTowerL1bLocalKummerSeries
import HodgeLean.Foundations.Program.SchoenTowerL1bLocalBinomialEmbedding
import HodgeLean.Foundations.Program.SchoenTowerL1bLocalRamificationOrder
import HodgeLean.Foundations.Program.SchoenTowerL1bRotationEigenOrder
import Mathlib.RingTheory.Localization.FractionRing

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A prime-detecting base expansion and the specified binomial character
extend to compatible local fractions on the same covering generator. -/
theorem s2v_l1b_local_kummer_embedding
    {R F E K : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    [Field F] [Field E] [Field K] [CharZero K] [IsAlgClosed K]
    [Algebra R F] [IsFractionRing R F] [Algebra F E] [FiniteDimensional F E]
    (β : R →+* PowerSeries K) (hβ : Function.Injective β)
    (p : R) (hp : Prime p) (hβp : β p = PowerSeries.X)
    (hlocal : ∀ v : R, ¬ p ∣ v → (β v).constantCoeff ≠ 0)
    (t : E) (a b u : R) (ha : a ≠ 0) (hb : b ≠ 0)
    (m : ℕ) (hm : m ≠ 0)
    (hgen : IntermediateField.adjoin F ({t} : Set E) = ⊤)
    (hdegree : Module.finrank F E = m)
    (hpow : t ^ m = algebraMap F E (algebraMap R F a / algebraMap R F b))
    (τ : E ≃+* E)
    (hfixu : τ (algebraMap F E (algebraMap R F u)) = algebraMap F E (algebraMap R F u))
    (hchar : τ t = algebraMap F E (algebraMap R F u) * t)
    (ξ : K) (hβu : β u = PowerSeries.C ξ) (hξ : IsPrimitiveRoot ξ m) :
    let L := FractionRing (PowerSeries K)
    let ι := algebraMap (PowerSeries K) L
    ∃ (ψ : E →+* L) (e q k : ℕ) (ζ : K) (A B : PowerSeries K),
      Function.Injective ψ ∧ ψ t = ι A / ι B ∧ e ≠ 0 ∧ IsPrimitiveRoot ζ e ∧
      A ≠ 0 ∧ B ≠ 0 ∧ m = e * q ∧
      ψ ((τ ^ q) t) = ι (PowerSeries.C (ζ ^ k)) * ψ t ∧
      PowerSeries.rescale ζ A * B = PowerSeries.C (ζ ^ k) * (A * PowerSeries.rescale ζ B) ∧
      (m : ℤ) * ((A.order.toNat : ℤ) - (B.order.toNat : ℤ)) =
        (e : ℤ) * (((emultiplicity p a).toNat : ℤ) - ((emultiplicity p b).toNat : ℤ)) := by
  let L := FractionRing (PowerSeries K)
  let ι := algebraMap (PowerSeries K) L
  have hι : Function.Injective ι := IsFractionRing.injective _ _
  have hβa : β a ≠ 0 := fun h => ha (hβ (h.trans β.map_zero.symm))
  have hβb : β b ≠ 0 := fun h => hb (hβ (h.trans β.map_zero.symm))
  obtain ⟨e, q, k, ζ, A, B, he, hq, hζ, hme, hζk, hA, hB, hbin, hcross⟩ :=
    s2v_l1b_local_kummer_series (β a) (β b) hβa hβb m hm ξ hξ
  let βe : R →+* PowerSeries K := (PowerSeries.expand e he).toRingHom.comp β
  have hβe : Function.Injective βe := by
    intro r s h
    apply hβ
    ext n
    have hh := congrArg (PowerSeries.coeff (e * n)) h
    simpa only [βe, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, PowerSeries.coeff_expand_mul] using hh
  let g : R →+* L := ι.comp βe
  have hg : Function.Injective g := hι.comp hβe
  let f : F →+* L := IsFractionRing.lift hg
  letI : Algebra F L := f.toAlgebra
  have hf (r : R) : algebraMap F L (algebraMap R F r) = ι (βe r) :=
    IsFractionRing.lift_algebraMap hg r
  have hiB : ι B ≠ 0 := fun h => hB (hι (h.trans (map_zero _).symm))
  have hiβb : ι (βe b) ≠ 0 :=
    fun h => hb (hg (h.trans (map_zero _).symm))
  have hroot : (ι A / ι B) ^ m =
      algebraMap F L (algebraMap R F a / algebraMap R F b) := by
    rw [map_div₀, hf, hf, div_pow]
    apply (div_eq_div_iff (pow_ne_zero m hiB) hiβb).mpr
    change ι A ^ m * ι (PowerSeries.expand e he (β b)) =
      ι (PowerSeries.expand e he (β a)) * ι B ^ m
    simpa only [map_mul, map_pow] using congrArg ι hbin
  obtain ⟨ψ, hψt⟩ := s2v_l1b_local_binomial_embedding t m
    (algebraMap R F a / algebraMap R F b) hm hgen hdegree hpow (ι A / ι B) hroot
  have hbase (r : R) : ψ.toRingHom (algebraMap F E (algebraMap R F r)) = ι (βe r) :=
    (ψ.commutes (algebraMap R F r)).trans (hf r)
  refine ⟨ψ.toRingHom, e, q, k, ζ, A, B, ψ.injective, hψt, he, hζ,
    hA, hB, hme, ?_, hcross, ?_⟩
  · rw [s2v_l1b_rotation_eigenfunction_iterate τ hfixu hchar q, map_mul, map_pow, hbase]
    change ι (PowerSeries.expand e he (β u)) ^ q * ψ t = _
    rw [hβu, PowerSeries.expand_C, ← map_pow, ← map_pow, hζk]
    rfl
  · have hlocE (v : R) (hv : ¬ p ∣ v) : (βe v).constantCoeff ≠ 0 := by
      change (PowerSeries.expand e he (β v)).constantCoeff ≠ 0
      rw [PowerSeries.constantCoeff_expand]
      exact hlocal v hv
    let ρ := (algebraMap F E).comp (algebraMap R F)
    have hpower : t ^ m = ρ a / ρ b := by
      simpa only [ρ, RingHom.comp_apply, map_div₀] using hpow
    have hβea : βe a ≠ 0 := fun h => ha (hβe (h.trans (map_zero _).symm))
    have hβeb : βe b ≠ 0 := fun h => hb (hβe (h.trans (map_zero _).symm))
    have hord := s2v_l1b_local_ramification_order ρ ψ.toRingHom ι βe hι p hp
      hlocE hbase t a b ha hb hβea hβeb A B hA hB m hpower hψt
    have hpord : (βe p).order.toNat = e := by
      change (PowerSeries.expand e he (β p)).order.toNat = e
      rw [hβp, PowerSeries.expand_X, PowerSeries.order_pow, PowerSeries.order_X,
        nsmul_eq_mul, mul_one, ENat.toNat_natCast]
    rwa [hpord] at hord

end HodgeLean.Foundations.Program
