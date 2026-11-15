import HodgeLean.Foundations.Mathlib.ZmtIsoDefs
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.Inverse

/-! General normalization and parameter interfaces.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace DiscreteValuationRing.ParameterExpansion

/-- General library interface.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 9.2. -/
theorem stalk_dvr_of_coheight_one_aux
    (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) [IsRegularLocalRing (X.presheaf.stalk x)]
    (hx : Order.coheight x = 1) :
    IsDiscreteValuationRing (X.presheaf.stalk x) := by
  let R := X.presheaf.stalk x
  have hdim : ringKrullDim R = 1 := by
    simpa only [hx, WithBot.coe_one] using ringKrullDim_stalk_eq_coheight x
  have hnf : ¬ IsField R := by
    intro hfield
    have hzero := ringKrullDim_eq_zero_of_isField hfield
    rw [hdim] at hzero
    exact one_ne_zero hzero
  have hspan : (IsLocalRing.maximalIdeal R).spanFinrank = 1 := by
    exact_mod_cast ((isRegularLocalRing_iff R).mp inferInstance).trans hdim
  have hprincipal := ((Submodule.spanFinrank_eq_one_iff (IsLocalRing.maximalIdeal R)).mp hspan).1
  exact ((IsDiscreteValuationRing.TFAE R hnf).out 1 5).mpr hprincipal

/-- General library interface.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 9.2. -/
theorem residue_kernel_aux
    {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra K R]
    (ι : R →ₐ[K] PowerSeries K) (u : R) (hu : ι u = PowerSeries.X) :
    IsLocalHom (PowerSeries.constantCoeff.comp ι.toRingHom) ∧
    RingHom.ker (PowerSeries.constantCoeff.comp ι.toRingHom) = Ideal.span {u} := by
  let ρ := PowerSeries.constantCoeff.comp ι.toRingHom
  have hs : Function.Surjective ρ := by
    intro k
    refine ⟨algebraMap K R k, ?_⟩
    change PowerSeries.constantCoeff (ι (algebraMap K R k)) = k
    rw [ι.commutes, PowerSeries.algebraMap_eq, PowerSeries.constantCoeff_C]
  letI : IsLocalHom ρ := IsLocalHom.of_surjective ρ hs
  letI : IsLocalHom ι.toRingHom := isLocalHom_of_comp ι.toRingHom PowerSeries.constantCoeff
  have hirr : Irreducible u := Irreducible.of_map (f := ι.toRingHom)
    (by change Irreducible (ι u); rw [hu]; exact PowerSeries.X_irreducible)
  exact ⟨inferInstance, (IsLocalRing.ker_eq_maximalIdeal ρ hs).trans
    ((IsDiscreteValuationRing.irreducible_iff_uniformizer u).mp hirr)⟩

/-- If elements outside a prime divisor have nonzero constant coefficient,
series order is the prime multiplicity times the order of its image. -/
theorem local_multiplicity_order
    {R K : Type*} [CommRing R] [Field K]
    (ι : R →+* PowerSeries K) (p a : R)
    (hfin : FiniteMultiplicity p a)
    (hlocal : ∀ v : R, ¬ p ∣ v → (ι v).constantCoeff ≠ 0) :
    (ι a).order = emultiplicity p a * (ι p).order := by
  obtain ⟨v, hav, hpv⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  have hv : (ι v).order = 0 := by
    by_contra h
    exact hlocal v hpv (PowerSeries.order_ne_zero_iff_constCoeff_eq_zero.mp h)
  calc
    (ι a).order = (ι (p ^ multiplicity p a * v)).order :=
      congrArg (fun b => (ι b).order) hav
    _ = (multiplicity p a : ENat) * (ι p).order := by
      rw [map_mul, map_pow, PowerSeries.order_mul, PowerSeries.order_pow,
        hv, add_zero, nsmul_eq_mul]
    _ = _ := by rw [hfin.emultiplicity_eq_multiplicity]


/-- General library interface.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 9.2. -/
theorem order_eq_emultiplicity_aux
    {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra K R]
    (ι : R →ₐ[K] PowerSeries K) (u : R) (hu : ι u = PowerSeries.X)
    (a : R) (ha : a ≠ 0) :
    (ι a).order = emultiplicity u a := by
  obtain ⟨hcomp, hker⟩ := residue_kernel_aux ι u hu
  letI := hcomp
  letI : IsLocalHom ι.toRingHom := isLocalHom_of_comp ι.toRingHom PowerSeries.constantCoeff
  have hirr : Irreducible u := Irreducible.of_map (f := ι.toRingHom)
    (by change Irreducible (ι u); rw [hu]; exact PowerSeries.X_irreducible)
  have hlocal (v : R) (hv : ¬ u ∣ v) : (ι v).constantCoeff ≠ 0 := by
    intro hz
    apply hv
    apply Ideal.mem_span_singleton.mp
    rw [← hker]
    exact hz
  have H := local_multiplicity_order ι.toRingHom u a
    (FiniteMultiplicity.of_prime_left hirr.prime ha) hlocal
  change (ι a).order = emultiplicity u a * (ι u).order at H
  simpa only [hu, PowerSeries.order_X, mul_one] using H

example : RingHom.ker (PowerSeries.constantCoeff (R := ℚ)) =
    Ideal.span {(PowerSeries.X : PowerSeries ℚ)} := by
  rw [PowerSeries.ker_coeff_eq_max_ideal, PowerSeries.maximalIdeal_eq_span_X]

example (n : ℕ) : ((1 + PowerSeries.X : PowerSeries ℚ) * PowerSeries.X ^ n).order = (n : ℕ∞) := by
  rw [PowerSeries.order_mul, PowerSeries.order_zero_of_isUnit
    (PowerSeries.isUnit_iff_constantCoeff.mpr (by simp)), PowerSeries.order_pow,
    PowerSeries.order_X]
  simp

example (n : ℕ) :
    ((1 + PowerSeries.X : PowerSeries ℚ) * PowerSeries.X ^ n).order =
      emultiplicity PowerSeries.X ((1 + PowerSeries.X : PowerSeries ℚ) * PowerSeries.X ^ n) :=
  PowerSeries.order_eq_emultiplicity_X _

-- The special point of the formal disk is an actual scheme point.
private abbrev disk := Scheme.Spec.obj (Opposite.op (CommRingCat.of (PowerSeries ℚ)))
private abbrev special : disk :=
  ⟨IsLocalRing.maximalIdeal (PowerSeries ℚ), inferInstance⟩

private noncomputable instance : Algebra (PowerSeries ℚ) (disk.presheaf.stalk special) :=
  inferInstanceAs (Algebra (PowerSeries ℚ)
    ((AlgebraicGeometry.Spec.structureSheaf (PowerSeries ℚ)).presheaf.stalk special))

private noncomputable instance : IsLocalization.AtPrime (disk.presheaf.stalk special)
    (IsLocalRing.maximalIdeal (PowerSeries ℚ)) :=
  StructureSheaf.IsLocalization.to_stalk (PowerSeries ℚ)
    (⟨IsLocalRing.maximalIdeal (PowerSeries ℚ), inferInstance⟩ : PrimeSpectrum (PowerSeries ℚ))

private noncomputable def diskStalkEquiv :
    PowerSeries ℚ ≃+* disk.presheaf.stalk special := by
  exact (IsLocalization.atUnits (PowerSeries ℚ)
    (IsLocalRing.maximalIdeal (PowerSeries ℚ)).primeCompl
    (S := disk.presheaf.stalk special) (by
      intro a ha
      exact (IsLocalRing.notMem_maximalIdeal.mp ha))).toRingEquiv

private instance : IsDomain (disk.presheaf.stalk special) :=
  diskStalkEquiv.symm.toMulEquiv.isDomain _

example : IsDiscreteValuationRing (disk.presheaf.stalk special) :=
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing diskStalkEquiv

example : Order.coheight special = 1 := by
  let := IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing diskStalkEquiv
  have hd := IsDiscreteValuationRing.ringKrullDim_eq_one (disk.presheaf.stalk special)
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight] at hd
  exact_mod_cast hd

end DiscreteValuationRing.ParameterExpansion
