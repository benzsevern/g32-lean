import HodgeLean.Foundations.DiscreteValuationRing.ParameterExpansionProofs

/-! General APIs as implications from the displayed geometric and coefficient inputs.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace DiscreteValuationRing.ParameterExpansion

/-- General library interface.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 9.2; existing s2v_l1b_divisor_codimension_one_dvr. -/
theorem stalk_dvr_of_coheight_one
    (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    (x : X) [IsRegularLocalRing (X.presheaf.stalk x)]
    (hx : Order.coheight x = 1) :
    IsDiscreteValuationRing (X.presheaf.stalk x) :=
  stalk_dvr_of_coheight_one_aux X x hx


/-- General library interface.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 9.2; existing s2v_l1b_rotation_expansion_residue_kernel. -/
theorem residue_kernel
    {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra K R]
    (ι : R →ₐ[K] PowerSeries K) (u : R) (hu : ι u = PowerSeries.X) :
    IsLocalHom (PowerSeries.constantCoeff.comp ι.toRingHom) ∧
    RingHom.ker (PowerSeries.constantCoeff.comp ι.toRingHom) = Ideal.span {u} :=
  residue_kernel_aux ι u hu


/-- General library interface.
Source: Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 9.2; existing s2v_i2a_dvr_expansion_order. -/
theorem order_eq_emultiplicity
    {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra K R]
    (ι : R →ₐ[K] PowerSeries K) (u : R) (hu : ι u = PowerSeries.X)
    (a : R) (ha : a ≠ 0) :
    (ι a).order = emultiplicity u a :=
  order_eq_emultiplicity_aux ι u hu a ha


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
