import HodgeLean.Adapters.NormalConeB4aGysinNilpotentLocalization
import HodgeLean.Adapters.NormalConeB4aGysinSliceLength

/-! # Original generic multiplicities in local parameter quotients -/

noncomputable section
namespace HodgeLean.Adapters

/-- The parameter quotient at any source point of a finite flat split
nilpotent thickening retains the original affine generic stalk length. -/
theorem a3b4a_gysin_nilpotent_local_parameter_length
    {B A : Type*} [CommRing B] [IsDomain B] [CommRing A] [Algebra B A]
    [Module.Finite B A] [Module.Flat B A]
    (ε : A →ₐ[B] B) (hnil : IsNilpotent (RingHom.ker ε))
    (p : Ideal B) [p.IsPrime] (q : Ideal A) [q.IsPrime] [q.LiesOver p] :
    letI := Localization.AtPrime.algebraOfLiesOver p q
    letI : (RingHom.ker ε).IsPrime := RingHom.ker_isPrime ε
    Module.length
      (Localization.AtPrime q ⧸ (IsLocalRing.maximalIdeal (Localization.AtPrime p)).map
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)))
      (Localization.AtPrime q ⧸ (IsLocalRing.maximalIdeal (Localization.AtPrime p)).map
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))) =
      Module.length (Localization.AtPrime (RingHom.ker ε))
        (Localization.AtPrime (RingHom.ker ε)) := by
  have : IsLocalRing (p.Fiber A) :=
    a3b4a_gysin_nilpotent_retraction_fibre_local ε hnil p
  let F := IsLocalRing.maximalIdeal (p.Fiber A)
  let r := F.comap Algebra.TensorProduct.includeRight.toRingHom
  have : r.LiesOver p := by
    change (F.comap (Algebra.TensorProduct.includeRight : A →ₐ[B] p.Fiber A)).LiesOver p
    infer_instance
  have hr : q = r :=
    (a3b4a_gysin_nilpotent_retraction_prime ε hnil p q).trans
      (a3b4a_gysin_nilpotent_retraction_prime ε hnil p r).symm
  subst q
  letI := Localization.AtPrime.algebraOfLiesOver p r
  have hf := a3b4a_gysin_local_fibre_length_eq_source_quotient p F
  dsimp only at hf
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq]
  exact hf.symm.trans (a3b4a_gysin_nilpotent_fibre_length_eq_generic_length ε hnil p)

/-- An identification of the special local ring with a localized affine
thickening constructs flat slices with the original affine multiplicity. -/
theorem a3b4a_gysin_exists_flat_slice_original_generic_length
    {D B A R : Type*}
    [CommRing D] [IsDomain D] [IsDiscreteValuationRing D]
    [CommRing B] [IsDomain B] [CommRing A] [Algebra B A]
    [Module.Finite B A] [Module.Flat B A]
    (ε : A →ₐ[B] B) (hnil : IsNilpotent (RingHom.ker ε))
    (p : Ideal B) [p.IsPrime] (q : Ideal A) [q.IsPrime] [q.LiesOver p]
    [IsRegularLocalRing (Localization.AtPrime p)]
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra D R]
    [Module.Flat D R] (π : D) (hπ : Irreducible π)
    [Nontrivial (R ⧸ Ideal.span {algebraMap D R π})]
    (e : (R ⧸ Ideal.span {algebraMap D R π}) ≃+* Localization.AtPrime q) :
    letI : (RingHom.ker ε).IsPrime := RingHom.ker_isPrime ε
    ∃ xs : List R,
      (xs.length : WithBot ℕ∞) = ringKrullDim (Localization.AtPrime p) ∧
      (∀ x ∈ xs, x ∈ IsLocalRing.maximalIdeal R) ∧
      Module.Flat D (R ⧸ Ideal.ofList xs) ∧
      Module.length (R ⧸ (Ideal.span {algebraMap D R π} ⊔ Ideal.ofList xs))
        (R ⧸ (Ideal.span {algebraMap D R π} ⊔ Ideal.ofList xs)) =
      Module.length (Localization.AtPrime (RingHom.ker ε))
        (Localization.AtPrime (RingHom.ker ε)) := by
  let I := Ideal.span {algebraMap D R π}
  let Q := R ⧸ I
  let Bp := Localization.AtPrime p
  let Aq := Localization.AtPrime q
  letI := Localization.AtPrime.algebraOfLiesOver p q
  letI : Algebra Bp Q := (e.symm.toRingHom.comp (algebraMap Bp Aq)).toAlgebra
  let ae : Q ≃ₐ[Bp] Aq := { e with commutes' := fun b => e.apply_symm_apply _ }
  have hff := a3b4a_gysin_nilpotent_localization_finite_flat ε hnil p q
  have : Module.Flat Bp Aq := hff.2
  have : Module.Flat Bp Q := Module.Flat.of_linearEquiv ae.toLinearEquiv
  obtain ⟨εp, -, -⟩ := a3b4a_gysin_exists_localized_nilpotent_retraction ε hnil p q
  let εQ := εp.comp ae.toAlgHom
  have : IsLocalHom (algebraMap Bp Q) := ⟨fun b hb => by
    simpa using hb.map εQ.toRingHom⟩
  obtain ⟨xs, hlen, hmem, hflat, hideal⟩ :=
    a3b4a_gysin_exists_flat_slice_parameters (B := Bp) (R := R) π hπ
  refine ⟨xs, hlen, hmem, hflat, ?_⟩
  let JQ := (IsLocalRing.maximalIdeal Bp).map (algebraMap Bp Q)
  let JL := (IsLocalRing.maximalIdeal Bp).map (algebraMap Bp Aq)
  have hIJ : JL = JQ.map ae.toRingHom := by
    dsimp only [JL, JQ]
    rw [Ideal.map_map]
    congr 1
    exact ae.toAlgHom.comp_algebraMap.symm
  have hlength := (a3b2_length_eq_of_ringEquiv
    (Ideal.quotientEquivAlg JQ JL ae hIJ).toRingEquiv).trans
      (a3b4a_gysin_nilpotent_local_parameter_length ε hnil p q)
  have hmove := a3b2_length_eq_of_ringEquiv
    (Ideal.quotientEquivAlgOfEq R hideal).toRingEquiv
  exact (a3b2_length_eq_of_ringEquiv
    (DoubleQuot.quotQuotEquivQuotSup I (Ideal.ofList xs))).symm.trans
      (hmove.trans hlength)

end HodgeLean.Adapters
