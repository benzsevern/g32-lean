import HodgeLean.Adapters.NormalConeB4aGysinFibreLength
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Flat.Localization

/-! # Local rings of parameter fibres

Localization of a quotient identifies the local fibre length with the
self-length of the corresponding quotient of the ambient local ring.
-/

noncomputable section
namespace HodgeLean.Adapters

/-- Localizing a quotient at a prime preserves the self-length of the
corresponding quotient of the ambient localization. -/
theorem a3b4a_gysin_localized_quotient_length
    {R : Type*} [CommRing R] (I : Ideal R) (p : Ideal (R ⧸ I)) [p.IsPrime] :
    Module.length (Localization.AtPrime p) (Localization.AtPrime p) =
      Module.length
        (Localization.AtPrime (p.comap (Ideal.Quotient.mk I)) ⧸
          I.map (algebraMap R (Localization.AtPrime (p.comap (Ideal.Quotient.mk I)))))
        (Localization.AtPrime (p.comap (Ideal.Quotient.mk I)) ⧸
          I.map (algebraMap R (Localization.AtPrime (p.comap (Ideal.Quotient.mk I))))) := by
  let P := p.comap (Ideal.Quotient.mk I)
  let A := Localization.AtPrime P
  let B := A ⧸ I.map (algebraMap R A)
  have hloc : IsLocalization p.primeCompl B := by
    have h := (inferInstance :
      IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) P.primeCompl) B)
    change IsLocalization (P.primeCompl.map (Ideal.Quotient.mk I)) B at h
    rw [Ideal.map_primeCompl_comap_of_surjective _ Ideal.Quotient.mk_surjective] at h
    exact h
  letI := hloc
  exact a3b2_length_eq_of_ringEquiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p) B).toRingEquiv

open scoped TensorProduct
universe u

/-- The exact local length of a parameter fibre equals the evaluation fibre
length of the ambient localization at the corresponding prime. -/
theorem a3b4a_gysin_localized_parameter_fibre_length
    {k R : Type u} [Field k] [CommRing R] [Algebra (Polynomial k) R]
    (s : k) [Algebra (Polynomial k) k]
    (hs : algebraMap (Polynomial k) k = Polynomial.evalRingHom s)
    (p : Ideal (R ⧸ Ideal.span
      {algebraMap (Polynomial k) R (Polynomial.X - Polynomial.C s)})) [p.IsPrime] :
    let I := Ideal.span {algebraMap (Polynomial k) R (Polynomial.X - Polynomial.C s)}
    let A := Localization.AtPrime (p.comap (Ideal.Quotient.mk I))
    Module.length (Localization.AtPrime p) (Localization.AtPrime p) =
      Module.length (A ⊗[Polynomial k] k) (A ⊗[Polynomial k] k) := by
  let I := Ideal.span {algebraMap (Polynomial k) R (Polynomial.X - Polynomial.C s)}
  let A := Localization.AtPrime (p.comap (Ideal.Quotient.mk I))
  have hmap : I.map (algebraMap R A) =
      Ideal.span {algebraMap (Polynomial k) A (Polynomial.X - Polynomial.C s)} := by
    dsimp only [I]
    rw [Ideal.map_span, Set.image_singleton, ← IsScalarTower.algebraMap_apply]
  change Module.length (Localization.AtPrime p) (Localization.AtPrime p) =
    Module.length (A ⊗[Polynomial k] k) (A ⊗[Polynomial k] k)
  rw [a3b4a_gysin_localized_quotient_length I p, hmap,
    a3b4a_gysin_tensor_fibre_length s hs]
  exact (Module.length_eq_of_surjective Ideal.Quotient.mk_surjective).symm

/-- At a generic prime of the actual parameter quotient, its local length
is the sum of reduced-component parameter lengths with generic local weights. -/
theorem a3b4a_gysin_generic_parameter_fibre_length_sum
    {k R : Type u} [Field k] [CommRing R] [IsNoetherianRing R]
    [Algebra (Polynomial k) R] [Module.Flat (Polynomial k) R]
    (s : k) [Algebra (Polynomial k) k]
    (hs : algebraMap (Polynomial k) k = Polynomial.evalRingHom s)
    (p : Ideal (R ⧸ Ideal.span
      {algebraMap (Polynomial k) R (Polynomial.X - Polynomial.C s)}))
    [p.IsPrime] (hp : p ∈ minimalPrimes _) :
    let I := Ideal.span {algebraMap (Polynomial k) R (Polynomial.X - Polynomial.C s)}
    let A := Localization.AtPrime (p.comap (Ideal.Quotient.mk I))
    ∃ Φ : Finset (PrimeSpectrum A),
      (∀ q : PrimeSpectrum A, q ∈ Φ ↔ q.asIdeal ∈ minimalPrimes A) ∧
      (Module.length (Localization.AtPrime p) (Localization.AtPrime p)).toNat =
        ∑ q ∈ Φ, (a3e_locLen q A).toNat *
          (Module.length A (QuotSMulTop
            (algebraMap (Polynomial k) A (Polynomial.X - Polynomial.C s))
            (A ⧸ q.asIdeal))).toNat := by
  let I := Ideal.span {algebraMap (Polynomial k) R (Polynomial.X - Polynomial.C s)}
  let P := p.comap (Ideal.Quotient.mk I)
  let A := Localization.AtPrime P
  let T := A ⊗[Polynomial k] k
  letI : Ring.KrullDimLE 0 (Localization.AtPrime p) := Ring.krullDimLE_iff.mpr (by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p,
      Ideal.height_eq_zero_iff.mpr hp]
    simp)
  letI : IsArtinianRing (Localization.AtPrime p) :=
    IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  have hlen : Module.length (Localization.AtPrime p) (Localization.AtPrime p) =
      Module.length T T := a3b4a_gysin_localized_parameter_fibre_length s hs p
  have hfinite : Module.length T T ≠ ⊤ := by
    rw [← hlen]
    exact Module.length_ne_top
  have hfl : IsFiniteLength T T := Module.length_ne_top_iff.mp hfinite
  letI : IsArtinianRing T := (isArtinianRing_iff_isFiniteLength T).mpr hfl
  letI : Module.Flat R A := IsLocalization.flat A P.primeCompl
  letI : Module.Flat (Polynomial k) A := Module.Flat.trans (Polynomial k) R A
  have hrm : algebraMap (Polynomial k) A (Polynomial.X - Polynomial.C s) ∈
      IsLocalRing.maximalIdeal A := by
    rw [IsScalarTower.algebraMap_apply (Polynomial k) R A]
    apply (IsLocalization.AtPrime.to_map_mem_maximal_iff A P _).mpr
    change Ideal.Quotient.mk I
      (algebraMap (Polynomial k) R (Polynomial.X - Polynomial.C s)) ∈ p
    have hz : Ideal.Quotient.mk I
        (algebraMap (Polynomial k) R (Polynomial.X - Polynomial.C s)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
    rw [hz]
    exact p.zero_mem
  obtain ⟨Φ, hΦ, hsum⟩ := a3b4a_gysin_artinian_fibre_length_sum (A := A) s hs hrm
  exact ⟨Φ, hΦ, (congrArg ENat.toNat hlen).trans hsum⟩

end HodgeLean.Adapters
