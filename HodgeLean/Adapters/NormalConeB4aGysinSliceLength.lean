import HodgeLean.Adapters.NormalConeB4aGysinNilpotentFibre
import HodgeLean.Adapters.NormalConeB4aGysinLiftParameters

/-! # Exact multiplicities of lifted parameter slices -/

noncomputable section
namespace HodgeLean.Adapters

/-- The fibre over the maximal ideal of a local base has the exact length of
its parameter quotient. -/
theorem a3b4a_gysin_local_base_fibre_length
    {B A : Type*} [CommRing B] [IsLocalRing B] [CommRing A] [Algebra B A] :
    Module.length ((IsLocalRing.maximalIdeal B).Fiber A)
      ((IsLocalRing.maximalIdeal B).Fiber A) =
    Module.length (A ⧸ (IsLocalRing.maximalIdeal B).map (algebraMap B A))
      (A ⧸ (IsLocalRing.maximalIdeal B).map (algebraMap B A)) := by
  let p := IsLocalRing.maximalIdeal B
  let M := Algebra.algebraMapSubmonoid A p.primeCompl
  let S := Localization M
  have hu : M ≤ IsUnit.submonoid A := by
    rintro a ⟨b, hb, rfl⟩
    exact (IsLocalRing.notMem_maximalIdeal.mp hb).map (algebraMap B A)
  let e : A ≃ₐ[A] S := IsLocalization.atUnits A M hu
  let I := p.map (algebraMap B A)
  let eq := Ideal.quotientEquivAlg I (I.map (algebraMap A S)) e (by
    congr 1)
  letI : Algebra A (p.Fiber A) := Algebra.TensorProduct.rightAlgebra
  exact a3b2_length_eq_of_ringEquiv
    ((Ideal.Fiber.algEquivAux₁ p).toRingEquiv.trans eq.symm.toRingEquiv)

/-- The parameter quotient of a finite flat split nilpotent thickening has
its full generic multiplicity. -/
theorem a3b4a_gysin_nilpotent_parameter_length
    {B A : Type*} [CommRing B] [IsLocalRing B] [IsDomain B] [CommRing A]
    [Algebra B A] [Module.Finite B A] [Module.Flat B A]
    (ε : A →ₐ[B] B) (hnil : IsNilpotent (RingHom.ker ε)) :
    letI : (RingHom.ker ε).IsPrime := RingHom.ker_isPrime ε
    Module.length (A ⧸ (IsLocalRing.maximalIdeal B).map (algebraMap B A))
      (A ⧸ (IsLocalRing.maximalIdeal B).map (algebraMap B A)) =
    Module.length (Localization.AtPrime (RingHom.ker ε))
      (Localization.AtPrime (RingHom.ker ε)) := by
  exact (a3b4a_gysin_local_base_fibre_length (B := B) (A := A)).symm.trans
    (a3b4a_gysin_nilpotent_fibre_length_eq_generic_length ε hnil
      (IsLocalRing.maximalIdeal B))

/-- A split finite flat nilpotent special fibre constructs flat parameter
slices with exactly its generic multiplicity. -/
theorem a3b4a_gysin_exists_flat_slice_exact_length
    {A B R : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsRegularLocalRing B] [IsDomain B]
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra A R]
    [Module.Flat A R] (π : A) (hπ : Irreducible π)
    [Nontrivial (R ⧸ Ideal.span {algebraMap A R π})]
    [Algebra B (R ⧸ Ideal.span {algebraMap A R π})]
    [Module.Flat B (R ⧸ Ideal.span {algebraMap A R π})]
    [Module.Finite B (R ⧸ Ideal.span {algebraMap A R π})]
    (ε : (R ⧸ Ideal.span {algebraMap A R π}) →ₐ[B] B)
    (hnil : IsNilpotent (RingHom.ker ε)) :
    letI : (RingHom.ker ε).IsPrime := RingHom.ker_isPrime ε
    ∃ xs : List R,
      (xs.length : WithBot ℕ∞) = ringKrullDim B ∧
      (∀ x ∈ xs, x ∈ IsLocalRing.maximalIdeal R) ∧
      Module.Flat A (R ⧸ Ideal.ofList xs) ∧
      Module.length (R ⧸ (Ideal.span {algebraMap A R π} ⊔ Ideal.ofList xs))
        (R ⧸ (Ideal.span {algebraMap A R π} ⊔ Ideal.ofList xs)) =
      Module.length (Localization.AtPrime (RingHom.ker ε))
        (Localization.AtPrime (RingHom.ker ε)) := by
  let I := Ideal.span {algebraMap A R π}
  have : IsLocalHom (algebraMap B (R ⧸ I)) := ⟨fun b hb => by
    simpa using hb.map ε.toRingHom⟩
  obtain ⟨xs, hlen, hmem, hflat, hideal⟩ :=
    a3b4a_gysin_exists_flat_slice_parameters (B := B) (R := R) π hπ
  refine ⟨xs, hlen, hmem, hflat, ?_⟩
  have hlength := a3b4a_gysin_nilpotent_parameter_length ε hnil
  rw [← hideal] at hlength
  exact (a3b2_length_eq_of_ringEquiv
    (DoubleQuot.quotQuotEquivQuotSup I (Ideal.ofList xs))).symm.trans hlength

end HodgeLean.Adapters
