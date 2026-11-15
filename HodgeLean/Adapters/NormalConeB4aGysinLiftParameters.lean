import HodgeLean.Adapters.IntersectionProductCMQuotient
import HodgeLean.Adapters.NormalConeB4aGysinSliceFlat
import Mathlib.RingTheory.Regular.Flat

/-! # Lifting parameters from a flat local normalization -/

noncomputable section
namespace HodgeLean.Adapters

/-- Parameters of a regular local base lift to a regular sequence on a flat
local quotient, with their length and extended parameter ideal retained. -/
theorem a3b4a_gysin_lift_flat_local_parameters
    {B R : Type*} [CommRing B] [IsRegularLocalRing B]
    [CommRing R] [IsLocalRing R] (I : Ideal R) [Nontrivial (R ⧸ I)]
    [Algebra B (R ⧸ I)] [Module.Flat B (R ⧸ I)]
    [IsLocalHom (algebraMap B (R ⧸ I))] :
    ∃ xs : List R,
      (xs.length : WithBot ℕ∞) = ringKrullDim B ∧
      (∀ x ∈ xs, x ∈ IsLocalRing.maximalIdeal R) ∧
      RingTheory.Sequence.IsRegular (R ⧸ I) xs ∧
      (Ideal.ofList xs).map (Ideal.Quotient.mk I) =
        (IsLocalRing.maximalIdeal B).map (algebraMap B (R ⧸ I)) := by
  letI : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  letI : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨ys, hlen, hys, -, hreg⟩ := a3c_exists_regular_sop B
  let s : R ⧸ I → R := Function.surjInv Ideal.Quotient.mk_surjective
  have hs : ∀ y, Ideal.Quotient.mk I (s y) = y :=
    Function.surjInv_eq Ideal.Quotient.mk_surjective
  let xs := (ys.map (algebraMap B (R ⧸ I))).map s
  have hmap : xs.map (algebraMap R (R ⧸ I)) =
      ys.map (algebraMap B (R ⧸ I)) := by
    simp only [xs, List.map_map]
    exact List.map_congr_left fun y _ => hs _
  have hmem : ∀ x ∈ xs, x ∈ IsLocalRing.maximalIdeal R := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
    rw [← IsLocalRing.maximalIdeal_comap (Ideal.Quotient.mk I), Ideal.mem_comap, hs]
    change z ∈ (IsLocalRing.maximalIdeal (R ⧸ I)).comap (algebraMap B (R ⧸ I))
    rw [IsLocalRing.maximalIdeal_comap]
    exact hys ▸ Ideal.subset_span hz
  refine ⟨xs, by simpa [xs] using hlen, hmem, ?_, ?_⟩
  · apply (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem).mpr
    rw [← RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff (S := R ⧸ I), hmap]
    exact hreg.of_flat
  · rw [Ideal.map_ofList]
    change Ideal.ofList (xs.map (algebraMap R (R ⧸ I))) = _
    rw [hmap, ← Ideal.map_ofList, hys]

/-- A flat local normalization of the special fibre supplies lifted parameters
whose slice of the total local algebra stays flat over the parameter DVR. -/
theorem a3b4a_gysin_exists_flat_slice_parameters
    {A B R : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsRegularLocalRing B]
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra A R]
    [Module.Flat A R] (π : A) (hπ : Irreducible π)
    [Nontrivial (R ⧸ Ideal.span {algebraMap A R π})]
    [Algebra B (R ⧸ Ideal.span {algebraMap A R π})]
    [Module.Flat B (R ⧸ Ideal.span {algebraMap A R π})]
    [IsLocalHom (algebraMap B (R ⧸ Ideal.span {algebraMap A R π}))] :
    ∃ xs : List R,
      (xs.length : WithBot ℕ∞) = ringKrullDim B ∧
      (∀ x ∈ xs, x ∈ IsLocalRing.maximalIdeal R) ∧
      Module.Flat A (R ⧸ Ideal.ofList xs) ∧
      (Ideal.ofList xs).map (Ideal.Quotient.mk (Ideal.span {algebraMap A R π})) =
        (IsLocalRing.maximalIdeal B).map
          (algebraMap B (R ⧸ Ideal.span {algebraMap A R π})) := by
  obtain ⟨xs, hlen, hmem, hreg, hideal⟩ :=
    a3b4a_gysin_lift_flat_local_parameters (B := B)
      (Ideal.span {algebraMap A R π})
  refine ⟨xs, hlen, hmem, ?_, hideal⟩
  apply a3b4a_gysin_regular_slice_flat π hπ xs
  unfold QuotSMulTop
  rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
  exact hreg

end HodgeLean.Adapters
