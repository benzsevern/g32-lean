import HodgeLean.Adapters.NormalConeB2Defs

/-! # Localization of the extended Rees algebra

Localizing the coefficient ring away from one element localizes the extended Rees algebra,
through the functorial map of stage A3-B2. The proof works coefficient by coefficient.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicGeometry LaurentPolynomial

/-- Coefficients of the image of an element under the functorial map.
Source: Mathlib, `AddMonoidAlgebra.coeff_mapRingHom`. -/
theorem a3b2_deformationMap_coeff {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (I : Ideal R) (J : Ideal S) (h : I.map φ ≤ J) (x : a3cc3_deformationAlgebra I) (n : ℤ) :
    ((a3b2_deformationMap φ I J h x : LaurentPolynomial S)).coeff n =
      φ ((x : LaurentPolynomial R).coeff n) :=
  AddMonoidAlgebra.coeff_mapRingHom _ _ _

/-- Coefficients of a scalar multiple in the extended Rees algebra.
Source: Mathlib, `AddMonoidAlgebra.coeff_smul`. -/
theorem a3b2_algebraMap_mul_coeff {R : Type*} [CommRing R] (I : Ideal R) (r : R)
    (x : a3cc3_deformationAlgebra I) (n : ℤ) :
    ((algebraMap R (a3cc3_deformationAlgebra I) r * x : a3cc3_deformationAlgebra I) :
      LaurentPolynomial R).coeff n = r * (x : LaurentPolynomial R).coeff n := by
  rw [← Algebra.smul_def]
  rfl

/-- Localization of the extended Rees algebra away from one element, for any localization.
Source: Fulton, *Intersection Theory*, second edition, §5.1, p. 88; Atiyah–Macdonald,
*Introduction to Commutative Algebra*, Proposition 3.3. -/
theorem a3b2_isLocalization_away {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal R) (f : R) [IsLocalization.Away f S] :
    letI : Algebra (a3cc3_deformationAlgebra I)
        (a3cc3_deformationAlgebra (I.map (algebraMap R S))) :=
      (a3b2_deformationMap (algebraMap R S) I _ le_rfl).toAlgebra
    IsLocalization.Away (algebraMap R (a3cc3_deformationAlgebra I) f)
      (a3cc3_deformationAlgebra (I.map (algebraMap R S))) := by
  set φ := algebraMap R S
  set J := I.map φ
  set Φ := a3b2_deformationMap φ I J le_rfl
  letI : Algebra (a3cc3_deformationAlgebra I) (a3cc3_deformationAlgebra J) := Φ.toAlgebra
  have hΦ : ∀ x, algebraMap (a3cc3_deformationAlgebra I) (a3cc3_deformationAlgebra J) x =
      Φ x := fun _ => rfl
  have hcoeff : ∀ x n, ((Φ x : LaurentPolynomial S)).coeff n =
      φ ((x : LaurentPolynomial R).coeff n) := fun x n => a3b2_deformationMap_coeff _ _ _ _ x n
  have hpow : ∀ (x : a3cc3_deformationAlgebra I) (N : ℕ),
      x * (algebraMap R (a3cc3_deformationAlgebra I) f) ^ N =
        algebraMap R (a3cc3_deformationAlgebra I) (f ^ N) * x := by
    intro x N
    rw [map_pow, mul_comm]
  have hfu : IsUnit (φ f) := IsLocalization.Away.algebraMap_isUnit f
  refine
    { map_units := ?_
      surj := ?_
      exists_of_eq := ?_ }
  · rintro ⟨_, N, rfl⟩
    change IsUnit (algebraMap _ _ ((algebraMap R (a3cc3_deformationAlgebra I) f) ^ N))
    rw [map_pow]
    refine IsUnit.pow N ?_
    rw [hΦ]
    obtain ⟨u, hu⟩ := hfu
    refine ⟨⟨Φ (algebraMap R _ f),
      ⟨C (u⁻¹ : Sˣ).1, (a3cc3_mem_deformationAlgebra_iff J _).2 fun n => ?_⟩, ?_, ?_⟩, rfl⟩
    · by_cases hn : n = 0
      · subst hn; simp
      · rw [C_apply, if_neg hn]; exact Ideal.zero_mem _
    · apply Subtype.ext
      change (AddMonoidAlgebra.mapRingHom ℤ φ) (C f) * C (u⁻¹ : Sˣ).1 = 1
      rw [show (AddMonoidAlgebra.mapRingHom ℤ φ) (C f) = C (φ f) from
        AddMonoidAlgebra.mapRingHom_single _ _ _, ← map_mul, ← hu]
      simp
    · apply Subtype.ext
      change C (u⁻¹ : Sˣ).1 * (AddMonoidAlgebra.mapRingHom ℤ φ) (C f) = 1
      rw [show (AddMonoidAlgebra.mapRingHom ℤ φ) (C f) = C (φ f) from
        AddMonoidAlgebra.mapRingHom_single _ _ _, ← map_mul, ← hu]
      simp
  · intro b
    classical
    have hb : ∀ n : ℤ, ∃ (c : R) (N : ℕ), c ∈ I ^ (-n).toNat ∧
        (b : LaurentPolynomial S).coeff n * φ f ^ N = φ c := by
      intro n
      have h := (a3cc3_mem_deformationAlgebra_iff J _).1 b.2 n
      rw [show J ^ (-n).toNat = (I ^ (-n).toNat).map φ from (Ideal.map_pow _ _ _).symm,
        IsLocalization.mem_map_algebraMap_iff (Submonoid.powers f) S] at h
      obtain ⟨⟨⟨c, hc⟩, ⟨_, N, rfl⟩⟩, h⟩ := h
      exact ⟨c, N, hc, by simpa using h⟩
    choose c N hc hcN using hb
    set s := (b : LaurentPolynomial S).coeff.support
    set M := ∑ n ∈ s, N n
    have hle : ∀ n ∈ s, N n ≤ M := fun n hn => Finset.single_le_sum (fun _ _ => Nat.zero_le _) hn
    let a : LaurentPolynomial R := AddMonoidAlgebra.ofCoeff
      (Finsupp.onFinset s (fun n => if n ∈ s then c n * f ^ (M - N n) else 0) (by
        intro n hn
        by_contra h
        exact hn (if_neg h)))
    have ha : a ∈ a3cc3_deformationAlgebra I := by
      rw [a3cc3_mem_deformationAlgebra_iff]
      intro n
      change (if n ∈ s then c n * f ^ (M - N n) else 0) ∈ _
      split_ifs
      · exact Ideal.mul_mem_right _ _ (hc n)
      · exact Ideal.zero_mem _
    refine ⟨⟨⟨a, ha⟩, ⟨_, ⟨M, rfl⟩⟩⟩, ?_⟩
    change b * Φ (algebraMap R _ f ^ M) = Φ ⟨a, ha⟩
    apply Subtype.ext
    apply AddMonoidAlgebra.coeff_injective
    ext n
    rw [map_pow, mul_comm, show Φ (algebraMap R _ f) =
      algebraMap S (a3cc3_deformationAlgebra J) (φ f) from Subtype.ext
        (AddMonoidAlgebra.mapRingHom_single _ _ _), ← map_pow]
    change ((algebraMap S (a3cc3_deformationAlgebra J) (φ f ^ M) * b :
      a3cc3_deformationAlgebra J) : LaurentPolynomial S).coeff n =
      (Φ ⟨a, ha⟩ : LaurentPolynomial S).coeff n
    rw [a3b2_algebraMap_mul_coeff, hcoeff]
    change _ = φ (if n ∈ s then c n * f ^ (M - N n) else 0)
    split_ifs with hn
    · rw [map_mul, ← hcN, map_pow, mul_assoc, ← pow_add, Nat.add_sub_cancel' (hle n hn),
        mul_comm]
    · rw [Finsupp.notMem_support_iff.1 hn, mul_zero, map_zero]
  · intro x y hxy
    classical
    have h0 : Φ (x - y) = 0 := by rw [map_sub, sub_eq_zero]; exact hxy
    have hz : ∀ n : ℤ, ∃ N : ℕ, f ^ N * ((x - y : a3cc3_deformationAlgebra I) :
        LaurentPolynomial R).coeff n = 0 := by
      intro n
      have h := congrArg (fun p : a3cc3_deformationAlgebra J => (p : LaurentPolynomial S).coeff n)
        h0
      simp only [hcoeff] at h
      obtain ⟨⟨_, N, rfl⟩, hN⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers f) S _).1 h
      exact ⟨N, hN⟩
    choose N hN using hz
    set s := ((x - y : a3cc3_deformationAlgebra I) : LaurentPolynomial R).coeff.support
    set M := ∑ n ∈ s, N n
    have hle : ∀ n ∈ s, N n ≤ M := fun n hn => Finset.single_le_sum (fun _ _ => Nat.zero_le _) hn
    refine ⟨⟨_, ⟨M, rfl⟩⟩, ?_⟩
    change (algebraMap R _ f) ^ M * x = (algebraMap R _ f) ^ M * y
    rw [← sub_eq_zero, ← mul_sub, ← map_pow]
    apply Subtype.ext
    apply AddMonoidAlgebra.coeff_injective
    ext n
    rw [a3b2_algebraMap_mul_coeff]
    change _ = (0 : R)
    by_cases hn : n ∈ s
    · rw [← Nat.sub_add_cancel (hle n hn), pow_add, mul_assoc, hN n, mul_zero]
    · rw [Finsupp.notMem_support_iff.1 hn, mul_zero]

end HodgeLean.Adapters
