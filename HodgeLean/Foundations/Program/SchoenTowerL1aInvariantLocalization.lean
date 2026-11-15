import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Operations
import Mathlib.Algebra.Module.Rat

/-! # Invariant numerators on principal open subsets

Implication from compatible endomorphisms of a domain and its principal
localization to an invariant numerator for every invariant localized element.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- An invariant localized element has an invariant numerator when its denominator is fixed.
Source: Hartshorne, Algebraic Geometry, II.2, localization on principal affine opens. -/
theorem s2v_l1a_invariant_localization_numerator
    {R A T : Type*} [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]
    (d : R) [IsLocalization.Away d A]
    (ρ : T → (R →+* R)) (σ : T → (A →+* A))
    (hmap : ∀ t, (σ t).comp (algebraMap R A) = (algebraMap R A).comp (ρ t))
    (hd : ∀ t, ρ t d = d)
    (s : A) (hs : ∀ t, σ t s = s) :
    ∃ (n : ℕ) (r : R), (∀ t, ρ t r = r) ∧
      s * algebraMap R A d ^ n = algebraMap R A r := by
  by_cases hd0 : d = 0
  · refine ⟨1, 0, fun t => map_zero _, ?_⟩
    simp only [hd0, map_zero, pow_one, mul_zero]
  · have hinj := IsLocalization.injective A
      (powers_le_nonZeroDivisors_of_noZeroDivisors hd0)
    obtain ⟨n, r, hr⟩ := IsLocalization.Away.surj d s
    refine ⟨n, r, ?_, hr⟩
    intro t
    apply hinj
    have hm (x : R) : σ t (algebraMap R A x) = algebraMap R A (ρ t x) :=
      DFunLike.congr_fun (hmap t) x
    rw [← hm, ← hr, map_mul, map_pow, hm, hs t, hd t]

/-- For a finite action in characteristic zero, averaging supplies invariant numerators
without a domain assumption.
Source: Stacks Project, tag 04A9, invariant functions under a group action; localization and finite averaging. -/
theorem s2v_l1a_invariant_localization_numerator_of_finite_action
    {R A G : Type*} [CommRing R] [CommRing A] [Group G] [Fintype G]
    [Algebra ℚ R] [Algebra ℚ A] [Algebra R A] [IsScalarTower ℚ R A]
    [MulSemiringAction G R] [MulSemiringAction G A]
    [SMulCommClass G ℚ R] [SMulCommClass G ℚ A]
    (d : R) [IsLocalization.Away d A]
    (hmap : ∀ (g : G) (r : R), g • algebraMap R A r = algebraMap R A (g • r))
    (hd : ∀ g : G, g • d = d) (s : A) (hs : ∀ g : G, g • s = s) :
    ∃ (n : ℕ) (r : R), (∀ g : G, g • r = r) ∧
      s * algebraMap R A d ^ n = algebraMap R A r := by
  classical
  obtain ⟨n, r, hr⟩ := IsLocalization.Away.surj d s
  let r' : R := (Fintype.card G : ℚ)⁻¹ • ∑ g : G, g • r
  have hcard : (Fintype.card G : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hfixed (g : G) : g • r' = r' := by
    dsimp only [r']
    rw [smul_comm, Finset.smul_sum]
    simp_rw [smul_smul]
    congr 1
    exact Equiv.sum_comp (Equiv.mulLeft g) (fun h : G => h • r)
  have hgr (g : G) : algebraMap R A (g • r) = s * algebraMap R A d ^ n := by
    rw [← hmap, ← hr, smul_mul', smul_pow', hs, hmap, hd]
  refine ⟨n, r', hfixed, ?_⟩
  symm
  change (IsScalarTower.toAlgHom ℚ R A) r' = _
  simp only [r', map_smul, map_sum]
  change (Fintype.card G : ℚ)⁻¹ • ∑ g : G, algebraMap R A (g • r) = _
  simp_rw [hgr]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℚ,
    smul_smul, inv_mul_cancel₀ hcard, one_smul]

/-- An invariant element is a unit in the fixed subalgebra precisely when it is a unit in the ambient ring.
Source: Stacks Project, tag 04A9, invariant functions; uniqueness of multiplicative inverses. -/
theorem s2v_l1a_isUnit_fixed_subalgebra
    {R G : Type*} [CommRing R] [Group G] [Algebra ℚ R]
    [MulSemiringAction G R] [SMulCommClass G ℚ R]
    (r : FixedPoints.subalgebra ℚ R G) : IsUnit r ↔ IsUnit (r : R) := by
  constructor
  · exact fun h => h.map (FixedPoints.subalgebra ℚ R G).val.toRingHom
  · rintro ⟨u, hu⟩
    have hufix (g : G) : g • (u : R) = (u : R) := by
      rw [hu]
      exact r.property g
    have hinv (g : G) : g • (↑(u⁻¹) : R) = ↑(u⁻¹) := by
      apply u.isUnit.mul_left_cancel
      calc
        (u : R) * (g • (↑(u⁻¹) : R)) =
            (g • (u : R)) * (g • (↑(u⁻¹) : R)) := by rw [hufix]
        _ = g • ((u : R) * (↑(u⁻¹) : R)) := (smul_mul' g _ _).symm
        _ = 1 := by simp
        _ = (u : R) * (↑(u⁻¹) : R) := by simp
    refine ⟨⟨r, ⟨↑(u⁻¹), hinv⟩, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext
      change (r : R) * (↑(u⁻¹) : R) = 1
      rw [← hu]
      exact u.val_inv
    · apply Subtype.ext
      change (↑(u⁻¹) : R) * (r : R) = 1
      rw [← hu]
      exact u.inv_val

/-- Finite-group invariants commute with principal localization when the denominator is invariant.
Source: Stacks Project, tag 04A9, invariant functions; localization and finite averaging. -/
theorem s2v_l1a_fixed_subalgebra_localization
    {R A G : Type*} [CommRing R] [CommRing A] [Group G] [Fintype G]
    [Algebra ℚ R] [Algebra ℚ A] [Algebra R A] [IsScalarTower ℚ R A]
    [MulSemiringAction G R] [MulSemiringAction G A]
    [SMulCommClass G ℚ R] [SMulCommClass G ℚ A]
    [Algebra (FixedPoints.subalgebra ℚ R G) (FixedPoints.subalgebra ℚ A G)]
    (hfixedMap : ∀ r : FixedPoints.subalgebra ℚ R G,
      (algebraMap (FixedPoints.subalgebra ℚ R G) (FixedPoints.subalgebra ℚ A G) r : A) =
        algebraMap R A (r : R))
    (d : R) [IsLocalization.Away d A]
    (hmap : ∀ (g : G) (r : R), g • algebraMap R A r = algebraMap R A (g • r))
    (hd : ∀ g : G, g • d = d) :
    IsLocalization.Away (⟨d, hd⟩ : FixedPoints.subalgebra ℚ R G)
      (FixedPoints.subalgebra ℚ A G) := by
  apply IsLocalization.Away.mk
  · apply (s2v_l1a_isUnit_fixed_subalgebra _).mpr
    rw [hfixedMap]
    exact IsLocalization.map_units A ⟨d, Submonoid.mem_powers d⟩
  · intro s
    obtain ⟨n, r, hr, heq⟩ := s2v_l1a_invariant_localization_numerator_of_finite_action
      d hmap hd (s : A) s.property
    refine ⟨n, ⟨r, hr⟩, ?_⟩
    apply Subtype.ext
    change (s : A) *
      (algebraMap (FixedPoints.subalgebra ℚ R G) (FixedPoints.subalgebra ℚ A G)
        ⟨d, hd⟩ : A) ^ n = _
    rw [hfixedMap, hfixedMap]
    exact heq
  · intro a b hab
    have heq : algebraMap R A (a : R) = algebraMap R A (b : R) := by
      simpa only [hfixedMap] using congrArg Subtype.val hab
    obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq d heq
    refine ⟨n, ?_⟩
    exact Subtype.ext hn

/-- Finitely many fixed-point equations have a common invariant numerator after clearing their localization denominators.
Source: Hartshorne, Algebraic Geometry, II.2, localization and finitely many equations. -/
theorem s2v_l1a_invariant_localization_numerator_of_finite_family
    {R A T : Type*} [CommRing R] [CommRing A] [Algebra R A] [Finite T]
    (d : R) [IsLocalization.Away d A]
    (ρ : T → (R →+* R)) (σ : T → (A →+* A))
    (hmap : ∀ t, (σ t).comp (algebraMap R A) = (algebraMap R A).comp (ρ t))
    (hd : ∀ t, ρ t d = d) (s : A) (hs : ∀ t, σ t s = s) :
    ∃ (n : ℕ) (r : R), (∀ t, ρ t r = r) ∧
      s * algebraMap R A d ^ n = algebraMap R A r := by
  classical
  letI := Fintype.ofFinite T
  obtain ⟨n, r, hr⟩ := IsLocalization.Away.surj d s
  have heq (t : T) : algebraMap R A (ρ t r) = algebraMap R A r := by
    have hm (x : R) : σ t (algebraMap R A x) = algebraMap R A (ρ t x) :=
      DFunLike.congr_fun (hmap t) x
    rw [← hm, ← hr, map_mul, map_pow, hm, hs t, hd t]
  choose m hm using fun t => IsLocalization.Away.exists_of_eq d (heq t)
  let N := ∑ t : T, m t
  refine ⟨n + N, d ^ N * r, ?_, ?_⟩
  · intro t
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le
      (Finset.single_le_sum (fun j _ => Nat.zero_le (m j)) (Finset.mem_univ t))
    change ρ t (d ^ N * r) = d ^ N * r
    rw [map_mul, map_pow, hd t]
    change d ^ N * ρ t r = d ^ N * r
    have hNt : N = m t + k := hk
    rw [hNt, pow_add]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using congrArg (fun x => d ^ k * x) (hm t)
  · rw [map_mul, map_pow, pow_add, ← mul_assoc, hr, mul_comm]

end HodgeLean.Foundations.Program
