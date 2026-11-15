import Mathlib

/-! Local normality for smooth root covers.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open TensorProduct
namespace AlgebraicGeometry.TameMonomialCover.Helpers
universe u w
variable {κbase : Type w} [Field κbase] [IsAlgClosed κbase] [CharZero κbase]
/-- A reduced Artinian ring whose only idempotents are `0` and `1` is a field.
Source: Mathlib, PrimeSpectrum.subsingleton_iff_isField_of_isReduced and PrimeSpectrum.isClopen_iff. -/
theorem isField_of_isArtinianRing {L : Type*} [CommRing L] [IsArtinianRing L]
    [_root_.IsReduced L] [Nontrivial L] (h : ∀ e : L, IsIdempotentElem e → e = 0 ∨ e = 1) :
    IsField L := by
  refine (PrimeSpectrum.subsingleton_iff_isField_of_isReduced).mp ⟨fun x y ↦ ?_⟩
  obtain ⟨e, he, hx⟩ := PrimeSpectrum.isClopen_iff.mp (isClopen_discrete {x})
  rcases h e he with rfl | rfl
  · have : x ∈ ({x} : Set (PrimeSpectrum L)) := rfl
    rw [hx] at this
    simp at this
  · have : y ∈ ({x} : Set (PrimeSpectrum L)) := by rw [hx]; simp
    exact (Set.mem_singleton_iff.mp this).symm

/-- The local rings of an étale algebra over a normal domain are normal domains.
Source: Mathlib, toIntegralClosure_bijective_of_smooth and Algebra.FormallyUnramified.isReduced_of_field. -/
theorem normal_localization_of_etale {T B : Type*} [CommRing T] [IsDomain T]
    [IsIntegrallyClosed T] [CommRing B] [Algebra T B] [Algebra.Etale T B] (q : Ideal B)
    [q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  let A := Localization.AtPrime q
  let K := FractionRing T
  have hbij : Function.Bijective (toIntegralClosure T A K) :=
    toIntegralClosure_bijective_of_tower (S := B) toIntegralClosure_bijective_of_smooth
      (toIntegralClosure_bijective_of_isLocalization q.primeCompl)
  -- Every element of `A ⊗[T] K` integral over `A` comes from `A`.
  have hmap (z : A ⊗[T] integralClosure T K) : ∃ a : A,
      algebraMap A (A ⊗[T] K) a = Algebra.TensorProduct.map (AlgHom.id T A)
        (integralClosure T K).val z := by
    induction z with
    | tmul a c =>
      obtain ⟨t, ht⟩ := IsIntegrallyClosed.isIntegral_iff.mp c.2
      refine ⟨t • a, ?_⟩
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.coe_val, ← ht,
        Algebra.algebraMap_eq_smul_one (A := K) t, tmul_smul, smul_tmul']
      rfl
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩
  have hint (y : A ⊗[T] K) (hy : _root_.IsIntegral A y) : ∃ a : A, algebraMap A _ a = y := by
    obtain ⟨z, hz⟩ := hbij.2 ⟨y, hy⟩
    obtain ⟨a, ha⟩ := hmap z
    refine ⟨a, ha.trans ?_⟩
    exact congrArg Subtype.val hz
  have hinj : Function.Injective (algebraMap A (A ⊗[T] K)) := by
    intro a b hab
    have h := Module.Flat.lTensor_preserves_injective_linearMap (M := A)
      (Algebra.linearMap T K) (IsFractionRing.injective T K)
    have e1 (x : A) : (Algebra.linearMap T K).lTensor A (x ⊗ₜ[T] (1 : T)) =
        algebraMap A (A ⊗[T] K) x := by
      rw [LinearMap.lTensor_tmul, Algebra.linearMap_apply, map_one]
      rfl
    have : (a ⊗ₜ[T] (1 : T)) = b ⊗ₜ[T] (1 : T) := h (by rw [e1, e1, hab])
    have := congrArg (TensorProduct.rid T A) this
    rwa [TensorProduct.rid_tmul, TensorProduct.rid_tmul, one_smul, one_smul] at this
  -- The ring `A ⊗[T] K` is a field.
  let L := K ⊗[T] A
  have : Module.Finite K L := Algebra.FormallyUnramified.finite_of_free K L
  have : IsArtinianRing L := isArtinian_of_tower K inferInstance
  have : _root_.IsReduced L := Algebra.FormallyUnramified.isReduced_of_field K L
  let e : A ⊗[T] K ≃ₐ[T] L := Algebra.TensorProduct.comm T A K
  have : Nontrivial (A ⊗[T] K) := hinj.nontrivial
  have : Nontrivial L := e.injective.nontrivial
  have hidem (x : L) (hx : IsIdempotentElem x) : x = 0 ∨ x = 1 := by
    have hy : IsIdempotentElem (e.symm x) := by
      rw [IsIdempotentElem, ← map_mul, hx.eq]
    obtain ⟨a, ha⟩ := hint (e.symm x) ⟨Polynomial.X ^ 2 - Polynomial.X,
      Polynomial.monic_X_pow_sub (Polynomial.degree_X_le.trans_lt (by norm_num)),
      by simp [sq, hy.eq]⟩
    have hia : IsIdempotentElem a := hinj (by rw [map_mul, ha, hy.eq])
    have : a = 0 ∨ a = 1 := by
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with h | h
      · exact Or.inr (h.mul_left_cancel (by rw [hia.eq, mul_one]))
      · exact Or.inl (h.mul_left_cancel (by rw [mul_zero, sub_mul, one_mul, hia.eq, sub_self]))
    rcases this with rfl | rfl
    · left
      rw [← e.apply_symm_apply x, ← ha, map_zero, map_zero]
    · right
      rw [← e.apply_symm_apply x, ← ha, map_one, map_one]
  have hfield : IsField (A ⊗[T] K) :=
    e.toMulEquiv.isField (isField_of_isArtinianRing hidem)
  have : IsDomain (A ⊗[T] K) := hfield.isDomain
  have : IsDomain A := hinj.isDomain (algebraMap A (A ⊗[T] K))
  refine ⟨this, (isIntegrallyClosed_iff (FractionRing A)).mpr fun {x} hx ↦ ?_⟩
  have hunit (y : nonZeroDivisors A) : IsUnit (algebraMap A (A ⊗[T] K) y) := by
    obtain ⟨b, hb⟩ := hfield.mul_inv_cancel
      ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero y.2))
    exact IsUnit.of_mul_eq_one _ hb
  let φ : FractionRing A →+* A ⊗[T] K := IsLocalization.lift hunit
  have hφ (a : A) : φ (algebraMap A (FractionRing A) a) = algebraMap A (A ⊗[T] K) a :=
    IsLocalization.lift_eq hunit a
  obtain ⟨a, ha⟩ := hint (φ x) (IsIntegral.map_of_comp_eq (RingHom.id A) φ
    (RingHom.ext fun a ↦ (hφ a).symm) hx)
  refine ⟨a, φ.injective ?_⟩
  rw [← ha, hφ]

/-- The local rings of a smooth algebra over a field are normal domains.
Source: Mathlib, Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial. -/
theorem normal_localization_of_smooth {k R : Type*} [Field k] [CommRing R]
    [Algebra k R] [Algebra.Smooth k R] (p : Ideal R) [p.IsPrime] :
    IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  obtain ⟨f, hf, n, _, _, _⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := k) (p := p)
  let q := p.map (algebraMap R (Localization.Away f))
  have hdisj : Disjoint (Submonoid.powers f : Set R) p :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hf
  have : q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (.powers f) _ _ ‹_› hdisj
  have hq : q.comap (algebraMap R (Localization.Away f)) = p :=
    IsLocalization.under_map_of_isPrime_disjoint (.powers f) _ ‹_› hdisj
  have : IsLocalization.AtPrime (Localization.AtPrime q) p := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.powers f) (Localization.AtPrime q) q
    convert this
    exact hq.symm
  let e : Localization.AtPrime p ≃+* Localization.AtPrime q :=
    (IsLocalization.algEquiv p.primeCompl _ _).toRingEquiv
  obtain ⟨_, h₂⟩ := normal_localization_of_etale (T := MvPolynomial (Fin n) k) q
  exact ⟨e.toMulEquiv.isDomain, h₂.of_equiv e.symm⟩

/-- Every prime localization of an etale algebra over the root polynomial ring is a normal domain.
Source: Mathlib, Algebra.Smooth.of_equiv, Algebra.Smooth.comp and Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial. -/
theorem etale_root_localization_normal
    (n : ℕ) (A : Type u) [CommRing A]
    (b : ULift.{0} (MvPolynomial (Fin n) κbase) →+* A) (hb : b.Etale)
    (p : Ideal A) [p.IsPrime] :
    IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  let B := ULift.{0} (MvPolynomial (Fin n) κbase)
  letI : Algebra B A := b.toAlgebra
  letI : SMul B A := (inferInstance : Algebra B A).toSMul
  letI : Module B A := Algebra.toModule (R := B) (A := A)
  letI : Algebra κbase A := (b.comp (algebraMap κbase B)).toAlgebra
  haveI : IsScalarTower κbase B A := IsScalarTower.of_algebraMap_eq' (R := κbase) (S := B) (A := A) rfl
  letI : Algebra.Etale B A := hb.toAlgebra
  letI : Algebra.Smooth κbase B := Algebra.Smooth.of_equiv
    (ULift.algEquiv (R := κbase) (A := MvPolynomial (Fin n) κbase)).symm
  letI : Algebra.Smooth κbase A := Algebra.Smooth.comp κbase B A
  exact normal_localization_of_smooth (k := κbase) p

/-- A field map on an integral cover selects a minimal prime when its restriction to the base is injective.
Source: Mathlib, Ideal.IsIntegral.mem_minimalPrimes_map_under and RingHom.comap_ker. -/
theorem integral_cover_kernel_minimal
    {R A L : Type*} [CommRing R] [CommRing A] [Field L]
    (i : R →+* A) (hi : i.IsIntegral) (τ : A →+* L)
    (hinj : Function.Injective (τ.comp i)) : IsMinimalPrime (RingHom.ker τ) := by
  letI := i.toAlgebra
  letI : Algebra.IsIntegral R A := algebraMap_isIntegral_iff.mp hi
  letI : (RingHom.ker τ).IsPrime := RingHom.ker_isPrime τ
  have hzero : (RingHom.ker τ).under R = ⊥ := by
    change (RingHom.ker τ).comap i = ⊥
    rw [RingHom.comap_ker]
    exact (RingHom.injective_iff_ker_eq_bot _).mp hinj
  have H := Ideal.IsIntegral.mem_minimalPrimes_map_under (R := R) (RingHom.ker τ)
  rw [hzero, Ideal.map_bot] at H
  exact H

/-- A minimal-prime field map embeds a domain localization at every prime containing its kernel.
Source: Mathlib, IsLocalization.lift and IsLocalization.minimalPrimes_map. -/
theorem localized_component_embedding
    {A L S : Type*} [CommRing A] [Field L] [CommRing S] [IsDomain S]
    (q : Ideal A) [q.IsPrime] [Algebra A S] [IsLocalization.AtPrime S q]
    (τ : A →+* L) (hmin : IsMinimalPrime (RingHom.ker τ))
    (hq : RingHom.ker τ ≤ q) :
    ∃ σ : S →+* L, Function.Injective σ ∧ σ.comp (algebraMap A S) = τ := by
  have hunit : ∀ y : q.primeCompl, IsUnit (τ y) := by
    intro y
    apply isUnit_iff_ne_zero.mpr
    intro hy
    exact y.2 (hq hy)
  let σ : S →+* L := IsLocalization.lift hunit
  have hσ : σ.comp (algebraMap A S) = τ := IsLocalization.lift_comp hunit
  have hker : (RingHom.ker σ).under A = RingHom.ker τ := by
    rw [Ideal.under_def, RingHom.comap_ker, hσ]
  have H : RingHom.ker σ ∈ ((⊥ : Ideal A).map (algebraMap A S)).minimalPrimes := by
    rw [IsLocalization.minimalPrimes_map q.primeCompl S]
    change IsMinimalPrime ((RingHom.ker σ).under A)
    rw [hker]
    exact hmin
  rw [Ideal.map_bot] at H
  have hzero : RingHom.ker σ = ⊥ := le_antisymm
    (H.2 ⟨inferInstance, bot_le⟩ bot_le) bot_le
  exact ⟨σ, (RingHom.injective_iff_ker_eq_bot σ).mpr hzero, hσ⟩

end AlgebraicGeometry.TameMonomialCover.Helpers
