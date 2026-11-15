import HodgeLean.Foundations.AnalyticGermExtension
import Mathlib.RingTheory.Polynomial.ScaleRoots

/-! # Finite analytic images and component comparison

Implication from finite proper representatives to analytic images, from faithful finite parameters to
neighbourhood surjectivity. Component dimensions use calibrated parameters.
Coefficient continuation, exact equations and point extension remain deferred.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Filter Topology Polynomial
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
namespace HodgeLean.Foundations

private def adim7_constantGerm (n : ℕ) : ℂ →+* AnalyticGerm n where
  toFun c := ⟨Germ.ofFun (fun _ ↦ c), fun _ ↦ c, analyticAt_const, rfl⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

private def adim7_linearGerm {n : ℕ} (ℓ : (Fin n → ℂ) →L[ℂ] ℂ) : AnalyticGerm n :=
  ⟨Germ.ofFun (fun z ↦ ℓ z), fun z ↦ ℓ z, ℓ.analyticAt 0, rfl⟩

private def adim7_linearGermMap {n : ℕ} {L : Type*} [CommRing L] [Algebra ℂ L]
    (f : AnalyticGerm n →+* L)
    (hconst : ∀ c, f (adim7_constantGerm n c) = algebraMap ℂ L c) :
    ((Fin n → ℂ) →L[ℂ] ℂ) →ₗ[ℂ] L where
  toFun ℓ := f (adim7_linearGerm ℓ)
  map_add' ℓ m := by
    have h : adim7_linearGerm (ℓ + m) = adim7_linearGerm ℓ + adim7_linearGerm m := rfl
    rw [h, map_add]
  map_smul' c ℓ := by
    have h : adim7_linearGerm (c • ℓ) =
        adim7_constantGerm n c * adim7_linearGerm ℓ := rfl
    rw [h, map_mul, hconst, Algebra.smul_def]
    rfl

private theorem adim7_finite_fraction_extension
    (A S K L : Type*) [CommRing A] [IsDomain A] [CommRing S] [IsDomain S]
    [Field K] [Field L] [CharZero K]
    [Algebra A S] [FaithfulSMul A S] [Module.Finite A S]
    [Algebra A K] [IsFractionRing A K] [Algebra S L] [IsFractionRing S L]
    [Algebra A L] [Algebra K L] [IsScalarTower A S L] [IsScalarTower A K L] :
    Module.Finite K L ∧ Algebra.IsSeparable K L ∧
      ∃ x : L, IntermediateField.adjoin K {x} = ⊤ := by
  letI : Module.Finite K L := Module.Finite.of_isLocalization A S (nonZeroDivisors A)
  exact ⟨inferInstance, inferInstance, Field.exists_primitive_element K L⟩

private theorem adim7_bezout_of_separable_fraction_map
    {A K : Type*} [CommRing A] [IsDomain A] [Field K]
    [Algebra A K] [IsFractionRing A K]
    (Q : Polynomial A) (hdeg : 0 < Q.natDegree)
    (hsep : (Q.map (algebraMap A K)).Separable) :
    ∃ (δ : A) (B C : Polynomial A), δ ≠ 0 ∧
      B * Q + C * Q.derivative = Polynomial.C δ := by
  let δ := Q.resultant Q.derivative
  have hinj := IsFractionRing.injective A K
  have hnz : δ ≠ 0 := by
    have h := Polynomial.resultant_ne_zero _ _ hsep
    rw [Polynomial.derivative_map] at h
    simp only [Polynomial.natDegree_map_eq_of_injective hinj,
      Polynomial.resultant_map_map] at h
    exact fun hz ↦ h (by change algebraMap A K δ = 0; rw [hz, map_zero])
  obtain ⟨B, C, _, _, hBC⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant
    Q Q.derivative le_rfl le_rfl (Or.inl (Nat.ne_of_gt hdeg))
  exact ⟨δ, B, C, hnz, by simpa only [mul_comm] using hBC⟩

private theorem adim7_clear_one_coordinate {A S K L : Type*} [CommRing A] [IsDomain A] [CommRing S] [IsDomain S]
    [Field K] [Field L] [Algebra A S] [Algebra A K] [IsFractionRing A K]
    [Algebra S L] [IsFractionRing S L] [Algebra A L] [Algebra K L]
    [IsScalarTower A S L] [IsScalarTower A K L]
    (v x : S) (hx : algebraMap S L x ∈ Algebra.adjoin K {algebraMap S L v}) :
    ∃ (a : A) (R : Polynomial A), a ≠ 0 ∧
      algebraMap A S a * x = Polynomial.aeval v R := by
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hx
  obtain ⟨p, hp⟩ := hx
  obtain ⟨a, ha, hR⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors A) p
  refine ⟨a, IsLocalization.integerNormalization (nonZeroDivisors A) p,
    nonZeroDivisors.ne_zero ha, ?_⟩
  apply IsFractionRing.injective S L
  rw [← IsScalarTower.algebraMap_smul K a p] at hR
  have he := congrArg (Polynomial.aeval (algebraMap S L v)) hR
  simp only [Polynomial.aeval_map_algebraMap, map_smul, hp,
    Polynomial.aeval_algebraMap_apply] at he
  simpa only [map_mul, ← IsScalarTower.algebraMap_apply, Algebra.smul_def] using he.symm

private theorem adim7_clear_coordinates
    {A S K L : Type*} [CommRing A] [IsDomain A] [CommRing S] [IsDomain S]
    [Field K] [Field L] [Algebra A S] [Algebra A K] [IsFractionRing A K]
    [Algebra S L] [IsFractionRing S L] [Algebra A L] [Algebra K L]
    [IsScalarTower A S L] [IsScalarTower A K L]
    {n : ℕ} (v : S) (x : Fin n → S)
    (hx : ∀ i, algebraMap S L (x i) ∈ Algebra.adjoin K {algebraMap S L v}) :
    ∃ (a : A) (R : Fin n → Polynomial A), a ≠ 0 ∧
      ∀ i, algebraMap A S a * x i = Polynomial.aeval v (R i) := by
  classical
  choose a R ha hR using fun i ↦ adim7_clear_one_coordinate (A := A) v (x i) (hx i)
  let b : Fin n → A := fun i ↦ ∏ j ∈ Finset.univ.erase i, a j
  refine ⟨∏ i, a i, fun i ↦ Polynomial.C (b i) * R i,
    Finset.prod_ne_zero_iff.mpr (fun i _ ↦ ha i), fun i ↦ ?_⟩
  have hprod : (∏ j, a j) = b i * a i :=
    (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm
  rw [hprod, map_mul, mul_assoc, hR i, map_mul, Polynomial.aeval_C]

open IntermediateField in
private theorem adim7_primitive_pair_in_infinite_set {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra K L] [Finite (IntermediateField K L)]
    (ι : k →+* K) (s : Set k) (hs : s.Infinite) (α β : L) :
    ∃ c ∈ s, IntermediateField.adjoin K {α, β} =
      IntermediateField.adjoin K {α + (ι c) • β} := by
  letI : Infinite s := hs.to_subtype
  let f : s → IntermediateField K L := fun c ↦ adjoin K {α + (ι c.val) • β}
  obtain ⟨x, y, hneq, heq⟩ := Finite.exists_ne_map_eq_of_infinite f
  refine ⟨x.val, x.property, le_antisymm ?_ ?_⟩
  · rw [adjoin_le_iff]
    have hx : α + (ι x.val) • β ∈ adjoin K {α + (ι x.val) • β} :=
      mem_adjoin_simple_self K _
    have hy : α + (ι y.val) • β ∈ adjoin K {α + (ι x.val) • β} := by
      rw [show adjoin K {α + (ι x.val) • β} = adjoin K {α + (ι y.val) • β} from heq]
      exact mem_adjoin_simple_self K _
    have hβ := sub_mem hx hy
    rw [show (α + (ι x.val) • β) - (α + (ι y.val) • β) =
      (ι x.val - ι y.val) • β by rw [sub_smul]; abel] at hβ
    replace hβ := smul_mem _ hβ (x := (ι x.val - ι y.val)⁻¹)
    have hdiff : ι x.val - ι y.val ≠ 0 :=
      sub_ne_zero.mpr (fun h ↦ hneq (Subtype.ext (ι.injective h)))
    rw [smul_smul, inv_mul_cancel₀ hdiff, one_smul] at hβ
    have hα : α ∈ adjoin K {α + (ι x.val) • β} := by
      simpa using sub_mem hx (smul_mem _ hβ (x := ι x.val))
    rintro z (rfl | rfl) <;> assumption
  · rw [adjoin_simple_le_iff]
    have hα : α ∈ adjoin K {α, β} := subset_adjoin K _ (Set.mem_insert α {β})
    have hβ : β ∈ adjoin K {α, β} := subset_adjoin K _ (Set.mem_insert_of_mem α rfl)
    exact (adjoin K {α, β}).add_mem hα ((adjoin K {α, β}).smul_mem hβ)

private theorem adim7_good_scalars_infinite (a b : ℂ) (ha : a ≠ 0) :
    {c : ℂ | a + c * b ≠ 0}.Infinite := by
  by_cases hb : b = 0
  · have hset : {c : ℂ | a + c * b ≠ 0} = Set.univ := by ext c; simp [hb, ha]
    rw [hset]
    exact Set.infinite_univ
  · apply Set.infinite_of_finite_compl
    apply (Set.finite_singleton (-a / b)).subset
    intro c hc
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_not] at hc
    simp only [Set.mem_singleton_iff]
    apply (eq_div_iff hb).mpr
    linear_combination hc


private theorem adim7_linear_primitive_with_constraint
    {K L V : Type*} [Field K] [Field L]
    [Algebra ℂ K] [Algebra ℂ L] [Algebra K L] [IsScalarTower ℂ K L]
    [Finite (IntermediateField K L)] [AddCommGroup V] [Module ℂ V]
    (T : V →ₗ[ℂ] L) (e : V →ₗ[ℂ] ℂ) (v₀ : V) (hv₀ : e v₀ ≠ 0 ∨ e = 0)
    (s : Finset V) :
    ∃ v : V, (e v ≠ 0 ∨ e = 0) ∧
      ∀ x ∈ s, T x ∈ IntermediateField.adjoin K {T v} := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨v₀, hv₀, by simp⟩
  | @insert x s hx ih =>
    obtain ⟨v, hv, hmem⟩ := ih
    let good : Set ℂ := {c | e v + c * e x ≠ 0 ∨ e = 0}
    have hgood : good.Infinite := by
      rcases hv with hv | he
      · exact (adim7_good_scalars_infinite (e v) (e x) hv).mono
          (fun c hc ↦ Or.inl hc)
      · simpa only [good, he, or_true, Set.setOf_true] using (Set.infinite_univ : (Set.univ : Set ℂ).Infinite)
    obtain ⟨c, hc, hfield⟩ := adim7_primitive_pair_in_infinite_set
      (algebraMap ℂ K) good hgood (T v) (T x)
    have hTv : T (v + c • x) = T v + (algebraMap ℂ K c) • T x := by
      rw [map_add, map_smul, IsScalarTower.algebraMap_smul]
    refine ⟨v + c • x, ?_, ?_⟩
    · simpa only [good, Set.mem_setOf_eq, map_add, map_smul, smul_eq_mul] using hc
    · intro y hy
      rw [hTv, ← hfield]
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact IntermediateField.subset_adjoin K _ (Set.mem_insert_of_mem _ rfl)
      · apply (show IntermediateField.adjoin K {T v} ≤
            IntermediateField.adjoin K {T v, T x} from ?_) (hmem y hy)
        apply IntermediateField.adjoin.mono
        exact Set.singleton_subset_iff.mpr (Set.mem_insert _ _)

private theorem adim7_weierstrass_of_monic_dvd {d : ℕ}
    {Q W : Polynomial (AnalyticGerm d)} (hW : IsWeierstrassPolynomial W)
    (hQ : Q.Monic) (hdeg : 0 < Q.natDegree) (hdiv : Q ∣ W) :
    IsWeierstrassPolynomial Q := by
  have hWmap : W.map (analyticGermValue d) = X ^ W.natDegree := by
    ext j
    rw [coeff_map, coeff_X_pow]
    split_ifs with hj
    · subst j
      rw [← leadingCoeff, hW.1, map_one]
    · by_cases hjlt : j < W.natDegree
      · exact hW.2.2 j hjlt
      · rw [coeff_eq_zero_of_natDegree_lt (by omega), map_zero]
  have hmapdiv : Q.map (analyticGermValue d) ∣ X ^ W.natDegree := by
    rw [← hWmap]
    exact Polynomial.map_dvd _ hdiv
  obtain ⟨k, _, hk⟩ := (dvd_prime_pow (prime_X (R := ℂ)) W.natDegree).mp hmapdiv
  have heq : Q.map (analyticGermValue d) = X ^ k :=
    eq_of_monic_of_associated (hQ.map _) (monic_X_pow k) hk
  have hkdeg : k = Q.natDegree := by
    simpa only [hQ.natDegree_map, natDegree_X_pow] using
      (congrArg Polynomial.natDegree heq).symm
  refine ⟨hQ, hdeg, fun j hj ↦ ?_⟩
  change analyticGermValue d (Q.coeff j) = 0
  have hcoeff := congrArg (fun p : Polynomial ℂ ↦ p.coeff j) heq
  simpa only [coeff_map, coeff_X_pow, hkdeg, if_neg (ne_of_lt hj)] using hcoeff

private theorem adim7_exists_exact_monic_relation (n d : ℕ)
    (P : Ideal (AnalyticGerm n)) (hP : P.IsPrime)
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hfinite : θ.Finite) (hinj : Function.Injective θ)
    (v : AnalyticGerm n) :
    ∃ Q : Polynomial (AnalyticGerm d), Q.Monic ∧ 0 < Q.natDegree ∧
      ∀ T : Polynomial (AnalyticGerm d),
        T.eval₂ θ (Ideal.Quotient.mk P v) = 0 ↔ Q ∣ T := by
  letI : P.IsPrime := hP
  letI : UniqueFactorizationMonoid (AnalyticGerm d) := spec_analyticGerm_ufd d
  letI : IsDomain (AnalyticGerm d) := {}
  letI : Algebra (AnalyticGerm d) (AnalyticGerm n ⧸ P) := θ.toAlgebra
  letI : Module.IsTorsionFree (AnalyticGerm d) (AnalyticGerm n ⧸ P) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  have hv : IsIntegral (AnalyticGerm d) (Ideal.Quotient.mk P v) :=
    hfinite.to_isIntegral _
  exact ⟨minpoly (AnalyticGerm d) (Ideal.Quotient.mk P v),
    minpoly.monic hv, minpoly.natDegree_pos hv,
    fun T ↦ minpoly.isIntegrallyClosed_dvd_iff hv T⟩

private theorem adim7_exists_linear_form_ne_zero_on_ker (n d : ℕ)
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)) (hnd : d < n) :
    ∃ (ℓ : (Fin n → ℂ) →L[ℂ] ℂ) (z : Fin n → ℂ), π z = 0 ∧ ℓ z ≠ 0 := by
  have hker : LinearMap.ker π.toLinearMap ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    simpa using hnd
  obtain ⟨z, hzker, hz⟩ := (Submodule.ne_bot_iff _).mp hker
  have hzi : ∃ i, z i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hz (funext h)
  obtain ⟨i, hi⟩ := hzi
  exact ⟨ContinuousLinearMap.proj i, z, hzker, hi⟩

private theorem adim7_exists_primitive_linear_form
    {K L : Type*} [Field K] [Field L]
    [Algebra ℂ K] [Algebra ℂ L] [Algebra K L] [IsScalarTower ℂ K L]
    [Finite (IntermediateField K L)] (n d : ℕ)
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (T : ((Fin n → ℂ) →L[ℂ] ℂ) →ₗ[ℂ] L) :
    ∃ ℓ : (Fin n → ℂ) →L[ℂ] ℂ,
      (d < n → ∃ z, π z = 0 ∧ ℓ z ≠ 0) ∧
      ∀ i : Fin n, T (ContinuousLinearMap.proj i) ∈ IntermediateField.adjoin K {T ℓ} := by
  classical
  let s := Finset.univ.image (fun i : Fin n ↦ (ContinuousLinearMap.proj i :
    (Fin n → ℂ) →L[ℂ] ℂ))
  have hmem (i : Fin n) : (ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℂ] ℂ) ∈ s :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  by_cases hnd : d < n
  · obtain ⟨ℓ₀, z, hzπ, hzℓ⟩ := adim7_exists_linear_form_ne_zero_on_ker n d π hnd
    let e : ((Fin n → ℂ) →L[ℂ] ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun ℓ ↦ ℓ z, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
    obtain ⟨ℓ, hℓ, hcoords⟩ := adim7_linear_primitive_with_constraint (K := K) T e ℓ₀ (Or.inl hzℓ) s
    have he : e ≠ 0 := fun he ↦ hzℓ (by change e ℓ₀ = 0; rw [he]; rfl)
    exact ⟨ℓ, fun _ ↦ ⟨z, hzπ, hℓ.resolve_right he⟩, fun i ↦ hcoords _ (hmem i)⟩
  · obtain ⟨ℓ, _, hcoords⟩ := adim7_linear_primitive_with_constraint (K := K) T 0 0 (Or.inr rfl) s
    exact ⟨ℓ, fun h ↦ (hnd h).elim, fun i ↦ hcoords _ (hmem i)⟩

private theorem adim7_map_preserves_germ_value (n d : ℕ) (P : Ideal (AnalyticGerm n))
    (hP : P ≠ ⊤) (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hcomp : ∀ (a : AnalyticGerm d) (f : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ f 0 → Germ.ofFun f = a.val → ∀ (b : AnalyticGerm n),
      Germ.ofFun (fun z ↦ f (π z)) = b.val → θ a = Ideal.Quotient.mk P b) :
    ∀ (a : AnalyticGerm d) (b : AnalyticGerm n),
      θ a = Ideal.Quotient.mk P b → analyticGermValue d a = analyticGermValue n b := by
  letI : IsLocalRing (AnalyticGerm n) := by
    apply IsLocalRing.of_isUnit_or_isUnit_of_isUnit_add
    intro x y hxy
    rw [analyticGerm_isUnit_iff] at hxy
    simp only [map_add] at hxy
    by_cases hx : analyticGermValue n x = 0
    · right
      rw [analyticGerm_isUnit_iff]
      simpa [hx] using hxy
    · left
      rwa [analyticGerm_isUnit_iff]
  have hmax : IsLocalRing.maximalIdeal (AnalyticGerm n) = analyticGermMaximalIdeal n := by
    symm
    apply IsLocalRing.eq_maximalIdeal
    apply RingHom.ker_isMaximal_of_surjective
    intro z
    exact ⟨⟨Germ.ofFun (fun _ ↦ z), fun _ ↦ z, analyticAt_const, rfl⟩, rfl⟩
  intro a b hab
  obtain ⟨fa, hfa, hfarep⟩ := a.property
  let c : AnalyticGerm n :=
    ⟨Germ.ofFun (fun z ↦ fa (π z)), fun z ↦ fa (π z),
      hfa.comp_of_eq (π.analyticAt 0) (map_zero π), rfl⟩
  have hac : θ a = Ideal.Quotient.mk P c := hcomp a fa hfa hfarep c rfl
  have hbc : b - c ∈ P :=
    (Ideal.Quotient.mk_eq_mk_iff_sub_mem b c).mp (hab.symm.trans hac)
  have hbc' : b - c ∈ analyticGermMaximalIdeal n := by
    rw [← hmax]
    exact IsLocalRing.le_maximalIdeal hP hbc
  have hval : analyticGermValue n b = analyticGermValue n c := by
    change analyticGermValue n (b - c) = 0 at hbc'
    exact sub_eq_zero.mp (by simpa using hbc')
  rw [hval]
  change a.val.value = c.val.value
  rw [← hfarep]
  change (Germ.ofFun fa).value = (Germ.ofFun (fun z ↦ fa (π z))).value
  simp only [Germ.value_ofFun, map_zero]

private theorem adim7_exists_linear_germ (n d : ℕ)
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)) :
    ∃ (ℓ : (Fin n → ℂ) →L[ℂ] ℂ) (v : AnalyticGerm n),
      v.val = Germ.ofFun (fun z ↦ ℓ z) ∧
      analyticGermValue n v = 0 ∧
      (d < n → ∃ z, π z = 0 ∧ ℓ z ≠ 0) := by
  by_cases hnd : d < n
  · obtain ⟨ℓ, z, hzπ, hzℓ⟩ := adim7_exists_linear_form_ne_zero_on_ker n d π hnd
    let v : AnalyticGerm n :=
      ⟨Germ.ofFun (fun x ↦ ℓ x), fun x ↦ ℓ x, ℓ.analyticAt 0, rfl⟩
    refine ⟨ℓ, v, rfl, ?_, fun _ ↦ ⟨z, hzπ, hzℓ⟩⟩
    change ℓ 0 = 0
    exact map_zero ℓ
  · let ℓ : (Fin n → ℂ) →L[ℂ] ℂ := 0
    let v : AnalyticGerm n :=
      ⟨Germ.ofFun (fun x ↦ ℓ x), fun x ↦ ℓ x, ℓ.analyticAt 0, rfl⟩
    refine ⟨ℓ, v, rfl, ?_, fun h ↦ (hnd h).elim⟩
    change ℓ 0 = 0
    exact map_zero ℓ

private theorem adim7_exists_distinguished_linear_relation (n d : ℕ)
    (P : Ideal (AnalyticGerm n)) (hP : P.IsPrime)
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P)) (θfinite : θ.Finite)
    (hcomp : ∀ (a : AnalyticGerm d) (f : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ f 0 → Germ.ofFun f = a.val → ∀ (b : AnalyticGerm n),
      Germ.ofFun (fun z ↦ f (π z)) = b.val → θ a = Ideal.Quotient.mk P b) :
    ∃ (ℓ : (Fin n → ℂ) →L[ℂ] ℂ) (v : AnalyticGerm n)
      (Q : Polynomial (AnalyticGerm d)),
      v.val = Germ.ofFun (fun z ↦ ℓ z) ∧
      (d < n → ∃ z, π z = 0 ∧ ℓ z ≠ 0) ∧
      IsWeierstrassPolynomial Q ∧
      Q.eval₂ θ (Ideal.Quotient.mk P v) = 0 := by
  obtain ⟨ℓ, v, hv, hv0, hℓ⟩ := adim7_exists_linear_germ n d π
  have hlocal := adim7_map_preserves_germ_value n d P hP.ne_top π θ hcomp
  obtain ⟨Q, hQ, hQroot⟩ :=
    adim5_distinguished_relation n d P hP.ne_top θ θfinite hlocal v hv0
  exact ⟨ℓ, v, Q, hv, hℓ, hQ, hQroot⟩

private theorem adim7_exists_distinguished_exact_linear_relation (n d : ℕ)
    (P : Ideal (AnalyticGerm n)) (hP : P.IsPrime)
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hfinite : θ.Finite) (hinj : Function.Injective θ)
    (hcomp : ∀ (a : AnalyticGerm d) (f : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ f 0 → Germ.ofFun f = a.val → ∀ (b : AnalyticGerm n),
      Germ.ofFun (fun z ↦ f (π z)) = b.val → θ a = Ideal.Quotient.mk P b) :
    ∃ (ℓ : (Fin n → ℂ) →L[ℂ] ℂ) (v : AnalyticGerm n)
      (Q : Polynomial (AnalyticGerm d)),
      v.val = Germ.ofFun (fun z ↦ ℓ z) ∧
      (d < n → ∃ z, π z = 0 ∧ ℓ z ≠ 0) ∧
      IsWeierstrassPolynomial Q ∧
      ∀ T : Polynomial (AnalyticGerm d),
        T.eval₂ θ (Ideal.Quotient.mk P v) = 0 ↔ Q ∣ T := by
  obtain ⟨ℓ, v, W, hv, hℓ, hW, hroot⟩ :=
    adim7_exists_distinguished_linear_relation n d P hP π θ hfinite hcomp
  obtain ⟨Q, hQ, hdeg, hmin⟩ :=
    adim7_exists_exact_monic_relation n d P hP θ hfinite hinj v
  exact ⟨ℓ, v, Q, hv, hℓ,
    adim7_weierstrass_of_monic_dvd hW hQ hdeg ((hmin W).mp hroot), hmin⟩

private theorem adim7_distinguished_exact_bezout (n d : ℕ)
    (P : Ideal (AnalyticGerm n)) (hP : P.IsPrime)
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hfinite : θ.Finite) (hinj : Function.Injective θ)
    (hcomp : ∀ (a : AnalyticGerm d) (f : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ f 0 → Germ.ofFun f = a.val → ∀ (b : AnalyticGerm n),
      Germ.ofFun (fun z ↦ f (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (v : AnalyticGerm n) (hv : analyticGermValue n v = 0) :
    ∃ (Q : Polynomial (AnalyticGerm d)) (δ : AnalyticGerm d)
      (B C : Polynomial (AnalyticGerm d)),
      IsWeierstrassPolynomial Q ∧ δ ≠ 0 ∧
      B * Q + C * Q.derivative = Polynomial.C δ ∧
      ∀ T : Polynomial (AnalyticGerm d),
        T.eval₂ θ (Ideal.Quotient.mk P v) = 0 ↔ Q ∣ T := by
  letI : P.IsPrime := hP
  letI : UniqueFactorizationMonoid (AnalyticGerm d) := spec_analyticGerm_ufd d
  letI : IsDomain (AnalyticGerm d) := {}
  letI : CharZero (AnalyticGerm d) := (analyticGermValue d).charZero
  letI : Algebra (AnalyticGerm d) (AnalyticGerm n ⧸ P) := θ.toAlgebra
  letI : Module.IsTorsionFree (AnalyticGerm d) (AnalyticGerm n ⧸ P) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  have hvint : IsIntegral (AnalyticGerm d) (Ideal.Quotient.mk P v) := hfinite.to_isIntegral _
  let Q := minpoly (AnalyticGerm d) (Ideal.Quotient.mk P v)
  have hQ : Q.Monic := minpoly.monic hvint
  have hdeg : 0 < Q.natDegree := minpoly.natDegree_pos hvint
  have hmin : ∀ T, T.eval₂ θ (Ideal.Quotient.mk P v) = 0 ↔ Q ∣ T :=
    fun T ↦ minpoly.isIntegrallyClosed_dvd_iff hvint T
  have hsep : (Q.map (algebraMap (AnalyticGerm d) (FractionRing (AnalyticGerm d)))).Separable :=
    ((hQ.irreducible_iff_irreducible_map_fraction_map).mp (minpoly.irreducible hvint)).separable
  obtain ⟨δ, B, C, hδ, hBC⟩ := adim7_bezout_of_separable_fraction_map Q hdeg hsep
  obtain ⟨W, hW, hroot⟩ := adim5_distinguished_relation n d P hP.ne_top θ hfinite
    (adim7_map_preserves_germ_value n d P hP.ne_top π θ hcomp) v hv
  exact ⟨Q, δ, B, C, adim7_weierstrass_of_monic_dvd hW hQ hdeg ((hmin W).mp hroot),
    hδ, hBC, hmin⟩

/-- Primitive linear coordinate, distinguished minimal relation and a common denominator.
The Bezout identity includes the branch locus in the denominator's zero germ.
Source: Gunning--Rossi, III.B--C, local parametrization; Nicolaescu, Notes on the Topology of Complex Singularities, Theorem 9.2.11 and Remark 9.2.12(b). -/
theorem adim7_primitive_form_aux (n d : ℕ) (P : Ideal (AnalyticGerm n))
    (hP : P.IsPrime) (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hfinite : θ.Finite) (hinj : Function.Injective θ)
    (hcomp : ∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm n,
      Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (c : Fin n → AnalyticGerm n)
    (hc : ∀ i, (c i).val = Germ.ofFun (fun z : Fin n → ℂ ↦ z i)) :
    ∃ (ℓ : (Fin n → ℂ) →L[ℂ] ℂ) (v : AnalyticGerm n)
      (Q : Polynomial (AnalyticGerm d)) (δ : AnalyticGerm d)
      (R : Fin n → Polynomial (AnalyticGerm d))
      (B C : Polynomial (AnalyticGerm d)),
      v.val = Germ.ofFun (fun z ↦ ℓ z) ∧
      (d < n → ∃ z, π z = 0 ∧ ℓ z ≠ 0) ∧
      IsWeierstrassPolynomial Q ∧ δ ≠ 0 ∧
      B * Q + C * Q.derivative = Polynomial.C δ ∧
      (∀ T : Polynomial (AnalyticGerm d),
        T.eval₂ θ (Ideal.Quotient.mk P v) = 0 ↔ Q ∣ T) ∧
      ∀ i, θ δ * Ideal.Quotient.mk P (c i) =
        (R i).eval₂ θ (Ideal.Quotient.mk P v) := by
  classical
  let A := AnalyticGerm d
  let S := AnalyticGerm n ⧸ P
  letI : P.IsPrime := hP
  letI : UniqueFactorizationMonoid A := spec_analyticGerm_ufd d
  letI : IsDomain A := {}
  letI : CharZero A := (analyticGermValue d).charZero
  letI : Algebra A S := θ.toAlgebra
  letI : FaithfulSMul A S := (faithfulSMul_iff_algebraMap_injective A S).mpr hinj
  letI : Module.Finite A S := hfinite
  let K := FractionRing A
  let L := FractionRing S
  letI : FaithfulSMul A L := (faithfulSMul_iff_algebraMap_injective A L).mpr
    ((IsFractionRing.injective S L).comp hinj)
  letI : Algebra K L := FractionRing.liftAlgebra A L
  letI : SMul K L := (inferInstance : Algebra K L).toSMul
  letI : Module K L := Algebra.toModule
  letI : IsScalarTower A K L := FractionRing.isScalarTower_liftAlgebra A L
  letI : Algebra ℂ A := (adim7_constantGerm d).toAlgebra
  letI : Algebra ℂ K := ((algebraMap A K).comp (adim7_constantGerm d)).toAlgebra
  letI : Algebra ℂ L := ((algebraMap A L).comp (adim7_constantGerm d)).toAlgebra
  letI : SMul ℂ K := (inferInstance : Algebra ℂ K).toSMul
  letI : Module ℂ K := Algebra.toModule
  letI : SMul ℂ L := (inferInstance : Algebra ℂ L).toSMul
  letI : Module ℂ L := Algebra.toModule
  letI : IsScalarTower ℂ K L := IsScalarTower.of_algebraMap_eq fun z ↦ by
    change algebraMap A L (adim7_constantGerm d z) =
      algebraMap K L (algebraMap A K (adim7_constantGerm d z))
    exact IsScalarTower.algebraMap_apply A K L _
  obtain ⟨hfin, hsep, hprim⟩ := adim7_finite_fraction_extension A S K L
  letI : Module.Finite K L := hfin
  letI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  letI : Algebra.IsSeparable K L := hsep
  letI : Finite (IntermediateField K L) :=
    Field.finite_intermediateField_of_exists_primitive_element K L hprim
  let f : AnalyticGerm n →+* L := (algebraMap S L).comp (Ideal.Quotient.mk P)
  have hconst (z : ℂ) : f (adim7_constantGerm n z) = algebraMap ℂ L z := by
    have hz := hcomp (adim7_constantGerm d z) (fun _ ↦ z) analyticAt_const rfl
      (adim7_constantGerm n z) rfl
    change algebraMap S L (Ideal.Quotient.mk P (adim7_constantGerm n z)) =
      algebraMap S L (θ (adim7_constantGerm d z))
    rw [hz]
  let T := adim7_linearGermMap f hconst
  obtain ⟨ℓ, hℓ, hcoords⟩ := adim7_exists_primitive_linear_form (K := K) n d π T
  let v := adim7_linearGerm ℓ
  have hcoords' (i : Fin n) : algebraMap S L (Ideal.Quotient.mk P (c i)) ∈
      Algebra.adjoin K {algebraMap S L (Ideal.Quotient.mk P v)} := by
    have hci : c i = adim7_linearGerm (ContinuousLinearMap.proj i) := Subtype.ext (hc i)
    rw [← IntermediateField.adjoin_toSubalgebra, hci]
    exact hcoords i
  obtain ⟨a, R, ha, hR⟩ := adim7_clear_coordinates (A := A)
    (Ideal.Quotient.mk P v) (fun i ↦ Ideal.Quotient.mk P (c i)) hcoords'
  have hv : analyticGermValue n v = 0 := by
    change ℓ 0 = 0
    exact map_zero ℓ
  obtain ⟨Q, δ, B, C, hQ, hδ, hBC, hmin⟩ :=
    adim7_distinguished_exact_bezout n d P hP π θ hfinite hinj hcomp v hv
  refine ⟨ℓ, v, Q, δ * a, fun i ↦ Polynomial.C δ * R i,
    Polynomial.C a * B, Polynomial.C a * C, rfl, hℓ, hQ,
    mul_ne_zero hδ ha, ?_, hmin, ?_⟩
  · calc
      Polynomial.C a * B * Q + Polynomial.C a * C * Q.derivative =
          Polynomial.C a * (B * Q + C * Q.derivative) := by ring
      _ = Polynomial.C (δ * a) := by rw [hBC, ← map_mul, mul_comm a δ]
  · intro i
    change θ (δ * a) * Ideal.Quotient.mk P (c i) =
      (Polynomial.C δ * R i).eval₂ θ (Ideal.Quotient.mk P v)
    have hRi : θ a * Ideal.Quotient.mk P (c i) =
        (R i).eval₂ θ (Ideal.Quotient.mk P v) := by
      simpa only [Polynomial.aeval_def, RingHom.algebraMap_toAlgebra] using hR i
    rw [map_mul, mul_assoc, hRi, Polynomial.eval₂_mul, Polynomial.eval₂_C]

#print axioms adim7_primitive_form_aux

/-- Equality of polynomial coefficient germs holds simultaneously near the origin. -/
private theorem adim7_polynomial_representatives_eq (d : ℕ)
    (p q : Polynomial ((Fin d → ℂ) → ℂ))
    (h : p.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
      q.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ)))) :
    ∀ᶠ w in 𝓝 (0 : Fin d → ℂ),
      p.map (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) =
        q.map (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) := by
  classical
  have hc (i : ℕ) : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), p.coeff i w = q.coeff i w := by
    apply Germ.coe_eq.mp
    simpa only [Polynomial.coeff_map, Germ.coe_coeRingHom] using congrArg (fun a ↦ a.coeff i) h
  have hs : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ),
      ∀ i ∈ p.support ∪ q.support, p.coeff i w = q.coeff i w := by
    rw [Finset.eventually_all]
    exact fun i _ ↦ hc i
  filter_upwards [hs] with w hw
  ext i
  simp only [Polynomial.coeff_map, Pi.evalRingHom_apply]
  by_cases hi : i ∈ p.support ∪ q.support
  · exact hw i hi
  · have hp : p.coeff i = 0 := Polynomial.notMem_support_iff.mp
      (fun hip ↦ hi (Finset.mem_union_left _ hip))
    have hq : q.coeff i = 0 := Polynomial.notMem_support_iff.mp
      (fun hiq ↦ hi (Finset.mem_union_right _ hiq))
    rw [hp, hq]

/-- Divisibility of coefficient germs forces vanishing at every nearby representative root. -/
private theorem adim7_polynomial_roots_of_germ_dvd (d : ℕ)
    (p q : Polynomial ((Fin d → ℂ) → ℂ))
    (h : q.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) ∣
      p.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ)))) :
    ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ t : ℂ,
      q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 →
        p.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 := by
  obtain ⟨S, hS⟩ := h
  have hsurj : Function.Surjective (Germ.coeRingHom (R := ℂ) (𝓝 (0 : Fin d → ℂ))) :=
    Quot.mk_surjective
  obtain ⟨s, hs⟩ := Polynomial.map_surjective _ hsurj S
  have heq : p.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
      (q * s).map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) := by
    rw [Polynomial.map_mul, hs, hS]
  filter_upwards [adim7_polynomial_representatives_eq d p (q * s) heq] with w hw
  intro t ht
  have := congrArg (fun a : Polynomial ℂ ↦ a.eval t) hw
  simpa only [Polynomial.eval_map, Polynomial.eval₂_mul, ht, zero_mul] using this

/-- A polynomial relation in the primitive quotient vanishes on the representative roots. -/
private theorem adim7_polynomial_roots_of_relation (d : ℕ)
    {B : Type*} [CommRing B] (θ : AnalyticGerm d →+* B) (v : B)
    (Q T : Polynomial (AnalyticGerm d))
    (hmin : ∀ S : Polynomial (AnalyticGerm d), S.eval₂ θ v = 0 ↔ Q ∣ S)
    (hT : T.eval₂ θ v = 0)
    (q p : Polynomial ((Fin d → ℂ) → ℂ))
    (hq : ∀ i, Germ.ofFun (q.coeff i) = (Q.coeff i).val)
    (hp : ∀ i, Germ.ofFun (p.coeff i) = (T.coeff i).val) :
    ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ t : ℂ,
      q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 →
        p.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 := by
  apply adim7_polynomial_roots_of_germ_dvd d p q
  have hqmap : q.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
      Q.map (analyticGermSubring d).subtype := by
    ext i
    simpa only [Polynomial.coeff_map, Germ.coe_coeRingHom, Subring.subtype_apply] using hq i
  have hpmap : p.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
      T.map (analyticGermSubring d).subtype := by
    ext i
    simpa only [Polynomial.coeff_map, Germ.coe_coeRingHom, Subring.subtype_apply] using hp i
  rw [hqmap, hpmap]
  obtain ⟨S, hS⟩ := (hmin T).mp hT
  exact ⟨S.map (analyticGermSubring d).subtype, by rw [hS, Polynomial.map_mul]⟩

/-- Clearing one common denominator preserves linear relations in the primitive quotient. -/
private theorem adim7_linear_relation {A B : Type*} [CommRing A] [CommRing B]
    (n : ℕ) (θ : A →+* B) (v : B) (δ : A) (c : Fin n → B)
    (R : Fin n → Polynomial A) (hcoord : ∀ i, θ δ * c i = (R i).eval₂ θ v)
    (a : Fin n → A) (S : Polynomial A)
    (hlinear : ∑ i, θ (a i) * c i = S.eval₂ θ v) :
    (∑ i, C (a i) * R i - C δ * S).eval₂ θ v = 0 := by
  rw [Polynomial.eval₂_sub, sub_eq_zero]
  simp only [Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C]
  rw [← hlinear, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← hcoord i]
  ring

/-- A total-degree bound clears a common denominator in one coordinate monomial. -/
private theorem adim7_clear_monomial {A : Type*} [CommRing A]
    (n N : ℕ) (a δ : A) (x : Fin n → A) (e : Fin n → ℕ)
    (hN : ∑ i, e i ≤ N) :
    a * δ ^ (N - ∑ i, e i) * ∏ i, (δ * x i) ^ e i =
      δ ^ N * (a * ∏ i, x i ^ e i) := by
  simp_rw [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  calc
    a * δ ^ (N - ∑ i, e i) * (δ ^ (∑ i, e i) * ∏ i, x i ^ e i) =
        a * (δ ^ (N - ∑ i, e i) * δ ^ (∑ i, e i)) * ∏ i, x i ^ e i := by ring
    _ = δ ^ N * (a * ∏ i, x i ^ e i) := by
      rw [← pow_add, Nat.sub_add_cancel hN]
      ring

/-- Finite polynomial equations in the quotient hold on every reconstructed primitive root. -/
private theorem adim7_polynomial_equations_at_roots (n d k N : ℕ)
    {B : Type*} [CommRing B] (θ : AnalyticGerm d →+* B) (v : B)
    (Q : Polynomial (AnalyticGerm d)) (δ : AnalyticGerm d)
    (c : Fin n → B) (R : Fin n → Polynomial (AnalyticGerm d))
    (hmin : ∀ T : Polynomial (AnalyticGerm d), T.eval₂ θ v = 0 ↔ Q ∣ T)
    (hcoord : ∀ i, θ δ * c i = (R i).eval₂ θ v)
    (a : Fin k → AnalyticGerm d) (e : Fin k → Fin n → ℕ)
    (hN : ∀ j, ∑ i, e j i ≤ N)
    (hF : ∑ j, θ (a j) * ∏ i, c i ^ e j i = 0)
    (q : Polynomial ((Fin d → ℂ) → ℂ)) (Δ : (Fin d → ℂ) → ℂ)
    (r : Fin n → Polynomial ((Fin d → ℂ) → ℂ))
    (a₀ : Fin k → (Fin d → ℂ) → ℂ)
    (hq : ∀ i, Germ.ofFun (q.coeff i) = (Q.coeff i).val)
    (hΔ : Germ.ofFun Δ = δ.val)
    (hr : ∀ j i, Germ.ofFun ((r j).coeff i) = ((R j).coeff i).val)
    (ha : ∀ j, Germ.ofFun (a₀ j) = (a j).val) :
    ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ t : ℂ, Δ w ≠ 0 →
      q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 →
      ∑ j, a₀ j w * ∏ i,
        ((r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w) ^ e j i = 0 := by
  classical
  let T := ∑ j, C (a j * δ ^ (N - ∑ i, e j i)) * ∏ i, R i ^ e j i
  let p := ∑ j, C (a₀ j * Δ ^ (N - ∑ i, e j i)) * ∏ i, r i ^ e j i
  have hT : T.eval₂ θ v = 0 := by
    simp only [T, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul,
      Polynomial.eval₂_C, Polynomial.eval₂_finsetProd, Polynomial.eval₂_pow, map_mul, map_pow]
    simp_rw [← hcoord, adim7_clear_monomial n N _ _ _ _ (hN _)]
    rw [← Finset.mul_sum, hF, mul_zero]
  have hrmap (j : Fin n) : (r j).map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
      (R j).map (analyticGermSubring d).subtype := by
    ext i
    simpa only [Polynomial.coeff_map, Germ.coe_coeRingHom, Subring.subtype_apply] using hr j i
  have ha' (j : Fin k) : Germ.coeRingHom (𝓝 (0 : Fin d → ℂ)) (a₀ j) =
      (analyticGermSubring d).subtype (a j) := ha j
  have hΔ' : Germ.coeRingHom (𝓝 (0 : Fin d → ℂ)) Δ =
      (analyticGermSubring d).subtype δ := hΔ
  have hpmap : p.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
      T.map (analyticGermSubring d).subtype := by
    simp only [p, T, Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_prod, Polynomial.map_pow, map_mul, map_pow, ha', hΔ', hrmap]
  have hp : ∀ i, Germ.ofFun (p.coeff i) = (T.coeff i).val := by
    intro i
    simpa only [Polynomial.coeff_map, Germ.coe_coeRingHom, Subring.subtype_apply] using
      congrArg (fun F ↦ F.coeff i) hpmap
  filter_upwards [adim7_polynomial_roots_of_relation d θ v Q T hmin hT q p hq hp]
    with w hw
  intro t hΔw ht
  have hz := hw t ht
  simp only [p, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_finsetProd, Polynomial.eval₂_pow, Pi.evalRingHom_apply,
    Pi.mul_apply, Pi.pow_apply] at hz
  have hcoordw (i : Fin n) : Δ w *
      ((r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w) =
        (r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t :=
    mul_div_cancel₀ _ hΔw
  have hclear (j : Fin k) : a₀ j w * Δ w ^ (N - ∑ i, e j i) *
      ∏ i, (r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t ^ e j i =
      Δ w ^ N * (a₀ j w * ∏ i,
        ((r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w) ^ e j i) := by
    simpa only [hcoordw] using adim7_clear_monomial n N (a₀ j w) (Δ w)
      (fun i ↦ (r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w)
      (e j) (hN j)
  simp_rw [hclear] at hz
  rw [← Finset.mul_sum] at hz
  exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hΔw)

/-- Linear relations descend to the reconstructed coordinates at every nearby root. -/
private theorem adim7_linear_reconstruction (n d : ℕ)
    {B : Type*} [CommRing B] (θ : AnalyticGerm d →+* B) (v : B)
    (Q : Polynomial (AnalyticGerm d)) (δ : AnalyticGerm d)
    (c : Fin n → B) (R : Fin n → Polynomial (AnalyticGerm d))
    (hmin : ∀ T : Polynomial (AnalyticGerm d), T.eval₂ θ v = 0 ↔ Q ∣ T)
    (hcoord : ∀ i, θ δ * c i = (R i).eval₂ θ v)
    (a : Fin n → AnalyticGerm d) (S : Polynomial (AnalyticGerm d))
    (hlinear : ∑ i, θ (a i) * c i = S.eval₂ θ v)
    (q : Polynomial ((Fin d → ℂ) → ℂ)) (Δ : (Fin d → ℂ) → ℂ)
    (r : Fin n → Polynomial ((Fin d → ℂ) → ℂ))
    (a₀ : Fin n → (Fin d → ℂ) → ℂ) (s : Polynomial ((Fin d → ℂ) → ℂ))
    (hq : ∀ i, Germ.ofFun (q.coeff i) = (Q.coeff i).val)
    (hΔ : Germ.ofFun Δ = δ.val)
    (hr : ∀ j i, Germ.ofFun ((r j).coeff i) = ((R j).coeff i).val)
    (ha : ∀ i, Germ.ofFun (a₀ i) = (a i).val)
    (hs : ∀ i, Germ.ofFun (s.coeff i) = (S.coeff i).val) :
    ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ t : ℂ, Δ w ≠ 0 →
      q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 →
      ∑ i, a₀ i w *
        ((r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w) =
          s.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t := by
  classical
  let T := ∑ i, C (a i) * R i - C δ * S
  let p := ∑ i, C (a₀ i) * r i - C Δ * s
  have hmap (F : Polynomial ((Fin d → ℂ) → ℂ)) (G : Polynomial (AnalyticGerm d))
      (hFG : ∀ i, Germ.ofFun (F.coeff i) = (G.coeff i).val) :
      F.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
        G.map (analyticGermSubring d).subtype := by
    ext i
    simpa only [Polynomial.coeff_map, Germ.coe_coeRingHom, Subring.subtype_apply] using hFG i
  have hpmap : p.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
      T.map (analyticGermSubring d).subtype := by
    simp only [p, T, Polynomial.map_sub, Polynomial.map_sum, Polynomial.map_mul,
      Polynomial.map_C, Germ.coe_coeRingHom, Subring.subtype_apply, hΔ, ha,
      hmap s S hs, hmap _ _ (hr _)]
  have hp : ∀ i, Germ.ofFun (p.coeff i) = (T.coeff i).val := by
    intro i
    simpa only [Polynomial.coeff_map, Germ.coe_coeRingHom, Subring.subtype_apply] using
      congrArg (fun F ↦ F.coeff i) hpmap
  have hT := adim7_linear_relation n θ v δ c R hcoord a S hlinear
  filter_upwards [adim7_polynomial_roots_of_relation d θ v Q T hmin hT q p hq hp]
    with w hw
  intro t hΔw ht
  have heq := hw t ht
  simp only [p, Polynomial.eval₂_sub, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Pi.evalRingHom_apply, sub_eq_zero] at heq
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div, heq, mul_div_cancel_left₀ _ hΔw]

/-- Compatible parameter maps carry the coordinate expansion of a linear form to the quotient. -/
private theorem adim7_linear_germ_identity (n d : ℕ) (P : Ideal (AnalyticGerm n))
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hcomp : ∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm n,
      Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (c : Fin n → AnalyticGerm n)
    (hc : ∀ i, (c i).val = Germ.ofFun (fun z : Fin n → ℂ ↦ z i))
    (L : (Fin n → ℂ) →L[ℂ] ℂ) (b : AnalyticGerm n)
    (hb : b.val = Germ.ofFun (fun z ↦ L z))
    (a : Fin n → AnalyticGerm d)
    (ha : ∀ i, Germ.ofFun (fun _ : Fin d → ℂ ↦ L (Pi.single i 1)) = (a i).val) :
    ∑ i, θ (a i) * Ideal.Quotient.mk P (c i) = Ideal.Quotient.mk P b := by
  classical
  let a' : Fin n → AnalyticGerm n := fun i ↦
    ⟨Germ.ofFun (fun _ ↦ L (Pi.single i 1)), _, analyticAt_const, rfl⟩
  have hθ (i : Fin n) : θ (a i) = Ideal.Quotient.mk P (a' i) :=
    hcomp (a i) (fun _ ↦ L (Pi.single i 1)) analyticAt_const (ha i) (a' i) rfl
  simp_rw [hθ, ← map_mul, ← map_sum]
  congr 1
  apply Subtype.ext
  change (analyticGermSubring n).subtype (∑ i, a' i * c i) = b.val
  rw [map_sum, hb]
  simp only [map_mul, Subring.subtype_apply, hc]
  change (∑ i, Germ.coeRingHom (𝓝 (0 : Fin n → ℂ)) (fun _ ↦ L (Pi.single i 1)) *
    Germ.coeRingHom (𝓝 (0 : Fin n → ℂ)) (fun z ↦ z i)) =
      Germ.coeRingHom (𝓝 (0 : Fin n → ℂ)) (fun z ↦ L z)
  simp only [← map_mul, ← map_sum]
  congr 1
  funext z
  simp only [Finset.sum_apply, Pi.mul_apply]
  conv_rhs => rw [pi_eq_sum_univ' z]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, mul_comm]

/-- Polynomial expressions for linear forms agree with the reconstructed point. -/
private theorem adim7_linear_form_reconstruction (n d : ℕ) (P : Ideal (AnalyticGerm n))
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hcomp : ∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm n,
      Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (c : Fin n → AnalyticGerm n)
    (hc : ∀ i, (c i).val = Germ.ofFun (fun z : Fin n → ℂ ↦ z i))
    (v : AnalyticGerm n) (Q : Polynomial (AnalyticGerm d)) (δ : AnalyticGerm d)
    (R : Fin n → Polynomial (AnalyticGerm d))
    (hmin : ∀ T : Polynomial (AnalyticGerm d),
      T.eval₂ θ (Ideal.Quotient.mk P v) = 0 ↔ Q ∣ T)
    (hcoord : ∀ i, θ δ * Ideal.Quotient.mk P (c i) =
      (R i).eval₂ θ (Ideal.Quotient.mk P v))
    (q : Polynomial ((Fin d → ℂ) → ℂ)) (Δ : (Fin d → ℂ) → ℂ)
    (r : Fin n → Polynomial ((Fin d → ℂ) → ℂ))
    (hq : ∀ i, Germ.ofFun (q.coeff i) = (Q.coeff i).val)
    (hΔ : Germ.ofFun Δ = δ.val)
    (hr : ∀ j i, Germ.ofFun ((r j).coeff i) = ((R j).coeff i).val)
    (L : (Fin n → ℂ) →L[ℂ] ℂ) (b : AnalyticGerm n)
    (hb : b.val = Germ.ofFun (fun z ↦ L z))
    (S : Polynomial (AnalyticGerm d)) (s : Polynomial ((Fin d → ℂ) → ℂ))
    (hS : S.eval₂ θ (Ideal.Quotient.mk P v) = Ideal.Quotient.mk P b)
    (hs : ∀ i, Germ.ofFun (s.coeff i) = (S.coeff i).val) :
    ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ t : ℂ, Δ w ≠ 0 →
      q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 →
      L (fun i ↦ (r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w) =
        s.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t := by
  classical
  let a : Fin n → AnalyticGerm d := fun i ↦
    ⟨Germ.ofFun (fun _ ↦ L (Pi.single i 1)), _, analyticAt_const, rfl⟩
  have hlinear : ∑ i, θ (a i) * Ideal.Quotient.mk P (c i) =
      S.eval₂ θ (Ideal.Quotient.mk P v) := by
    rw [hS]
    exact adim7_linear_germ_identity n d P π θ hcomp c hc L b hb a (fun _ ↦ rfl)
  filter_upwards [adim7_linear_reconstruction n d θ (Ideal.Quotient.mk P v) Q δ
    (fun i ↦ Ideal.Quotient.mk P (c i)) R hmin hcoord a S hlinear q Δ r
    (fun i _ ↦ L (Pi.single i 1)) s hq hΔ hr (fun _ ↦ rfl) hs] with w hw
  intro t hΔw ht
  rw [← hw t hΔw ht]
  conv_lhs => rw [pi_eq_sum_univ'
    (fun i ↦ (r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w)]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, mul_comm]

/-- One shared root reconstructs both the parameter and the primitive linear coordinate. -/
private theorem adim7_reconstructed_projection_and_primitive (n d : ℕ) (P : Ideal (AnalyticGerm n))
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hcomp : ∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm n,
      Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (c : Fin n → AnalyticGerm n)
    (hc : ∀ i, (c i).val = Germ.ofFun (fun z : Fin n → ℂ ↦ z i))
    (v : AnalyticGerm n) (Q : Polynomial (AnalyticGerm d)) (δ : AnalyticGerm d)
    (R : Fin n → Polynomial (AnalyticGerm d))
    (hmin : ∀ T : Polynomial (AnalyticGerm d),
      T.eval₂ θ (Ideal.Quotient.mk P v) = 0 ↔ Q ∣ T)
    (hcoord : ∀ i, θ δ * Ideal.Quotient.mk P (c i) =
      (R i).eval₂ θ (Ideal.Quotient.mk P v))
    (q : Polynomial ((Fin d → ℂ) → ℂ)) (Δ : (Fin d → ℂ) → ℂ)
    (r : Fin n → Polynomial ((Fin d → ℂ) → ℂ))
    (hq : ∀ i, Germ.ofFun (q.coeff i) = (Q.coeff i).val)
    (hΔ : Germ.ofFun Δ = δ.val)
    (hr : ∀ j i, Germ.ofFun ((r j).coeff i) = ((R j).coeff i).val)
    (ℓ : (Fin n → ℂ) →L[ℂ] ℂ)
    (hv : v.val = Germ.ofFun (fun z ↦ ℓ z)) :
    ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ t : ℂ, Δ w ≠ 0 →
      q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 →
      let z : Fin n → ℂ := fun i ↦
        (r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w
      π z = w ∧ ℓ z = t := by
  classical
  have hX : ∀ i : ℕ,
      Germ.ofFun ((X : Polynomial ((Fin d → ℂ) → ℂ)).coeff i) =
        ((X : Polynomial (AnalyticGerm d)).coeff i).val := by
    intro i
    simp only [Polynomial.coeff_X]
    split_ifs <;> rfl
  have hℓ := adim7_linear_form_reconstruction n d P π θ hcomp c hc v Q δ R
    hmin hcoord q Δ r hq hΔ hr ℓ v hv X X (by simp only [Polynomial.eval₂_X]) hX
  have hπ (k : Fin d) : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ t : ℂ, Δ w ≠ 0 →
      q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 →
      (π (fun i ↦ (r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t /
        Δ w)) k = w k := by
    let L := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d ↦ ℂ) k).comp π
    let b : AnalyticGerm n := ⟨Germ.ofFun (fun z ↦ L z), _, L.analyticAt 0, rfl⟩
    let a : AnalyticGerm d := ⟨Germ.ofFun (fun w ↦ w k), _,
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d ↦ ℂ) k).analyticAt 0, rfl⟩
    have hS : (C a).eval₂ θ (Ideal.Quotient.mk P v) = Ideal.Quotient.mk P b := by
      rw [Polynomial.eval₂_C]
      exact hcomp a (fun w ↦ w k)
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d ↦ ℂ) k).analyticAt 0)
          (by rfl) b rfl
    have hs : ∀ i, Germ.ofFun ((C (fun w : Fin d → ℂ ↦ w k)).coeff i) =
        ((C a).coeff i).val := by
      intro i
      simp only [Polynomial.coeff_C]
      split_ifs <;> rfl
    simpa only [Polynomial.eval₂_C, Pi.evalRingHom_apply, L,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] using
      adim7_linear_form_reconstruction n d P π θ hcomp c hc v Q δ R hmin hcoord
        q Δ r hq hΔ hr L b rfl (C a) (C (fun w ↦ w k)) hS hs
  have hπall : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ k : Fin d, ∀ t : ℂ, Δ w ≠ 0 →
      q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 →
      (π (fun i ↦ (r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t /
        Δ w)) k = w k := by
    rw [Filter.eventually_all]
    exact hπ
  filter_upwards [hℓ, hπall] with w hwℓ hwπ
  intro t hΔw ht
  refine ⟨funext (fun k ↦ hwπ k t hΔw ht), ?_⟩
  simpa only [Polynomial.eval₂_X] using hwℓ t hΔw ht

/-- Monic germ polynomials have monic analytic coefficient representatives. -/
private theorem adim7_monic_representative (d : ℕ) (Q : Polynomial (AnalyticGerm d))
    (hQ : Q.Monic) :
    ∃ q : Polynomial ((Fin d → ℂ) → ℂ), q.Monic ∧
      ∀ i, AnalyticAt ℂ (q.coeff i) 0 ∧ Germ.ofFun (q.coeff i) = (Q.coeff i).val := by
  classical
  let k := Q.natDegree
  choose a ha hrep using fun i : Fin k ↦ (Q.coeff i).property
  let q : Polynomial ((Fin d → ℂ) → ℂ) := X ^ k + ∑ i : Fin k, C (a i) * X ^ (i : ℕ)
  have hmonic : q.Monic :=
    Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt a)
  have hform : Q = X ^ k + ∑ i : Fin k, C (Q.coeff i) * X ^ (i : ℕ) := by
    simpa only [← Fin.sum_univ_eq_sum_range] using hQ.as_sum
  have hcoeff (i : ℕ) : q.coeff i =
      (if i = k then 1 else 0) + ∑ j : Fin k, if (j : ℕ) = i then a j else 0 := by
    simp only [q, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff,
      Polynomial.coeff_C_mul_X_pow, eq_comm]
  have hmap : q.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
      Q.map (analyticGermSubring d).subtype := by
    conv_rhs => rw [hform]
    simp only [q, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C,
      Germ.coe_coeRingHom, Subring.subtype_apply, hrep]
  refine ⟨q, hmonic, fun i ↦ ⟨?_, ?_⟩⟩
  · rw [hcoeff]
    apply AnalyticAt.add
    · split_ifs <;> exact analyticAt_const
    · apply Finset.analyticAt_sum
      intro j _
      split_ifs <;> first | exact ha j | exact analyticAt_const
  · simpa only [Polynomial.coeff_map, Germ.coe_coeRingHom, Subring.subtype_apply] using
      congrArg (fun F ↦ F.coeff i) hmap

/-- A monic coordinate relation holds for the quotient reconstructed from a primitive root. -/
private theorem adim7_coordinate_relation (d : ℕ) {B : Type*} [CommRing B]
    (θ : AnalyticGerm d →+* B) (v x : B)
    (Q W R : Polynomial (AnalyticGerm d)) (δ : AnalyticGerm d)
    (hmin : ∀ T : Polynomial (AnalyticGerm d), T.eval₂ θ v = 0 ↔ Q ∣ T)
    (hcoord : θ δ * x = R.eval₂ θ v) (hW : W.Monic) (hWx : W.eval₂ θ x = 0)
    (q u r : Polynomial ((Fin d → ℂ) → ℂ)) (Δ : (Fin d → ℂ) → ℂ)
    (hq : ∀ i, Germ.ofFun (q.coeff i) = (Q.coeff i).val)
    (hu : ∀ i, Germ.ofFun (u.coeff i) = (W.coeff i).val) (humonic : u.Monic)
    (hr : ∀ i, Germ.ofFun (r.coeff i) = (R.coeff i).val)
    (hΔ : Germ.ofFun Δ = δ.val) :
    ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ t : ℂ, Δ w ≠ 0 →
      q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 →
      u.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w)
        (r.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w) = 0 := by
  let T := (W.scaleRoots δ).comp R
  let p := (u.scaleRoots Δ).comp r
  have hT : T.eval₂ θ v = 0 := by
    rw [Polynomial.eval₂_comp, ← hcoord]
    exact Polynomial.scaleRoots_eval₂_eq_zero θ hWx
  have hmap (F : Polynomial ((Fin d → ℂ) → ℂ)) (G : Polynomial (AnalyticGerm d))
      (hFG : ∀ i, Germ.ofFun (F.coeff i) = (G.coeff i).val) :
      F.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
        G.map (analyticGermSubring d).subtype := by
    ext i
    simpa only [Polynomial.coeff_map, Germ.coe_coeRingHom, Subring.subtype_apply] using hFG i
  have hpmap : p.map (Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
      T.map (analyticGermSubring d).subtype := by
    rw [Polynomial.map_comp, Polynomial.map_comp,
      Polynomial.map_scaleRoots u Δ _ (by rw [humonic.leadingCoeff, map_one]; exact one_ne_zero),
      Polynomial.map_scaleRoots W δ _ (by rw [hW.leadingCoeff, map_one]; exact one_ne_zero),
      hmap u W hu, hmap r R hr]
    congr 2
  have hp : ∀ i, Germ.ofFun (p.coeff i) = (T.coeff i).val := by
    intro i
    simpa only [Polynomial.coeff_map, Germ.coe_coeRingHom, Subring.subtype_apply] using
      congrArg (fun F ↦ F.coeff i) hpmap
  filter_upwards [adim7_polynomial_roots_of_relation d θ v Q T hmin hT q p hq hp]
    with w hw
  intro t hΔw ht
  have hz := hw t ht
  rw [Polynomial.eval₂_comp] at hz
  have heq := Polynomial.scaleRoots_eval₂_mul (p := u)
    (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w)
    (r.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w) Δ
  simp only [Pi.evalRingHom_apply, mul_div_cancel₀ _ hΔw] at heq
  rw [hz] at heq
  exact (mul_eq_zero.mp heq.symm).resolve_left (pow_ne_zero _ hΔw)

/-- Finiteness supplies distinguished relations for the ambient coordinate germs. -/
private theorem adim7_coordinate_weierstrass (n d : ℕ) (P : Ideal (AnalyticGerm n))
    (hP : P ≠ ⊤) (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P)) (hfinite : θ.Finite)
    (hcomp : ∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm n,
      Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (c : Fin n → AnalyticGerm n)
    (hc : ∀ i, (c i).val = Germ.ofFun (fun z : Fin n → ℂ ↦ z i)) :
    ∀ i, ∃ W : Polynomial (AnalyticGerm d), IsWeierstrassPolynomial W ∧
      W.eval₂ θ (Ideal.Quotient.mk P (c i)) = 0 := by
  have hlocal : ∀ (a : AnalyticGerm d) (b : AnalyticGerm n),
      θ a = Ideal.Quotient.mk P b → analyticGermValue d a = analyticGermValue n b := by
    intro a b hab
    obtain ⟨fa, hfa, hfarep⟩ := a.property
    let b' : AnalyticGerm n := ⟨Germ.ofFun (fun z ↦ fa (π z)), _,
      hfa.comp_of_eq (π.analyticAt 0) (map_zero π), rfl⟩
    have hab' : θ a = Ideal.Quotient.mk P b' := hcomp a fa hfa hfarep b' rfl
    have hdiff : b - b' ∈ P :=
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem b b').mp (hab.symm.trans hab')
    have hzero : analyticGermValue n (b - b') = 0 := by
      by_contra hne
      exact hP (P.eq_top_of_isUnit_mem hdiff ((analyticGerm_isUnit_iff _).mpr hne))
    have hval : analyticGermValue n b = analyticGermValue n b' := by
      simpa only [map_sub, sub_eq_zero] using hzero
    rw [hval]
    change a.val.value = b'.val.value
    rw [← hfarep]
    change (Germ.ofFun fa).value = (Germ.ofFun (fun z ↦ fa (π z))).value
    simp only [Germ.value_ofFun, map_zero]
  intro i
  apply adim5_distinguished_relation n d P hP θ hfinite hlocal (c i)
  change (c i).val.value = 0
  rw [hc i]
  rfl

private theorem adim7_weierstrass_representative (d : ℕ)
    (Q : Polynomial (AnalyticGerm d)) (q : Polynomial ((Fin d → ℂ) → ℂ))
    (hQ : IsWeierstrassPolynomial Q)
    (hq : ∀ i, AnalyticAt ℂ (q.coeff i) 0 ∧
      Germ.ofFun (q.coeff i) = (Q.coeff i).val) :
    ∃ (k : ℕ) (a : Fin k → (Fin d → ℂ) → ℂ),
      0 < k ∧ (∀ i, AnalyticAt ℂ (a i) 0) ∧ (∀ i, a i 0 = 0) ∧
      ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ t,
        q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t =
          AnalyticDivisorAlgebraic4.monicInLast a (w, t) := by
  classical
  let k := Q.natDegree
  let a : Fin k → (Fin d → ℂ) → ℂ := fun i ↦ q.coeff i
  have hk : 0 < k := hQ.2.1
  have ha : ∀ i, AnalyticAt ℂ (a i) 0 := fun i ↦ (hq i).1
  have ha0 : ∀ i, a i 0 = 0 := by
    intro i
    have hi := hQ.2.2 i i.isLt
    change (Q.coeff i).val.value = 0 at hi
    rw [← (hq i).2] at hi
    simpa [a] using hi
  have hlead : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), q.coeff k w = 1 := by
    apply Filter.Germ.coe_eq.mp
    rw [(hq k).2]
    have hcoeff : Q.coeff k = 1 := hQ.1.coeff_natDegree
    rw [hcoeff]
    rfl
  have hkq : k ≤ q.natDegree := by
    apply Polynomial.le_natDegree_of_ne_zero
    intro hz
    have hw := hlead.self_of_nhds
    rw [hz] at hw
    norm_num at hw
  have hhigh : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ),
      ∀ j ∈ Finset.Ioc k q.natDegree, q.coeff j w = 0 := by
    rw [Finset.eventually_all]
    intro j hj
    apply Filter.Germ.coe_eq.mp
    rw [(hq j).2, Polynomial.coeff_eq_zero_of_natDegree_lt (Finset.mem_Ioc.mp hj).1]
    rfl
  refine ⟨k, a, hk, ha, ha0, ?_⟩
  filter_upwards [hlead, hhigh] with w hwlead hwhigh
  intro t
  rw [Polynomial.eval₂_eq_sum_range]
  simp only [Pi.evalRingHom_apply]
  rw [show ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i w * t ^ i =
      t ^ k + ∑ i : Fin k, q.coeff i w * t ^ (i : ℕ) by
    calc
      ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i w * t ^ i =
          ∑ i ∈ Finset.range (k + 1), q.coeff i w * t ^ i := by
            symm
            apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hkq))
            intro j hjbig hjsmall
            rw [hwhigh j]
            · simp
            · simp only [Finset.mem_Ioc]
              simp only [Finset.mem_range, not_lt] at hjsmall
              simp only [Finset.mem_range, Nat.lt_succ_iff] at hjbig
              omega
      _ = (∑ i ∈ Finset.range k, q.coeff i w * t ^ i) +
          q.coeff k w * t ^ k := by rw [Finset.sum_range_succ]
      _ = t ^ k + ∑ i : Fin k, q.coeff i w * t ^ (i : ℕ) := by
          rw [hwlead, one_mul, add_comm, ← Fin.sum_univ_eq_sum_range]]
  rfl

private theorem adim7_weierstrass_root_near (d : ℕ)
    (Q : Polynomial (AnalyticGerm d)) (q : Polynomial ((Fin d → ℂ) → ℂ))
    (hQ : IsWeierstrassPolynomial Q)
    (hq : ∀ i, AnalyticAt ℂ (q.coeff i) 0 ∧
      Germ.ofFun (q.coeff i) = (Q.coeff i).val)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ V : Set (Fin d → ℂ), IsOpen V ∧ (0 : Fin d → ℂ) ∈ V ∧
      ∀ w ∈ V, ∃ t : ℂ,
        q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 ∧ ‖t‖ < ε := by
  classical
  obtain ⟨k, a, hk, ha, ha0, hqform⟩ :=
    adim7_weierstrass_representative d Q q hQ hq
  have hsmall : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ t,
      AnalyticDivisorAlgebraic4.monicInLast a (w, t) = 0 → ‖t‖ < ε :=
    AnalyticDivisorAlgebraic4.spec_monicInLast_roots_small
      (fun i ↦ (ha i).continuousAt) ha0 hε
  obtain ⟨V, hVsub, hVopen, hV0⟩ := mem_nhds_iff.mp (hqform.and hsmall)
  refine ⟨V, hVopen, hV0, ?_⟩
  intro w hw
  have hform := (hVsub hw).1
  have hroot_small := (hVsub hw).2
  let p : Polynomial ℂ := q.map (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w)
  let p₀ : Polynomial ℂ := X ^ k + ∑ i : Fin k, C (a i w) * X ^ (i : ℕ)
  have hp₀monic : p₀.Monic := by
    exact Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt (fun i ↦ a i w))
  have hp₀deg : p₀.natDegree = k := by
    have h := Polynomial.natDegree_add_eq_left_of_degree_lt
      (show (∑ i : Fin k, C (a i w) * X ^ (i : ℕ) : Polynomial ℂ).degree <
          (X ^ k : Polynomial ℂ).degree by
        simpa only [Polynomial.degree_X_pow] using
          (Polynomial.degree_sum_fin_lt (fun i ↦ a i w)))
    simpa [p₀] using h
  have hp : p = p₀ := by
    apply Polynomial.funext
    intro t
    rw [show p.eval t = q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t by
      simp [p, Polynomial.eval₂_eq_eval_map]]
    rw [hform]
    simp only [p₀, AnalyticDivisorAlgebraic4.monicInLast, Polynomial.eval_add,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_finset_sum,
      Polynomial.eval_mul, Polynomial.eval_C]
  have hpdeg : 0 < p.degree := by
    rw [hp, ← Polynomial.natDegree_pos_iff_degree_pos, hp₀deg]
    exact hk
  obtain ⟨t, ht⟩ := Complex.exists_root hpdeg
  refine ⟨t, ?_, ?_⟩
  · simpa [p, Polynomial.eval₂_eq_eval_map] using ht.eq_zero
  · apply hroot_small t
    rw [← hform]
    simpa [p, Polynomial.eval₂_eq_eval_map] using ht.eq_zero

/-- All reconstructed coordinates tend uniformly to zero along the primitive roots. -/
private theorem adim7_reconstructed_coordinates_small (n d : ℕ) (P : Ideal (AnalyticGerm n))
    (hP : P ≠ ⊤) (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hfinite : θ.Finite)
    (hcomp : ∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm n,
      Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (c : Fin n → AnalyticGerm n)
    (hc : ∀ i, (c i).val = Germ.ofFun (fun z : Fin n → ℂ ↦ z i))
    (v : AnalyticGerm n) (Q : Polynomial (AnalyticGerm d)) (δ : AnalyticGerm d)
    (R : Fin n → Polynomial (AnalyticGerm d))
    (hmin : ∀ T : Polynomial (AnalyticGerm d),
      T.eval₂ θ (Ideal.Quotient.mk P v) = 0 ↔ Q ∣ T)
    (hcoord : ∀ i, θ δ * Ideal.Quotient.mk P (c i) =
      (R i).eval₂ θ (Ideal.Quotient.mk P v))
    (q : Polynomial ((Fin d → ℂ) → ℂ)) (Δ : (Fin d → ℂ) → ℂ)
    (r : Fin n → Polynomial ((Fin d → ℂ) → ℂ))
    (hq : ∀ i, Germ.ofFun (q.coeff i) = (Q.coeff i).val)
    (hΔ : Germ.ofFun Δ = δ.val)
    (hr : ∀ j i, Germ.ofFun ((r j).coeff i) = ((R j).coeff i).val)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ t : ℂ, Δ w ≠ 0 →
      q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 →
      ∀ i, ‖(r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w‖ < ε := by
  classical
  have hsmall (i : Fin n) : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ t : ℂ, Δ w ≠ 0 →
      q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 →
      ‖(r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w‖ < ε := by
    obtain ⟨W, hW, hWx⟩ := adim7_coordinate_weierstrass n d P hP π θ hfinite hcomp c hc i
    obtain ⟨u, humonic, hu⟩ := adim7_monic_representative d W hW.1
    obtain ⟨k, a, _, ha, ha0, hform⟩ := adim7_weierstrass_representative d W u hW hu
    have hbound := AnalyticDivisorAlgebraic4.spec_monicInLast_roots_small
      (fun j ↦ (ha j).continuousAt) ha0 hε
    have hrelation := adim7_coordinate_relation d θ (Ideal.Quotient.mk P v)
      (Ideal.Quotient.mk P (c i)) Q W (R i) δ hmin (hcoord i) hW.1 hWx
      q u (r i) Δ hq (fun j ↦ (hu j).2) humonic (hr i) hΔ
    filter_upwards [hform, hbound, hrelation] with w hwform hwbound hwrelation
    intro t hΔw ht
    apply hwbound
    rw [← hwform]
    exact hwrelation t hΔw ht
  have hall := Filter.eventually_all.mpr hsmall
  filter_upwards [hall] with w hw
  exact fun t hΔw ht i ↦ hw i t hΔw ht

/-- Primitive roots reconstruct points in any prescribed neighbourhood with the correct linear data. -/
private theorem adim7_reconstructed_roots_in_neighbourhood (n d : ℕ) (P : Ideal (AnalyticGerm n))
    (hP : P.IsPrime) (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hfinite : θ.Finite)
    (hcomp : ∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm n,
      Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (c : Fin n → AnalyticGerm n)
    (hc : ∀ i, (c i).val = Germ.ofFun (fun z : Fin n → ℂ ↦ z i))
    (ℓ : (Fin n → ℂ) →L[ℂ] ℂ) (v : AnalyticGerm n)
    (hv : v.val = Germ.ofFun (fun z ↦ ℓ z))
    (Q : Polynomial (AnalyticGerm d)) (δ : AnalyticGerm d)
    (R : Fin n → Polynomial (AnalyticGerm d))
    (hQ : IsWeierstrassPolynomial Q)
    (hmin : ∀ T : Polynomial (AnalyticGerm d),
      T.eval₂ θ (Ideal.Quotient.mk P v) = 0 ↔ Q ∣ T)
    (hcoord : ∀ i, θ δ * Ideal.Quotient.mk P (c i) =
      (R i).eval₂ θ (Ideal.Quotient.mk P v))
    (q : Polynomial ((Fin d → ℂ) → ℂ)) (Δ : (Fin d → ℂ) → ℂ)
    (r : Fin n → Polynomial ((Fin d → ℂ) → ℂ))
    (hq : ∀ i, AnalyticAt ℂ (q.coeff i) 0 ∧
      Germ.ofFun (q.coeff i) = (Q.coeff i).val)
    (hΔrep : Germ.ofFun Δ = δ.val)
    (hr : ∀ j i, AnalyticAt ℂ ((r j).coeff i) 0 ∧
      Germ.ofFun ((r j).coeff i) = ((R j).coeff i).val)
    (U : Set (Fin n → ℂ)) (hU : IsOpen U) (hU0 : (0 : Fin n → ℂ) ∈ U) :
    ∃ V : Set (Fin d → ℂ), IsOpen V ∧ (0 : Fin d → ℂ) ∈ V ∧
      ∀ w ∈ V, Δ w ≠ 0 → ∃ t : ℂ,
        q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 ∧
        let z : Fin n → ℂ := fun i ↦
          (r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w
        z ∈ U ∧ π z = w ∧ ℓ z = t := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hU0)
  have hsmall := adim7_reconstructed_coordinates_small n d P hP.ne_top π θ hfinite
    hcomp c hc v Q δ R hmin hcoord q Δ r (fun i ↦ (hq i).2) hΔrep
    (fun j i ↦ (hr j i).2) ε hε
  have hlinear := adim7_reconstructed_projection_and_primitive n d P π θ hcomp c hc v
    Q δ R hmin hcoord q Δ r (fun i ↦ (hq i).2) hΔrep (fun j i ↦ (hr j i).2) ℓ hv
  obtain ⟨V₀, hV₀sub, hV₀open, hV₀zero⟩ := mem_nhds_iff.mp (hsmall.and hlinear)
  obtain ⟨V₁, hV₁open, hV₁zero, hroot⟩ :=
    adim7_weierstrass_root_near d Q q hQ hq 1 zero_lt_one
  refine ⟨V₀ ∩ V₁, hV₀open.inter hV₁open, ⟨hV₀zero, hV₁zero⟩, ?_⟩
  intro w hw hΔw
  obtain ⟨t, ht, _⟩ := hroot w hw.2
  refine ⟨t, ht, ?_, (hV₀sub hw.1).2 t hΔw ht⟩
  apply hball
  rw [Metric.mem_ball, dist_zero_right]
  exact (pi_norm_lt_iff hε).mpr ((hV₀sub hw.1).1 t hΔw ht)

/-- Weierstrass division permits any finite dimensional complex parameter space. -/
private theorem adim7_division_with_parameters
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {g : E × ℂ → ℂ} {k : ℕ} {a : Fin k → E → ℂ}
    (hg : AnalyticAt ℂ g 0) (ha : ∀ j, AnalyticAt ℂ (a j) 0)
    (ha0 : ∀ j, a j 0 = 0) :
    ∃ q : E × ℂ → ℂ, AnalyticAt ℂ q 0 ∧
      ∃ b : Fin k → E → ℂ, (∀ j, AnalyticAt ℂ (b j) 0) ∧
        g =ᶠ[𝓝 0] fun p ↦ q p * (p.2 ^ k + ∑ j, a j p.1 * p.2 ^ (j : ℕ)) +
          ∑ j, b j p.1 * p.2 ^ (j : ℕ) := by
  let e : E ≃L[ℂ] (Fin (Module.finrank ℂ E) → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let e' := e.prodCongr (ContinuousLinearEquiv.refl ℂ ℂ)
  obtain ⟨q, hq, b, hb, heq⟩ := AnalyticDivisorAlgebraic4.spec_weierstrass_division
    (hg.comp_of_eq (e'.symm.analyticAt 0) (map_zero _))
    (fun j ↦ (ha j).comp_of_eq (e.symm.analyticAt 0) (map_zero _))
    (fun j ↦ by simpa using ha0 j)
  refine ⟨fun p ↦ q (e' p), hq.comp_of_eq (e'.analyticAt 0) (map_zero _),
    fun j x ↦ b j (e x),
    fun j ↦ (hb j).comp_of_eq (e.analyticAt 0) (map_zero _), ?_⟩
  have ht : Tendsto e' (𝓝 0) (𝓝 0) := by
    simpa only [ContinuousAt, map_zero] using e'.continuous.continuousAt (x := 0)
  filter_upwards [ht.eventually heq] with p hp
  simpa [e', AnalyticDivisorAlgebraic4.monicInLast] using hp

/-- Separate the first fibre coordinate, retaining the other coordinates as parameters. -/
private def adim7_split_fibre {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (n : ℕ) :
    (E × (Fin (n + 1) → ℂ)) ≃L[ℂ] ((E × (Fin n → ℂ)) × ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun p ↦ ((p.1, Fin.tail p.2), p.2 0)
      invFun := fun p ↦ (p.1.1, Fin.cons p.2 p.1.2)
      left_inv := by intro p; simp
      right_inv := by intro p; simp
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

/-- Successive division gives an exact analytic identity with a bounded polynomial remainder. -/
private theorem adim7_simultaneous_division
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (n : ℕ) (k : Fin n → ℕ) (a : (i : Fin n) → Fin (k i) → E → ℂ)
    (ha : ∀ i j, AnalyticAt ℂ (a i j) 0) (ha0 : ∀ i j, a i j 0 = 0)
    (f : E × (Fin n → ℂ) → ℂ) (hf : AnalyticAt ℂ f 0) :
    ∃ (q : Fin n → E × (Fin n → ℂ) → ℂ)
      (b : ((i : Fin n) → Fin (k i)) → E → ℂ),
      (∀ i, AnalyticAt ℂ (q i) 0) ∧ (∀ e, AnalyticAt ℂ (b e) 0) ∧
      f =ᶠ[𝓝 0] fun p ↦
        (∑ i, q i p * (p.2 i ^ k i + ∑ j, a i j p.1 * p.2 i ^ (j : ℕ))) +
        ∑ e, b e p.1 * ∏ i, p.2 i ^ (e i : ℕ) := by
  classical
  induction n with
  | zero =>
      refine ⟨Fin.elim0, fun _ x ↦ f (x, 0), (fun i ↦ Fin.elim0 i), ?_, ?_⟩
      · intro e
        exact hf.comp_of_eq (analyticAt_id.prod analyticAt_const) rfl
      · exact Filter.Eventually.of_forall fun p ↦ by
          simp only [Fin.sum_univ_zero, Fin.prod_univ_zero, mul_one, zero_add]
          rw [Fintype.sum_unique]
          congr 1
          exact Prod.ext rfl (Subsingleton.elim _ _)
  | succ n ih =>
      let L := adim7_split_fibre (E := E) n
      obtain ⟨q₀, hq₀, b₀, hb₀, hdiv⟩ := adim7_division_with_parameters
        (g := fun p ↦ f (L.symm p)) (a := fun j p ↦ a 0 j p.1)
        (hf.comp_of_eq (L.symm.analyticAt 0) (map_zero _))
        (fun j ↦ (ha 0 j).comp_of_eq analyticAt_fst rfl)
        (fun j ↦ ha0 0 j)
      have hrec (j : Fin (k 0)) := ih (fun i ↦ k i.succ) (fun i ↦ a i.succ)
        (fun i ↦ ha i.succ) (fun i ↦ ha0 i.succ) (b₀ j) (hb₀ j)
      choose q b hq hb heq using hrec
      let tailMap : (E × (Fin (n + 1) → ℂ)) →L[ℂ] E × (Fin n → ℂ) :=
        (ContinuousLinearMap.fst ℂ (E × (Fin n → ℂ)) ℂ).comp L.toContinuousLinearMap
      let q' : Fin (n + 1) → E × (Fin (n + 1) → ℂ) → ℂ :=
        Fin.cons (fun p ↦ q₀ (L p))
          (fun i p ↦ ∑ j, q j i (tailMap p) * p.2 0 ^ (j : ℕ))
      let b' : ((i : Fin (n + 1)) → Fin (k i)) → E → ℂ :=
        fun e ↦ b (e 0) (fun i ↦ e i.succ)
      refine ⟨q', b', ?_, fun e ↦ hb _ _, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun i ↦ ?_) i
        · exact hq₀.comp_of_eq (L.analyticAt 0) (map_zero _)
        · change AnalyticAt ℂ (fun p ↦ ∑ j, q j i (tailMap p) * p.2 0 ^ (j : ℕ)) 0
          apply Finset.analyticAt_fun_sum
          intro j _
          apply AnalyticAt.mul
          · exact (hq j i).comp_of_eq (tailMap.analyticAt 0) (map_zero _)
          · exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) ↦ ℂ)
              0).analyticAt 0 |>.comp_of_eq analyticAt_snd rfl).pow _
      · have hL : Tendsto L (𝓝 0) (𝓝 0) := by
          simpa only [ContinuousAt, map_zero] using L.continuous.continuousAt (x := 0)
        have htail : Tendsto tailMap (𝓝 0) (𝓝 0) := by
          simpa only [ContinuousAt, map_zero] using tailMap.continuous.continuousAt (x := 0)
        filter_upwards [hL.eventually hdiv,
          htail.eventually (Filter.eventually_all.mpr heq)] with p hp hr
        rw [L.symm_apply_apply] at hp
        rw [hp]
        change q₀ (L p) * _ + (∑ j, b₀ j (tailMap p) * p.2 0 ^ (j : ℕ)) = _
        simp_rw [hr]
        rw [Fin.sum_univ_succ]
        simp only [q', Fin.cons_zero, Fin.cons_succ]
        have hrem :
            (∑ j : Fin (k 0), (∑ e : (i : Fin n) → Fin (k i.succ),
              b j e p.1 * ∏ i, p.2 i.succ ^ (e i : ℕ)) * p.2 0 ^ (j : ℕ)) =
            ∑ e : (i : Fin (n + 1)) → Fin (k i),
              b' e p.1 * ∏ i, p.2 i ^ (e i : ℕ) := by
          rw [← Equiv.sum_comp (Fin.consEquiv (fun i ↦ Fin (k i)))]
          rw [Fintype.sum_prod_type]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro e _
          simp only [b', Fin.consEquiv, Equiv.coe_fn_mk, Fin.cons_zero, Fin.cons_succ,
            Fin.prod_univ_succ]
          ring
        have hcor :
            (∑ j : Fin (k 0), (∑ i : Fin n, q j i (tailMap p) *
              (p.2 i.succ ^ k i.succ + ∑ l, a i.succ l p.1 * p.2 i.succ ^ (l : ℕ))) *
              p.2 0 ^ (j : ℕ)) =
            ∑ i : Fin n, (∑ j : Fin (k 0), q j i (tailMap p) * p.2 0 ^ (j : ℕ)) *
              (p.2 i.succ ^ k i.succ + ∑ l, a i.succ l p.1 * p.2 i.succ ^ (l : ℕ)) := by
          simp only [Finset.sum_mul]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          ring
        simp only [add_mul, Finset.sum_add_distrib]
        change q₀ (L p) * _ +
          ((∑ j : Fin (k 0), (∑ i : Fin n, q j i (tailMap p) *
            (p.2 i.succ ^ k i.succ + ∑ l, a i.succ l p.1 * p.2 i.succ ^ (l : ℕ))) *
            p.2 0 ^ (j : ℕ)) + _) = _
        simp only [show (tailMap p).1 = p.1 from rfl,
          show (tailMap p).2 = Fin.tail p.2 from rfl, Fin.tail]
        rw [hcor, hrem]
        simp only [show (L p).2 = p.2 0 from rfl,
          show (L p).1.1 = p.1 from rfl, add_assoc]

/-- Division by representative coordinate polynomials holds on a common product neighbourhood. -/
private theorem adim7_polynomial_simultaneous_division (n d : ℕ)
    (W : Fin n → Polynomial (AnalyticGerm d))
    (u : Fin n → Polynomial ((Fin d → ℂ) → ℂ))
    (hW : ∀ i, IsWeierstrassPolynomial (W i))
    (hu : ∀ i j, AnalyticAt ℂ ((u i).coeff j) 0 ∧
      Germ.ofFun ((u i).coeff j) = ((W i).coeff j).val)
    (f : (Fin d → ℂ) × (Fin n → ℂ) → ℂ) (hf : AnalyticAt ℂ f 0) :
    ∃ (k : Fin n → ℕ) (q : Fin n → (Fin d → ℂ) × (Fin n → ℂ) → ℂ)
      (b : ((i : Fin n) → Fin (k i)) → (Fin d → ℂ) → ℂ),
      (∀ i, 0 < k i) ∧ (∀ i, AnalyticAt ℂ (q i) 0) ∧
      (∀ e, AnalyticAt ℂ (b e) 0) ∧
      f =ᶠ[𝓝 0] fun p ↦
        (∑ i, q i p * (u i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) p.1) (p.2 i)) +
        ∑ e, b e p.1 * ∏ i, p.2 i ^ (e i : ℕ) := by
  classical
  have hform (i : Fin n) := adim7_weierstrass_representative d (W i) (u i) (hW i) (hu i)
  choose k a hk ha ha0 heq using hform
  obtain ⟨q, b, hq, hb, hdiv⟩ := adim7_simultaneous_division n k a ha ha0 f hf
  refine ⟨k, q, b, hk, hq, hb, ?_⟩
  have ht : Tendsto (Prod.fst : (Fin d → ℂ) × (Fin n → ℂ) → (Fin d → ℂ))
      (𝓝 0) (𝓝 0) := continuous_fst.continuousAt
  filter_upwards [hdiv, ht.eventually (Filter.eventually_all.mpr heq)] with p hp he
  rw [hp]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [he i]
  rfl

/-- Pullback of analytic germs along the linear parameter map. -/
private def adim7_parameter_pullback {n d : ℕ}
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)) : AnalyticGerm d →+* AnalyticGerm n := by
  have ht : Tendsto π (𝓝 0) (𝓝 0) := by
    simpa only [ContinuousAt, map_zero] using π.continuous.continuousAt (x := 0)
  let t : Germ (𝓝 (0 : Fin d → ℂ)) ℂ →+* Germ (𝓝 (0 : Fin n → ℂ)) ℂ :=
    { toFun := fun g ↦ g.compTendsto π ht
      map_one' := rfl
      map_zero' := rfl
      map_mul' := fun g h ↦ Germ.inductionOn g fun _ ↦ Germ.inductionOn h fun _ ↦ rfl
      map_add' := fun g h ↦ Germ.inductionOn g fun _ ↦ Germ.inductionOn h fun _ ↦ rfl }
  refine
    { toFun := fun a ↦ ⟨t a.val, ?_⟩
      map_one' := Subtype.ext t.map_one
      map_zero' := Subtype.ext t.map_zero
      map_mul' := fun a b ↦ Subtype.ext (t.map_mul a.val b.val)
      map_add' := fun a b ↦ Subtype.ext (t.map_add a.val b.val) }
  obtain ⟨f, hf, hrep⟩ := a.property
  refine ⟨fun z ↦ f (π z), hf.comp_of_eq (π.analyticAt 0) (map_zero _), ?_⟩
  change _ = a.val.compTendsto π ht
  rw [← hrep]
  rfl

private theorem adim7_parameter_pullback_rep {n d : ℕ}
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (a : AnalyticGerm d) (f : (Fin d → ℂ) → ℂ) (hrep : Germ.ofFun f = a.val) :
    Germ.ofFun (fun z ↦ f (π z)) = (adim7_parameter_pullback π a).val := by
  change _ = a.val.compTendsto π (by
    simpa only [ContinuousAt, map_zero] using π.continuous.continuousAt (x := 0))
  rw [← hrep]
  rfl

/-- Compatibility identifies the parameter map with pullback followed by the quotient map. -/
private theorem adim7_parameter_pullback_quotient {n d : ℕ} (P : Ideal (AnalyticGerm n))
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hcomp : ∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm n,
      Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b) :
    (Ideal.Quotient.mk P).comp (adim7_parameter_pullback π) = θ := by
  ext a
  obtain ⟨f, hf, hrep⟩ := a.property
  exact (hcomp a f hf hrep _ (adim7_parameter_pullback_rep π a f hrep)).symm

/-- Polynomial evaluation commutes with passing from functions to germs. -/
private theorem adim7_polynomial_eval_germ (n : ℕ)
    (p : Polynomial ((Fin n → ℂ) → ℂ)) (x : (Fin n → ℂ) → ℂ) :
    Germ.ofFun (fun z ↦ p.eval₂ (Pi.evalRingHom (fun _ : Fin n → ℂ ↦ ℂ) z) (x z)) =
      (p.map (Germ.coeRingHom (𝓝 (0 : Fin n → ℂ)))).eval (Germ.ofFun x) := by
  have heq : (fun z ↦ p.eval₂ (Pi.evalRingHom (fun _ : Fin n → ℂ ↦ ℂ) z) (x z)) =
      p.eval x := by
    funext z
    exact Polynomial.eval₂_at_apply _ _
  rw [heq, Polynomial.eval_map]
  exact (Polynomial.eval₂_at_apply (Germ.coeRingHom (𝓝 (0 : Fin n → ℂ))) x).symm

/-- Coordinate-polynomial representatives remain exact after parameter pullback. -/
private theorem adim7_coordinate_polynomial_rep (n d : ℕ)
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (W : Polynomial (AnalyticGerm d)) (u : Polynomial ((Fin d → ℂ) → ℂ))
    (hu : ∀ j, Germ.ofFun (u.coeff j) = (W.coeff j).val)
    (i : Fin n) (c : AnalyticGerm n)
    (hc : c.val = Germ.ofFun (fun z : Fin n → ℂ ↦ z i)) :
    Germ.ofFun (fun z ↦ u.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) (π z)) (z i)) =
      (W.eval₂ (adim7_parameter_pullback π) c).val := by
  let τ : ((Fin d → ℂ) → ℂ) →+* ((Fin n → ℂ) → ℂ) :=
    RingHom.pi (fun z ↦ Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) (π z))
  have hm : (u.map τ).map (Germ.coeRingHom (𝓝 (0 : Fin n → ℂ))) =
      W.map ((analyticGermSubring n).subtype.comp (adim7_parameter_pullback π)) := by
    ext j
    simp only [Polynomial.coeff_map, RingHom.comp_apply]
    exact adim7_parameter_pullback_rep π (W.coeff j) (u.coeff j) (hu j)
  have heq := adim7_polynomial_eval_germ n (u.map τ) (fun z ↦ z i)
  rw [hm, ← hc] at heq
  have hl : (fun z ↦ (u.map τ).eval₂
      (Pi.evalRingHom (fun _ : Fin n → ℂ ↦ ℂ) z) (z i)) =
      (fun z ↦ u.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) (π z)) (z i)) := by
    funext z
    rw [Polynomial.eval₂_map]
    rfl
  rw [hl] at heq
  rw [Polynomial.eval_map] at heq
  exact heq.trans (Polynomial.hom_eval₂ W (adim7_parameter_pullback π)
    (analyticGermSubring n).subtype c).symm

/-- An exact analytic division identity puts its finite remainder in the prime ideal. -/
private theorem adim7_division_remainder_in_quotient (n d : ℕ)
    {ι : Type*} [Fintype ι] (P : Ideal (AnalyticGerm n))
    (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hcomp : (Ideal.Quotient.mk P).comp (adim7_parameter_pullback π) = θ)
    (c : Fin n → AnalyticGerm n)
    (hc : ∀ i, (c i).val = Germ.ofFun (fun z : Fin n → ℂ ↦ z i))
    (W : Fin n → Polynomial (AnalyticGerm d))
    (u : Fin n → Polynomial ((Fin d → ℂ) → ℂ))
    (hu : ∀ i j, Germ.ofFun ((u i).coeff j) = ((W i).coeff j).val)
    (hW : ∀ i, (W i).eval₂ θ (Ideal.Quotient.mk P (c i)) = 0)
    (g : AnalyticGerm n) (hg : g ∈ P) (f : (Fin n → ℂ) → ℂ)
    (hf : Germ.ofFun f = g.val)
    (q : Fin n → (Fin n → ℂ) → ℂ) (hq : ∀ i, AnalyticAt ℂ (q i) 0)
    (B : ι → AnalyticGerm d) (b : ι → (Fin d → ℂ) → ℂ)
    (hb : ∀ j, Germ.ofFun (b j) = (B j).val) (e : ι → Fin n → ℕ)
    (hid : f =ᶠ[𝓝 0] fun z ↦
      (∑ i, q i z * (u i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) (π z)) (z i)) +
      ∑ j, b j (π z) * ∏ i, z i ^ e j i) :
    ∑ j, θ (B j) * ∏ i, Ideal.Quotient.mk P (c i) ^ e j i = 0 := by
  classical
  let qg : Fin n → AnalyticGerm n := fun i ↦ ⟨Germ.ofFun (q i), q i, hq i, rfl⟩
  have heq : g = (∑ i, qg i * (W i).eval₂ (adim7_parameter_pullback π) (c i)) +
      ∑ j, adim7_parameter_pullback π (B j) * ∏ i, c i ^ e j i := by
    apply Subtype.ext
    change g.val = (analyticGermSubring n).subtype
      ((∑ i, qg i * (W i).eval₂ (adim7_parameter_pullback π) (c i)) +
        ∑ j, adim7_parameter_pullback π (B j) * ∏ i, c i ^ e j i)
    rw [map_add, map_sum, map_sum]
    simp only [map_mul, map_prod, map_pow, Subring.subtype_apply]
    simp_rw [← hf, ← adim7_coordinate_polynomial_rep n d π _ _ (hu _) _ _ (hc _),
      ← adim7_parameter_pullback_rep π _ _ (hb _), hc]
    change Germ.coeRingHom (𝓝 (0 : Fin n → ℂ)) f =
      (∑ i, Germ.coeRingHom (𝓝 (0 : Fin n → ℂ)) (q i) *
        Germ.coeRingHom (𝓝 (0 : Fin n → ℂ))
          (fun z ↦ (u i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) (π z)) (z i))) +
      ∑ j, Germ.coeRingHom (𝓝 (0 : Fin n → ℂ)) (fun z ↦ b j (π z)) *
        ∏ i, Germ.coeRingHom (𝓝 (0 : Fin n → ℂ)) (fun z ↦ z i) ^ e j i
    simp only [← map_pow, ← map_prod, ← map_mul, ← map_sum, ← map_add]
    apply Germ.coe_eq.mpr
    filter_upwards [hid] with z hz
    simpa only [Pi.add_apply, Finset.sum_apply, Pi.mul_apply, Finset.prod_apply, Pi.pow_apply] using hz
  have hmap := congrArg (Ideal.Quotient.mk P) heq
  simp only [map_add, map_sum, map_mul, map_prod, map_pow] at hmap
  simp_rw [Polynomial.hom_eval₂, hcomp, hW, mul_zero] at hmap
  have hB (j : ι) : Ideal.Quotient.mk P (adim7_parameter_pullback π (B j)) = θ (B j) :=
    RingHom.congr_fun hcomp (B j)
  simpa only [hB, Finset.sum_const_zero, zero_add,
    Ideal.Quotient.eq_zero_iff_mem.mpr hg] using hmap.symm

/-- Exact simultaneous division transfers analytic equations to reconstructed roots. -/
private theorem adim7_analytic_equation_at_roots (n d : ℕ) (P : Ideal (AnalyticGerm n))
    (hP : P ≠ ⊤) (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hfinite : θ.Finite)
    (hcomp : ∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm n,
      Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (c : Fin n → AnalyticGerm n)
    (hc : ∀ i, (c i).val = Germ.ofFun (fun z : Fin n → ℂ ↦ z i))
    (v : AnalyticGerm n) (Q : Polynomial (AnalyticGerm d)) (δ : AnalyticGerm d)
    (R : Fin n → Polynomial (AnalyticGerm d))
    (hmin : ∀ T : Polynomial (AnalyticGerm d),
      T.eval₂ θ (Ideal.Quotient.mk P v) = 0 ↔ Q ∣ T)
    (hcoord : ∀ i, θ δ * Ideal.Quotient.mk P (c i) =
      (R i).eval₂ θ (Ideal.Quotient.mk P v))
    (q : Polynomial ((Fin d → ℂ) → ℂ)) (Δ : (Fin d → ℂ) → ℂ)
    (r : Fin n → Polynomial ((Fin d → ℂ) → ℂ))
    (hq : ∀ i, Germ.ofFun (q.coeff i) = (Q.coeff i).val)
    (hΔ : Germ.ofFun Δ = δ.val)
    (hr : ∀ j i, Germ.ofFun ((r j).coeff i) = ((R j).coeff i).val)
    (g : AnalyticGerm n) (hg : g ∈ P) (f : (Fin n → ℂ) → ℂ)
    (hf : AnalyticAt ℂ f 0) (hfrep : Germ.ofFun f = g.val) :
    ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ t : ℂ, Δ w ≠ 0 →
      q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 →
      f (fun i ↦ (r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w) = 0 := by
  classical
  choose W hW hWzero using adim7_coordinate_weierstrass n d P hP π θ hfinite hcomp c hc
  have hurep (i : Fin n) := adim7_monic_representative d (W i) (hW i).1
  choose u humonic hu using hurep
  obtain ⟨k, a, b, _, ha, hb, hdiv⟩ := adim7_polynomial_simultaneous_division n d W u hW hu
    (fun p ↦ f p.2) (hf.comp_of_eq analyticAt_snd rfl)
  let B : ((i : Fin n) → Fin (k i)) → AnalyticGerm d :=
    fun e ↦ ⟨Germ.ofFun (b e), b e, hb e, rfl⟩
  have hgraph : Tendsto (fun z ↦ (π z, z)) (𝓝 (0 : Fin n → ℂ)) (𝓝 0) := by
    let L : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ) × (Fin n → ℂ) :=
      π.prod (ContinuousLinearMap.id ℂ (Fin n → ℂ))
    have ht : Tendsto L (𝓝 0) (𝓝 0) := by
      simpa only [ContinuousAt, map_zero] using L.continuous.continuousAt (x := 0)
    exact ht
  have hF := adim7_division_remainder_in_quotient n d P π θ
    (adim7_parameter_pullback_quotient P π θ hcomp) c hc W u (fun i j ↦ (hu i j).2)
    hWzero g hg f hfrep (fun i z ↦ a i (π z, z))
    (fun i ↦ (ha i).comp_of_eq ((π.analyticAt 0).prod analyticAt_id) (by simp))
    B b (fun _ ↦ rfl) (fun e i ↦ (e i : ℕ)) (hgraph.eventually hdiv)
  let J := Fintype.equivFin ((i : Fin n) → Fin (k i))
  let N := ∑ j : Fin (Fintype.card ((i : Fin n) → Fin (k i))), ∑ i, (J.symm j i : ℕ)
  have hN (j : Fin (Fintype.card ((i : Fin n) → Fin (k i)))) :
      ∑ i, (J.symm j i : ℕ) ≤ N := Finset.single_le_sum (f := fun j ↦ ∑ i, (J.symm j i : ℕ))
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j)
  have hF' : ∑ j, θ (B (J.symm j)) * ∏ i, Ideal.Quotient.mk P (c i) ^ (J.symm j i : ℕ) = 0 :=
    (Equiv.sum_comp J.symm _).trans hF
  have hrem := adim7_polynomial_equations_at_roots n d _ N θ (Ideal.Quotient.mk P v)
    Q δ (fun i ↦ Ideal.Quotient.mk P (c i)) R hmin hcoord (fun j ↦ B (J.symm j))
    (fun j i ↦ (J.symm j i : ℕ)) hN hF' q Δ r (fun j ↦ b (J.symm j)) hq hΔ hr (fun _ ↦ rfl)
  have hrelations (i : Fin n) := adim7_coordinate_relation d θ (Ideal.Quotient.mk P v)
    (Ideal.Quotient.mk P (c i)) Q (W i) (R i) δ hmin (hcoord i) (hW i).1 (hWzero i)
    q (u i) (r i) Δ hq (fun j ↦ (hu i j).2) (humonic i) (hr i) hΔ
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hdiv
  have hsmall := adim7_reconstructed_coordinates_small n d P hP π θ hfinite hcomp c hc v Q δ R
    hmin hcoord q Δ r hq hΔ hr ε hε
  filter_upwards [hrem, Filter.eventually_all.mpr hrelations, hsmall,
    Metric.ball_mem_nhds (0 : Fin d → ℂ) hε] with w hwrem hwrel hwsmall hwnear
  intro t hΔw ht
  let z : Fin n → ℂ := fun i ↦ (r i).eval₂
    (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w
  have hz : ‖z‖ < ε := (pi_norm_lt_iff hε).mpr (hwsmall t hΔw ht)
  have hp := hball (show (w, z) ∈ Metric.ball 0 ε by
    rw [Metric.mem_ball, dist_zero_right, Prod.norm_def]
    exact max_lt (by simpa only [Metric.mem_ball, dist_zero_right] using hwnear) hz)
  have hrzero : ∑ e, b e w * ∏ i, z i ^ (e i : ℕ) = 0 :=
    (Equiv.sum_comp J.symm _).symm.trans (hwrem t hΔw ht)
  change f z = _ at hp
  dsimp only at hp
  rw [hp, hrzero, add_zero]
  apply Finset.sum_eq_zero
  intro i _
  rw [hwrel i t hΔw ht, mul_zero]

/-- Roots of one primitive relation realize the simultaneous analytic equations.
Coefficient representatives and the common denominator are explicit data.
Source: Gunning--Rossi, III.C, local parametrization; Nicolaescu, Theorem 9.2.11 and Remark 9.2.12(b). -/
theorem adim7_roots_off_discriminant_aux (n d : ℕ) (P : Ideal (AnalyticGerm n))
    (hP : P.IsPrime) (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hfinite : θ.Finite) (hinj : Function.Injective θ)
    (hcomp : ∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm n,
      Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (c : Fin n → AnalyticGerm n)
    (hc : ∀ i, (c i).val = Germ.ofFun (fun z : Fin n → ℂ ↦ z i))
    (ℓ : (Fin n → ℂ) →L[ℂ] ℂ) (v : AnalyticGerm n)
    (hv : v.val = Germ.ofFun (fun z ↦ ℓ z))
    (Q : Polynomial (AnalyticGerm d)) (δ : AnalyticGerm d)
    (R : Fin n → Polynomial (AnalyticGerm d))
    (hQ : IsWeierstrassPolynomial Q) (hδ : δ ≠ 0)
    (hmin : ∀ T : Polynomial (AnalyticGerm d),
      T.eval₂ θ (Ideal.Quotient.mk P v) = 0 ↔ Q ∣ T)
    (hcoord : ∀ i, θ δ * Ideal.Quotient.mk P (c i) =
      (R i).eval₂ θ (Ideal.Quotient.mk P v))
    (q : Polynomial ((Fin d → ℂ) → ℂ)) (Δ : (Fin d → ℂ) → ℂ)
    (r : Fin n → Polynomial ((Fin d → ℂ) → ℂ))
    (hq : ∀ i, AnalyticAt ℂ (q.coeff i) 0 ∧
      Germ.ofFun (q.coeff i) = (Q.coeff i).val)
    (hΔ : AnalyticAt ℂ Δ 0) (hΔrep : Germ.ofFun Δ = δ.val)
    (hr : ∀ j i, AnalyticAt ℂ ((r j).coeff i) 0 ∧
      Germ.ofFun ((r j).coeff i) = ((R j).coeff i).val)
    (m : ℕ) (g : Fin m → AnalyticGerm n) (hgen : Ideal.span (Set.range g) = P)
    (f : Fin m → (Fin n → ℂ) → ℂ)
    (U : Set (Fin n → ℂ)) (hU : IsOpen U) (hU0 : (0 : Fin n → ℂ) ∈ U)
    (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (hrep : ∀ j, Germ.ofFun (f j) = (g j).val) :
    ∃ V : Set (Fin d → ℂ), IsOpen V ∧ (0 : Fin d → ℂ) ∈ V ∧
      ∀ w ∈ V, Δ w ≠ 0 → ∃ t : ℂ,
        q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 ∧
        let z : Fin n → ℂ := fun i ↦
          (r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w
        z ∈ U ∧ π z = w ∧ ℓ z = t ∧ ∀ j, f j z = 0 := by
  have hzero (j : Fin m) := adim7_analytic_equation_at_roots n d P hP.ne_top π θ hfinite
    hcomp c hc v Q δ R hmin hcoord q Δ r (fun i ↦ (hq i).2) hΔrep
    (fun i j ↦ (hr i j).2) (g j)
    (hgen ▸ Ideal.subset_span (Set.mem_range_self j)) (f j) (hf j 0 hU0) (hrep j)
  obtain ⟨V₀, hV₀sub, hV₀open, hV₀zero⟩ :=
    mem_nhds_iff.mp (Filter.eventually_all.mpr hzero)
  obtain ⟨V₁, hV₁open, hV₁zero, hroot⟩ := adim7_reconstructed_roots_in_neighbourhood
    n d P hP π θ hfinite hcomp c hc ℓ v hv Q δ R hQ hmin hcoord q Δ r hq hΔrep hr U hU hU0
  refine ⟨V₀ ∩ V₁, hV₀open.inter hV₁open, ⟨hV₀zero, hV₁zero⟩, ?_⟩
  intro w hw hΔw
  obtain ⟨t, ht, hz, hπ, hℓ⟩ := hroot w hw.2 hΔw
  exact ⟨t, ht, hz, hπ, hℓ, fun j ↦ hV₀sub hw.1 j t hΔw ht⟩

#print axioms adim7_roots_off_discriminant_aux

/-- Every root of the primitive relation off the discriminant reconstructs a small point of
the zero germ, with the given parameter and primitive coordinate.
Source: Gunning--Rossi, III.C, local parametrization; Nicolaescu, Theorem 9.2.11 and Remark 9.2.12(b). -/
theorem adim7_reconstructed_roots_realised (n d : ℕ) (P : Ideal (AnalyticGerm n))
    (hP : P.IsPrime) (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hfinite : θ.Finite)
    (hcomp : ∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm n,
      Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (c : Fin n → AnalyticGerm n)
    (hc : ∀ i, (c i).val = Germ.ofFun (fun z : Fin n → ℂ ↦ z i))
    (ℓ : (Fin n → ℂ) →L[ℂ] ℂ) (v : AnalyticGerm n)
    (hv : v.val = Germ.ofFun (fun z ↦ ℓ z))
    (Q : Polynomial (AnalyticGerm d)) (δ : AnalyticGerm d)
    (R : Fin n → Polynomial (AnalyticGerm d))
    (hmin : ∀ T : Polynomial (AnalyticGerm d),
      T.eval₂ θ (Ideal.Quotient.mk P v) = 0 ↔ Q ∣ T)
    (hcoord : ∀ i, θ δ * Ideal.Quotient.mk P (c i) =
      (R i).eval₂ θ (Ideal.Quotient.mk P v))
    (q : Polynomial ((Fin d → ℂ) → ℂ)) (Δ : (Fin d → ℂ) → ℂ)
    (r : Fin n → Polynomial ((Fin d → ℂ) → ℂ))
    (hq : ∀ i, Germ.ofFun (q.coeff i) = (Q.coeff i).val)
    (hΔ : Germ.ofFun Δ = δ.val)
    (hr : ∀ j i, Germ.ofFun ((r j).coeff i) = ((R j).coeff i).val)
    (ε : ℝ) (hε : 0 < ε)
    (g : AnalyticGerm n) (hg : g ∈ P) (f : (Fin n → ℂ) → ℂ)
    (hf : AnalyticAt ℂ f 0) (hfrep : Germ.ofFun f = g.val) :
    ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ t : ℂ, Δ w ≠ 0 →
      q.eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t = 0 →
      let z : Fin n → ℂ := fun i ↦
        (r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) t / Δ w
      ‖z‖ < ε ∧ π z = w ∧ ℓ z = t ∧ f z = 0 := by
  filter_upwards [adim7_reconstructed_coordinates_small n d P hP.ne_top π θ hfinite hcomp c hc
      v Q δ R hmin hcoord q Δ r hq hΔ hr ε hε,
    adim7_reconstructed_projection_and_primitive n d P π θ hcomp c hc v Q δ R hmin hcoord
      q Δ r hq hΔ hr ℓ hv,
    adim7_analytic_equation_at_roots n d P hP.ne_top π θ hfinite hcomp c hc v Q δ R hmin
      hcoord q Δ r hq hΔ hr g hg f hf hfrep] with w hsmall hlin hzero
  intro t hΔw ht
  exact ⟨(pi_norm_lt_iff hε).mpr (hsmall t hΔw ht), (hlin t hΔw ht).1, (hlin t hΔw ht).2,
    hzero t hΔw ht⟩

private theorem adim7_dense_nonvanishing (d : ℕ)
    (V : Set (Fin d → ℂ)) (hV : IsOpen V) (hV0 : (0 : Fin d → ℂ) ∈ V)
    (hconn : IsPreconnected V) (Δ : (Fin d → ℂ) → ℂ)
    (hΔ : AnalyticOnNhd ℂ Δ V) (hne : ¬ (Δ =ᶠ[𝓝 (0 : Fin d → ℂ)] fun _ ↦ 0)) :
    Dense {w : V | Δ w.val ≠ 0} := by
  rw [dense_iff_inter_open]
  intro U hU hUne
  by_contra hmeet
  obtain ⟨O, hO, hOU⟩ := isOpen_induced_iff.mp hU
  obtain ⟨w, hwU⟩ := hUne
  have hwO : w.val ∈ O := by
    have : w ∈ (Subtype.val : V → Fin d → ℂ) ⁻¹' O := by simpa [hOU] using hwU
    exact this
  have hzeroU : ∀ x ∈ U, Δ x.val = 0 := by
    intro x hxU
    by_contra hx
    exact hmeet ⟨x, hxU, hx⟩
  have hlocal : Δ =ᶠ[𝓝 w.val] fun _ ↦ 0 := by
    filter_upwards [hO.mem_nhds hwO, hV.mem_nhds w.property] with x hxO hxV
    have hxU : (⟨x, hxV⟩ : V) ∈ U := by
      rw [← hOU]
      exact hxO
    simpa using hzeroU ⟨x, hxV⟩ hxU
  have hall : Set.EqOn Δ 0 V :=
    hΔ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn w.property hlocal
  apply hne
  filter_upwards [hV.mem_nhds hV0] with x hx
  exact hall hx

/-- A proper image containing the complement of a nonzero analytic discriminant
fills a connected parameter neighbourhood.
Source: Gunning--Rossi, I.A, identity theorem, and III.C, proper finite representatives. -/
theorem adim7_close_across_discriminant_aux (d : ℕ)
    (V : Set (Fin d → ℂ)) (hV : IsOpen V) (hV0 : (0 : Fin d → ℂ) ∈ V)
    (hconn : IsPreconnected V) (Δ : (Fin d → ℂ) → ℂ)
    (hΔ : AnalyticOnNhd ℂ Δ V) (hne : ¬ (Δ =ᶠ[𝓝 (0 : Fin d → ℂ)] fun _ ↦ 0))
    (Z : Type*) [TopologicalSpace Z] (p : Z → V) (hproper : IsProperMap p)
    (hroot : ∀ w : V, Δ w.val ≠ 0 → ∃ z, p z = w) :
    Function.Surjective p := by
  have hdense : Dense {w : V | Δ w.val ≠ 0} :=
    adim7_dense_nonvanishing d V hV hV0 hconn Δ hΔ hne
  have hsub : {w : V | Δ w.val ≠ 0} ⊆ Set.range p := by
    intro w hw
    exact hroot w hw
  have hclosure : closure {w : V | Δ w.val ≠ 0} ⊆ Set.range p :=
    closure_minimal hsub hproper.isClosed_range
  intro w
  apply hclosure
  rw [hdense.closure_eq]
  exact Set.mem_univ w

/-- Source: Gunning--Rossi, III.B--C, local parametrization; Grauert--Remmert, Coherent Analytic Sheaves, Chapter 3. -/
theorem adim7_surjective_projection_aux (n d m : ℕ) (P : Ideal (AnalyticGerm n))
    (hP : P.IsPrime) (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P)) (hfinite : θ.Finite) (hinj : Function.Injective θ)
    (hcomp : ∀ (a : AnalyticGerm d) (f : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ f 0 → Germ.ofFun f = a.val → ∀ (b : AnalyticGerm n),
      Germ.ofFun (fun z ↦ f (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (g : Fin m → AnalyticGerm n) (hgen : Ideal.span (Set.range g) = P)
    (f : Fin m → (Fin n → ℂ) → ℂ)
    (U : Set (Fin n → ℂ)) (hU : IsOpen U) (hU0 : (0 : Fin n → ℂ) ∈ U)
    (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (hrep : ∀ j, Germ.ofFun (f j) = (g j).val) :
    ∃ (W : Set (Fin n → ℂ)) (V : Set (Fin d → ℂ)),
      IsOpen W ∧ (0 : Fin n → ℂ) ∈ W ∧ W ⊆ U ∧
      IsOpen V ∧ (0 : Fin d → ℂ) ∈ V ∧
      ∃ p : {z : Fin n → ℂ // z ∈ W ∧ ∀ j, f j z = 0} → V,
        (∀ z, (p z).val = π z.val) ∧ IsProperMap p ∧
        (∀ w : V, (p ⁻¹' {w}).Finite) ∧ Function.Surjective p ∧
        ∀ z, (p z).val = 0 → z.val = 0 := by
  classical
  let c : Fin n → AnalyticGerm n := fun i ↦
    ⟨Germ.ofFun (fun z : Fin n → ℂ ↦ z i),
      fun z ↦ z i,
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n ↦ ℂ) i).analyticAt 0, rfl⟩
  have hc : ∀ i, (c i).val = Germ.ofFun (fun z : Fin n → ℂ ↦ z i) := fun _ ↦ rfl
  obtain ⟨ℓ, v, Q, δ, R, B, C, hv, hℓ, hQ, hδ, hbezout, hmin, hcoord⟩ :=
    adim7_primitive_form_aux n d P hP π θ hfinite hinj hcomp c hc
  obtain ⟨W₀, V₀, hW₀, hW₀0, hW₀U, hV₀, hV₀0, p₀, hp₀, hproper,
      hfib, hzero⟩ :=
    adim6_confined_projection_aux n d m P hP.ne_top π θ hfinite hcomp
      g hgen f U hU hU0 hf hrep
  choose qa hqa hqrep using fun i ↦ (Q.coeff i).property
  choose Δ hΔ hΔrep using δ.property
  choose ra hra hrrep using fun j i ↦ ((R j).coeff i).property
  let q : Polynomial ((Fin d → ℂ) → ℂ) :=
    Q.sum fun i _ ↦ Polynomial.monomial i (qa i)
  let r : Fin n → Polynomial ((Fin d → ℂ) → ℂ) := fun j ↦
    (R j).sum fun i _ ↦ Polynomial.monomial i (ra j i)
  have hq : ∀ i, AnalyticAt ℂ (q.coeff i) 0 ∧
      Germ.ofFun (q.coeff i) = (Q.coeff i).val := by
    intro i
    by_cases hi : i ∈ Q.support
    · simpa [q, Polynomial.sum, Polynomial.coeff_monomial, hi] using
        And.intro (hqa i) (hqrep i)
    · have hQi : Q.coeff i = 0 := by
        simpa [Polynomial.mem_support_iff] using hi
      simpa [q, Polynomial.sum, Polynomial.coeff_monomial, hi, hQi] using
        (And.intro (show AnalyticAt ℂ (0 : (Fin d → ℂ) → ℂ) 0 from analyticAt_const)
          (rfl : Germ.ofFun (0 : (Fin d → ℂ) → ℂ) = (0 : AnalyticGerm d).val))
  have hr : ∀ j i, AnalyticAt ℂ ((r j).coeff i) 0 ∧
      Germ.ofFun ((r j).coeff i) = ((R j).coeff i).val := by
    intro j i
    by_cases hi : i ∈ (R j).support
    · simpa [r, Polynomial.sum, Polynomial.coeff_monomial, hi] using
        And.intro (hra j i) (hrrep j i)
    · have hRi : (R j).coeff i = 0 := by
        simpa [Polynomial.mem_support_iff] using hi
      simpa [r, Polynomial.sum, Polynomial.coeff_monomial, hi, hRi] using
        (And.intro (show AnalyticAt ℂ (0 : (Fin d → ℂ) → ℂ) 0 from analyticAt_const)
          (rfl : Germ.ofFun (0 : (Fin d → ℂ) → ℂ) = (0 : AnalyticGerm d).val))
  obtain ⟨V₁, hV₁, hV₁0, hroots⟩ :=
    adim7_roots_off_discriminant_aux n d P hP π θ hfinite hinj hcomp c hc
      ℓ v hv Q δ R hQ hδ hmin hcoord q Δ r hq hΔ hΔrep hr
      m g hgen f W₀ hW₀ hW₀0 (fun j z hz ↦ hf j z (hW₀U hz)) hrep
  have hnear : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ),
      w ∈ V₀ ∧ w ∈ V₁ ∧ AnalyticAt ℂ Δ w := by
    filter_upwards [hV₀.mem_nhds hV₀0, hV₁.mem_nhds hV₁0,
      hΔ.eventually_analyticAt] with w hw₀ hw₁ hwΔ
    exact ⟨hw₀, hw₁, hwΔ⟩
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  let V : Set (Fin d → ℂ) := Metric.ball 0 ε
  have hV : IsOpen V := Metric.isOpen_ball
  have hV0 : (0 : Fin d → ℂ) ∈ V := Metric.mem_ball_self hε
  have hVV₀ : V ⊆ V₀ := fun w hw ↦ (hball hw).1
  have hVV₁ : V ⊆ V₁ := fun w hw ↦ (hball hw).2.1
  have hΔV : AnalyticOnNhd ℂ Δ V := fun w hw ↦ (hball hw).2.2
  have hΔne : ¬ (Δ =ᶠ[𝓝 (0 : Fin d → ℂ)] fun _ ↦ 0) := by
    intro he
    apply hδ
    apply Subtype.ext
    rw [← hΔrep]
    exact Filter.EventuallyEq.germ_eq he
  let W : Set (Fin n → ℂ) := W₀ ∩ π ⁻¹' V
  have hW : IsOpen W := hW₀.inter (hV.preimage π.continuous)
  have hW0 : (0 : Fin n → ℂ) ∈ W := by
    exact ⟨hW₀0, by simp [V, hε]⟩
  have hWU : W ⊆ U := fun _ hz ↦ hW₀U hz.1
  let A := {z : Fin n → ℂ // z ∈ W ∧ ∀ j, f j z = 0}
  let V' : Set V₀ := Subtype.val ⁻¹' V
  let A' : Set {z : Fin n → ℂ // z ∈ W₀ ∧ ∀ j, f j z = 0} := p₀ ⁻¹' V'
  let eV : V ≃ₜ V' :=
    { toFun := fun w ↦ ⟨⟨w.val, hVV₀ w.property⟩, w.property⟩
      invFun := fun w ↦ ⟨w.val.val, w.property⟩
      left_inv := by intro w; rfl
      right_inv := by intro w; rfl
      continuous_toFun := by
        apply Continuous.subtype_mk
        apply Continuous.subtype_mk
        exact continuous_subtype_val
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp continuous_subtype_val }
  let e : A ≃ₜ A' :=
    { toFun := fun z ↦ by
        have hzW : z.val ∈ W₀ ∧ π z.val ∈ V := by simpa [W] using z.property.1
        refine ⟨⟨z.val, hzW.1, z.property.2⟩, ?_⟩
        change (p₀ ⟨z.val, hzW.1, z.property.2⟩).val ∈ V
        rw [hp₀]
        exact hzW.2
      invFun := fun z ↦ by
        have hzV : π z.val.val ∈ V := by
          have hzprop := z.property
          change (p₀ z.val).val ∈ V at hzprop
          rwa [hp₀] at hzprop
        exact ⟨z.val.val, ⟨by exact ⟨z.val.property.1, hzV⟩, z.val.property.2⟩⟩
      left_inv := by intro z; rfl
      right_inv := by intro z; rfl
      continuous_toFun := by
        apply Continuous.subtype_mk
        apply Continuous.subtype_mk
        exact continuous_subtype_val
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp continuous_subtype_val }
  let p : A → V := eV.symm ∘ (V'.restrictPreimage p₀ : A' → V') ∘ e
  have hp : ∀ z, (p z).val = π z.val := by
    intro z
    exact hp₀ (e z)
  have hpProper : IsProperMap p :=
    eV.symm.isProperMap.comp ((hproper.restrictPreimage V').comp e.isProperMap)
  have hpFinite : ∀ w : V, (p ⁻¹' {w}).Finite := by
    intro w
    let w₀ : V₀ := ⟨w.val, hVV₀ w.property⟩
    let ι : A → {z : Fin n → ℂ // z ∈ W₀ ∧ ∀ j, f j z = 0} := fun z ↦ (e z).val
    have hι : Function.Injective ι := Subtype.val_injective.comp e.injective
    have hs : p ⁻¹' {w} ⊆ ι ⁻¹' (p₀ ⁻¹' {w₀}) := by
      intro z hz
      change p z = w at hz
      change p₀ (ι z) = w₀
      apply Subtype.ext
      have hzval := congrArg Subtype.val hz
      change (p z).val = w.val at hzval
      rw [hp z] at hzval
      exact (hp₀ (ι z)).trans (by simpa [ι, e] using hzval)
    exact (Set.Finite.preimage hι.injOn (hfib w₀)).subset hs
  have hpRoot : ∀ w : V, Δ w.val ≠ 0 → ∃ z, p z = w := by
    intro w hw
    obtain ⟨t, ht, hrest⟩ := hroots w.val (hVV₁ w.property) hw
    dsimp only at hrest
    let z : Fin n → ℂ := fun i ↦
      (r i).eval₂ (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w.val) t / Δ w.val
    change z ∈ W₀ ∧ π z = w.val ∧ ℓ z = t ∧ ∀ j, f j z = 0 at hrest
    obtain ⟨hzW₀, hzπ, hzℓ, hzf⟩ := hrest
    have hzV : π z ∈ V := by rw [hzπ]; exact w.property
    let za : A := ⟨z, ⟨hzW₀, hzV⟩, hzf⟩
    refine ⟨za, Subtype.ext ?_⟩
    exact (hp za).trans hzπ
  have hpSurj : Function.Surjective p :=
    adim7_close_across_discriminant_aux d V hV hV0
      (convex_ball 0 ε).isPreconnected Δ hΔV hΔne A p hpProper hpRoot
  refine ⟨W, V, hW, hW0, hWU, hV, hV0, p, hp, hpProper, hpFinite, hpSurj, ?_⟩
  intro z hz
  apply hzero (e z)
  exact (hp₀ (e z)).trans ((hp z).symm.trans hz)

private theorem adim7_local_equations_of_representatives (n m : ℕ)
    (A : Set (Fin n → ℂ)) (x : Fin n → ℂ)
    (U : Set (Fin n → ℂ)) (hU : IsOpen U) (hxU : x ∈ U)
    (f : Fin m → (Fin n → ℂ) → ℂ)
    (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (hA : ∀ z ∈ U, (z ∈ A ↔ ∀ j, f j z = 0)) :
    ∃ s : Finset (AnalyticGerm n), adim2_germ n A x = s.inf (adim2_zero n) := by
  classical
  let g : Fin m → AnalyticGerm n := fun i ↦
    ⟨Germ.ofFun (fun z ↦ f i (x + z)), fun z ↦ f i (x + z),
      (hf i x hxU).comp_of_eq (analyticAt_const.add analyticAt_id) (by simp), rfl⟩
  refine ⟨Finset.univ.image g, ?_⟩
  simp only [adim2_germ, adim2_zero, Finset.inf_image, Finset.inf_apply]
  have hinf : ∀ t : Finset (Fin m),
      t.inf (adim2_zero n ∘ g) =
        Filter.Germ.ofFun (fun z ↦ ∀ i ∈ t, f i (x + z) = 0) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        apply Filter.Germ.coe_eq.mpr
        exact Filter.Eventually.of_forall (by simp)
    | @insert a t ha ih =>
        rw [Finset.inf_insert, ih]
        apply Filter.Germ.coe_eq.mpr
        exact Filter.Eventually.of_forall (by simp [adim2_zero, g, ha])
  rw [hinf]
  apply Filter.Germ.coe_eq.mpr
  have hc : ContinuousAt (fun z : Fin n → ℂ ↦ x + z) 0 :=
    continuousAt_const.add continuousAt_id
  filter_upwards [hc.preimage_mem_nhds (hU.mem_nhds (by simpa using hxU))] with z hz
  simp only [Finset.mem_univ, forall_const, g]
  exact propext (hA (x + z) hz)

/-- Source: Gunning--Rossi, III.B--C, irreducible components and dimension; de Jong--Pfister, Chapters 3--4. -/
theorem adim7_component_comparison_aux (n : ℕ) (A : Set (Fin (n + 1) → ℂ))
    (x : Fin (n + 1) → ℂ) (hx : x ∈ A)
    (U : Set (Fin (n + 1) → ℂ)) (hU : IsOpen U) (hxU : x ∈ U)
    (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ)
    (hf : ∀ j, AnalyticOnNhd ℂ (f j) U)
    (hA : ∀ z ∈ U, (z ∈ A ↔ ∀ j, f j z = 0))
    (hdim : ∀ P ∈ (adim2_ideal (n + 1) (adim2_germ (n + 1) A x)).minimalPrimes,
      (1 : WithBot ℕ∞) ≤ ringKrullDim (AnalyticGerm (n + 1) ⧸ P)) :
    ∃ F : Finset (Ideal (AnalyticGerm (n + 1))),
      (F : Set (Ideal (AnalyticGerm (n + 1)))) =
        (adim2_ideal (n + 1) (adim2_germ (n + 1) A x)).minimalPrimes ∧
      adim2_germ (n + 1) A x = F.sup (adim2_zeroSet (n + 1)) ∧
      ∀ P ∈ F, adim2_zeroSet (n + 1) P ≤ adim2_germ (n + 1) A x ∧
        ∃ (d : ℕ) (π : (Fin (n + 1) → ℂ) →L[ℂ] (Fin d → ℂ))
          (θ : AnalyticGerm d →+* (AnalyticGerm (n + 1) ⧸ P)),
          1 ≤ d ∧ d ≤ n + 1 ∧ θ.Finite ∧ Function.Injective θ ∧
          (∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
            AnalyticAt ℂ h 0 → Germ.ofFun h = a.val → ∀ b : AnalyticGerm (n + 1),
            Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b) ∧
          ringKrullDim (AnalyticGerm (n + 1) ⧸ P) = (d : WithBot ℕ∞) := by
  classical
  obtain ⟨s, hs⟩ :=
    adim7_local_equations_of_representatives (n + 1) m A x U hU hxU f hf hA
  obtain ⟨F, hF, hcover⟩ := adim3_minimal_prime_cover (n + 1) s
  refine ⟨F, ?_, ?_, ?_⟩
  · rw [hs]
    exact hF
  · rw [hs]
    exact hcover
  · intro P hPF
    have hPmin : P ∈
        (adim2_ideal (n + 1) (adim2_germ (n + 1) A x)).minimalPrimes := by
      rw [hs, ← hF]
      exact hPF
    constructor
    · rw [hs, hcover]
      exact Finset.le_sup hPF
    · obtain ⟨d, π, θ, hdle, hfinite, hinj, hcomp, hparam⟩ :=
        adim5_finite_parameters (n + 1) P hPmin.isPrime
      have hquot : ringKrullDim (AnalyticGerm (n + 1) ⧸ P) =
          (d : WithBot ℕ∞) := by
        rw [← adim6_parameter_dimension d]
        exact hparam.symm
      have hdpos : 1 ≤ d := by
        have hdpos' : (1 : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by
          rw [← hquot]
          exact hdim P hPmin
        exact_mod_cast hdpos'
      exact ⟨d, π, θ, hdpos, hdle, hfinite, hinj, hcomp, hquot⟩

end HodgeLean.Foundations
