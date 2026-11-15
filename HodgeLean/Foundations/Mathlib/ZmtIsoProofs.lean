module

public import HodgeLean.Foundations.Mathlib.ZmtIsoDefs

/-! # Proof obligations for finite birational isomorphism specifications -/

@[expose] public noncomputable section

open CategoryTheory TensorProduct

namespace AlgebraicGeometry

universe u

/-- An integral ring map from a normal domain `A` into a ring `B` that embeds into the fraction
field of `A` compatibly with `A` is bijective. -/
private lemma zmtiso_bijective_of_isIntegral_of_fractionRing {A B K : Type*} [CommRing A]
    [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [Field K] [Algebra A K]
    [IsFractionRing A K] (φ : A →+* B) (ψ : B →+* K) (hψ : Function.Injective ψ)
    (hcomp : ψ.comp φ = algebraMap A K) (hφ : φ.IsIntegral) : Function.Bijective φ := by
  refine ⟨fun a b h ↦ IsFractionRing.injective A K ?_, fun b ↦ ?_⟩
  · rw [← hcomp, RingHom.comp_apply, RingHom.comp_apply, h]
  · let := φ.toAlgebra
    let ψ' : B →ₐ[A] K := { ψ with commutes' := fun a ↦ congr($hcomp a) }
    obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp
      ((show _root_.IsIntegral A b from hφ b).map ψ')
    refine ⟨a, hψ ?_⟩
    rw [← RingHom.comp_apply, hcomp, ha]
    rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- On a normal integral scheme, the sections over a nonempty affine open form a normal domain. -/
private lemma zmtiso_isIntegrallyClosed_of_isAffineOpen {X : Scheme.{u}} [IsIntegral X]
    (hX : zmtiso_IsNormal X) {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    IsIntegrallyClosed Γ(X, U) := by
  refine IsIntegrallyClosed.of_localization_maximal fun P _ hP ↦ ?_
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf
    ⟨hU.fromSpec ⟨P, hP.isPrime⟩, (hU.isoSpec.inv _).2⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec ⟨P, hP.isPrime⟩)) P :=
    hU.isLocalization_stalk' ⟨P, hP.isPrime⟩ (hU.isoSpec.inv _).2
  exact (hX _).2.of_equiv
    (IsLocalization.algEquiv P.primeCompl (X.presheaf.stalk (hU.fromSpec ⟨P, hP.isPrime⟩))
      (Localization.AtPrime P)).toRingEquiv

theorem zmtiso_isIso_of_finite_birational_normal_aux
    {Z X : Scheme.{u}} (f : Z ⟶ X) [IsIntegral Z] [IsIntegral X] [IsFinite f]
    (hX : zmtiso_IsNormal X) (hf : zmtiso_IsBirational f) : IsIso f := by
  obtain ⟨hgen, hstalk⟩ := hf
  rw [← MorphismProperty.isomorphisms.iff]
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (fun U : {U : X.affineOpens // (U : Set X).Nonempty} ↦ (U.1 : X.Opens)) ?_ fun U ↦ ?_
  · rw [eq_top_iff]
    rintro x -
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) (⊤ : X.Opens).2
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, ⟨x, hxV⟩⟩, hxV⟩
  obtain ⟨⟨U, hU⟩, hne⟩ := U
  rw [MorphismProperty.isomorphisms.iff, isIso_morphismRestrict_iff_isIso_app f hU,
    ConcreteCategory.isIso_iff_bijective]
  have : Nonempty U := hne.to_subtype
  have hηX : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using hne)
  have hηZ : genericPoint Z ∈ f ⁻¹ᵁ U := by
    change f (genericPoint Z) ∈ U
    rw [hgen]
    exact hηX
  have : Nonempty (f ⁻¹ᵁ U) := ⟨⟨_, hηZ⟩⟩
  have := zmtiso_isIntegrallyClosed_of_isAffineOpen hX hU
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  have hsp : genericPoint X ⤳ f (genericPoint Z) := (genericPoint_spec X).specializes trivial
  let ψ : Γ(Z, f ⁻¹ᵁ U) ⟶ X.functionField :=
    Z.presheaf.germ (f ⁻¹ᵁ U) _ hηZ ≫ inv (f.stalkMap _) ≫ X.presheaf.stalkSpecializes hsp
  have hψ : Function.Injective ψ.hom := by
    refine (IsFractionRing.injective (X.presheaf.stalk (f (genericPoint Z)))
      X.functionField).comp ((ConcreteCategory.bijective_of_isIso (inv (f.stalkMap _))).1.comp
        (germ_injective_of_isIntegral Z _ hηZ))
  have hcomp : ψ.hom.comp (f.app U).hom = algebraMap Γ(X, U) X.functionField := by
    change (f.app U ≫ ψ).hom = (X.presheaf.germ U (genericPoint X) hηX).hom
    congr 1
    simp only [ψ, ← Category.assoc]
    rw [← Scheme.Hom.germ_stalkMap f U (genericPoint Z) hηZ]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    exact TopCat.Presheaf.germ_stalkSpecializes _ _ _
  exact zmtiso_bijective_of_isIntegral_of_fractionRing (f.app U).hom ψ.hom hψ hcomp
    (f.isIntegral_app U hU)

section ZmtIsoAlgebra

open _root_.Polynomial

/-- A nonzero element of a finitely generated domain over an algebraically closed field `k` is
nonzero at some `k`-point. -/
private lemma zmtiso_exists_algHom_ne_zero {k A : Type*} [Field k] [IsAlgClosed k] [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] {a : A} (ha : a ≠ 0) :
    ∃ χ : A →ₐ[k] k, χ a ≠ 0 := by
  have : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k)
  have hJ : (⊥ : Ideal A).jacobson = ⊥ := IsJacobsonRing.out ‹_› Ideal.isRadical_bot
  obtain ⟨m, hm, ham⟩ : ∃ m : Ideal A, m.IsMaximal ∧ a ∉ m := by
    by_contra! h
    apply ha
    rw [← Ideal.mem_bot, ← hJ, Ideal.jacobson, Ideal.mem_sInf]
    exact fun J hJ ↦ h J hJ.2
  let := Ideal.Quotient.field m
  have : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  let e := AlgEquiv.ofBijective (Algebra.ofId k (A ⧸ m))
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k m), ?_⟩
  simpa [Ideal.Quotient.eq_zero_iff_mem] using ham

/-- Finitely many polynomials over the fraction field of `A` acquire coefficients in `A` after
multiplication by one nonzero constant. -/
private lemma zmtiso_exists_lift {A K : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] (s : Finset K[X]) :
    ∃ D : A, D ≠ 0 ∧ ∀ q ∈ s, ∃ q' : A[X], q'.map (algebraMap A K) = C (algebraMap A K D) * q := by
  classical
  obtain ⟨⟨D, hD⟩, h⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors A)
    (s.biUnion fun q ↦ q.support.image q.coeff)
  refine ⟨D, nonZeroDivisors.ne_zero hD, fun q hq ↦ ?_⟩
  rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
  intro n
  rw [coeff_C_mul]
  by_cases hn : q.coeff n = 0
  · exact ⟨0, by simp [hn]⟩
  · obtain ⟨a, ha⟩ := h (q.coeff n) (Finset.mem_biUnion.mpr
      ⟨q, hq, Finset.mem_image.mpr ⟨n, mem_support_iff.mpr hn, rfl⟩⟩)
    exact ⟨a, by rw [ha, Algebra.smul_def]⟩

/-- If `b` is not a quotient of elements of `A`, then finitely many polynomial relations of `b`
and one polynomial non-relation of `b` have two distinct common solutions over one `k`-point of
`A`; in the algebraic case this uses separability in characteristic zero. -/
private lemma zmtiso_exists_two_points {k A B : Type*} [Field k] [IsAlgClosed k] [CharZero k]
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [CommRing B] [IsDomain B] [Algebra A B] (hAB : Function.Injective (algebraMap A B))
    (b : B) (hb : ∀ a s : A, algebraMap A B s ≠ 0 → algebraMap A B a ≠ b * algebraMap A B s)
    {n : ℕ} (g : Fin n → A[X]) (hg : ∀ i, aeval b (g i) = 0) (f : A[X]) (hf : aeval b f ≠ 0) :
    ∃ (χ : A →ₐ[k] k) (c₁ c₂ : k), c₁ ≠ c₂ ∧ ∀ c ∈ ({c₁, c₂} : Set k),
      (∀ i, ((g i).map (χ : A →+* k)).eval c = 0) ∧ (f.map (χ : A →+* k)).eval c ≠ 0 := by
  classical
  let K := FractionRing A
  let L := FractionRing B
  have : FaithfulSMul A L := (faithfulSMul_iff_algebraMap_injective A L).mpr <| by
    rw [IsScalarTower.algebraMap_eq A B L]
    exact (IsFractionRing.injective B L).comp hAB
  let : Algebra K L := FractionRing.liftAlgebra A L
  have : IsScalarTower A K L := FractionRing.isScalarTower_liftAlgebra A L
  have : CharZero A := (RingHom.charZero_iff (algebraMap k A).injective).mp inferInstance
  have : CharZero K := (RingHom.charZero_iff (IsFractionRing.injective A K)).mp inferInstance
  let θ := algebraMap B L b
  have hmap (p : A[X]) : aeval θ (p.map (algebraMap A K)) = algebraMap B L (aeval b p) := by
    rw [aeval_map_algebraMap, aeval_algebraMap_apply]
  have hinjK := map_injective (algebraMap A K) (IsFractionRing.injective A K)
  have hfL : algebraMap B L (aeval b f) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective B L)).mpr hf
  by_cases hθ : _root_.IsIntegral K θ
  · let P := minpoly K θ
    have hirr : Irreducible P := minpoly.irreducible hθ
    have hP1 : P.natDegree ≠ 1 := by
      rw [Ne, minpoly.natDegree_eq_one_iff]
      rintro ⟨x, hx⟩
      obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := A) x
      have hs0 : algebraMap A B s ≠ 0 :=
        (map_ne_zero_iff _ hAB).mpr (nonZeroDivisors.ne_zero hs)
      have hsL : algebraMap A L s ≠ 0 := by
        rw [IsScalarTower.algebraMap_apply A B L]
        exact (map_ne_zero_iff _ (IsFractionRing.injective B L)).mpr hs0
      apply hb a s hs0
      apply IsFractionRing.injective B L
      simp only [map_mul, θ] at hx ⊢
      rw [← hx, map_div₀, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, div_mul_cancel₀ _ hsL]
    obtain ⟨U, V, hUV⟩ := hirr.separable
    obtain ⟨X₁, Y₁, hXY⟩ : IsCoprime P (f.map (algebraMap A K)) := by
      rw [hirr.coprime_iff_not_dvd, minpoly.dvd_iff, hmap]
      exact hfL
    have hQ (i : Fin n) : P ∣ (g i).map (algebraMap A K) := by
      rw [minpoly.dvd_iff, hmap, hg, map_zero]
    choose Q hQ using hQ
    obtain ⟨D, hD, hlift⟩ := zmtiso_exists_lift (A := A) (K := K)
      ({P, U, V, X₁, Y₁} ∪ Finset.univ.image Q)
    obtain ⟨P₀, hP₀⟩ := hlift P (by simp)
    obtain ⟨U₀, hU₀⟩ := hlift U (by simp)
    obtain ⟨V₀, hV₀⟩ := hlift V (by simp)
    obtain ⟨X₀, hX₀⟩ := hlift X₁ (by simp)
    obtain ⟨Y₀, hY₀⟩ := hlift Y₁ (by simp)
    choose Q₀ hQ₀ using fun i ↦ hlift (Q i) (by simp)
    let d := algebraMap A K D
    have hd : d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hD
    have e₁ : U₀ * P₀ + V₀ * derivative P₀ = C D ^ 2 := hinjK <| by
      simp only [Polynomial.map_add, Polynomial.map_mul, ← derivative_map, hP₀, hU₀, hV₀,
        Polynomial.map_pow, Polynomial.map_C, derivative_C_mul]
      linear_combination (C d) ^ 2 * hUV
    have e₂ : X₀ * P₀ + C D * Y₀ * f = C D ^ 2 := hinjK <| by
      simp only [Polynomial.map_add, Polynomial.map_mul, hP₀, hX₀, hY₀,
        Polynomial.map_pow, Polynomial.map_C]
      linear_combination (C d) ^ 2 * hXY
    have e₃ (i : Fin n) : P₀ * Q₀ i = C D ^ 2 * g i := hinjK <| by
      simp only [Polynomial.map_mul, hP₀, hQ₀, Polynomial.map_pow, Polynomial.map_C]
      linear_combination (-(C d) ^ 2) * hQ i
    have hlc : P₀.leadingCoeff = D := by
      apply IsFractionRing.injective A K
      rw [← leadingCoeff_map_of_injective (IsFractionRing.injective A K), hP₀, leadingCoeff_mul,
        leadingCoeff_C, (minpoly.monic hθ).leadingCoeff, mul_one]
    have hdeg : P₀.natDegree = P.natDegree := by
      rw [← natDegree_map_eq_of_injective (IsFractionRing.injective A K), hP₀, natDegree_C_mul hd]
    obtain ⟨χ, hχ⟩ := zmtiso_exists_algHom_ne_zero (k := k) hD
    let p := P₀.map (χ : A →+* k)
    have hpdeg : p.natDegree = P.natDegree := by
      rw [natDegree_map_of_leadingCoeff_ne_zero _ (by rw [hlc]; exact hχ), hdeg]
    have hp2 : 1 < p.natDegree := by
      have : 0 < P.natDegree := minpoly.natDegree_pos hθ
      omega
    have hp0 : p ≠ 0 := by
      rintro h
      rw [h, natDegree_zero] at hp2
      omega
    have hsep : p.Separable := by
      have h := congr(($e₁).map (χ : A →+* k))
      simp only [Polynomial.map_add, Polynomial.map_mul, ← derivative_map, Polynomial.map_pow,
        Polynomial.map_C] at h
      have hu : (χ : A →+* k) D ^ 2 ≠ 0 := pow_ne_zero _ hχ
      refine ⟨C ((χ : A →+* k) D ^ 2)⁻¹ * U₀.map (χ : A →+* k),
        C ((χ : A →+* k) D ^ 2)⁻¹ * V₀.map (χ : A →+* k), ?_⟩
      rw [mul_assoc, mul_assoc, ← mul_add, h, ← C_pow, ← C_mul, inv_mul_cancel₀ hu, C_1]
    have hcard : 1 < p.roots.toFinset.card := by
      rwa [Multiset.toFinset_card_of_nodup (nodup_roots hsep), IsAlgClosed.card_roots_eq_natDegree]
    obtain ⟨c₁, hc₁, c₂, hc₂, hne⟩ := Finset.one_lt_card.mp hcard
    refine ⟨χ, c₁, c₂, hne, fun c hc ↦ ?_⟩
    have hroot : p.eval c = 0 := by
      rcases hc with rfl | rfl
      · exact (mem_roots hp0).mp (Multiset.mem_toFinset.mp hc₁)
      · exact (mem_roots hp0).mp (Multiset.mem_toFinset.mp hc₂)
    have hD2 : (χ : A →+* k) D ^ 2 ≠ 0 := pow_ne_zero _ hχ
    refine ⟨fun i ↦ ?_, fun h ↦ ?_⟩
    · have h := congrArg (fun q ↦ (q.map (χ : A →+* k)).eval c) (e₃ i)
      simp only [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C, eval_mul, eval_pow,
        eval_C] at h
      rw [show eval c (map (χ : A →+* k) P₀) = 0 from hroot, zero_mul] at h
      exact (mul_eq_zero.mp h.symm).resolve_left hD2
    · have h' := congrArg (fun q ↦ (q.map (χ : A →+* k)).eval c) e₂
      simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
        eval_add, eval_mul, eval_pow, eval_C, h, mul_zero, add_zero] at h'
      rw [show eval c (map (χ : A →+* k) P₀) = 0 from hroot, mul_zero] at h'
      exact hD2 h'.symm
  · have hg0 (i : Fin n) : g i = 0 := by
      by_contra h
      apply hθ
      refine IsAlgebraic.isIntegral ⟨(g i).map (algebraMap A K),
        (Polynomial.map_ne_zero_iff (IsFractionRing.injective A K)).mpr h, ?_⟩
      rw [hmap, hg, map_zero]
    have hf0 : f ≠ 0 := by
      rintro rfl
      simp at hf
    obtain ⟨χ, hχ⟩ := zmtiso_exists_algHom_ne_zero (k := k) (leadingCoeff_ne_zero.mpr hf0)
    let p := f.map (χ : A →+* k)
    have hp0 : p ≠ 0 := by
      rw [← leadingCoeff_ne_zero, leadingCoeff_map_of_leadingCoeff_ne_zero (χ : A →+* k) hχ]
      exact hχ
    obtain ⟨c₁, h₁⟩ := Infinite.exists_notMem_finset p.roots.toFinset
    obtain ⟨c₂, h₂⟩ := Infinite.exists_notMem_finset (insert c₁ p.roots.toFinset)
    refine ⟨χ, c₁, c₂, fun h ↦ h₂ (h ▸ Finset.mem_insert_self _ _), fun c hc ↦
      ⟨fun i ↦ by simp [hg0], fun h ↦ ?_⟩⟩
    have hc' : c ∈ p.roots.toFinset := Multiset.mem_toFinset.mpr ((mem_roots hp0).mpr h)
    rcases hc with rfl | rfl
    · exact h₁ hc'
    · exact h₂ (Finset.mem_insert_of_mem hc')

/-- If a finitely generated domain `B` over a finitely generated domain `A` over an algebraically
closed characteristic-zero field has its maximal ideals determined by their contractions to `A`,
then every element of `B` is a quotient of elements of `A`. The proof applies Chevalley's theorem
to `A[X] → B`, `X ↦ b`. -/
private lemma zmtiso_exists_eq_mul_of_maximal_injective {k A B : Type*} [Field k] [IsAlgClosed k]
    [CharZero k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [CommRing B] [IsDomain B] [Algebra A B] [Algebra.FiniteType A B]
    (hAB : Function.Injective (algebraMap A B))
    (hmax : ∀ n₁ n₂ : Ideal B, n₁.IsMaximal → n₂.IsMaximal →
      n₁.comap (algebraMap A B) = n₂.comap (algebraMap A B) → n₁ = n₂)
    (b : B) : ∃ a s : A, algebraMap A B s ≠ 0 ∧ algebraMap A B a = b * algebraMap A B s := by
  by_contra! hb
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  let Ψ : A[X] →+* B := (aeval b).toRingHom
  have hΨC : Ψ.comp C = algebraMap A B := (aeval b).comp_algebraMap
  have hfp : Ψ.FinitePresentation := RingHom.FinitePresentation.of_finiteType.mp
    (RingHom.FiniteType.of_comp_finiteType (f := C) (by
      rw [hΨC]; exact RingHom.finiteType_algebraMap.mpr ‹_›))
  obtain ⟨S, hS⟩ := PrimeSpectrum.exists_constructibleSetData_iff.mpr
    (PrimeSpectrum.isConstructible_range_comap hfp)
  have h₀ : PrimeSpectrum.comap Ψ ⟨⊥, Ideal.isPrime_bot⟩ ∈ S.toSet := hS ▸ Set.mem_range_self _
  obtain ⟨Cd, hCS, hC⟩ := Set.mem_iUnion₂.mp h₀
  simp only [PrimeSpectrum.BasicConstructibleSetData.toSet, Set.mem_sdiff,
    PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, Set.range_subset_iff] at hC
  obtain ⟨hg, hf⟩ := hC
  obtain ⟨χ, c₁, c₂, hne, hcs⟩ := zmtiso_exists_two_points (k := k) hAB b hb Cd.g
    (fun i ↦ by simpa [Ψ] using hg i) Cd.f (by simpa [Ψ] using hf)
  have key (c : k) (hc : c ∈ ({c₁, c₂} : Set k)) : ∃ n : Ideal B, n.IsMaximal ∧
      n.comap (algebraMap A B) = RingHom.ker (χ : A →+* k) ∧
      b - algebraMap A B (algebraMap k A c) ∈ n := by
    obtain ⟨hcg, hcf⟩ := hcs c hc
    let e : A[X] →+* k := (evalRingHom c).comp (mapRingHom (χ : A →+* k))
    have heC : e.comp C = χ := by ext; simp [e]
    have he : Function.Surjective e := fun x ↦ ⟨C (algebraMap k A x), by simp [e]⟩
    have hM := RingHom.ker_isMaximal_of_surjective e he
    have hmem : (⟨RingHom.ker e, hM.isPrime⟩ : PrimeSpectrum A[X]) ∈ S.toSet :=
      Set.mem_iUnion₂.mpr ⟨Cd, hCS, by
        simp only [PrimeSpectrum.BasicConstructibleSetData.toSet, Set.mem_sdiff,
          PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, Set.range_subset_iff]
        exact ⟨fun i ↦ by simpa [e] using hcg i, by simpa [e] using hcf⟩⟩
    rw [hS] at hmem
    obtain ⟨q, hq⟩ := hmem
    obtain ⟨n, hn, hqn⟩ := Ideal.exists_le_maximal q.asIdeal q.isPrime.ne_top
    have hnM : n.comap Ψ = RingHom.ker e := by
      refine (hM.eq_of_le (Ideal.comap_ne_top Ψ hn.ne_top) ?_).symm
      have := congrArg PrimeSpectrum.asIdeal hq
      simp only [PrimeSpectrum.comap_asIdeal] at this
      exact this ▸ Ideal.comap_mono hqn
    refine ⟨n, hn, ?_, ?_⟩
    · rw [← hΨC, ← Ideal.comap_comap, hnM, RingHom.comap_ker, heC]
    · have : X - C (algebraMap k A c) ∈ n.comap Ψ := by
        rw [hnM, RingHom.mem_ker]
        simp [e]
      simpa [Ψ] using this
  obtain ⟨n₁, hn₁, hc₁, hb₁⟩ := key c₁ (by simp)
  obtain ⟨n₂, hn₂, hc₂, hb₂⟩ := key c₂ (by simp)
  obtain rfl := hmax n₁ n₂ hn₁ hn₂ (hc₁.trans hc₂.symm)
  have h := n₁.sub_mem hb₁ hb₂
  rw [sub_sub_sub_cancel_left, ← map_sub, ← map_sub, ← Ideal.mem_comap, hc₁,
    RingHom.mem_ker] at h
  apply hne
  simpa [sub_eq_zero, eq_comm] using h

end ZmtIsoAlgebra

theorem zmtiso_birational_of_injective_char0_aux
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {Z X : Scheme.{u}} (sZ : Z ⟶ Spec (.of k)) (sX : X ⟶ Spec (.of k))
    (f : Z ⟶ X) [IsIntegral Z] [IsIntegral X]
    [LocallyOfFiniteType sZ] [LocallyOfFiniteType sX]
    (hover : f ≫ sX = sZ)
    (hinj : ∀ ⦃z₁ z₂ : Z⦄,
      IsClosed ({z₁} : Set Z) → IsClosed ({z₂} : Set Z) →
      f z₁ = f z₂ → z₁ = z₂)
    (hsurj : ∀ x : X, IsClosed ({x} : Set X) →
      ∃ z : Z, IsClosed ({z} : Set Z) ∧ f z = x)
    (hres : ∀ z : Z, IsClosed ({z} : Set Z) → IsIso (f.residueFieldMap z)) :
    zmtiso_IsBirational f := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  have : JacobsonSpace Z := LocallyOfFiniteType.jacobsonSpace sZ
  have : LocallyOfFiniteType f := by
    have : LocallyOfFiniteType (f ≫ sX) := hover ▸ ‹LocallyOfFiniteType sZ›
    exact locallyOfFiniteType_of_comp f sX
  have hgen : f (genericPoint Z) = genericPoint X := by
    refine ((genericPoint_spec X).eq ?_).symm
    refine Set.eq_univ_of_univ_subset ?_
    rw [← closure_closedPoints]
    refine closure_minimal (fun x hx ↦ ?_) isClosed_closure
    obtain ⟨z, -, rfl⟩ := hsurj x hx
    exact specializes_iff_mem_closure.mp ((genericPoint_specializes z).map f.continuous)
  refine ⟨hgen, ?_⟩
  obtain ⟨_, ⟨V, hV, rfl⟩, hηV, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint X)) (⊤ : X.Opens).2
  have hV : IsAffineOpen V := hV
  have hηZV : genericPoint Z ∈ f ⁻¹ᵁ V := by
    change f (genericPoint Z) ∈ V
    rw [hgen]
    exact hηV
  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, hUV⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    hηZV (f ⁻¹ᵁ V).2
  have hU : IsAffineOpen U := hU
  have : Nonempty V := ⟨⟨_, hηV⟩⟩
  have : Nonempty U := ⟨⟨_, hηU⟩⟩
  let φ := f.appLE V U hUV
  have hsp : f (genericPoint Z) ⤳ genericPoint X := hgen ▸ specializes_rfl
  let ρ := X.presheaf.stalkSpecializes hsp
  have : IsIso ρ := ⟨X.presheaf.stalkSpecializes (genericPoint_specializes _), by simp [ρ], by
    simp [ρ]⟩
  let ψ : X.functionField ⟶ Z.functionField := ρ ≫ f.stalkMap (genericPoint Z)
  have hψ' : X.presheaf.germ V _ hηV ≫ ψ = φ ≫ Z.presheaf.germ U _ hηU := by
    rw [TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]
    simp [φ, Scheme.Hom.appLE]
  have hψ (a : Γ(X, V)) : ψ (X.presheaf.germ V _ hηV a) = Z.presheaf.germ U _ hηU (φ a) :=
    congr($hψ' a)
  have hψinj : Function.Injective ψ := ψ.hom.injective
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    apply germ_injective_of_isIntegral X _ hηV
    apply hψinj
    rw [hψ, ha, map_zero, map_zero, map_zero]
  let ιk : k →+* Γ(X, V) := ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appLE ⊤ V le_top).hom
  let : Algebra k Γ(X, V) := ιk.toAlgebra
  have : Algebra.FiniteType k Γ(X, V) := by
    have h₁ := HasRingHomProperty.appLE @LocallyOfFiniteType sX ‹_› ⟨⊤, isAffineOpen_top _⟩
      ⟨V, hV⟩ le_top
    exact RingHom.FiniteType.comp h₁ (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv).2)
  let : Algebra Γ(X, V) Γ(Z, U) := φ.hom.toAlgebra
  have : Algebra.FiniteType Γ(X, V) Γ(Z, U) :=
    HasRingHomProperty.appLE @LocallyOfFiniteType f ‹_› ⟨V, hV⟩ ⟨U, hU⟩ hUV
  have hpt (p : Spec Γ(Z, U)) : f (hU.fromSpec p) = hV.fromSpec (Spec.map φ p) :=
    congr($(IsAffineOpen.SpecMap_appLE_fromSpec f hV hU hUV) p).symm
  have hcl (p : Spec Γ(Z, U)) (hp : IsClosed ({p} : Set (Spec Γ(Z, U)))) :
      IsClosed ({hU.fromSpec p} : Set Z) := by
    refine isClosed_singleton_of_isLocallyClosed_singleton ?_
    rw [← Set.image_singleton]
    refine hp.isLocallyClosed.image hU.fromSpec.isOpenEmbedding.isInducing ?_
    rw [hU.range_fromSpec]
    exact U.2.isLocallyClosed
  have hmax (n₁ n₂ : Ideal Γ(Z, U)) (h₁ : n₁.IsMaximal) (h₂ : n₂.IsMaximal)
      (h : n₁.comap (algebraMap Γ(X, V) Γ(Z, U)) = n₂.comap (algebraMap Γ(X, V) Γ(Z, U))) :
      n₁ = n₂ := by
    let p₁ : Spec Γ(Z, U) := (⟨n₁, h₁.isPrime⟩ : PrimeSpectrum Γ(Z, U))
    let p₂ : Spec Γ(Z, U) := (⟨n₂, h₂.isPrime⟩ : PrimeSpectrum Γ(Z, U))
    have := hinj (hcl p₁ ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr h₁))
      (hcl p₂ ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr h₂))
      (by rw [hpt, hpt]; exact congrArg hV.fromSpec (PrimeSpectrum.ext h))
    exact congrArg PrimeSpectrum.asIdeal (hU.fromSpec.isOpenEmbedding.injective this)
  have hfrac := zmtiso_exists_eq_mul_of_maximal_injective (k := k) hφinj hmax
  have := functionField_isFractionRing_of_isAffineOpen Z U hU
  have hB (b : Γ(Z, U)) : ∃ x, ψ x = algebraMap Γ(Z, U) Z.functionField b := by
    obtain ⟨a, s, hs, hb⟩ := hfrac b
    refine ⟨X.presheaf.germ V _ hηV a / X.presheaf.germ V _ hηV s, ?_⟩
    have hs' : Z.presheaf.germ U _ hηU (φ s) ≠ 0 := fun h ↦
      hs (germ_injective_of_isIntegral Z _ hηU (h.trans (map_zero _).symm))
    rw [map_div₀, hψ, hψ, div_eq_iff hs']
    change _ = Z.presheaf.germ U _ hηU b * _
    rw [← map_mul]
    exact congrArg _ hb
  have hψsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨b₁, b₂, -, rfl⟩ := IsFractionRing.div_surjective (A := Γ(Z, U)) y
    obtain ⟨x₁, hx₁⟩ := hB b₁
    obtain ⟨x₂, hx₂⟩ := hB b₂
    exact ⟨x₁ / x₂, by rw [map_div₀, hx₁, hx₂]⟩
  have : IsIso (ρ ≫ f.stalkMap (genericPoint Z)) :=
    (ConcreteCategory.isIso_iff_bijective ψ).mpr ⟨hψinj, hψsurj⟩
  exact IsIso.of_isIso_comp_left ρ _

/-- A reduced Artinian ring whose only idempotents are `0` and `1` is a field. -/
private lemma zmtiso_isField_of_isArtinianRing {L : Type*} [CommRing L] [IsArtinianRing L]
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

/-- The local rings of an étale algebra over a normal domain are normal domains. -/
private lemma zmtiso_normal_localization_of_etale {T B : Type*} [CommRing T] [IsDomain T]
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
    e.toMulEquiv.isField (zmtiso_isField_of_isArtinianRing hidem)
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

/-- The local rings of a smooth algebra over a field are normal domains. -/
private lemma zmtiso_normal_localization_of_smooth {k R : Type*} [Field k] [CommRing R]
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
  obtain ⟨_, h₂⟩ := zmtiso_normal_localization_of_etale (T := MvPolynomial (Fin n) k) q
  exact ⟨e.toMulEquiv.isDomain, h₂.of_equiv e.symm⟩

theorem zmtiso_normal_of_smooth_aux
    {k : Type u} [Field k] (X : Scheme.{u}) (sX : X ⟶ Spec (.of k)) [Smooth sX] :
    zmtiso_IsNormal X := by
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) (⊤ : X.Opens).2
  have hsm : (sX.appLE ⊤ U le_top).hom.Smooth :=
    HasRingHomProperty.appLE (P := @Smooth) sX inferInstance ⟨⊤, isAffineOpen_top _⟩
      ⟨U, hU⟩ _
  let φ : k →+* Γ(X, U) :=
    (sX.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom
  have : φ.Smooth := RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective (ConcreteCategory.bijective_of_isIso _)) hsm
  algebraize [φ]
  let P := hU.primeIdealOf ⟨x, hxU⟩
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  obtain ⟨_, h₂⟩ := zmtiso_normal_localization_of_smooth (k := k) P.asIdeal
  let e : X.presheaf.stalk x ≃+* Localization.AtPrime P.asIdeal :=
    (IsLocalization.algEquiv P.asIdeal.primeCompl _ _).toRingEquiv
  exact ⟨e.toMulEquiv.isDomain, h₂.of_equiv e.symm⟩

/-- A morphism of schemes locally of finite type over a field, proper and injective on closed
points, is locally quasi-finite: its fibres over closed points are subsingletons, and the image of
the closed complement of the quasi-finite locus would otherwise contain a closed point. -/
private lemma zmtiso_locallyQuasiFinite_of_injective_closedPoints
    {k : Type u} [Field k] {Z X : Scheme.{u}} (sZ : Z ⟶ Spec (.of k)) (sX : X ⟶ Spec (.of k))
    (f : Z ⟶ X) [IsProper f] [LocallyOfFiniteType sZ] [LocallyOfFiniteType sX]
    (hinj : ∀ ⦃z₁ z₂ : Z⦄,
      IsClosed ({z₁} : Set Z) → IsClosed ({z₂} : Set Z) →
      f z₁ = f z₂ → z₁ = z₂) :
    LocallyQuasiFinite f := by
  have : JacobsonSpace Z := LocallyOfFiniteType.jacobsonSpace sZ
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  have hfib (x : X) (hx : IsClosed ({x} : Set X)) : (f ⁻¹' {x}).Subsingleton := by
    have hS : IsClosed (f ⁻¹' {x}) := hx.preimage f.continuous
    have hT : (f ⁻¹' {x} ∩ closedPoints Z).Subsingleton := fun a ha b hb ↦
      hinj ha.2 hb.2 (ha.1.trans hb.1.symm)
    have hcl := JacobsonSpace.closure_inter_closedPoints_eq_closure hS.isLocallyClosed
    rw [hS.closure_eq] at hcl
    rw [← hcl]
    rcases hT.eq_empty_or_singleton with h | ⟨z, h⟩
    · simp [h]
    · have hz : IsClosed ({z} : Set Z) :=
        (show z ∈ f ⁻¹' {x} ∩ closedPoints Z from h ▸ Set.mem_singleton z).2
      rw [h, hz.closure_eq]
      exact Set.subsingleton_singleton
  have hqf (z : Z) (hz : IsClosed ({f z} : Set X)) : f.QuasiFiniteAt z := by
    have : Finite (f ⁻¹' {f z}) := (hfib _ hz).finite.to_subtype
    have : Finite (f.fiber (f z)) := (f.fiberHomeo (f z)).finite_iff.mpr ‹_›
    exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)
  rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff, eq_top_iff]
  intro z _
  by_contra hz
  have hC : IsClosed (f '' (f.quasiFiniteLocus : Set Z)ᶜ) :=
    f.isClosedMap _ f.quasiFiniteLocus.isOpen.isClosed_compl
  obtain ⟨_, ⟨c, hc, rfl⟩, hcl⟩ :=
    nonempty_inter_closedPoints (Set.Nonempty.image f ⟨z, hz⟩) hC.isLocallyClosed
  exact hc (hqf c hcl)

theorem zmtiso_isIso_of_proper_injective_normal_aux
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {Z X : Scheme.{u}} (sZ : Z ⟶ Spec (.of k)) (sX : X ⟶ Spec (.of k))
    (f : Z ⟶ X) [IsIntegral Z] [IsIntegral X] [IsProper f]
    [LocallyOfFiniteType sZ] [LocallyOfFiniteType sX]
    (hX : zmtiso_IsNormal X) (hover : f ≫ sX = sZ)
    (hinj : ∀ ⦃z₁ z₂ : Z⦄,
      IsClosed ({z₁} : Set Z) → IsClosed ({z₂} : Set Z) →
      f z₁ = f z₂ → z₁ = z₂)
    (hsurj : ∀ x : X, IsClosed ({x} : Set X) →
      ∃ z : Z, IsClosed ({z} : Set Z) ∧ f z = x)
    (hres : ∀ z : Z, IsClosed ({z} : Set Z) → IsIso (f.residueFieldMap z)) : IsIso f := by
  have := zmtiso_locallyQuasiFinite_of_injective_closedPoints sZ sX f hinj
  have := IsFinite.of_isProper_of_locallyQuasiFinite f
  exact zmtiso_isIso_of_finite_birational_normal_aux f hX
    (zmtiso_birational_of_injective_char0_aux sZ sX f hover hinj hsurj hres)

end AlgebraicGeometry
