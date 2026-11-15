import Mathlib

/-! # Galois descent from `ℂ` to `ℚ` (Track G2, helpers for the Lie bridge)

* `g2l_exists_rat_of_fixed`: a complex number fixed by every field automorphism of `ℂ` is
  rational. An irrational `z` has a conjugate `z' ≠ z` with the same rational relations (another
  root of its minimal polynomial, or `z + 1` when `z` is transcendental), and the isomorphism
  `ℚ[z] ≅ ℚ[z']` extends to `ℂ` by the classification of uncountable algebraically closed fields
  over a countable base (equal transcendence bases).
* `g2l_linearIndependent_galois`, `g2l_span_galois_eq_top`: Artin's lemma for `Aut(ℂ)`.
* `g2l_matrix_descent`, `g2l_mvPolynomial_descent`: a `ℂ`-subspace of matrices or of
  polynomials that is stable under `Aut(ℂ)` acting on entries or coefficients is spanned by its
  rational elements.

Sources: Borel, *Linear Algebraic Groups*, 2nd ed., AG.14.1–14.4 (the Galois criterion);
Bourbaki, *Algèbre*, ch. V, §10 (Artin's lemma) and ch. V, §14 (extension of isomorphisms of
algebraically closed fields).
-/

noncomputable section

namespace HodgeLean.Foundations

open Cardinal

/-- A copy of `ℂ`, used to put a second algebra structure on it.
Source: a type synonym; Bourbaki, *Algèbre*, ch. V, §14 (two embeddings of a subfield). -/
def g2l_CC : Type := ℂ

example : g2l_CC = ℂ := rfl

instance : Field g2l_CC := inferInstanceAs (Field ℂ)
instance : IsAlgClosed g2l_CC := inferInstanceAs (IsAlgClosed ℂ)

/-- Two embeddings of a countable domain into `ℂ` differ by an automorphism of `ℂ`. -/
theorem g2l_exists_ringEquiv_comp {R : Type} [CommRing R] [IsDomain R] (hR : #R ≤ ℵ₀)
    (ι₁ ι₂ : R →+* ℂ) (h₁ : Function.Injective ι₁) (h₂ : Function.Injective ι₂) :
    ∃ σ : ℂ ≃+* ℂ, ∀ r, σ (ι₁ r) = ι₂ r := by
  let A₁ : Algebra R ℂ := ι₁.toAlgebra
  let A₂ : Algebra R g2l_CC := (ι₂ : R →+* ℂ).toAlgebra
  have : FaithfulSMul R ℂ := (faithfulSMul_iff_algebraMap_injective R ℂ).mpr h₁
  have : FaithfulSMul R g2l_CC := (faithfulSMul_iff_algebraMap_injective R g2l_CC).mpr h₂
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis R ℂ
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis R g2l_CC
  have hC : ℵ₀ < #ℂ := by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum
  have hC' : ℵ₀ < #g2l_CC := hC
  have e1 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ hs hR hC
  have e2 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht hR hC'
  have hst : #s = #t := by
    rw [← e1, ← e2]
    rfl
  obtain ⟨e⟩ := Cardinal.eq.mp hst
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hs
  let := IsAlgClosed.isAlgClosure_of_transcendence_basis _ ht
  let f : Algebra.adjoin R (Set.range ((↑) : s → ℂ)) ≃ₐ[R]
      Algebra.adjoin R (Set.range ((↑) : t → g2l_CC)) :=
    hs.1.aevalEquiv.symm.trans ((MvPolynomial.renameEquiv R e).trans ht.1.aevalEquiv)
  refine ⟨IsAlgClosure.equivOfEquiv ℂ g2l_CC f.toRingEquiv, fun r => ?_⟩
  have h1 : ι₁ r = algebraMap (Algebra.adjoin R (Set.range ((↑) : s → ℂ))) ℂ
      (algebraMap R _ r) := rfl
  have h2 := IsAlgClosure.equivOfEquiv_algebraMap ℂ g2l_CC f.toRingEquiv (algebraMap R _ r)
  rw [h1]
  refine h2.trans ?_
  rw [AlgEquiv.coe_toRingEquiv, AlgEquiv.commutes]
  rfl

/-- An irrational complex number has a different conjugate with the same rational relations. -/
theorem g2l_exists_conj_ne (z : ℂ) (hz : ∀ q : ℚ, (q : ℂ) ≠ z) :
    ∃ z' : ℂ, z' ≠ z ∧ ∀ f : Polynomial ℚ, Polynomial.aeval z' f = 0 ↔ Polynomial.aeval z f = 0 := by
  by_cases halg : IsAlgebraic ℚ z
  · have hint : IsIntegral ℚ z := halg.isIntegral
    set m := minpoly ℚ z with hm
    have hirr : Irreducible m := minpoly.irreducible hint
    have hsep : m.Separable := hirr.separable
    have hspl : (m.map (algebraMap ℚ ℂ)).Splits := IsAlgClosed.splits _
    have hdeg : 2 ≤ m.natDegree := by
      by_contra hlt
      have h0 : 0 < m.natDegree := minpoly.natDegree_pos hint
      have h1 : m.natDegree = 1 := by omega
      obtain ⟨q, hq⟩ := minpoly.natDegree_eq_one_iff.mp h1
      exact hz q hq
    have hcard := Polynomial.card_rootSet_eq_natDegree hsep hspl (K := ℂ)
    have hz_mem : z ∈ m.rootSet ℂ := by
      rw [Polynomial.mem_rootSet]
      exact ⟨minpoly.ne_zero hint, minpoly.aeval ℚ z⟩
    obtain ⟨⟨z', hz'⟩, hne⟩ : ∃ w : m.rootSet ℂ, w ≠ ⟨z, hz_mem⟩ := by
      by_contra hcon
      push Not at hcon
      have : Fintype.card (m.rootSet ℂ) ≤ 1 :=
        Fintype.card_le_one_iff.mpr fun a b => (hcon a).trans (hcon b).symm
      omega
    have hne' : z' ≠ z := fun h => hne (Subtype.ext h)
    rw [Polynomial.mem_rootSet] at hz'
    have hint' : IsIntegral ℚ z' := ⟨m, minpoly.monic hint, by
      rw [← Polynomial.aeval_def]; exact hz'.2⟩
    have hm' : minpoly ℚ z' = m :=
      (minpoly.eq_of_irreducible_of_monic hirr hz'.2 (minpoly.monic hint)).symm
    refine ⟨z', hne', fun f => ?_⟩
    rw [← minpoly.dvd_iff, ← minpoly.dvd_iff, hm']
  · have htr : Transcendental ℚ z := halg
    refine ⟨z + 1, by simp, fun f => ?_⟩
    have key : Polynomial.aeval (z + 1) f = Polynomial.aeval z (f.comp (Polynomial.X + 1)) := by
      rw [Polynomial.aeval_comp]
      simp
    rw [key]
    constructor
    · intro h
      have h0 : f.comp (Polynomial.X + 1) = 0 := by
        by_contra hne
        exact htr ⟨_, hne, h⟩
      have : f = (f.comp (Polynomial.X + 1)).comp (Polynomial.X - 1) := by
        rw [Polynomial.comp_assoc]
        simp
      rw [this, h0, Polynomial.zero_comp, map_zero]
    · intro h
      have h0 : f = 0 := by
        by_contra hne
        exact htr ⟨_, hne, h⟩
      rw [h0, Polynomial.zero_comp, map_zero]

/-- **The fixed field of `Aut(ℂ)` is `ℚ`.** -/
theorem g2l_exists_rat_of_fixed (z : ℂ) (hz : ∀ σ : ℂ ≃+* ℂ, σ z = z) : ∃ q : ℚ, (q : ℂ) = z := by
  by_contra hcon
  push Not at hcon
  obtain ⟨z', hne, hiff⟩ := g2l_exists_conj_ne z hcon
  let φ : Polynomial ℚ →+* ℂ := (Polynomial.aeval z).toRingHom
  let φ' : Polynomial ℚ →+* ℂ := (Polynomial.aeval z').toRingHom
  have hker : RingHom.ker φ' = RingHom.ker φ := by
    ext f
    simp only [RingHom.mem_ker, φ, φ', AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    exact hiff f
  let ι₁ : Polynomial ℚ ⧸ RingHom.ker φ →+* ℂ := RingHom.kerLift φ
  let ι₂ : Polynomial ℚ ⧸ RingHom.ker φ →+* ℂ :=
    (RingHom.kerLift φ').comp (Ideal.quotEquivOfEq hker.symm).toRingHom
  have hι₁ : Function.Injective ι₁ := RingHom.kerLift_injective φ
  have hι₂ : Function.Injective ι₂ :=
    (RingHom.kerLift_injective φ').comp (Ideal.quotEquivOfEq hker.symm).injective
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hR : #(Polynomial ℚ ⧸ RingHom.ker φ) ≤ ℵ₀ := by
    refine (Cardinal.mk_le_of_surjective Ideal.Quotient.mk_surjective).trans ?_
    refine Polynomial.cardinalMk_le_max.trans ?_
    simp
  obtain ⟨σ, hσ⟩ := g2l_exists_ringEquiv_comp hR ι₁ ι₂ hι₁ hι₂
  have h1 := hσ (Ideal.Quotient.mk _ Polynomial.X)
  have e1 : ι₁ (Ideal.Quotient.mk _ Polynomial.X) = z := by
    simp only [ι₁, RingHom.kerLift_mk]
    simp only [φ]
    simp
  have e2 : ι₂ (Ideal.Quotient.mk _ Polynomial.X) = z' := by
    simp only [ι₂, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      Ideal.quotEquivOfEq_mk, RingHom.kerLift_mk]
    simp [φ']
  rw [e1, e2, hz σ] at h1
  exact hne h1.symm

/-- Artin's lemma for `Aut(ℂ)`: `ℚ`-independent complex numbers give `ℂ`-independent functions
`σ ↦ σ (a k)` on `Aut(ℂ)`. -/
theorem g2l_linearIndependent_galois {K : Type*} [Fintype K] (a : K → ℂ)
    (ha : LinearIndependent ℚ a) :
    LinearIndependent ℂ (fun k (σ : RingAut ℂ) => σ (a k)) := by
  classical
  set F := FixedPoints.subfield (RingAut ℂ) ℂ
  have hF : LinearIndependent F a := by
    refine Fintype.linearIndependent_iff.mpr fun g hg i => ?_
    have hq : ∀ k, ∃ q : ℚ, (q : ℂ) = (g k : ℂ) := fun k =>
      g2l_exists_rat_of_fixed _ fun σ => (g k).2 σ
    choose q hq using hq
    have h0 : ∑ k, q k • a k = 0 := by
      have := congrArg (fun x : ℂ => x) hg
      simp only [Subfield.smul_def, smul_eq_mul] at this
      rw [← this]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Rat.smul_def, hq k]
    have := Fintype.linearIndependent_iff.mp ha q h0 i
    apply Subtype.ext
    rw [← hq i, this]
    simp
  have hinj : Function.Injective a := ha.injective
  have hs : LinearIndepOn F id ((Finset.univ.image a : Finset ℂ) : Set ℂ) := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact (linearIndepOn_id_range_iff hinj).mpr hF
  have h := FixedPoints.linearIndependent_smul_of_linearIndependent (RingAut ℂ) ℂ hs
  have h2 := h.comp (fun k => (⟨a k, by simp⟩ : ((Finset.univ.image a : Finset ℂ) : Set ℂ)))
    (fun k k' hk => hinj (congrArg Subtype.val hk))
  convert h2 using 1
  funext k σ
  rfl

/-- The vectors `(σ (a k))_k`, `σ ∈ Aut(ℂ)`, span `ℂ^K` when the `a k` are `ℚ`-independent. -/
theorem g2l_span_galois_eq_top {K : Type*} [Fintype K] (a : K → ℂ)
    (ha : LinearIndependent ℚ a) :
    Submodule.span ℂ (Set.range fun σ : RingAut ℂ => fun k => σ (a k)) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨ℓ, hℓ, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  have hval : ∀ v : K → ℂ, ℓ v = ∑ k, v k * ℓ (Pi.single k 1) := by
    intro v
    conv_lhs => rw [show v = ∑ k, v k • Pi.single k 1 by
      ext j; simp [Finset.sum_apply, Pi.single_apply]]
    simp [map_sum]
  have hrel : ∑ k, ℓ (Pi.single k 1) • (fun σ : RingAut ℂ => σ (a k)) = 0 := by
    funext σ
    have hm : ℓ (fun k => σ (a k)) = 0 := hle (Submodule.subset_span ⟨σ, rfl⟩)
    rw [hval] at hm
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← hm]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hz := Fintype.linearIndependent_iff.mp (g2l_linearIndependent_galois a ha) _ hrel
  apply hℓ
  refine LinearMap.ext fun v => ?_
  rw [hval]
  simp [hz]

/-- **Galois descent, the core step.** If `v = Σ a_k u_k` with `ℚ`-independent `a_k` and every
conjugate `Σ σ(a_k) u_k` lies in a `ℂ`-submodule `W`, then every `u_k` lies in `W`. -/
theorem g2l_mem_of_galois {M : Type*} [AddCommGroup M] [Module ℂ M] (W : Submodule ℂ M)
    {K : Type*} [Fintype K] (a : K → ℂ) (ha : LinearIndependent ℚ a) (u : K → M)
    (hW : ∀ σ : RingAut ℂ, ∑ k, σ (a k) • u k ∈ W) (k : K) : u k ∈ W := by
  classical
  let L : (K → ℂ) →ₗ[ℂ] M := Fintype.linearCombination ℂ u
  have hspan : Submodule.span ℂ (Set.range fun σ : RingAut ℂ => fun k => σ (a k)) ≤
      W.comap L := by
    rw [Submodule.span_le]
    rintro _ ⟨σ, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, L, Fintype.linearCombination_apply]
    exact hW σ
  rw [g2l_span_galois_eq_top a ha] at hspan
  have := hspan (Submodule.mem_top (x := Pi.single k 1))
  simpa [L, Fintype.linearCombination_apply, Pi.single_apply] using this

/-- A finite family of complex numbers is a family of rational combinations of finitely many
`ℚ`-independent complex numbers. -/
theorem g2l_exists_rat_decomp {ι : Type*} [Finite ι] (v : ι → ℂ) :
    ∃ (K : Type) (_ : Fintype K) (a : K → ℂ) (q : ι → K → ℚ), LinearIndependent ℚ a ∧
      ∀ i, v i = ∑ k, (q i k : ℂ) * a k := by
  set W := Submodule.span ℚ (Set.range v)
  have : FiniteDimensional ℚ W := FiniteDimensional.span_of_finite ℚ (Set.finite_range v)
  let b := Module.finBasis ℚ W
  refine ⟨Fin (Module.finrank ℚ W), inferInstance, fun k => (b k : ℂ),
    fun i k => b.repr ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩ k,
    b.linearIndependent.map' W.subtype (Submodule.ker_subtype W), fun i => ?_⟩
  have h := congrArg Subtype.val (b.sum_repr ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩)
  have h' : v i = ((∑ k, b.repr ⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩ k • b k : W) : ℂ) :=
    h.symm
  rw [h', Submodule.coe_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Submodule.coe_smul, Rat.smul_def]

/-- **Galois descent for subspaces of matrices.** A `ℂ`-subspace of `M_n(ℂ)` stable under every
field automorphism of `ℂ` (acting on entries) is spanned by its rational matrices. -/
theorem g2l_matrix_descent {n : ℕ} (W : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ))
    (hW : ∀ σ : RingAut ℂ, ∀ Y ∈ W, Y.map σ ∈ W) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : Y ∈ W) :
    Y ∈ Submodule.span ℂ
      {Z | Z ∈ W ∧ ∃ R : Matrix (Fin n) (Fin n) ℚ, R.map (algebraMap ℚ ℂ) = Z} := by
  obtain ⟨K, _, a, q, ha, hq⟩ := g2l_exists_rat_decomp (fun ij : Fin n × Fin n => Y ij.1 ij.2)
  let R : K → Matrix (Fin n) (Fin n) ℚ := fun k => Matrix.of fun i j => q (i, j) k
  have hYsum : ∀ σ : RingAut ℂ, Y.map σ = ∑ k, σ (a k) • (R k).map (algebraMap ℚ ℂ) := by
    intro σ
    ext i j
    have := hq (i, j)
    simp only at this
    simp only [Matrix.map_apply, this, map_sum, map_mul, map_ratCast, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, R, Matrix.of_apply, eq_ratCast]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hmem : ∀ k, (R k).map (algebraMap ℚ ℂ) ∈ W :=
    g2l_mem_of_galois W a ha _ fun σ => (hYsum σ) ▸ hW σ Y hY
  have hY' : Y = ∑ k, a k • (R k).map (algebraMap ℚ ℂ) := by
    have := hYsum (RingEquiv.refl ℂ)
    rwa [show Y.map (RingEquiv.refl ℂ) = Y by ext; rfl] at this
  rw [hY']
  exact Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨hmem k, R k, rfl⟩)

/-- **Galois descent for subspaces of polynomials.** A `ℂ`-subspace of `ℂ[x]` stable under every
field automorphism of `ℂ` (acting on coefficients) is spanned by its rational polynomials. -/
theorem g2l_mvPolynomial_descent {ι : Type*} (W : Submodule ℂ (MvPolynomial ι ℂ))
    (hW : ∀ σ : RingAut ℂ, ∀ f ∈ W, MvPolynomial.map (σ : ℂ →+* ℂ) f ∈ W)
    {f : MvPolynomial ι ℂ} (hf : f ∈ W) :
    f ∈ Submodule.span ℂ
      {g | g ∈ W ∧ ∃ p : MvPolynomial ι ℚ, MvPolynomial.map (algebraMap ℚ ℂ) p = g} := by
  classical
  obtain ⟨K, _, a, q, ha, hq⟩ := g2l_exists_rat_decomp (fun m : f.support => f.coeff m)
  let p : K → MvPolynomial ι ℚ := fun k =>
    ∑ m ∈ f.support.attach, MvPolynomial.monomial (m : ι →₀ ℕ) (q m k)
  have hsum : ∀ σ : RingAut ℂ, MvPolynomial.map (σ : ℂ →+* ℂ) f =
      ∑ k, σ (a k) • MvPolynomial.map (algebraMap ℚ ℂ) (p k) := by
    intro σ
    conv_lhs => rw [f.as_sum, ← Finset.sum_attach]
    simp only [p, map_sum, MvPolynomial.map_monomial, Finset.smul_sum, MvPolynomial.smul_monomial]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← map_sum]
    congr 1
    rw [hq m, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, map_ratCast, eq_ratCast, smul_eq_mul, mul_comm]
    rfl
  have hmem : ∀ k, MvPolynomial.map (algebraMap ℚ ℂ) (p k) ∈ W :=
    g2l_mem_of_galois W a ha _ fun σ => (hsum σ) ▸ hW σ f hf
  have hf' : f = ∑ k, a k • MvPolynomial.map (algebraMap ℚ ℂ) (p k) := by
    have := hsum (RingEquiv.refl ℂ)
    rwa [show MvPolynomial.map ((RingEquiv.refl ℂ : RingAut ℂ) : ℂ →+* ℂ) f = f by
      rw [show ((RingEquiv.refl ℂ : RingAut ℂ) : ℂ →+* ℂ) = RingHom.id ℂ from rfl,
        MvPolynomial.map_id]] at this
  rw [hf']
  exact Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨hmem k, p k, rfl⟩)

end HodgeLean.Foundations
