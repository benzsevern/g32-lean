import HodgeLean.Foundations.HodgeGroupAlgebraicDefs
import HodgeLean.Foundations.MatrixAlgGroupLieIdentityComponent

/-! # Galois descent for `ℚ`-closed sets of `GL_n(ℂ)` (Track G2, helpers)

* `g2h_exists_ringEquiv_ne`: a complex number fixed by every field automorphism of `ℂ` is
  rational (extension of isomorphisms along transcendence bases, `IsAlgClosure.equivOfEquiv`).
* `g2h_eval_eq_zero_of_mem_ratClosure`: for a set `Γ` stable under `Aut(ℂ)`, every complex
  polynomial vanishing on `Γ` vanishes on the `ℚ`-closure of `Γ` (the minimal-support argument
  of Galois descent).
* `g2h_isRatAlgSubgroup_ratClosure`: the `ℚ`-closure of an `Aut(ℂ)`-stable subgroup is a
  `ℚ`-algebraic subgroup.
* `g2h_ratClosure_eq_closure`: for such a set the `ℚ`-closure is the closure in `g1_zariski`.
-/

noncomputable section
set_option maxHeartbeats 400000

namespace HodgeLean.Foundations

open MvPolynomial Cardinal TopologicalSpace

/-! ## Automorphisms of `ℂ` -/

/-- A ring isomorphism between two fields over which `ℂ` has transcendence bases indexed by
equipotent sets extends to an automorphism of `ℂ` carrying one basis to the other. -/
theorem g2h_exists_ringEquiv_extend {K K' : Type*} [Field K] [Field K'] [Algebra K ℂ]
    [Algebra K' ℂ] (ψ : K ≃+* K') {s s' : Set ℂ} (hv : IsTranscendenceBasis K ((↑) : s → ℂ))
    (hw : IsTranscendenceBasis K' ((↑) : s' → ℂ)) (e : s ≃ s') :
    ∃ σ : ℂ ≃+* ℂ, (∀ x : K, σ (algebraMap K ℂ x) = algebraMap K' ℂ (ψ x)) ∧
      ∀ i : s, σ i = e i := by
  let S := Algebra.adjoin K (Set.range ((↑) : s → ℂ))
  let R := Algebra.adjoin K' (Set.range ((↑) : s' → ℂ))
  have : IsAlgClosure S ℂ := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hv
  have : IsAlgClosure R ℂ := IsAlgClosed.isAlgClosure_of_transcendence_basis _ hw
  let iso : S ≃+* R := hv.1.aevalEquiv.symm.toRingEquiv.trans
     ((MvPolynomial.mapEquiv s ψ).trans
       ((MvPolynomial.renameEquiv K' e).toRingEquiv.trans hw.1.aevalEquiv.toRingEquiv))
  refine ⟨IsAlgClosure.equivOfEquiv ℂ ℂ iso, fun x => ?_, fun i => ?_⟩
  · have h1 : algebraMap K ℂ x = algebraMap S ℂ (hv.1.aevalEquiv (MvPolynomial.C x)) := by
      rw [AlgebraicIndependent.algebraMap_aevalEquiv]; simp
    rw [h1, IsAlgClosure.equivOfEquiv_algebraMap]
    simp [iso]
  · have h1 : (i : ℂ) = algebraMap S ℂ (hv.1.aevalEquiv (MvPolynomial.X i)) := by
      rw [AlgebraicIndependent.algebraMap_aevalEquiv]; simp
    rw [h1, IsAlgClosure.equivOfEquiv_algebraMap]
    simp [iso]

open IntermediateField in
/-- **The fixed field of `Aut(ℂ)` is `ℚ`**: an irrational complex number is moved by some field
automorphism of `ℂ`. An algebraic one goes to another root of its minimal polynomial, a
transcendental one to another element of a transcendence basis.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.14.3 (`K^{Aut(K/k)} = k` for `K`
algebraically closed of infinite transcendence degree over perfect `k`); Bourbaki, *Algèbre*,
ch. V, §14. -/
theorem g2h_exists_ringEquiv_ne {c : ℂ} (hc : c ∉ Set.range (algebraMap ℚ ℂ)) :
    ∃ σ : ℂ ≃+* ℂ, σ c ≠ c := by
  have hℂ : ℵ₀ < #ℂ := by rw [mk_complex]; exact aleph0_lt_continuum
  by_cases halg : IsAlgebraic ℚ c
  · have hint : IsIntegral ℚ c := halg.isIntegral
    have hdeg : 2 ≤ (minpoly ℚ c).natDegree := by
      have h0 := minpoly.natDegree_pos hint
      have h1 : (minpoly ℚ c).natDegree ≠ 1 := fun h => hc (minpoly.natDegree_eq_one_iff.mp h)
      omega
    obtain ⟨c', hc'root, hc'ne⟩ : ∃ c' ∈ (minpoly ℚ c).aroots ℂ, c' ≠ c := by
      have hsep := (minpoly.irreducible hint).separable
      have hspl : ((minpoly ℚ c).map (algebraMap ℚ ℂ)).Splits := IsAlgClosed.splits _
      have hcard := Polynomial.card_rootSet_eq_natDegree hsep hspl
      by_contra hcon
      push Not at hcon
      have : Fintype.card ((minpoly ℚ c).rootSet ℂ) ≤ 1 := by
        rw [Fintype.card_le_one_iff]
        rintro ⟨a, ha⟩ ⟨b, hb⟩
        rw [Polynomial.mem_rootSet'] at ha hb
        have ha' := hcon a (Polynomial.mem_aroots'.mpr ha)
        have hb' := hcon b (Polynomial.mem_aroots'.mpr hb)
        exact Subtype.ext (ha'.trans hb'.symm)
      omega
    let φ : ℚ⟮c⟯ →ₐ[ℚ] ℂ := (algHomAdjoinIntegralEquiv ℚ hint).symm ⟨c', hc'root⟩
    let F' : IntermediateField ℚ ℂ := φ.fieldRange
    let ψ : ℚ⟮c⟯ ≃+* F' := RingEquiv.ofBijective
      ((φ : ℚ⟮c⟯ →+* ℂ).codRestrict F'.toSubfield fun x => AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩)
      ⟨fun x y h => φ.injective (congrArg Subtype.val h), fun y => by
        obtain ⟨x, hx⟩ := AlgHom.mem_fieldRange.mp y.2
        exact ⟨x, Subtype.ext hx⟩⟩
    have hF : #ℚ⟮c⟯ ≤ ℵ₀ := by
      have : Algebra.IsAlgebraic ℚ ℚ⟮c⟯ := isAlgebraic_adjoin_simple hint
      simpa using Algebra.IsAlgebraic.cardinalMk_le_max ℚ ℚ⟮c⟯
    have hF' : #F' ≤ ℵ₀ := (Cardinal.mk_congr ψ.toEquiv).symm.le.trans hF
    obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℚ⟮c⟯ ℂ
    obtain ⟨s', hs'⟩ := exists_isTranscendenceBasis F' ℂ
    have h1 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ hs hF hℂ
    have h2 := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ hs' hF' hℂ
    obtain ⟨e⟩ := Cardinal.eq.mp (h1.symm.trans h2)
    obtain ⟨σ, hσ, -⟩ := g2h_exists_ringEquiv_extend ψ hs hs' e
    refine ⟨σ, ?_⟩
    have := hσ (AdjoinSimple.gen ℚ c)
    simp only [IntermediateField.algebraMap_apply, AdjoinSimple.coe_gen] at this
    rw [this]
    change φ (AdjoinSimple.gen ℚ c) ≠ c
    rw [algHomAdjoinIntegralEquiv_symm_apply_gen]
    exact hc'ne
  · have htr : AlgebraicIndepOn ℚ id ({c} : Set ℂ) :=
      (algebraicIndependent_singleton_iff (⟨c, rfl⟩ : ({c} : Set ℂ))).mpr halg
    obtain ⟨t, hct, ht⟩ := exists_isTranscendenceBasis_superset htr
    obtain ⟨c', hc't, hc'ne⟩ : ∃ c' ∈ t, c' ≠ c := by
      by_contra hcon
      push Not at hcon
      have hsub : Subsingleton t :=
        ⟨fun a b => Subtype.ext ((hcon a a.2).trans (hcon b b.2).symm)⟩
      have := IsAlgClosed.cardinal_le_max_transcendence_basis' _ ht
      have h1 : #t ≤ ℵ₀ := mk_le_aleph0
      have h2 : #ℚ ≤ ℵ₀ := mk_le_aleph0
      exact absurd (this.trans (max_le (max_le h2 h1) le_rfl)) (not_le.mpr hℂ)
    let e : t ≃ t := Equiv.swap ⟨c, hct rfl⟩ ⟨c', hc't⟩
    obtain ⟨σ, -, hσ⟩ := g2h_exists_ringEquiv_extend (RingEquiv.refl ℚ) ht ht e
    refine ⟨σ, ?_⟩
    have := hσ ⟨c, hct rfl⟩
    simp only [e, Equiv.swap_apply_left] at this
    rw [this]
    exact hc'ne

/-! ## Twisting polynomials and points by automorphisms -/

variable {n : ℕ}

theorem g2h_eval_map (σ : ℂ ≃+* ℂ) {ι : Type*} (y : ι → ℂ) (f : MvPolynomial ι ℂ) :
    eval (fun i => σ (y i)) (map (σ : ℂ →+* ℂ) f) = σ (eval y f) := by
  rw [MvPolynomial.eval_map]
  change _ = (σ : ℂ →+* ℂ) (eval₂ (RingHom.id ℂ) y f)
  rw [MvPolynomial.eval₂_comp_left]
  rfl

theorem g2h_aeval_ringEquiv (σ : ℂ ≃+* ℂ) {ι : Type*} (y : ι → ℂ) (f : MvPolynomial ι ℚ) :
    aeval (fun i => σ (y i)) f = σ (aeval y f) := by
  have h : ((σ : ℂ →+* ℂ).comp (aeval y : MvPolynomial ι ℚ →ₐ[ℚ] ℂ).toRingHom) =
      (aeval (fun i => σ (y i)) : MvPolynomial ι ℚ →ₐ[ℚ] ℂ).toRingHom :=
    MvPolynomial.ringHom_ext (fun r => by simp) (fun i => by simp)
  exact (RingHom.congr_fun h f).symm

theorem g2h_coords_map (σ : ℂ ≃+* ℂ) (g : Matrix.GeneralLinearGroup (Fin n) ℂ) :
    g1_coords (Matrix.GeneralLinearGroup.map (σ : ℂ →+* ℂ) g) = fun ij => σ (g1_coords g ij) :=
  rfl

theorem g2h_map_symm_map (σ : ℂ ≃+* ℂ) (g : Matrix.GeneralLinearGroup (Fin n) ℂ) :
    Matrix.GeneralLinearGroup.map (σ : ℂ →+* ℂ)
      (Matrix.GeneralLinearGroup.map (σ.symm : ℂ →+* ℂ) g) = g := by
  ext i j
  simp

/-- A set of complex points is **`Aut(ℂ)`-stable** when every field automorphism of `ℂ`,
applied to the entries, maps it into itself.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.14.1 (the action of `Aut(K/k)` on
`K`-points). -/
def g2h_GaloisStable (Γ : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)) : Prop :=
  ∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, Matrix.GeneralLinearGroup.map (σ : ℂ →+* ℂ) g ∈ Γ

example : g2h_GaloisStable (Set.univ : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)) :=
  fun _ _ _ => trivial

/-- Zero sets of rational polynomials are `Aut(ℂ)`-stable. -/
theorem g2h_galoisStable_ratZeroSet (S : Set (MvPolynomial (Fin n × Fin n) ℚ)) :
    g2h_GaloisStable (g2_ratZeroSet S) := by
  intro σ g hg f hf
  rw [g2h_coords_map, g2h_aeval_ringEquiv, hg f hf, map_zero]

/-- The galois orbit of a set is `Aut(ℂ)`-stable. -/
theorem g2h_galoisStable_galoisOrbit (S : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)) :
    g2h_GaloisStable (g2_galoisOrbit S) := by
  intro σ g hg
  obtain ⟨τ, hτ⟩ := Set.mem_iUnion.mp hg
  obtain ⟨x, hx, rfl⟩ := hτ
  refine Set.mem_iUnion.mpr ⟨τ.trans σ, x, hx, ?_⟩
  ext i j
  simp

/-- The subgroup generated by an `Aut(ℂ)`-stable set is `Aut(ℂ)`-stable. -/
theorem g2h_galoisStable_closure {S : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)}
    (hS : g2h_GaloisStable S) :
    g2h_GaloisStable (Subgroup.closure S : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)) := by
  intro σ g hg
  have h : Subgroup.map (Matrix.GeneralLinearGroup.map (σ : ℂ →+* ℂ)) (Subgroup.closure S) ≤
      Subgroup.closure S := by
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_le _ |>.mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.subset_closure (hS σ x hx)
  exact h ⟨g, hg, rfl⟩

/-! ## Descent of vanishing polynomials -/

/-- **Galois descent.** For an `Aut(ℂ)`-stable set `Γ`, a complex polynomial vanishing on `Γ`
vanishes on the `ℚ`-closure of `Γ`: the complex vanishing ideal of `Γ` is spanned by rational
polynomials. Minimal-support argument: normalize one coefficient to `1`; an irrational
coefficient is moved by some `σ`, and `σ f - f` vanishes on `Γ` with smaller support.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.14.2–14.4; Bourbaki, *Algèbre*, ch. V,
§10, no. 4 (Galois descent of subspaces). -/
theorem g2h_eval_eq_zero_of_mem_ratClosure {Γ : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)}
    (hΓ : g2h_GaloisStable Γ) (f : MvPolynomial (Fin n × Fin n) ℂ)
    (hf : ∀ g ∈ Γ, eval (g1_coords g) f = 0) {x : Matrix.GeneralLinearGroup (Fin n) ℂ}
    (hx : x ∈ g2_ratClosure Γ) : eval (g1_coords x) f = 0 := by
  classical
  induction hN : f.support.card using Nat.strong_induction_on generalizing f with
  | _ N ih =>
  by_cases hf0 : f = 0
  · simp [hf0]
  obtain ⟨m₀, hm₀⟩ : f.support.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr (fun h => hf0 (MvPolynomial.support_eq_empty.mp h))
  set a := f.coeff m₀ with ha_def
  have ha : a ≠ 0 := mem_support_iff.mp hm₀
  obtain ⟨f', hf'_def⟩ : ∃ f', f' = C a⁻¹ * f := ⟨_, rfl⟩
  have hf'Γ : ∀ g ∈ Γ, eval (g1_coords g) f' = 0 := fun g hg => by
    simp [hf'_def, hf g hg]
  have hsupp' : f'.support = f.support := by
    rw [hf'_def, ← smul_eq_C_mul]
    exact support_smul_eq (inv_ne_zero ha) f
  suffices h : eval (g1_coords x) f' = 0 by
    have hff : f = C a * f' := by
      rw [hf'_def, ← mul_assoc, ← C_mul, mul_inv_cancel₀ ha, C_1, one_mul]
    rw [hff, eval_mul, h, mul_zero]
  have hm₀' : f'.coeff m₀ = 1 := by
    rw [hf'_def, coeff_C_mul, ← ha_def, inv_mul_cancel₀ ha]
  by_cases hrat : ∀ m, f'.coeff m ∈ Set.range (algebraMap ℚ ℂ)
  · obtain ⟨Q, hQ⟩ : f' ∈ Set.range (map (algebraMap ℚ ℂ)) := by
      rw [mem_range_map_iff_coeffs_subset]
      intro c hc
      obtain ⟨m, -, rfl⟩ := mem_coeffs_iff.mp hc
      exact hrat m
    have hQΓ : ∀ g ∈ Γ, aeval (g1_coords g) Q = 0 := fun g hg => by
      rw [aeval_def, ← eval_map, hQ]
      exact hf'Γ g hg
    have := hx Q hQΓ
    rwa [aeval_def, ← eval_map, hQ] at this
  push Not at hrat
  obtain ⟨m, hm⟩ := hrat
  set c := f'.coeff m with hc_def
  obtain ⟨σ, hσ⟩ := g2h_exists_ringEquiv_ne hm
  have hc0 : c ≠ 0 := fun h => hm ⟨0, by rw [h, map_zero]⟩
  obtain ⟨g, hg_def⟩ : ∃ g, g = map (σ : ℂ →+* ℂ) f' - f' := ⟨_, rfl⟩
  have hcoeffg : ∀ m', g.coeff m' = σ (f'.coeff m') - f'.coeff m' := fun m' => by
    rw [hg_def, coeff_sub, coeff_map]
    rfl
  have hgΓ : ∀ γ ∈ Γ, eval (g1_coords γ) g = 0 := fun γ hγ => by
    have h1 := g2h_eval_map σ (g1_coords (Matrix.GeneralLinearGroup.map (σ.symm : ℂ →+* ℂ) γ)) f'
    rw [← g2h_coords_map, g2h_map_symm_map, hf'Γ _ (hΓ σ.symm γ hγ), map_zero] at h1
    rw [hg_def, eval_sub, h1, hf'Γ γ hγ, sub_zero]
  have hsubg : g.support ⊆ f'.support := fun m' hm' => by
    rw [mem_support_iff] at hm' ⊢
    intro h0
    rw [hcoeffg, h0, map_zero, sub_zero] at hm'
    exact hm' rfl
  have hgx : eval (g1_coords x) g = 0 := by
    refine ih _ ?_ g hgΓ rfl
    rw [← hN, ← hsupp']
    refine Finset.card_lt_card ⟨hsubg, fun h => ?_⟩
    have := h (mem_support_iff.mpr (by rw [hm₀']; exact one_ne_zero))
    rw [mem_support_iff, hcoeffg, hm₀', map_one, sub_self] at this
    exact this rfl
  have hgm : g.coeff m ≠ 0 := by
    rw [hcoeffg, ← hc_def]
    exact sub_ne_zero.mpr hσ
  obtain ⟨h, hh_def⟩ : ∃ h, h = f' - C (c / g.coeff m) * g := ⟨_, rfl⟩
  have hcoeffh : ∀ m', h.coeff m' = f'.coeff m' - c / g.coeff m * g.coeff m' := fun m' => by
    rw [hh_def, coeff_sub, coeff_C_mul]
  have hhΓ : ∀ γ ∈ Γ, eval (g1_coords γ) h = 0 := fun γ hγ => by
    rw [hh_def, eval_sub, eval_mul, hgΓ γ hγ, hf'Γ γ hγ, mul_zero, sub_zero]
  have hhx : eval (g1_coords x) h = 0 := by
    refine ih _ ?_ h hhΓ rfl
    rw [← hN, ← hsupp']
    refine Finset.card_lt_card ⟨fun m' hm' => ?_, fun hsub => ?_⟩
    · rw [mem_support_iff] at hm' ⊢
      intro h0
      have hg0 : g.coeff m' = 0 := by
        by_contra hne
        exact (mem_support_iff.mp (hsubg (mem_support_iff.mpr hne))) h0
      rw [hcoeffh, h0, hg0, mul_zero, sub_zero] at hm'
      exact hm' rfl
    · have := hsub (mem_support_iff.mpr hc0)
      rw [mem_support_iff, hcoeffh, ← hc_def, div_mul_cancel₀ _ hgm, sub_self] at this
      exact this rfl
  have hfh : f' = h + C (c / g.coeff m) * g := by
    rw [hh_def, sub_add_cancel]
  rw [hfh, eval_add, eval_mul, hhx, hgx, mul_zero, add_zero]

/-! ## The `ℚ`-closure as a Zariski closure -/

section Zariski

set_option warn.classDefReducibility false in
attribute [local instance] g1_zariski

/-- A map of `GL_n(k)` pulling zero sets of polynomials back to zero sets is Zariski
continuous. -/
theorem g2h_continuous_of_poly {k : Type*} [Field k]
    (φ : Matrix.GeneralLinearGroup (Fin n) k → Matrix.GeneralLinearGroup (Fin n) k)
    (h : ∀ f : MvPolynomial (Fin n × Fin n) k, ∃ F : MvPolynomial (Fin n × Fin n) k,
      ∀ g, eval (g1_coords g) F = 0 ↔ eval (g1_coords (φ g)) f = 0) : Continuous φ := by
  refine continuous_iff_isClosed.mpr fun Z hZ => ?_
  obtain ⟨s, rfl⟩ := (g1_isClosed_iff Z).mp hZ
  choose F hF using h
  refine (g1_isClosed_iff _).mpr ⟨F '' s, ?_⟩
  ext g
  simp only [Set.mem_preimage, g1_zeroSet, Set.mem_ofPred_eq, Set.mem_image,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact forall₂_congr fun f _ => (hF f g).symm

/-- Right translations of `GL_n(k)` are Zariski continuous. -/
theorem g2h_continuous_mul_right {k : Type*} [Field k]
    (a : Matrix.GeneralLinearGroup (Fin n) k) : Continuous (fun g => g * a) := by
  refine g2h_continuous_of_poly _ fun f => ⟨bind₁ (fun ij : Fin n × Fin n =>
    ∑ l, X (ij.1, l) * C ((a : Matrix (Fin n) (Fin n) k) l ij.2)) f, fun g => ?_⟩
  have : eval (g1_coords g) (bind₁ (fun ij : Fin n × Fin n =>
      ∑ l, X (ij.1, l) * C ((a : Matrix (Fin n) (Fin n) k) l ij.2)) f) =
      eval (g1_coords (g * a)) f := by
    change aeval (g1_coords g) (bind₁ _ f) = aeval (g1_coords (g * a)) f
    rw [aeval_bind₁]
    congr 2
    funext ij
    simp [g1_coords, Matrix.mul_apply]
  rw [this]

/-- Field automorphisms of `ℂ`, applied to the entries, are Zariski continuous. -/
theorem g2h_continuous_map (σ : ℂ ≃+* ℂ) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin n) (σ : ℂ →+* ℂ)) := by
  refine g2h_continuous_of_poly _ fun f => ⟨map (σ.symm : ℂ →+* ℂ) f, fun g => ?_⟩
  have h := g2h_eval_map σ (g1_coords g) (map (σ.symm : ℂ →+* ℂ) f)
  rw [MvPolynomial.map_map] at h
  have hid : (σ : ℂ →+* ℂ).comp (σ.symm : ℂ →+* ℂ) = RingHom.id ℂ := by
    ext z
    simp
  rw [hid, map_id, ← g2h_coords_map] at h
  rw [h, map_eq_zero_iff σ σ.injective]

/-- For an `Aut(ℂ)`-stable set, the `ℚ`-closure is the Zariski closure.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.14.4. -/
theorem g2h_ratClosure_eq_closure {Γ : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)}
    (hΓ : g2h_GaloisStable Γ) : g2_ratClosure Γ = closure Γ := by
  apply le_antisymm
  · obtain ⟨s, hs⟩ := (g1_isClosed_iff _).mp (isClosed_closure (s := Γ))
    intro x hx
    rw [hs]
    intro f hf
    refine g2h_eval_eq_zero_of_mem_ratClosure hΓ f (fun g hg => ?_) hx
    have : g ∈ closure Γ := subset_closure hg
    rw [hs] at this
    exact this f hf
  · refine closure_minimal (fun g hg q hq => hq g hg) ?_
    refine (g1_isClosed_iff _).mpr ⟨(map (algebraMap ℚ ℂ)) '' {q | ∀ g ∈ Γ,
      aeval (g1_coords g) q = 0}, ?_⟩
    ext x
    simp only [g2_ratClosure, g2_ratZeroSet, g1_zeroSet, Set.mem_ofPred_eq, Set.mem_image,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, eval_map, ← aeval_def]

/-- **The `ℚ`-closure of an `Aut(ℂ)`-stable subgroup is a `ℚ`-algebraic subgroup.** It is
the Zariski closure, closed under translations; inverses come from the descending chain
`x^k Γ̄` of closed sets.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.3 (the closure of a subgroup is a
subgroup) and AG.14.4. -/
theorem g2h_isRatAlgSubgroup_ratClosure (Γ : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℂ))
    (hΓ : g2h_GaloisStable (Γ : Set (Matrix.GeneralLinearGroup (Fin n) ℂ))) :
    g2_IsRatAlgSubgroup (g2_ratClosure (Γ : Set (Matrix.GeneralLinearGroup (Fin n) ℂ))) := by
  have hR := g2h_ratClosure_eq_closure hΓ
  set R := g2_ratClosure (Γ : Set (Matrix.GeneralLinearGroup (Fin n) ℂ))
  have hRc : IsClosed R := hR ▸ isClosed_closure
  have hΓR : (Γ : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)) ⊆ R := hR ▸ subset_closure
  have hleft : ∀ γ ∈ Γ, ∀ x ∈ R, γ * x ∈ R := by
    intro γ hγ x hx
    rw [hR] at hx ⊢
    have h1 := image_closure_subset_closure_image (g1_continuous_mul_left γ) ⟨x, hx, rfl⟩
    refine closure_mono ?_ h1
    rintro _ ⟨y, hy, rfl⟩
    exact Γ.mul_mem hγ hy
  have hmul : ∀ x ∈ R, ∀ y ∈ R, x * y ∈ R := by
    intro x hx y hy
    have hx' : x ∈ closure (Γ : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)) := hR ▸ hx
    have h1 := image_closure_subset_closure_image (g2h_continuous_mul_right y) ⟨x, hx', rfl⟩
    refine closure_minimal ?_ hRc h1
    rintro _ ⟨γ, hγ, rfl⟩
    exact hleft γ hγ y hy
  have hone : (1 : Matrix.GeneralLinearGroup (Fin n) ℂ) ∈ R := hΓR Γ.one_mem
  refine ⟨⟨_, rfl⟩, hone, hmul, fun x hx => ?_⟩
  have := g1_noetherianSpace (k := ℂ) (n := n)
  let Z : ℕ → Closeds (Matrix.GeneralLinearGroup (Fin n) ℂ) := fun k =>
    ⟨(fun g => x ^ k * g) '' R, by
      rw [Set.image_mul_left]
      exact hRc.preimage (g1_continuous_mul_left _)⟩
  obtain ⟨_, ⟨k, rfl⟩, hmin⟩ := (wellFounded_lt (α := Closeds _)).has_min (Set.range Z)
    ⟨Z 0, 0, rfl⟩
  have hle : Z (k + 1) ≤ Z k := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨x * y, hmul x hx y hy, by simp only [pow_succ, mul_assoc]⟩
  have heq : Z (k + 1) = Z k := by
    by_contra hne
    exact hmin _ ⟨k + 1, rfl⟩ (lt_of_le_of_ne hle hne)
  have hxk : x ^ k ∈ (Z k : Set _) := ⟨1, hone, mul_one _⟩
  rw [← heq] at hxk
  obtain ⟨y, hy, hxy⟩ := hxk
  have : y = x⁻¹ := by
    simp only [pow_succ, mul_assoc] at hxy
    have h2 := mul_left_cancel (a := x ^ k) (hxy.trans (mul_one _).symm)
    exact eq_inv_of_mul_eq_one_right h2
  exact this ▸ hy

end Zariski

end HodgeLean.Foundations
