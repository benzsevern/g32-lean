import HodgeLean.Foundations.AnalyticGermDimension

/-! # Finite projection: auxiliary statements

The algebraic preparation step and the geometry of a distinguished polynomial family.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Filter Topology Polynomial
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
namespace HodgeLean.Foundations

open Lean Elab Term in
syntax "adim4Private% " str : term

open Lean Elab Term in
elab_rules : term
  | `(adim4Private% $s:str) =>
      let n := (s.getString.splitOn ".").foldl (fun n p =>
        match p.toNat? with | some k => Name.num n k | none => Name.str n p) Name.anonymous
      return mkConst n

private abbrev adim4CanonicalEmbedding :=
  adim4Private% "_private.HodgeLean.Foundations.AnalyticDivisorAlgebraic6Proofs.0.HodgeLean.Foundations.AnalyticDivisorAlgebraic6.canonicalEmbedding"

private abbrev adim4CanonicalEmbeddingSpec :=
  adim4Private% "_private.HodgeLean.Foundations.AnalyticDivisorAlgebraic6Proofs.0.HodgeLean.Foundations.AnalyticDivisorAlgebraic6.canonicalEmbedding_spec"

private abbrev adim4CanonicalEmbeddingDvdIff :=
  adim4Private% "_private.HodgeLean.Foundations.AnalyticDivisorAlgebraic6Proofs.0.HodgeLean.Foundations.AnalyticDivisorAlgebraic6.canonicalEmbedding_dvd_iff"

private theorem adim4_polynomial_eq_sum {n : ℕ} {R : Polynomial (AnalyticGerm n)} {d : ℕ}
    (hR : R.degree < d) : R = ∑ j : Fin d, C (R.coeff j) * X ^ (j : ℕ) := by
  exact R.sum_C_mul_X_pow_eq.symm.trans
    (Polynomial.sum_fin (fun j a ↦ C a * X ^ j) (fun _ ↦ by simp) hR).symm

/-- Source: Gunning--Rossi, II.B and III.B, division and finite hypersurface projection. -/
theorem adim4_prepared_finite_aux (n : ℕ)
    (ι : Polynomial (AnalyticGerm n) →+* AnalyticGerm (n + 1))
    (hι : IsWeierstrassEmbedding ι) (P : Polynomial (AnalyticGerm n))
    (hP : IsWeierstrassPolynomial P) :
    ((Ideal.Quotient.mk (Ideal.span {ι P})).comp (ι.comp C)).Finite ∧
      Function.Injective ((Ideal.Quotient.mk (Ideal.span {ι P})).comp (ι.comp C)) := by
  let I : Ideal (AnalyticGerm (n + 1)) := Ideal.span {ι P}
  let f : AnalyticGerm n →+* AnalyticGerm (n + 1) ⧸ I :=
    (Ideal.Quotient.mk I).comp (ι.comp C)
  letI : Algebra (AnalyticGerm n) (AnalyticGerm (n + 1) ⧸ I) := f.toAlgebra
  have hfinite : f.Finite := by
    apply Module.Finite.of_fg_top
    rw [Submodule.fg_def]
    let b : Fin P.natDegree → AnalyticGerm (n + 1) ⧸ I :=
      fun j ↦ Ideal.Quotient.mk I (ι (X ^ (j : ℕ)))
    refine ⟨Set.range b, Set.finite_range b, ?_⟩
    apply top_unique
    intro x _
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨q, r, hr, hgr⟩ := adim_division_representative n ι hι P hP g
    rw [hgr, map_add, map_mul]
    have hPzero : Ideal.Quotient.mk I (ι P) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp [I]))
    rw [hPzero, mul_zero, zero_add, adim4_polynomial_eq_sum hr, map_sum]
    rw [map_sum]
    apply Submodule.sum_mem
    intro j _
    rw [map_mul, map_mul]
    change (r.coeff j) • b j ∈ Submodule.span (AnalyticGerm n) (Set.range b)
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self j))
  have hinjective : Function.Injective f := by
    intro g h hg
    have hmem : ι (C (g - h)) ∈ I := by
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change f (g - h) = 0
      rw [map_sub, hg, sub_self]
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hmem
    have hi : ι = adim4CanonicalEmbedding n :=
      weierstrassEmbedding_unique hι (adim4CanonicalEmbeddingSpec n)
    rw [hi] at hq
    have hdiv : P ∣ C (g - h) :=
      (adim4CanonicalEmbeddingDvdIff hP).mp ⟨q, hq⟩
    by_contra hne
    have hc : C (g - h) ≠ 0 := C_ne_zero.mpr (sub_ne_zero.mpr hne)
    have hle := hP.1.natDegree_le_of_dvd hc hdiv
    rw [natDegree_C] at hle
    exact (Nat.not_lt_zero _ (lt_of_lt_of_le hP.2.1 hle))
  exact ⟨hfinite, hinjective⟩

/-- Source: de Jong--Pfister, Local Analytic Geometry, Chapter 3, finite analytic algebras. -/
theorem adim4_contraction_finite_aux (n : ℕ)
    (ι : Polynomial (AnalyticGerm n) →+* AnalyticGerm (n + 1))
    (hι : IsWeierstrassEmbedding ι) (P : Polynomial (AnalyticGerm n))
    (hP : IsWeierstrassPolynomial P) (I : Ideal (AnalyticGerm (n + 1)))
    (hI : ι P ∈ I) :
    (Ideal.quotientMap I (ι.comp C) (le_refl (I.comap (ι.comp C)))).Finite := by
  let J : Ideal (AnalyticGerm (n + 1)) := Ideal.span {ι P}
  have hJI : J ≤ I := Ideal.span_le.2 (by simpa using hI)
  let q : AnalyticGerm (n + 1) ⧸ J →+* AnalyticGerm (n + 1) ⧸ I :=
    Ideal.quotientMap I (RingHom.id _) (by simpa using hJI)
  have hq_surjective : Function.Surjective q :=
    Ideal.quotientMap_surjective Function.surjective_id
  have hq_finite : q.Finite := RingHom.Finite.of_surjective q hq_surjective
  have hprepared :
      ((Ideal.Quotient.mk J).comp (ι.comp C)).Finite :=
    (adim4_prepared_finite_aux n ι hι P hP).1
  have hcomposite :
      (q.comp ((Ideal.Quotient.mk J).comp (ι.comp C))).Finite :=
    hq_finite.comp hprepared
  apply RingHom.Finite.of_comp_finite
    (f := Ideal.Quotient.mk (I.comap (ι.comp C)))
  rw [Ideal.quotientMap_comp_mk]
  convert hcomposite using 1
  ext x
  simp [q, J]

private lemma adim4_fiberPolynomial_monic (k : ℕ) (b : Fin k → ℂ) :
    (X ^ k + ∑ i : Fin k, C (b i) * X ^ (i : ℕ) : ℂ[X]).Monic := by
  exact monic_X_pow_add (degree_sum_fin_lt b)

private lemma adim4_root_norm_lt (k : ℕ) (hk : 0 < k) (p : ℂ[X]) (hp : p.Monic)
    (hdeg : p.natDegree = k) (e : ℝ) (he : 0 < e)
    (hcoeff : ∀ j : ℕ, ‖(X ^ k).coeff j - p.coeff j‖ < e)
    (R : ℝ) (hsmall_one : ((k + 1 : ℕ) * e) ^ (k : ℝ)⁻¹ < 1)
    (hsmall_R : ((k + 1 : ℕ) * e) ^ (k : ℝ)⁻¹ < R)
    (w : ℂ) (hw : p.eval w = 0) : ‖w‖ < R := by
  obtain ⟨v, hv, hwv⟩ :=
    Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt he hw hp (monic_X_pow k)
      (by simpa [hdeg]) hcoeff (IsAlgClosed.splits (X ^ k))
  have hv0 : v = 0 := by
    rw [Polynomial.mem_roots (pow_ne_zero k X_ne_zero)] at hv
    simpa [hk.ne'] using hv
  norm_num [Nat.cast_add, Nat.cast_one] at hsmall_one hsmall_R
  rw [hv0, sub_zero, hdeg] at hwv
  by_cases hw1 : ‖w‖ < 1
  · rw [max_eq_right hw1.le] at hwv
    have hwv' : ‖w‖ < (((k : ℝ) + 1) * e) ^ (k : ℝ)⁻¹ := by
      simpa only [mul_one] using hwv
    exact hwv'.trans hsmall_R
  · have hw1' : 1 ≤ ‖w‖ := le_of_not_gt hw1
    rw [max_eq_left hw1'] at hwv
    have := mul_lt_mul_of_pos_right hsmall_one (lt_of_lt_of_le (by positivity) hw1')
    exact (lt_asymm hwv (by simpa using this)).elim

/-- Source: Gunning--Rossi, III.B--C, distinguished polynomials and local projection;
Chirka, Complex Analytic Sets, §3, local parametrization. -/
theorem adim4_polynomial_projection_aux (n k : ℕ) (hk : 0 < k)
    (a : Fin k → (Fin n → ℂ) → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0) (ha0 : ∀ i, a i 0 = 0)
    (r : ℝ) (hr : 0 < r) :
    ∃ V : Set (Fin n → ℂ), IsOpen V ∧ (0 : Fin n → ℂ) ∈ V ∧
      ∃ p : {z : (Fin n → ℂ) × ℂ //
        z.1 ∈ V ∧ ‖z.2‖ < r ∧ z.2 ^ k + ∑ i : Fin k, a i z.1 * z.2 ^ (i : ℕ) = 0} → V,
        (∀ z, (p z).val = z.val.1) ∧ IsProperMap p ∧ Function.Surjective p ∧
        (∀ w : V, (p ⁻¹' {w}).Finite) ∧
        ∀ z, (p z).val = 0 → z.val = (0, 0) := by
  classical
  let R : ℝ := r / 2
  let t : ℝ := min 1 R / 2
  let e : ℝ := t ^ k / (k + 1)
  have hR : 0 < R := by dsimp [R]; linarith
  have ht : 0 < t := by dsimp [t]; positivity
  have he : 0 < e := by dsimp [e]; positivity
  have hscale : (((k : ℝ) + 1) * e) ^ (k : ℝ)⁻¹ = t := by
    have hk0 : k ≠ 0 := hk.ne'
    have hmul : ((k : ℝ) + 1) * e = t ^ k := by
      dsimp [e]
      field_simp
    rw [hmul, Real.pow_rpow_inv_natCast ht.le hk0]
  have ht_one : t < 1 := by
    dsimp [t]
    have : min 1 R ≤ 1 := min_le_left _ _
    linarith [lt_min (by norm_num : (0 : ℝ) < 1) hR]
  have ht_R : t < R := by
    dsimp [t]
    have : min 1 R ≤ R := min_le_right _ _
    linarith [lt_min (by norm_num : (0 : ℝ) < 1) hR]
  let S : Set (Fin n → ℂ) :=
    (⋂ i : Fin k, a i ⁻¹' Metric.ball 0 e) ∩
      ⋂ i : Fin k, {z | ContinuousAt (a i) z}
  have hS : S ∈ nhds (0 : Fin n → ℂ) := by
    refine Filter.inter_mem
      (Filter.iInter_mem.2 fun i ↦ (ha i).continuousAt
        (Metric.isOpen_ball.mem_nhds (by simpa [ha0 i] using he)))
      (Filter.iInter_mem.2 fun i ↦ (ha i).eventually_continuousAt)
  let V : Set (Fin n → ℂ) := interior S
  have hVopen : IsOpen V := isOpen_interior
  have hV0 : (0 : Fin n → ℂ) ∈ V := by
    exact mem_interior_iff_mem_nhds.mpr hS
  refine ⟨V, hVopen, hV0, ?_⟩
  let p : {z : (Fin n → ℂ) × ℂ //
      z.1 ∈ V ∧ ‖z.2‖ < r ∧ z.2 ^ k + ∑ i : Fin k, a i z.1 * z.2 ^ (i : ℕ) = 0} → V :=
    fun z ↦ ⟨z.val.1, z.property.1⟩
  have hroot (z : Fin n → ℂ) (hz : z ∈ V) (w : ℂ)
      (hw : w ^ k + ∑ i : Fin k, a i z * w ^ (i : ℕ) = 0) : ‖w‖ < R := by
    let q : ℂ[X] := X ^ k + ∑ i : Fin k, C (a i z) * X ^ (i : ℕ)
    have hqdeg : q.natDegree = k := by
      have h := natDegree_add_eq_left_of_degree_lt
        (p := X ^ k) (q := ∑ i : Fin k, C (a i z) * X ^ (i : ℕ))
        (by simpa only [degree_X_pow] using degree_sum_fin_lt (fun i ↦ a i z))
      simpa [q] using h
    apply adim4_root_norm_lt k hk q (adim4_fiberPolynomial_monic k (fun i ↦ a i z))
      hqdeg e he
    · intro j
      by_cases hj : j < k
      · let i : Fin k := ⟨j, hj⟩
        have hai : ‖a i z‖ < e := by
          have hzS : z ∈ S := interior_subset hz
          simpa [S] using Set.mem_iInter.mp hzS.1 i
        have hsum : (∑ x : Fin k, if j = (x : ℕ) then a x z else 0) = a i z := by
          rw [Finset.sum_eq_single i]
          · simp [i]
          · intro b hb hbi
            simp [show j ≠ (b : ℕ) by
              intro h
              apply hbi
              exact Fin.ext (by simpa [i] using h.symm)]
          · simp
        simpa [q, hj, hsum] using hai
      · have hkj : k ≤ j := le_of_not_gt hj
        have hsum : (∑ x : Fin k, if j = (x : ℕ) then a x z else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          simp [ne_of_gt (lt_of_lt_of_le i.isLt hkj)]
        simpa [q, coeff_X_pow, hsum] using he
    · simpa [hscale] using ht_one
    · simpa [hscale] using ht_R
    · simpa [q, eval_add, eval_finset_sum] using hw
  refine ⟨p, fun z ↦ rfl, ?_, ?_, ?_, ?_⟩
  · refine isProperMap_iff_isCompact_preimage.mpr ⟨by fun_prop, ?_⟩
    intro K hK
    rw [IsEmbedding.subtypeVal.isCompact_iff]
    have haV (i : Fin k) : Continuous (fun z : V ↦ a i z.val) := by
      rw [continuous_iff_continuousAt]
      intro z
      have hzS : z.val ∈ S := interior_subset z.property
      have hcont : ContinuousAt (a i) z.val := Set.mem_iInter.mp hzS.2 i
      exact hcont.comp continuous_subtype_val.continuousAt
    let F : V × ℂ → ℂ := fun z ↦
      z.2 ^ k + ∑ i : Fin k, a i z.1.val * z.2 ^ (i : ℕ)
    have hF : Continuous F := by
      dsimp [F]
      exact (continuous_snd.pow k).add <| continuous_finset_sum _ fun i _ ↦
        ((haV i).comp continuous_fst).mul (continuous_snd.pow (i : ℕ))
    let B : Set (V × ℂ) := K ×ˢ Metric.closedBall 0 R
    have hB : IsCompact B := hK.prod (isCompact_closedBall 0 R)
    let Z : Set (V × ℂ) := B ∩ F ⁻¹' {0}
    have hZ : IsCompact Z := hB.inter_right (isClosed_singleton.preimage hF)
    have himg := hZ.image (continuous_subtype_val.fst'.prodMk continuous_snd)
    convert himg using 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hyp : p y ∈ K := by simpa using hy
      exact ⟨(p y, y.val.2), ⟨⟨hyp, by
        simpa [Metric.mem_closedBall, dist_zero_right] using
          (hroot y.val.1 y.property.1 y.val.2 y.property.2.2).le⟩, y.property.2.2⟩, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      have hyK : y.1 ∈ K := hy.1.1
      have hyeq : F y = 0 := hy.2
      have hyR : ‖y.2‖ < R := hroot y.1.val y.1.property y.2 (by simpa [F] using hyeq)
      have hyr : ‖y.2‖ < r := hyR.trans (by dsimp [R]; linarith)
      let d : {z : (Fin n → ℂ) × ℂ // z.1 ∈ V ∧ ‖z.2‖ < r ∧
          z.2 ^ k + ∑ i : Fin k, a i z.1 * z.2 ^ (i : ℕ) = 0} :=
        ⟨(y.1.val, y.2), y.1.property, hyr, by simpa [F] using hyeq⟩
      refine ⟨d, ?_, rfl⟩
      change p d ∈ K
      simpa [d, p] using hyK
  · intro z
    let q : ℂ[X] := X ^ k + ∑ i : Fin k, C (a i z.val) * X ^ (i : ℕ)
    have hqm : q.Monic := adim4_fiberPolynomial_monic k (fun i ↦ a i z.val)
    have hqdeg : q.degree ≠ 0 := by
      rw [degree_eq_natDegree hqm.ne_zero]
      simp [show q.natDegree = k by
        have h := natDegree_add_eq_left_of_degree_lt
          (p := X ^ k) (q := ∑ i : Fin k, C (a i z.val) * X ^ (i : ℕ))
          (by simpa only [degree_X_pow] using degree_sum_fin_lt (fun i ↦ a i z.val))
        simpa [q] using h, hk.ne']
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_root q hqdeg
    have hweq : w ^ k + ∑ i : Fin k, a i z.val * w ^ (i : ℕ) = 0 := by
      simpa [q, eval_add, eval_finset_sum] using hw
    have hwR := hroot z.val z.property w hweq
    have hwr : ‖w‖ < r := hwR.trans (by dsimp [R]; linarith)
    exact ⟨⟨(z.val, w), z.property, hwr, hweq⟩, Subtype.ext rfl⟩
  · intro z
    let q : ℂ[X] := X ^ k + ∑ i : Fin k, C (a i z.val) * X ^ (i : ℕ)
    have hq0 : q ≠ 0 := (adim4_fiberPolynomial_monic k (fun i ↦ a i z.val)).ne_zero
    refine Set.Finite.of_finite_image
      (s := p ⁻¹' {z})
      (f := fun x : {y : (Fin n → ℂ) × ℂ // y.1 ∈ V ∧ ‖y.2‖ < r ∧
        y.2 ^ k + ∑ i : Fin k, a i y.1 * y.2 ^ (i : ℕ) = 0} ↦ x.val.2) ?_ ?_
    · refine (Polynomial.finite_setOfPred_isRoot hq0).subset ?_
      rintro w ⟨x, hx, rfl⟩
      have heq := x.property.2.2
      have hxz : x.val.1 = z.val := by
        have : p x = z := by simpa using hx
        exact congrArg Subtype.val this
      rw [hxz] at heq
      simpa [q, IsRoot, eval_add, eval_finset_sum] using heq
    · intro x hx y hy hxy
      apply Subtype.ext
      apply Prod.ext
      · have hxz : p x = z := by simpa using hx
        have hyz : p y = z := by simpa using hy
        exact congrArg Subtype.val (hxz.trans hyz.symm)
      · exact hxy
  · intro z hz
    apply Prod.ext
    · exact hz
    · have heq := z.property.2.2
      have hz1 : z.val.1 = 0 := hz
      rw [hz1] at heq
      simpa [ha0, hk.ne'] using heq

end HodgeLean.Foundations
