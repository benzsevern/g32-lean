import HodgeLean.Foundations.AnalyticDivisorAlgebraic13Defs

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic13

open Filter Polynomial Set Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11

/-- Source: Gunning--Rossi, II.B, Theorem 2, after translation to the origin. -/
theorem spec_preparation_at_aux {n : ℕ} (p : Fin (n + 1) → ℂ)
    (g : AnalyticGermAt (n + 1) p)
    (hreg : ∃ e : AnalyticGermAt (n + 1) p ≃+* AnalyticGerm (n + 1),
      (∀ a, analyticGermValue (n + 1) (e a) = analyticGermAtValue (n + 1) p a) ∧
      (∀ (f : (Fin (n + 1) → ℂ) → ℂ) (hf : AnalyticAt ℂ f p)
          (ht : AnalyticAt ℂ (fun z ↦ f (p + z)) 0),
        e ⟨@Filter.Germ.ofFun (Fin (n + 1) → ℂ) ℂ (nhds p) f, ⟨f, hf, rfl⟩⟩ =
          ⟨@Filter.Germ.ofFun (Fin (n + 1) → ℂ) ℂ (nhds 0) (fun z ↦ f (p + z)),
            ⟨fun z ↦ f (p + z), ht, rfl⟩⟩) ∧
      IsRegularInLast (e g)) (hnu : ¬ IsUnit g) :
    ∃ (eFull : AnalyticGermAt (n + 1) p ≃+* AnalyticGerm (n + 1))
        (eBase : AnalyticGermAt n (gaga13_basePoint p) ≃+* AnalyticGerm n)
        (ι₀ : Polynomial (AnalyticGerm n) →+* AnalyticGerm (n + 1))
        (ι : Polynomial (AnalyticGermAt n (gaga13_basePoint p)) →+* AnalyticGermAt (n + 1) p)
        (P : Polynomial (AnalyticGermAt n (gaga13_basePoint p)))
        (u : AnalyticGermAt (n + 1) p),
      (∀ a, analyticGermValue (n + 1) (eFull a) =
        analyticGermAtValue (n + 1) p a) ∧
      (∀ (f : (Fin (n + 1) → ℂ) → ℂ) (hf : AnalyticAt ℂ f p)
          (ht : AnalyticAt ℂ (fun z ↦ f (p + z)) 0),
        eFull ⟨@Filter.Germ.ofFun (Fin (n + 1) → ℂ) ℂ (nhds p) f, ⟨f, hf, rfl⟩⟩ =
          ⟨@Filter.Germ.ofFun (Fin (n + 1) → ℂ) ℂ (nhds 0) (fun z ↦ f (p + z)),
            ⟨fun z ↦ f (p + z), ht, rfl⟩⟩) ∧
      (∀ a, analyticGermValue n (eBase a) =
        analyticGermAtValue n (gaga13_basePoint p) a) ∧
      (∀ (f : (Fin n → ℂ) → ℂ) (hf : AnalyticAt ℂ f (gaga13_basePoint p))
          (ht : AnalyticAt ℂ (fun z ↦ f (gaga13_basePoint p + z)) 0),
        eBase ⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds (gaga13_basePoint p)) f,
            ⟨f, hf, rfl⟩⟩ =
          ⟨@Filter.Germ.ofFun (Fin n → ℂ) ℂ (nhds 0)
              (fun z ↦ f (gaga13_basePoint p + z)),
            ⟨fun z ↦ f (gaga13_basePoint p + z), ht, rfl⟩⟩) ∧
      IsWeierstrassEmbedding ι₀ ∧
      (∀ Q, eFull (ι Q) = ι₀ (Q.map eBase.toRingHom)) ∧
      IsWeierstrassPolynomialAt P ∧ IsUnit u ∧ g = u * ι P := by
  obtain ⟨e, hval, hrep, hreg'⟩ := hreg
  obtain ⟨eB, hBval, hBrep⟩ := spec_germ_translation_equiv n (gaga13_basePoint p)
  have hnu' : ¬ IsUnit (e g) := fun h ↦ hnu (by simpa using h.map e.symm)
  obtain ⟨ι₀, P₀, hι₀, hP₀, v, hv⟩ := spec_preparation_transfer hreg' hnu'
  let ι : Polynomial (AnalyticGermAt n (gaga13_basePoint p)) →+* AnalyticGermAt (n + 1) p :=
    e.symm.toRingHom.comp (ι₀.comp (Polynomial.mapRingHom eB.toRingHom))
  have hιP : ι (P₀.map eB.symm.toRingHom) = e.symm (ι₀ P₀) := by
    have hcomp : eB.toRingHom.comp eB.symm.toRingHom = RingHom.id _ := by
      ext c
      simp
    simp only [ι, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_map, hcomp,
      Polynomial.map_id]
    rfl
  refine ⟨e, eB, ι₀, ι, P₀.map eB.symm.toRingHom, e.symm (↑v⁻¹ : AnalyticGerm (n + 1)),
    hval, hrep, hBval, hBrep, hι₀, ?_, ?_, ?_, ?_⟩
  · intro Q
    simp [ι]
  · obtain ⟨hmon, hdeg, hcoeff⟩ := hP₀
    have hmd := spec_polynomial_translation_monic_degree eB.symm P₀
    refine ⟨hmd.1.mpr hmon, hmd.2 ▸ hdeg, ?_⟩
    intro j hj
    rw [hmd.2] at hj
    rw [spec_polynomial_translation_coeff, ← hBval]
    simpa [analyticGermMaximalIdeal] using hcoeff j hj
  · exact (Units.isUnit v⁻¹).map e.symm
  · rw [hιP, ← hv]
    apply e.injective
    simp only [map_mul, RingEquiv.apply_symm_apply]
    rw [mul_comm, mul_assoc, Units.mul_inv, mul_one]

/-- Source: Gunning--Rossi, II.B, Theorem 2; regularity in the distinguished variable is
necessary for a transported coordinate Weierstrass factorization. -/
theorem spec_first_coordinate_no_transported_preparation_aux :
    let g : AnalyticGermAt 2 0 :=
      ⟨@Filter.Germ.ofFun (Fin 2 → ℂ) ℂ (nhds 0) (fun z ↦ z 0),
        ⟨fun z ↦ z 0,
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 => ℂ) 0).analyticAt 0, rfl⟩⟩
    ¬ ∃ (eFull : AnalyticGermAt 2 0 ≃+* AnalyticGerm 2)
        (eBase : AnalyticGermAt 1 0 ≃+* AnalyticGerm 1)
        (ι₀ : Polynomial (AnalyticGerm 1) →+* AnalyticGerm 2)
        (ι : Polynomial (AnalyticGermAt 1 0) →+* AnalyticGermAt 2 0)
        (P : Polynomial (AnalyticGermAt 1 0)) (u : AnalyticGermAt 2 0),
      (∀ a, (eFull a).1 = a.1) ∧ (∀ a, (eBase a).1 = a.1) ∧
      IsWeierstrassEmbedding ι₀ ∧
      (∀ Q, eFull (ι Q) = ι₀ (Q.map eBase.toRingHom)) ∧
      IsWeierstrassPolynomialAt P ∧ IsUnit u ∧ g = u * ι P := by
  intro g
  rintro ⟨eFull, eBase, ι₀, ι, P, u, hF, hB, hι₀, hsq, hP, hu, hg⟩
  -- Restrict germs at the origin of `ℂ²` to the last coordinate axis.
  have hz : (![0, 0] : Fin 2 → ℂ) = 0 := by
    ext i
    fin_cases i <;> rfl
  have hc : Continuous (fun w : ℂ ↦ (![0, w] : Fin 2 → ℂ)) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simp <;> fun_prop
  have hj : Tendsto (fun w : ℂ ↦ (![0, w] : Fin 2 → ℂ)) (𝓝 0) (𝓝 0) :=
    hz ▸ hc.tendsto 0
  let R : Germ (𝓝 (0 : Fin 2 → ℂ)) ℂ →+* Germ (𝓝 (0 : ℂ)) ℂ :=
    { toFun := fun F ↦ F.compTendsto _ hj
      map_one' := rfl
      map_mul' := fun F G ↦ Germ.inductionOn₂ F G fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun F G ↦ Germ.inductionOn₂ F G fun _ _ ↦ rfl }
  let R' : AnalyticGerm 2 →+* Germ (𝓝 (0 : ℂ)) ℂ := R.comp (analyticGermSubring 2).subtype
  have hR : ∀ (a : AnalyticGerm 2) (f : (Fin 2 → ℂ) → ℂ),
      a.1 = (f : Germ (𝓝 (0 : Fin 2 → ℂ)) ℂ) →
        R' a = ((fun w : ℂ ↦ f ![0, w]) : Germ (𝓝 (0 : ℂ)) ℂ) := by
    intro a f ha
    change R a.1 = _
    rw [ha]
    rfl
  -- The transported polynomial at the origin.
  set P₀ := P.map eBase.toRingHom with hP₀def
  have hd := spec_polynomial_translation_monic_degree eBase P
  have hmon : P₀.Monic := hd.1.2 hP.1
  have hcoeff : ∀ j < P₀.natDegree, R' (ι₀ (C (P₀.coeff j))) = 0 := by
    intro j hj
    rw [hd.2] at hj
    obtain ⟨f, -, hfa, hfb⟩ := hι₀.2.1 (P₀.coeff j)
    rw [hR _ _ hfb.symm]
    have hf0 : f 0 = 0 := by
      have h0 := hP.2.2 j hj
      have : analyticGermAtValue 1 0 (P.coeff j) = analyticGermValue 1 (P₀.coeff j) := by
        rw [hP₀def, Polynomial.coeff_map]
        change Germ.value (P.coeff j).1 = Germ.value (eBase (P.coeff j)).1
        rw [hB]
      rw [this] at h0
      change Germ.value (P₀.coeff j).1 = 0 at h0
      rw [← hfa] at h0
      exact h0
    have hconst : (fun w : ℂ ↦ f (fun i : Fin 1 ↦ (![0, w] : Fin 2 → ℂ) i.castSucc)) =
        fun _ ↦ 0 := by
      funext w
      have h0w : (fun i : Fin 1 ↦ (![0, w] : Fin 2 → ℂ) i.castSucc) = 0 := by
        funext i
        fin_cases i
        rfl
      rw [h0w, hf0]
    rw [hconst]
    rfl
  have hX : R' (ι₀ X) = ((fun w : ℂ ↦ w) : Germ (𝓝 (0 : ℂ)) ℂ) := by
    obtain ⟨h, hh, hXh⟩ := hι₀.2.2
    rw [hXh, hR _ _ hh]
    rfl
  have hpow : R' (ι₀ P₀) = ((fun w : ℂ ↦ w ^ P₀.natDegree) : Germ (𝓝 (0 : ℂ)) ℂ) := by
    conv_lhs => rw [hmon.as_sum]
    rw [map_add, map_add, map_sum, map_sum, map_pow, map_pow, hX]
    rw [Finset.sum_eq_zero, add_zero]
    · rfl
    · intro j hj
      rw [map_mul, map_mul, hcoeff j (Finset.mem_range.1 hj), zero_mul]
  -- Apply the restriction to the factorization.
  have hgz : R' (eFull g) = 0 := by
    rw [hR _ (fun z ↦ z 0) (by rw [hF])]
    rfl
  have hfac : eFull g = eFull u * ι₀ P₀ := by
    rw [hg, map_mul, hsq]
  have hunit : IsUnit (R' (eFull u)) :=
    ((spec_polynomial_translation_units eFull u).2 hu).map R'
  have h0 : ((fun w : ℂ ↦ w ^ P₀.natDegree) : Germ (𝓝 (0 : ℂ)) ℂ) = 0 := by
    rw [← hpow, ← hunit.mul_right_eq_zero, ← map_mul, ← hfac, hgz]
  have hev : ∀ᶠ w : ℂ in 𝓝 0, w = 0 := by
    have := Germ.coe_eq.1 h0
    filter_upwards [this] with w hw
    exact pow_eq_zero_iff (n := P₀.natDegree) (by rw [hd.2]; exact hP.2.1.ne') |>.1 hw
  have hne : ∀ᶠ w : ℂ in 𝓝[≠] 0, False := by
    filter_upwards [nhdsWithin_le_nhds hev, self_mem_nhdsWithin] with w hw hw'
    exact hw' hw
  exact hne.exists.elim fun _ h ↦ h

/-- Source: Bourbaki, *Algebra*, Ch. IV, §1, invariance under ring equivalence. -/
theorem spec_factors_translate_to_zero_aux {n k : ℕ} (p : Fin n → ℂ)
    (P : Fin k → Polynomial (AnalyticGermAt n p)) :
    ∃ e : AnalyticGermAt n p ≃+* AnalyticGerm n,
      (∀ i, Irreducible ((P i).map e.toRingHom) ↔ Irreducible (P i)) ∧
      (Pairwise (fun i j ↦ IsCoprime ((P i).map e.toRingHom) ((P j).map e.toRingHom)) ↔
        Pairwise (fun i j ↦ IsCoprime (P i) (P j))) := by
  obtain ⟨e, -, -⟩ := spec_germ_translation_equiv n p
  refine ⟨e, fun i ↦ spec_polynomial_translation_irreducible e (P i), ?_⟩
  constructor
  · intro h i j hij
    exact (spec_polynomial_translation_coprime e (P i) (P j)).mp (h hij)
  · intro h i j hij
    exact (spec_polynomial_translation_coprime e (P i) (P j)).mpr (h hij)

/-- Source: Gunning--Rossi, II.B, Definition 1; translation is a homeomorphism. -/
theorem spec_clean_regular_locus_translation_aux {n k : ℕ}
    (p : (Fin n → ℂ) × ℂ) (P : Fin k → (Fin n → ℂ) × ℂ → ℂ)
    (i : Fin k) :
    p ∈ closure {y | P i y = 0 ∧ (∀ j, j ≠ i → P j y ≠ 0) ∧ fderiv ℂ (P i) y ≠ 0} ↔
      (0 : (Fin n → ℂ) × ℂ) ∈ closure
        {z | P i (p + z) = 0 ∧ (∀ j, j ≠ i → P j (p + z) ≠ 0) ∧
          fderiv ℂ (fun y ↦ P i (p + y)) z ≠ 0} := by
  let S := {y | P i y = 0 ∧ (∀ j, j ≠ i → P j y ≠ 0) ∧ fderiv ℂ (P i) y ≠ 0}
  let e := Homeomorph.addLeft p
  have hpre : e ⁻¹' S =
      {z | P i (p + z) = 0 ∧ (∀ j, j ≠ i → P j (p + z) ≠ 0) ∧
        fderiv ℂ (fun y ↦ P i (p + y)) z ≠ 0} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, S, e, Homeomorph.coe_addLeft]
    rw [fderiv_comp_add_left]
  change p ∈ closure S ↔ (0 : (Fin n → ℂ) × ℂ) ∈ closure _
  rw [← hpre]
  rw [← e.preimage_closure]
  simp only [Set.mem_preimage, e, Homeomorph.coe_addLeft, add_zero]

/-- Source: Gunning--Rossi, Ch. III; Chirka, §§2--5, transported by translation. -/
theorem spec_point_mem_closure_clean_regular_factor_aux {n k : ℕ}
    (p : (Fin n → ℂ) × ℂ) {P : Fin k → (Fin n → ℂ) × ℂ → ℂ}
    (hP : ∀ i, AnalyticAt ℂ (P i) p ∧ IsIrreducibleAt (P i) p)
    (hcP : Pairwise (fun i j ↦ IsCoprimeAt (P i) (P j) p)) (i : Fin k) :
    p ∈ closure
      {y | P i y = 0 ∧ (∀ j, j ≠ i → P j y ≠ 0) ∧ fderiv ℂ (P i) y ≠ 0} := by
  let Q : Fin k → (Fin n → ℂ) × ℂ → ℂ := fun j z ↦ P j (p + z)
  have hsub : Tendsto (fun y : (Fin n → ℂ) × ℂ ↦ y - p) (nhds p) (nhds 0) := by
    exact (continuous_id.sub continuous_const).tendsto' p 0 (by simp)
  have hQ : ∀ j, AnalyticAt ℂ (Q j) 0 ∧ IsIrreducibleAt (Q j) 0 := by
    intro j
    refine ⟨(hP j).1.comp_of_eq (analyticAt_const.add analyticAt_id) (by simp), ?_⟩
    refine ⟨by simp [Q, (hP j).2.1], ?_⟩
    intro g h hg hh hfac
    let g' := fun y : (Fin n → ℂ) × ℂ ↦ g (y - p)
    let h' := fun y : (Fin n → ℂ) × ℂ ↦ h (y - p)
    have hg' : AnalyticAt ℂ g' p :=
      hg.comp_of_eq (analyticAt_id.sub analyticAt_const) (by simp)
    have hh' : AnalyticAt ℂ h' p :=
      hh.comp_of_eq (analyticAt_id.sub analyticAt_const) (by simp)
    have hfac' : P j =ᶠ[nhds p] fun y ↦ g' y * h' y := by
      have := hfac.comp_tendsto hsub
      filter_upwards [this] with y hy
      change P j (p + (y - p)) = g (y - p) * h (y - p) at hy
      simpa only [add_sub_cancel] using hy
    rcases (hP j).2.2 g' h' hg' hh' hfac' with hg0 | hh0
    · left
      simpa only [g', sub_self] using hg0
    · right
      simpa only [h', sub_self] using hh0
  have hcQ : Pairwise (fun a b ↦ IsCoprimeAt (Q a) (Q b) 0) := by
    intro a b hab
    intro hcommon
    rcases hcommon with ⟨q, r, s, hq, hr, hs, hq0, hQa, hQb⟩
    let q' := fun y : (Fin n → ℂ) × ℂ ↦ q (y - p)
    let r' := fun y : (Fin n → ℂ) × ℂ ↦ r (y - p)
    let s' := fun y : (Fin n → ℂ) × ℂ ↦ s (y - p)
    apply hcP hab
    refine ⟨q', r', s', ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hq.comp_of_eq (analyticAt_id.sub analyticAt_const) (by simp)
    · exact hr.comp_of_eq (analyticAt_id.sub analyticAt_const) (by simp)
    · exact hs.comp_of_eq (analyticAt_id.sub analyticAt_const) (by simp)
    · simpa only [q', sub_self] using hq0
    · have := hQa.comp_tendsto hsub
      filter_upwards [this] with y hy
      change P a (p + (y - p)) = q (y - p) * r (y - p) at hy
      simpa only [add_sub_cancel] using hy
    · have := hQb.comp_tendsto hsub
      filter_upwards [this] with y hy
      change P b (p + (y - p)) = q (y - p) * s (y - p) at hy
      simpa only [add_sub_cancel] using hy
  apply (spec_clean_regular_locus_translation_aux p P i).2
  exact AnalyticDivisorAlgebraic9.spec_zero_mem_closure_clean_regular_factor hQ hcQ i

end HodgeLean.Foundations.AnalyticDivisorAlgebraic13
