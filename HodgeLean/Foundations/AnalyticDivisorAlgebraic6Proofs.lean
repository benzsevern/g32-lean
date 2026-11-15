import HodgeLean.Foundations.AnalyticDivisorAlgebraic6Defs
import HodgeLean.Foundations.AnalyticDivisorAlgebraic5

noncomputable section
open Set Filter Topology Polynomial
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic6

open HodgeLean.Foundations.AnalyticDivisorAlgebraic5
open HodgeLean.Foundations.AnalyticDivisorAlgebraic3
variable {n : ℕ}

theorem spec_analyticGerm_ufd_zero_aux : UniqueFactorizationMonoid (AnalyticGerm 0) := by
  let e : AnalyticGerm 0 ≃+* ℂ := RingEquiv.ofBijective (analyticGermValue 0) ⟨by
    rintro ⟨g, f, hf, rfl⟩ ⟨h, k, hk, rfl⟩ hv
    apply Subtype.ext
    rw [Filter.Germ.coe_eq]
    filter_upwards [] with z
    have hz : z = 0 := Subsingleton.elim _ _
    change f 0 = k 0 at hv
    simpa [hz] using hv
  , by
    intro c
    refine ⟨⟨@Filter.Germ.ofFun (Fin 0 → ℂ) ℂ (nhds 0) (fun _ ↦ c),
      ⟨fun _ ↦ c, analyticAt_const, rfl⟩⟩, ?_⟩
    change (@Filter.Germ.ofFun (Fin 0 → ℂ) ℂ (nhds 0) (fun _ ↦ c)).value = c
    simpa using (Filter.Germ.value_ofFun (fun _ : Fin 0 → ℂ ↦ c) (0 : Fin 0 → ℂ))⟩
  exact e.toMulEquiv.symm.uniqueFactorizationMonoid inferInstance

/-- Evaluation of a coordinate extension at the origin agrees with the original germ. -/
private theorem coordinateExtension_value {a : AnalyticGerm n} {b : AnalyticGerm (n + 1)}
    (h : IsCoordinateExtension a b) : analyticGermValue (n + 1) b = analyticGermValue n a := by
  obtain ⟨f, hf, ha, hb⟩ := h
  change b.1.value = a.1.value
  rw [← ha, ← hb]
  simp only [Filter.Germ.value_ofFun]
  rfl

/-- A distinguished polynomial has value zero after the canonical substitution. -/
private theorem weierstrassEmbedding_value
    (ι : Polynomial (AnalyticGerm n) →+* AnalyticGerm (n + 1))
    (hι : IsWeierstrassEmbedding ι) (P : Polynomial (AnalyticGerm n)) :
    analyticGermValue (n + 1) (ι P) = analyticGermValue n (P.coeff 0) := by
  have hmap : (analyticGermValue (n + 1)).comp ι =
      Polynomial.eval₂RingHom (analyticGermValue n) 0 := by
    apply Polynomial.ringHom_ext
    · intro a
      simpa only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
        using coordinateExtension_value (hι.2.1 a)
    · obtain ⟨h, hh, hX⟩ := hι.2.2
      change analyticGermValue (n + 1) (ι X) = _
      rw [hX]
      change h.1.value = _
      rw [hh]
      simp only [Filter.Germ.value_ofFun, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
      rfl
  have h := RingHom.congr_fun hmap P
  simpa only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_at_zero] using h

/-- The constant unit is regular of order zero, which is allowed by `IsRegularInLast`. -/
theorem regularInLast_one : IsRegularInLast (1 : AnalyticGerm (n + 1)) := by
  refine ⟨fun _ ↦ 1, analyticAt_const, rfl, ?_⟩
  have h : analyticOrderAt (fun _ : ℂ ↦ (1 : ℂ)) 0 = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr one_ne_zero)
  rw [h]
  exact ENat.zero_ne_top

/-- The frozen preparation statement fails for the constant unit: its proposed positive-degree
polynomial vanishes at the origin, whereas a unit cannot vanish there.
Source: Gunning--Rossi, *Analytic Functions of Several Complex Variables*, II.B, Definition 2. -/
theorem not_preparation_transfer_one :
    ¬ ∃ (ι : Polynomial (AnalyticGerm n) →+* AnalyticGerm (n + 1))
      (P : Polynomial (AnalyticGerm n)),
      IsWeierstrassEmbedding ι ∧ IsWeierstrassPolynomial P ∧
        Associated (1 : AnalyticGerm (n + 1)) (ι P) := by
  rintro ⟨ι, P, hι, hP, ha⟩
  have hzero : analyticGermValue n (P.coeff 0) = 0 := hP.2.2 0 hP.2.1
  have hu := (ha.isUnit isUnit_one).map (analyticGermValue (n + 1))
  rw [weierstrassEmbedding_value ι hι P, hzero] at hu
  exact not_isUnit_zero hu

private theorem coordinateExtension_unique {a : AnalyticGerm n}
    {b c : AnalyticGerm (n + 1)} (hb : IsCoordinateExtension a b)
    (hc : IsCoordinateExtension a c) : b = c := by
  obtain ⟨f, hf, hfa, hfb⟩ := hb
  obtain ⟨g, hg, hga, hgc⟩ := hc
  have hfg : f =ᶠ[nhds 0] g := Filter.Germ.coe_eq.mp (hfa.trans hga.symm)
  have ht : Tendsto (fun z : Fin (n + 1) → ℂ ↦ fun i : Fin n ↦ z i.castSucc)
      (nhds 0) (nhds 0) := by
    have hcont : Continuous (fun z : Fin (n + 1) → ℂ ↦ fun i : Fin n ↦ z i.castSucc) :=
      continuous_pi fun i ↦ continuous_apply i.castSucc
    exact hcont.continuousAt
  apply Subtype.ext
  rw [← hfb, ← hgc, Filter.Germ.coe_eq]
  exact ht.eventually hfg

/-- The representative-based conditions determine the polynomial substitution map uniquely. -/
theorem weierstrassEmbedding_unique
    {ι κ : Polynomial (AnalyticGerm n) →+* AnalyticGerm (n + 1)}
    (hι : IsWeierstrassEmbedding ι) (hκ : IsWeierstrassEmbedding κ) : ι = κ := by
  apply Polynomial.ringHom_ext
  · intro a
    exact coordinateExtension_unique (hι.2.1 a) (hκ.2.1 a)
  · obtain ⟨b, hb, hXb⟩ := hι.2.2
    obtain ⟨c, hc, hXc⟩ := hκ.2.2
    rw [hXb, hXc]
    exact Subtype.ext (hb.trans hc.symm)

private def germPrecompRingHom {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (φ : X → Y) {x : X} {y : Y} (hφ : Tendsto φ (nhds x) (nhds y)) :
    Filter.Germ (nhds y) ℂ →+* Filter.Germ (nhds x) ℂ where
  toFun g := g.compTendsto φ hφ
  map_one' := rfl
  map_mul' g h := Filter.Germ.inductionOn g fun _ ↦ Filter.Germ.inductionOn h fun _ ↦ rfl
  map_zero' := rfl
  map_add' g h := Filter.Germ.inductionOn g fun _ ↦ Filter.Germ.inductionOn h fun _ ↦ rfl

private theorem continuousLinearEquiv_tendsto_zero
    (L : (Fin (n + 1) → ℂ) ≃L[ℂ] (Fin (n + 1) → ℂ)) :
    Tendsto L (nhds 0) (nhds 0) := by
  have h := (L.continuous.continuousAt : ContinuousAt L (0 : Fin (n + 1) → ℂ))
  change Tendsto L (nhds 0) (nhds (L 0)) at h
  simpa using h

private theorem germPrecomp_linear_symm
    (L : (Fin (n + 1) → ℂ) ≃L[ℂ] (Fin (n + 1) → ℂ))
    (g : Filter.Germ (nhds (0 : Fin (n + 1) → ℂ)) ℂ) :
    germPrecompRingHom L.symm (continuousLinearEquiv_tendsto_zero L.symm)
        (germPrecompRingHom L (continuousLinearEquiv_tendsto_zero L) g) = g := by
  induction g using Filter.Germ.inductionOn with
  | _ f =>
      change (↑(fun z ↦ f (L (L.symm z))) :
        Filter.Germ (nhds (0 : Fin (n + 1) → ℂ)) ℂ) = ↑f
      rw [Filter.Germ.coe_eq]
      exact Eventually.of_forall fun z ↦ by simp

private def analyticGermLinearEquiv
    (L : (Fin (n + 1) → ℂ) ≃L[ℂ] (Fin (n + 1) → ℂ)) :
    AnalyticGerm (n + 1) ≃+* AnalyticGerm (n + 1) where
  toFun g := ⟨germPrecompRingHom L
      (continuousLinearEquiv_tendsto_zero L) g.1, by
    obtain ⟨f, hf, hfg⟩ := g.2
    have hfL : AnalyticAt ℂ f (L 0) := by simpa using hf
    refine ⟨fun z ↦ f (L z), hfL.comp (L.analyticAt 0), ?_⟩
    change (↑(fun z ↦ f (L z)) : Filter.Germ (nhds (0 : Fin (n + 1) → ℂ)) ℂ) =
      germPrecompRingHom L (continuousLinearEquiv_tendsto_zero L) g.1
    rw [← hfg]
    rfl⟩
  invFun g := ⟨germPrecompRingHom L.symm
      (continuousLinearEquiv_tendsto_zero L.symm) g.1, by
    obtain ⟨f, hf, hfg⟩ := g.2
    have hfL : AnalyticAt ℂ f (L.symm 0) := by simpa using hf
    refine ⟨fun z ↦ f (L.symm z), hfL.comp (L.symm.analyticAt 0), ?_⟩
    change (↑(fun z ↦ f (L.symm z)) :
      Filter.Germ (nhds (0 : Fin (n + 1) → ℂ)) ℂ) =
      germPrecompRingHom L.symm (continuousLinearEquiv_tendsto_zero L.symm) g.1
    rw [← hfg]
    rfl⟩
  left_inv g := by
    apply Subtype.ext
    exact germPrecomp_linear_symm L g.1
  right_inv g := by
    apply Subtype.ext
    exact germPrecomp_linear_symm L.symm g.1
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

private def splitCoordinates (n : ℕ) :
    (Fin (n + 1) → ℂ) ≃L[ℂ] ((Fin n → ℂ) × ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toEquiv := (Fin.snocEquiv (fun _ : Fin (n + 1) ↦ ℂ)).symm.trans
        (Equiv.prodComm _ _)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }

private theorem splitCoordinates_tendsto (n : ℕ) :
    Tendsto (splitCoordinates n) (nhds 0) (nhds 0) := by
  simpa only [ContinuousAt, map_zero] using
    (splitCoordinates n).continuous.continuousAt (x := 0)

private theorem splitCoordinates_symm_tendsto (n : ℕ) :
    Tendsto (splitCoordinates n).symm (nhds 0) (nhds 0) := by
  simpa only [ContinuousAt, map_zero] using
    (splitCoordinates n).symm.continuous.continuousAt (x := 0)

private def splitGermEquiv (n : ℕ) :
    AnalyticGerm (n + 1) ≃+* ProductAnalyticGerm n where
  toFun g := ⟨germPrecompRingHom (splitCoordinates n).symm
      (splitCoordinates_symm_tendsto n) g.1, by
    obtain ⟨f, hf, hfg⟩ := g.2
    refine ⟨fun p ↦ f ((splitCoordinates n).symm p), ?_, ?_⟩
    · exact (show AnalyticAt ℂ f ((splitCoordinates n).symm 0) by simpa using hf).comp
        ((splitCoordinates n).symm.analyticAt 0)
    · change _ = germPrecompRingHom _ _ g.1
      rw [← hfg]
      rfl⟩
  invFun g := ⟨germPrecompRingHom (splitCoordinates n)
      (splitCoordinates_tendsto n) g.1, by
    obtain ⟨f, hf, hfg⟩ := g.2
    refine ⟨fun z ↦ f (splitCoordinates n z), ?_, ?_⟩
    · exact (show AnalyticAt ℂ f (splitCoordinates n 0) by simpa using hf).comp
        ((splitCoordinates n).analyticAt 0)
    · change _ = germPrecompRingHom _ _ g.1
      rw [← hfg]
      rfl⟩
  left_inv g := by
    apply Subtype.ext
    obtain ⟨f, hf, hfg⟩ := g.2
    change germPrecompRingHom _ _ (germPrecompRingHom _ _ g.1) = g.1
    rw [← hfg]
    change (↑(fun z ↦ f ((splitCoordinates n).symm (splitCoordinates n z))) :
      Filter.Germ (nhds (0 : Fin (n + 1) → ℂ)) ℂ) = ↑f
    congr 1
    funext z
    rw [ContinuousLinearEquiv.symm_apply_apply]
  right_inv g := by
    apply Subtype.ext
    obtain ⟨f, hf, hfg⟩ := g.2
    change germPrecompRingHom _ _ (germPrecompRingHom _ _ g.1) = g.1
    rw [← hfg]
    change (↑(fun p ↦ f (splitCoordinates n ((splitCoordinates n).symm p))) :
      Filter.Germ (nhds (0 : (Fin n → ℂ) × ℂ)) ℂ) = ↑f
    congr 1
    funext p
    rw [ContinuousLinearEquiv.apply_symm_apply]
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

open HodgeLean.Foundations.AnalyticDivisorAlgebraic4

/-- An analytic germ is a unit precisely when its value is nonzero. -/
theorem analyticGerm_isUnit_iff (g : AnalyticGerm n) :
    IsUnit g ↔ analyticGermValue n g ≠ 0 := by
  constructor
  · intro h
    exact (h.map (analyticGermValue n)).ne_zero
  · obtain ⟨f, hf, hfg⟩ := g.2
    intro h
    have hf0 : f 0 ≠ 0 := by
      change g.1.value ≠ 0 at h
      rw [← hfg, Filter.Germ.value_ofFun] at h
      exact h
    let k : AnalyticGerm n := ⟨↑(fun z ↦ (f z)⁻¹), fun z ↦ (f z)⁻¹, hf.inv hf0, rfl⟩
    have hk : g * k = 1 := by
      apply Subtype.ext
      change g.1 * k.1 = 1
      rw [← hfg]
      apply Filter.Germ.coe_eq.mpr
      filter_upwards [hf.continuousAt.eventually_ne hf0] with z hz
      exact mul_inv_cancel₀ hz
    exact isUnit_iff_exists_inv.mpr ⟨k, hk⟩

private def baseToProduct (n : ℕ) : AnalyticGerm n →+* ProductAnalyticGerm n where
  toFun g := ⟨germPrecompRingHom Prod.fst continuous_fst.continuousAt g.1, by
    obtain ⟨f, hf, hfg⟩ := g.2
    refine ⟨fun p ↦ f p.1, hf.comp_of_eq analyticAt_fst rfl, ?_⟩
    change _ = germPrecompRingHom _ _ g.1
    rw [← hfg]
    rfl⟩
  map_one' := rfl
  map_zero' := rfl
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

private def productVariable (n : ℕ) : ProductAnalyticGerm n :=
  ⟨↑(fun p : (Fin n → ℂ) × ℂ ↦ p.2), _, analyticAt_snd, rfl⟩

private def productPolynomial (n : ℕ) :
    Polynomial (AnalyticGerm n) →+* ProductAnalyticGerm n :=
  Polynomial.eval₂RingHom (baseToProduct n) (productVariable n)

private theorem productPolynomial_sum {d : ℕ} (b : Fin d → AnalyticGerm n)
    (f : Fin d → (Fin n → ℂ) → ℂ) (hf : ∀ j, (↑(f j) : Filter.Germ (nhds (0 : Fin n → ℂ)) ℂ) = (b j).1) :
    (productPolynomial n (∑ j, C (b j) * X ^ (j : ℕ))).1 =
      ↑(fun p : (Fin n → ℂ) × ℂ ↦ ∑ j, f j p.1 * p.2 ^ (j : ℕ)) := by
  change (productAnalyticGermSubring n).subtype (productPolynomial n
    (∑ j, C (b j) * X ^ (j : ℕ))) = _
  simp only [map_sum, map_mul, map_pow, productPolynomial, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_C, Polynomial.eval₂_X, Subring.coe_mul, Subring.coe_pow]
  change (∑ j, (baseToProduct n (b j)).1 * (productVariable n).1 ^ (j : ℕ)) = _
  have he : ∀ j, (baseToProduct n (b j)).1 =
      (↑(fun p : (Fin n → ℂ) × ℂ ↦ f j p.1) :
        Filter.Germ (nhds (0 : (Fin n → ℂ) × ℂ)) ℂ) := by
    intro j
    change germPrecompRingHom _ _ (b j).1 = _
    rw [← hf j]
    rfl
  simp only [he]
  let c := Filter.Germ.coeRingHom (R := ℂ) (nhds (0 : (Fin n → ℂ) × ℂ))
  change (∑ j, c (fun p ↦ f j p.1 * p.2 ^ (j : ℕ))) =
    c (fun p ↦ ∑ j, f j p.1 * p.2 ^ (j : ℕ))
  rw [← map_sum]
  congr 1
  funext p
  exact Finset.sum_apply p _ _

private theorem productPolynomial_injective (n : ℕ) :
    Function.Injective (productPolynomial n) := by
  apply (injective_iff_map_eq_zero _).2
  intro P hP
  let d := P.natDegree + 1
  choose f hf hfg using fun j : Fin d ↦ (P.coeff j).2
  have hsum : P = ∑ j : Fin d, C (P.coeff j) * X ^ (j : ℕ) := by
    exact P.as_sum_range_C_mul_X_pow.trans (Fin.sum_univ_eq_sum_range
      (fun j ↦ C (P.coeff j) * X ^ j) d).symm
  have heq : ∀ᶠ p : (Fin n → ℂ) × ℂ in nhds 0,
      (0 : ℂ) * monicInLast (fun _ _ ↦ 0 : Fin d → (Fin n → ℂ) → ℂ) p +
        ∑ j, f j p.1 * p.2 ^ (j : ℕ) = 0 := by
    have h := congrArg Subtype.val hP
    rw [hsum, productPolynomial_sum _ f hfg] at h
    exact (Filter.Germ.coe_eq.mp h).mono fun p hp ↦ by simpa using hp
  have hc := (spec_weierstrass_division_unique (fun _ ↦ continuousAt_const)
    (fun _ ↦ rfl) analyticAt_const heq).2
  apply Polynomial.ext
  intro j
  rw [coeff_zero]
  by_cases hj : j < d
  · have h := Filter.Germ.coe_eq.mpr (hc ⟨j, hj⟩)
    apply Subtype.ext
    exact (hfg ⟨j, hj⟩).symm.trans h
  · exact coeff_eq_zero_of_natDegree_lt (by dsimp [d] at hj; omega)

private def canonicalEmbedding (n : ℕ) :
    Polynomial (AnalyticGerm n) →+* AnalyticGerm (n + 1) :=
  (splitGermEquiv n).symm.toRingHom.comp (productPolynomial n)

private theorem canonicalEmbedding_spec (n : ℕ) :
    IsWeierstrassEmbedding (canonicalEmbedding n) := by
  refine ⟨(splitGermEquiv n).symm.injective.comp (productPolynomial_injective n), ?_, ?_⟩
  · intro a
    obtain ⟨f, hf, hfa⟩ := a.2
    refine ⟨f, hf, hfa, ?_⟩
    simp only [canonicalEmbedding, RingHom.comp_apply, productPolynomial,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    change _ = germPrecompRingHom (splitCoordinates n) (splitCoordinates_tendsto n)
      (germPrecompRingHom Prod.fst continuous_fst.continuousAt a.1)
    rw [← hfa]
    rfl
  · refine ⟨canonicalEmbedding n X, ?_, rfl⟩
    simp only [canonicalEmbedding, RingHom.comp_apply, RingEquiv.coe_toRingHom,
      productPolynomial, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    rfl

private def distinguishedPolynomial {d : ℕ} (a : Fin d → AnalyticGerm n) :
    Polynomial (AnalyticGerm n) := X ^ d + ∑ j, C (a j) * X ^ (j : ℕ)

private theorem distinguishedPolynomial_degree {d : ℕ} (a : Fin d → AnalyticGerm n) :
    (distinguishedPolynomial a).Monic ∧ (distinguishedPolynomial a).natDegree = d := by
  have hlt : (∑ j : Fin d, C (a j) * X ^ (j : ℕ)).degree <
      (X ^ d : Polynomial (AnalyticGerm n)).degree := by
    rw [degree_X_pow]
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).2 fun j _ ↦ ?_
    exact lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) (by exact_mod_cast j.2)
  exact ⟨(monic_X_pow d).add_of_left hlt,
    (natDegree_add_eq_left_of_degree_lt hlt).trans (natDegree_X_pow d)⟩

private theorem distinguishedPolynomial_coeff {d : ℕ} (a : Fin d → AnalyticGerm n)
    (j : Fin d) : (distinguishedPolynomial a).coeff j = a j := by
  simp [distinguishedPolynomial, coeff_X_pow, ne_of_lt j.2,
    coeff_C_mul_X_pow, Fin.val_inj]

private theorem distinguishedPolynomial_spec {d : ℕ} (a : Fin d → AnalyticGerm n)
    (hd : 0 < d) (ha : ∀ j, analyticGermValue n (a j) = 0) :
    IsWeierstrassPolynomial (distinguishedPolynomial a) := by
  obtain ⟨hm, hdeg⟩ := distinguishedPolynomial_degree a
  refine ⟨hm, by simpa only [hdeg] using hd, ?_⟩
  intro j hj
  rw [hdeg] at hj
  change analyticGermValue n ((distinguishedPolynomial a).coeff j) = 0
  rw [distinguishedPolynomial_coeff a ⟨j, hj⟩]
  exact ha _

private theorem distinguishedPolynomial_rep {d : ℕ} (a : Fin d → AnalyticGerm n)
    (f : Fin d → (Fin n → ℂ) → ℂ)
    (hf : ∀ j, (↑(f j) : Filter.Germ (nhds (0 : Fin n → ℂ)) ℂ) = (a j).1) :
    (productPolynomial n (distinguishedPolynomial a)).1 =
      ↑(monicInLast f) := by
  change (productPolynomial n (X ^ d + ∑ j, C (a j) * X ^ (j : ℕ))).1 = _
  simp only [map_add, map_pow, Subring.coe_add, Subring.coe_pow]
  rw [show productPolynomial n X = productVariable n from Polynomial.eval₂_X _ _]
  change (productVariable n).1 ^ d +
    (productPolynomial n (∑ j, C (a j) * X ^ (j : ℕ))).1 = _
  rw [productPolynomial_sum a f hf]
  rfl

theorem spec_preparation_transfer_aux {g : AnalyticGerm (n + 1)}
    (hg : IsRegularInLast g) (hnu : ¬ IsUnit g) :
    ∃ (ι : Polynomial (AnalyticGerm n) →+* AnalyticGerm (n + 1))
      (P : Polynomial (AnalyticGerm n)),
      IsWeierstrassEmbedding ι ∧ IsWeierstrassPolynomial P ∧ Associated g (ι P) := by
  obtain ⟨f, hf, hfg, hord⟩ := hg
  let F : (Fin n → ℂ) × ℂ → ℂ := fun p ↦ f ((splitCoordinates n).symm p)
  have hF : AnalyticAt ℂ F 0 :=
    hf.comp_of_eq ((splitCoordinates n).symm.analyticAt 0) (map_zero _)
  have haxis : (fun w : ℂ ↦ F (0, w)) = fun w ↦ f (Pi.single (Fin.last n) w) := by
    funext w
    change f ((splitCoordinates n).symm (0, w)) = f (Pi.single (Fin.last n) w)
    apply congrArg f
    ext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simp [splitCoordinates, Pi.single_apply]
    · simp [splitCoordinates, Fin.init, Pi.single_apply, Fin.castSucc_ne_last]
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp hord
  have horder : analyticOrderAt (fun w ↦ F (0, w)) 0 = d := by
    rw [haxis]
    exact hd.symm
  have hf0 : f 0 = 0 := by
    by_contra h
    apply hnu
    apply (analyticGerm_isUnit_iff g).2
    change g.1.value ≠ 0
    rw [← hfg, Filter.Germ.value_ofFun]
    exact h
  have hdpos : 0 < d := by
    by_contra hn
    have hdz : d = 0 := by omega
    have hFa : AnalyticAt ℂ (fun w ↦ F (0, w)) 0 :=
      hF.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
    have he := analyticOrderAt_eq_zero.mp (horder.trans (by simp [hdz]))
    rcases he with he | he
    · exact he hFa
    · exact he (by change f ((splitCoordinates n).symm 0) = 0; simpa using hf0)
  obtain ⟨u, hu, hu0, a, ha, hfac⟩ := spec_weierstrass_preparation hF horder
  let A : Fin d → AnalyticGerm n := fun j ↦ ⟨↑(a j), a j, (ha j).1, rfl⟩
  let U : AnalyticGerm (n + 1) := (splitGermEquiv n).symm
    ⟨↑u, u, hu, rfl⟩
  have hU : IsUnit U := by
    apply (analyticGerm_isUnit_iff U).2
    change (↑(fun z ↦ u (splitCoordinates n z)) :
      Filter.Germ (nhds (0 : Fin (n + 1) → ℂ)) ℂ).value ≠ 0
    simpa using hu0
  have hprod : g = U * canonicalEmbedding n (distinguishedPolynomial A) := by
    apply (splitGermEquiv n).injective
    rw [map_mul]
    apply Subtype.ext
    change (germPrecompRingHom _ _ g.1) =
      (splitGermEquiv n U).1 *
        (splitGermEquiv n (canonicalEmbedding n (distinguishedPolynomial A))).1
    rw [← hfg]
    have he : ∀ b, (splitGermEquiv n) ((splitGermEquiv n).symm.toRingHom b) = b :=
      fun b ↦ (splitGermEquiv n).apply_symm_apply b
    simp only [U, canonicalEmbedding, RingHom.comp_apply,
      RingEquiv.apply_symm_apply, he]
    rw [distinguishedPolynomial_rep A a (fun _ ↦ rfl)]
    exact Filter.Germ.coe_eq.mpr hfac
  refine ⟨canonicalEmbedding n, distinguishedPolynomial A, canonicalEmbedding_spec n,
    distinguishedPolynomial_spec A hdpos (fun j ↦ ?_), ?_⟩
  · change a j 0 = 0
    exact (ha j).2
  · rw [hprod]
    exact associated_unit_mul_left _ _ hU

private theorem weierstrass_representative {P : Polynomial (AnalyticGerm n)}
    (hP : IsWeierstrassPolynomial P) :
    ∃ a : Fin P.natDegree → (Fin n → ℂ) → ℂ,
      (∀ j, AnalyticAt ℂ (a j) 0 ∧ a j 0 = 0) ∧
      (productPolynomial n P).1 = ↑(monicInLast a) := by
  choose a ha hrep using fun j : Fin P.natDegree ↦ (P.coeff j).2
  refine ⟨a, fun j ↦ ⟨ha j, ?_⟩, ?_⟩
  · have h := hP.2.2 j j.2
    change (P.coeff j).1.value = 0 at h
    rwa [← hrep j, Filter.Germ.value_ofFun] at h
  · have hsum : P = distinguishedPolynomial (fun j : Fin P.natDegree ↦ P.coeff j) := by
      exact hP.1.as_sum.trans (congrArg (fun r ↦ X ^ P.natDegree + r)
        (Fin.sum_univ_eq_sum_range (fun j ↦ C (P.coeff j) * X ^ j) P.natDegree).symm)
    exact (congrArg (fun Q ↦ (productPolynomial n Q).1) hsum).trans
      (distinguishedPolynomial_rep _ a hrep)

private theorem polynomial_sum_of_degree_lt {R : Polynomial (AnalyticGerm n)} {d : ℕ}
    (hR : R.degree < d) : R = ∑ j : Fin d, C (R.coeff j) * X ^ (j : ℕ) := by
  exact R.sum_C_mul_X_pow_eq.symm.trans
    (Polynomial.sum_fin (fun j a ↦ C a * X ^ j) (fun _ ↦ by simp) hR).symm

private theorem product_division_unique {P R : Polynomial (AnalyticGerm n)}
    (hP : IsWeierstrassPolynomial P) (hR : R.degree < P.natDegree)
    (q : ProductAnalyticGerm n)
    (he : q * productPolynomial n P + productPolynomial n R = 0) : q = 0 ∧ R = 0 := by
  obtain ⟨a, ha, hPa⟩ := weierstrass_representative hP
  obtain ⟨f, hf, hfq⟩ := q.2
  choose b hb hbR using fun j : Fin P.natDegree ↦ (R.coeff j).2
  have hsum := polynomial_sum_of_degree_lt hR
  have hRa : (productPolynomial n R).1 =
      ↑(fun p : (Fin n → ℂ) × ℂ ↦ ∑ j : Fin P.natDegree, b j p.1 * p.2 ^ (j : ℕ)) := by
    rw [hsum]
    exact productPolynomial_sum _ b hbR
  have hh := congrArg Subtype.val he
  change q.1 * (productPolynomial n P).1 + (productPolynomial n R).1 = 0 at hh
  rw [← hfq, hPa, hRa] at hh
  have hu := spec_weierstrass_division_unique (fun j ↦ (ha j).1.continuousAt)
    (fun j ↦ (ha j).2) hf (Filter.Germ.coe_eq.mp hh)
  constructor
  · apply Subtype.ext
    exact hfq.symm.trans (Filter.Germ.coe_eq.mpr hu.1)
  · rw [hsum]
    apply Finset.sum_eq_zero
    intro j _
    have hc : R.coeff j = 0 := Subtype.ext
      ((hbR j).symm.trans (Filter.Germ.coe_eq.mpr (hu.2 j)))
    simp only [hc, map_zero, zero_mul]

private theorem productPolynomial_dvd_iff {P Q : Polynomial (AnalyticGerm n)}
    (hP : IsWeierstrassPolynomial P) :
    productPolynomial n P ∣ productPolynomial n Q ↔ P ∣ Q := by
  constructor
  · rintro ⟨q, hq⟩
    have hdeg : (Q %ₘ P).degree < P.natDegree := by
      simpa only [P.degree_eq_natDegree hP.1.ne_zero] using degree_modByMonic_lt Q hP.1
    have h := congrArg (productPolynomial n) (modByMonic_add_div Q P)
    simp only [map_add, map_mul] at h
    have he : (productPolynomial n (Q /ₘ P) - q) * productPolynomial n P +
        productPolynomial n (Q %ₘ P) = 0 := by
      rw [hq] at h
      linear_combination h
    exact (modByMonic_eq_zero_iff_dvd hP.1).mp (product_division_unique hP hdeg _ he).2
  · exact fun h ↦ map_dvd (productPolynomial n) h

private theorem canonicalEmbedding_dvd_iff {P Q : Polynomial (AnalyticGerm n)}
    (hP : IsWeierstrassPolynomial P) :
    canonicalEmbedding n P ∣ canonicalEmbedding n Q ↔ P ∣ Q := by
  change (splitGermEquiv n).symm (productPolynomial n P) ∣
    (splitGermEquiv n).symm (productPolynomial n Q) ↔ _
  constructor
  · intro h
    apply (productPolynomial_dvd_iff hP).mp
    simpa only [RingEquiv.apply_symm_apply] using map_dvd (splitGermEquiv n) h
  · intro h
    exact map_dvd (splitGermEquiv n).symm ((productPolynomial_dvd_iff hP).mpr h)

private theorem canonicalEmbedding_mul_cancel {P : Polynomial (AnalyticGerm n)}
    (hP : IsWeierstrassPolynomial P) {a b : AnalyticGerm (n + 1)}
    (h : a * canonicalEmbedding n P = b * canonicalEmbedding n P) : a = b := by
  have he : ((splitGermEquiv n) (a - b)) * productPolynomial n P +
      productPolynomial n (0 : Polynomial (AnalyticGerm n)) = 0 := by
    have hh := congrArg (splitGermEquiv n) (sub_eq_zero.mpr h)
    have hc : (splitGermEquiv n) (canonicalEmbedding n P) = productPolynomial n P :=
      (splitGermEquiv n).apply_symm_apply _
    simpa only [map_sub, map_mul, hc, sub_mul, map_zero, add_zero] using hh
  have hz := (product_division_unique hP (by simp) _ he).1
  exact sub_eq_zero.mp ((splitGermEquiv n).injective (by simpa only [map_zero] using hz))

private theorem lastAxis_tendsto (n : ℕ) :
    Tendsto (fun w : ℂ ↦ Pi.single (Fin.last n) w) (nhds 0)
      (nhds (0 : Fin (n + 1) → ℂ)) := by
  simpa only [ContinuousAt, ContinuousLinearMap.single_apply, Pi.single_zero] using
    (ContinuousLinearMap.single ℂ (fun _ : Fin (n + 1) ↦ ℂ) (Fin.last n)).continuous.continuousAt (x := 0)

private theorem regularInLast_of_mul_left {g h : AnalyticGerm (n + 1)}
    (hr : IsRegularInLast (g * h)) : IsRegularInLast g := by
  obtain ⟨r, hr, hrep, hord⟩ := hr
  obtain ⟨f, hf, hfg⟩ := g.2
  obtain ⟨k, hk, hkh⟩ := h.2
  refine ⟨f, hf, hfg, ?_⟩
  intro ht
  apply hord
  apply analyticOrderAt_eq_top.mpr
  have he : r =ᶠ[nhds 0] fun z ↦ f z * k z := by
    apply Filter.Germ.coe_eq.mp
    change (↑r : Filter.Germ (nhds (0 : Fin (n + 1) → ℂ)) ℂ) = ↑f * ↑k
    rw [hfg, hkh]
    exact hrep
  filter_upwards [(lastAxis_tendsto n).eventually he, analyticOrderAt_eq_top.mp ht] with w hw hz
  rw [hw, hz, zero_mul]

private theorem canonicalEmbedding_regular {P : Polynomial (AnalyticGerm n)}
    (hP : IsWeierstrassPolynomial P) : IsRegularInLast (canonicalEmbedding n P) := by
  obtain ⟨a, ha, hPa⟩ := weierstrass_representative hP
  have hma : AnalyticAt ℂ (monicInLast a) 0 := by
    apply AnalyticAt.add (analyticAt_snd.pow _)
    exact Finset.analyticAt_fun_sum _ fun j _ ↦
      ((ha j).1.comp_of_eq analyticAt_fst rfl).mul (analyticAt_snd.pow _)
  refine ⟨fun z ↦ monicInLast a (splitCoordinates n z),
    hma.comp_of_eq ((splitCoordinates n).analyticAt 0) (map_zero _), ?_, ?_⟩
  · change _ = germPrecompRingHom (splitCoordinates n) (splitCoordinates_tendsto n)
      (productPolynomial n P).1
    rw [hPa]
    rfl
  · have he : (fun w : ℂ ↦ monicInLast a (splitCoordinates n (Pi.single (Fin.last n) w))) =
        fun w ↦ w ^ P.natDegree := by
      funext w
      have hsplit : splitCoordinates n (Pi.single (Fin.last n) w) = (0, w) := by
        ext j
        · simp [splitCoordinates, Fin.init, Pi.single_apply, Fin.castSucc_ne_last]
        · simp [splitCoordinates]
      rw [hsplit]
      simp [monicInLast, fun j ↦ (ha j).2]
    rw [he]
    change analyticOrderAt ((id : ℂ → ℂ) ^ P.natDegree) 0 ≠ ⊤
    rw [analyticOrderAt_pow analyticAt_id, analyticOrderAt_id]
    simpa using ENat.natCast_ne_top P.natDegree

private theorem weierstrass_not_isUnit {P : Polynomial (AnalyticGerm n)}
    (hP : IsWeierstrassPolynomial P) : ¬ IsUnit P := by
  intro h
  have he := hP.1.eq_one_of_isUnit h
  have hd := hP.2.1
  rw [he, natDegree_one] at hd
  omega

private theorem canonicalEmbedding_factor_unit {P Q R : Polynomial (AnalyticGerm n)}
    (hP : IsWeierstrassPolynomial P) (hfac : P = Q * R)
    (hQ : IsUnit (canonicalEmbedding n Q)) : IsUnit Q := by
  have hdiv : canonicalEmbedding n P ∣ canonicalEmbedding n R := by
    rw [hfac, map_mul]
    exact (associated_unit_mul_left _ _ hQ).dvd
  obtain ⟨T, hT⟩ := (canonicalEmbedding_dvd_iff hP).mp hdiv
  have hmul : Q * T = 1 := by
    apply hP.1.isRegular.2
    change (Q * T) * P = 1 * P
    calc
      (Q * T) * P = Q * (P * T) := by ring
      _ = Q * R := by rw [← hT]
      _ = 1 * P := by rw [← hfac, one_mul]
  exact isUnit_iff_exists_inv.mpr ⟨T, hmul⟩

theorem spec_irreducible_transfer_aux
    (ι : Polynomial (AnalyticGerm n) →+* AnalyticGerm (n + 1))
    (hι : IsWeierstrassEmbedding ι) {P : Polynomial (AnalyticGerm n)}
    (hP : IsWeierstrassPolynomial P) : Irreducible P ↔ Irreducible (ι P) := by
  have hi : ι = canonicalEmbedding n := weierstrassEmbedding_unique hι (canonicalEmbedding_spec n)
  subst ι
  constructor
  · intro hI
    refine ⟨?_, ?_⟩
    · intro hu
      have hz : analyticGermValue (n + 1) (canonicalEmbedding n P) = 0 := by
        rw [weierstrassEmbedding_value _ (canonicalEmbedding_spec n)]
        exact hP.2.2 0 hP.2.1
      exact ((analyticGerm_isUnit_iff _).mp hu) hz
    · intro a b hab
      by_cases hau : IsUnit a
      · exact Or.inl hau
      right
      have har : IsRegularInLast a := regularInLast_of_mul_left
        (hab ▸ canonicalEmbedding_regular hP)
      obtain ⟨κ, Q, hκ, hQ, haQ⟩ := spec_preparation_transfer_aux har hau
      have hk : κ = canonicalEmbedding n :=
        weierstrassEmbedding_unique hκ (canonicalEmbedding_spec n)
      subst κ
      have hdiv : Q ∣ P := (canonicalEmbedding_dvd_iff hQ).mp
        (haQ.symm.dvd.trans ⟨b, hab⟩)
      obtain ⟨R, hR⟩ := hdiv
      have hRu : IsUnit R := (hI.isUnit_or_isUnit hR).resolve_left (weierstrass_not_isUnit hQ)
      have hPa : Associated (canonicalEmbedding n P) a := by
        apply Associated.trans _ haQ.symm
        rw [hR, map_mul]
        exact associated_mul_unit_left _ _ (hRu.map (canonicalEmbedding n))
      obtain ⟨u, hu⟩ := hPa
      have hbu : b * (u : AnalyticGerm (n + 1)) = 1 := by
        apply canonicalEmbedding_mul_cancel hP
        calc
          (b * ↑u) * canonicalEmbedding n P = (canonicalEmbedding n P * ↑u) * b := by ring
          _ = a * b := by rw [hu]
          _ = 1 * canonicalEmbedding n P := by rw [← hab, one_mul]
      exact isUnit_iff_exists_inv.mpr ⟨↑u, hbu⟩
  · intro hI
    refine ⟨weierstrass_not_isUnit hP, ?_⟩
    intro Q R hQR
    have h := hI.isUnit_or_isUnit (by simpa only [map_mul] using congrArg (canonicalEmbedding n) hQR)
    rcases h with h | h
    · exact Or.inl (canonicalEmbedding_factor_unit hP hQR h)
    · exact Or.inr (canonicalEmbedding_factor_unit hP (hQR.trans (mul_comm _ _)) h)

theorem spec_finSucc_product_equiv_aux :
    ∃ e : AnalyticGerm (n + 1) ≃+* ProductAnalyticGerm n,
      e ⟨@Filter.Germ.ofFun (Fin (n + 1) → ℂ) ℂ (nhds 0)
          (fun z ↦ z (Fin.last n)),
        ⟨fun z ↦ z (Fin.last n),
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + 1) => ℂ)
            (Fin.last n)).analyticAt 0, rfl⟩⟩ =
        ⟨@Filter.Germ.ofFun ((Fin n → ℂ) × ℂ) ℂ (nhds 0) (fun p ↦ p.2),
          ⟨fun p ↦ p.2, analyticAt_snd, rfl⟩⟩ := by
  refine ⟨splitGermEquiv n, ?_⟩
  apply Subtype.ext
  change (↑(fun p : (Fin n → ℂ) × ℂ ↦
    ((splitCoordinates n).symm p) (Fin.last n)) : Filter.Germ (nhds (0 : (Fin n → ℂ) × ℂ)) ℂ) =
    ↑(fun p : (Fin n → ℂ) × ℂ ↦ p.2)
  congr 1
  funext p
  exact Fin.snoc_last (α := fun _ : Fin (n + 1) ↦ ℂ) p.2 p.1

theorem spec_linearChange_automorphism_aux
    (L : (Fin (n + 1) → ℂ) ≃L[ℂ] (Fin (n + 1) → ℂ)) :
    ∃ e : AnalyticGerm (n + 1) ≃+* AnalyticGerm (n + 1),
      (∀ (g : AnalyticGerm (n + 1)) (f : (Fin (n + 1) → ℂ) → ℂ),
        AnalyticAt ℂ f 0 →
        (@Filter.Germ.ofFun (Fin (n + 1) → ℂ) ℂ (nhds 0) f) = g.1 →
        (@Filter.Germ.ofFun (Fin (n + 1) → ℂ) ℂ (nhds 0) (fun z ↦ f (L z))) =
          (e g).1) ∧
      (∀ g, Irreducible (e g) ↔ Irreducible g) ∧
      (∀ g h, Associated (e g) (e h) ↔ Associated g h) := by
  refine ⟨analyticGermLinearEquiv L, ?_, ?_, ?_⟩
  · intro g f hf hfg
    dsimp only [analyticGermLinearEquiv]
    change (↑(fun z ↦ f (L z)) :
      Filter.Germ (nhds (0 : Fin (n + 1) → ℂ)) ℂ) =
      germPrecompRingHom L (continuousLinearEquiv_tendsto_zero L) g.1
    rw [← hfg]
    rfl
  · intro g
    exact MulEquiv.irreducible_iff (analyticGermLinearEquiv L)
  · intro g h
    constructor
    · intro ha
      simpa using ha.map (analyticGermLinearEquiv L).symm
    · exact fun ha ↦ ha.map (analyticGermLinearEquiv L)

theorem spec_exists_linearChange_regular_aux {g : AnalyticGerm (n + 1)}
    (hg0 : g ≠ 0) (hgu : ¬ IsUnit g) :
    ∃ (L : (Fin (n + 1) → ℂ) ≃L[ℂ] (Fin (n + 1) → ℂ))
      (e : AnalyticGerm (n + 1) ≃+* AnalyticGerm (n + 1)),
      (∀ (a : AnalyticGerm (n + 1)) (f : (Fin (n + 1) → ℂ) → ℂ),
        AnalyticAt ℂ f 0 →
        (@Filter.Germ.ofFun (Fin (n + 1) → ℂ) ℂ (nhds 0) f) = a.1 →
        (@Filter.Germ.ofFun (Fin (n + 1) → ℂ) ℂ (nhds 0) (fun z ↦ f (L z))) =
      (e a).1) ∧
      IsRegularInLast (e g) := by
  obtain ⟨f, hf, hfg⟩ := g.2
  have hfnz : ¬ ∀ᶠ z in nhds 0, f z = 0 := by
    intro hz
    apply hg0
    apply Subtype.ext
    rw [← hfg]
    exact Filter.Germ.coe_eq.mpr hz
  obtain ⟨m, -, -, hd⟩ := spec_exists_multiplicity hf hfnz
  simp only [zero_add] at hd
  let v₀ : Fin (n + 1) → ℂ := Pi.single (Fin.last n) 1
  have hv₀ : v₀ ≠ 0 := by
    intro h
    have := congrFun h (Fin.last n)
    simpa [v₀] using this
  obtain ⟨v, hv0, hv⟩ := hd.inter_open_nonempty {v | v ≠ 0} isOpen_ne ⟨v₀, hv₀⟩
  obtain ⟨L, hL⟩ := SeparatingDual.exists_continuousLinearEquiv_apply_eq
    (R := ℂ) hv₀ hv0
  obtain ⟨e, he, -, -⟩ := spec_linearChange_automorphism_aux L
  refine ⟨L, e, he, fun z ↦ f (L z), hf.comp_of_eq (L.analyticAt 0) (map_zero L),
    he g f hf hfg, ?_⟩
  have hline : (fun w : ℂ ↦ f (L (Pi.single (Fin.last n) w))) =
      fun w ↦ f (w • v) := by
    funext w
    rw [← hL, ← map_smul]
    congr 2
    ext i
    simp [v₀, Pi.single_apply]
  rw [hline, show analyticOrderAt (fun w : ℂ ↦ f (w • v)) 0 = m from hv]
  exact ENat.natCast_ne_top m

private theorem preparation_canonical {g : AnalyticGerm (n + 1)}
    (hr : IsRegularInLast g) (hu : ¬ IsUnit g) :
    ∃ P : Polynomial (AnalyticGerm n), IsWeierstrassPolynomial P ∧
      Associated g (canonicalEmbedding n P) := by
  obtain ⟨ι, P, hι, hP, hg⟩ := spec_preparation_transfer_aux hr hu
  rw [weierstrassEmbedding_unique hι (canonicalEmbedding_spec n)] at hg
  exact ⟨P, hP, hg⟩

/-- Nonzero analytic germs cancel, by preparation after a linear change. -/
theorem analyticGerm_noZeroDivisors_succ : NoZeroDivisors (AnalyticGerm (n + 1)) := by
  constructor
  intro a b hab
  by_cases ha : a = 0
  · exact Or.inl ha
  right
  by_cases hu : IsUnit a
  · exact (hu.mul_right_inj).mp (hab.trans (mul_zero a).symm)
  obtain ⟨L, e, he, hr⟩ := spec_exists_linearChange_regular_aux ha hu
  have heu : ¬ IsUnit (e a) := fun h ↦ hu (by simpa using h.map e.symm)
  obtain ⟨P, hP, u, hPu⟩ := preparation_canonical hr heu
  have hz : e b * canonicalEmbedding n P = 0 * canonicalEmbedding n P := by
    rw [← hPu, ← mul_assoc, mul_comm (e b) (e a), ← map_mul, hab,
      map_zero, zero_mul, zero_mul]
  have hb := canonicalEmbedding_mul_cancel hP hz
  exact e.injective (hb.trans (map_zero e).symm)

private theorem regularInLast_of_dvd {a b : AnalyticGerm (n + 1)}
    (hb : IsRegularInLast b) (hab : a ∣ b) : IsRegularInLast a := by
  obtain ⟨c, rfl⟩ := hab
  exact regularInLast_of_mul_left hb

private theorem regularInLast_of_associated {a b : AnalyticGerm (n + 1)}
    (hb : IsRegularInLast b) (hab : Associated a b) : IsRegularInLast a :=
  regularInLast_of_dvd hb hab.dvd

private instance analyticGerm_cancel (m : ℕ) : IsCancelMulZero (AnalyticGerm m) := by
  cases m with
  | zero => exact spec_analyticGerm_ufd_zero_aux.toIsCancelMulZero
  | succ m =>
    letI := analyticGerm_noZeroDivisors_succ (n := m)
    infer_instance

private theorem analyticGerm_irreducible_prime
    (hn : UniqueFactorizationMonoid (AnalyticGerm n))
    {p : AnalyticGerm (n + 1)} (hp : Irreducible p) : Prime p := by
  letI := hn
  refine ⟨hp.ne_zero, hp.not_isUnit, ?_⟩
  intro a b hd
  by_cases hz : a * b = 0
  · rcases mul_eq_zero.mp hz with rfl | rfl
    · exact Or.inl (dvd_zero p)
    · exact Or.inr (dvd_zero p)
  by_cases hau : IsUnit a
  · exact Or.inr (hd.trans (associated_unit_mul_left b a hau).dvd)
  by_cases hbu : IsUnit b
  · exact Or.inl (hd.trans (associated_mul_unit_left a b hbu).dvd)
  have hnu : ¬ IsUnit (a * b) := fun h ↦ hp.not_isUnit (isUnit_of_dvd_unit hd h)
  obtain ⟨L, e, he, hr⟩ := spec_exists_linearChange_regular_aux hz hnu
  have hpr : IsRegularInLast (e p) := regularInLast_of_dvd hr (map_dvd e hd)
  have har : IsRegularInLast (e a) := regularInLast_of_dvd hr (map_dvd e (dvd_mul_right a b))
  have hbr : IsRegularInLast (e b) := regularInLast_of_dvd hr (map_dvd e (dvd_mul_left b a))
  obtain ⟨P, hP, hpP⟩ := preparation_canonical hpr
    (fun h ↦ hp.not_isUnit (by simpa using h.map e.symm))
  obtain ⟨A, hA, haA⟩ := preparation_canonical har
    (fun h ↦ hau (by simpa using h.map e.symm))
  obtain ⟨B, hB, hbB⟩ := preparation_canonical hbr
    (fun h ↦ hbu (by simpa using h.map e.symm))
  have hpi : Irreducible (e p) := (MulEquiv.irreducible_iff e).mpr hp
  have hPi : Irreducible P :=
    (spec_irreducible_transfer_aux _ (canonicalEmbedding_spec n) hP).mpr
      (hpP.irreducible hpi)
  have hPd : P ∣ A * B := (canonicalEmbedding_dvd_iff hP).mp (by
    rw [map_mul]
    have hed : e p ∣ e a * e b := by simpa only [map_mul] using map_dvd e hd
    exact hpP.dvd'.trans (hed.trans (haA.mul_mul hbB).dvd))
  rcases (UniqueFactorizationMonoid.irreducible_iff_prime.mp hPi).dvd_or_dvd hPd with h | h
  · left
    have h' := hpP.dvd.trans ((map_dvd (canonicalEmbedding n) h).trans haA.dvd')
    simpa using map_dvd e.symm h'
  · right
    have h' := hpP.dvd.trans ((map_dvd (canonicalEmbedding n) h).trans hbB.dvd')
    simpa using map_dvd e.symm h'

private theorem canonicalEmbedding_irreducible_of_dvd
    {P Q : Polynomial (AnalyticGerm n)} (hP : IsWeierstrassPolynomial P)
    (hQ : Irreducible Q) (hQP : Q ∣ P) : Irreducible (canonicalEmbedding n Q) := by
  have hnu : ¬ IsUnit (canonicalEmbedding n Q) := by
    obtain ⟨S, hS⟩ := hQP
    exact fun h ↦ hQ.not_isUnit (canonicalEmbedding_factor_unit hP hS h)
  have hr := regularInLast_of_dvd (canonicalEmbedding_regular hP)
    (map_dvd (canonicalEmbedding n) hQP)
  obtain ⟨R, hR, hQR⟩ := preparation_canonical hr hnu
  have hRQ : R ∣ Q := (canonicalEmbedding_dvd_iff hR).mp hQR.dvd'
  have hQR' : Associated Q R :=
    (hQ.dvd_iff.mp hRQ).resolve_left (weierstrass_not_isUnit hR)
  exact hQR.symm.irreducible
    ((spec_irreducible_transfer_aux _ (canonicalEmbedding_spec n) hR).mp
      (hQR'.irreducible hQ))

theorem spec_analyticGerm_ufd_succ_aux
    (hn : UniqueFactorizationMonoid (AnalyticGerm n)) :
    UniqueFactorizationMonoid (AnalyticGerm (n + 1)) := by
  classical
  letI := hn
  apply UniqueFactorizationMonoid.of_exists_prime_factors
  intro g hg
  by_cases hu : IsUnit g
  · exact ⟨0, by simp, by simpa using (associated_one_iff_isUnit.mpr hu).symm⟩
  obtain ⟨L, e, he, hr⟩ := spec_exists_linearChange_regular_aux hg hu
  obtain ⟨P, hP, hgP⟩ := preparation_canonical hr
    (fun h ↦ hu (by simpa using h.map e.symm))
  obtain ⟨F, hF, hFP⟩ := WfDvdMonoid.exists_factors P hP.1.ne_zero
  let φ : Polynomial (AnalyticGerm n) →+* AnalyticGerm (n + 1) :=
    e.symm.toRingHom.comp (canonicalEmbedding n)
  refine ⟨F.map φ, ?_, ?_⟩
  · intro q hq
    obtain ⟨Q, hQ, rfl⟩ := Multiset.mem_map.mp hq
    apply analyticGerm_irreducible_prime hn
    apply (MulEquiv.irreducible_iff e.symm).mpr
    exact canonicalEmbedding_irreducible_of_dvd hP (hF Q hQ)
      ((Multiset.dvd_prod hQ).trans hFP.dvd)
  · rw [← map_multiset_prod]
    exact (hFP.map φ).trans (by simpa [φ] using hgP.symm.map e.symm)


theorem spec_analyticGerm_ufd_aux : ∀ n, UniqueFactorizationMonoid (AnalyticGerm n) := by
  intro n
  induction n with
  | zero => exact spec_analyticGerm_ufd_zero_aux
  | succ n ih => exact spec_analyticGerm_ufd_succ_aux ih

private theorem productAnalyticGerm_isUnit_iff (g : ProductAnalyticGerm n) :
    IsUnit g ↔ g.1.value ≠ 0 := by
  constructor
  · intro h
    exact (h.map ((Filter.Germ.valueRingHom (X := (Fin n → ℂ) × ℂ) (E := ℂ)).comp
      (productAnalyticGermSubring n).subtype)).ne_zero
  · obtain ⟨f, hf, hfg⟩ := g.2
    intro h
    have hf0 : f 0 ≠ 0 := by
      rw [← hfg, Filter.Germ.value_ofFun] at h
      exact h
    let k : ProductAnalyticGerm n :=
      ⟨↑(fun z ↦ (f z)⁻¹), fun z ↦ (f z)⁻¹, hf.inv hf0, rfl⟩
    have hk : g * k = 1 := by
      apply Subtype.ext
      change g.1 * k.1 = 1
      rw [← hfg]
      apply Filter.Germ.coe_eq.mpr
      filter_upwards [hf.continuousAt.eventually_ne hf0] with z hz
      exact mul_inv_cancel₀ hz
    exact isUnit_iff_exists_inv.mpr ⟨k, hk⟩

private theorem squareFreeAt_of_irreducible_productGerm {f : (Fin n → ℂ) × ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0)
    (hi : Irreducible (⟨↑f, f, hf, rfl⟩ : ProductAnalyticGerm n)) :
    IsSquareFreeAt f 0 := by
  intro g h hg hh hg0 hfac
  let G : ProductAnalyticGerm n := ⟨↑g, g, hg, rfl⟩
  let H : ProductAnalyticGerm n := ⟨↑h, h, hh, rfl⟩
  have he : (⟨↑f, f, hf, rfl⟩ : ProductAnalyticGerm n) = G * (G * H) := by
    apply Subtype.ext
    exact Filter.Germ.coe_eq.mpr (hfac.mono fun z hz ↦ by simpa [pow_two, mul_assoc] using hz)
  have hGu : IsUnit G := (hi.isUnit_or_isUnit he).elim id (fun h ↦ isUnit_of_mul_isUnit_left h)
  exact ((productAnalyticGerm_isUnit_iff G).mp hGu) hg0

theorem spec_exists_squarefree_decomposition_aux {f : (Fin n → ℂ) × ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0) (hnz : ¬ ∀ᶠ y in nhds 0, f y = 0) :
    ∃ k : ℕ, ∃ u : (Fin n → ℂ) × ℂ → ℂ,
      ∃ P : Fin k → (Fin n → ℂ) × ℂ → ℂ, ∃ m : Fin k → ℕ,
        AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
        (∀ i, AnalyticAt ℂ (P i) 0 ∧ P i 0 = 0 ∧ 0 < m i ∧ IsSquareFreeAt (P i) 0) ∧
        Pairwise (fun i j ↦ IsCoprimeAt (P i) (P j) 0) ∧
        f =ᶠ[nhds 0] fun y ↦ u y * ∏ i, (P i y) ^ (m i) := by
  classical
  letI : UniqueFactorizationMonoid (ProductAnalyticGerm n) :=
    (splitGermEquiv n).toMulEquiv.uniqueFactorizationMonoid
      (spec_analyticGerm_ufd_aux (n + 1))
  letI : StrongNormalizationMonoid (ProductAnalyticGerm n) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let G : ProductAnalyticGerm n := ⟨↑f, f, hf, rfl⟩
  have hG : G ≠ 0 := fun h ↦ hnz (Filter.Germ.coe_eq.mp (congrArg Subtype.val h))
  let F := UniqueFactorizationMonoid.normalizedFactors G
  let S := F.toFinset
  let k := Fintype.card S
  let e : Fin k ≃ S := (Fintype.equivFin S).symm
  let p : Fin k → ProductAnalyticGerm n := fun i ↦ (e i).1
  have hmem : ∀ i, p i ∈ F := fun i ↦ Multiset.mem_toFinset.mp (e i).2
  have hp : ∀ i, Prime (p i) := fun i ↦
    UniqueFactorizationMonoid.prime_of_normalized_factor _ (hmem i)
  let m : Fin k → ℕ := fun i ↦ F.count (p i)
  have hm : ∀ i, 0 < m i := fun i ↦ Multiset.count_pos.mpr (hmem i)
  have hprod : (∏ i, p i ^ m i) = F.prod := by
    rw [Finset.prod_multiset_count]
    exact (Fintype.prod_equiv e _ (fun q ↦ q.1 ^ F.count q.1) (fun _ ↦ rfl)).trans
      (Finset.prod_coe_sort S (fun q ↦ q ^ F.count q))
  obtain ⟨v, hv⟩ := UniqueFactorizationMonoid.prod_normalizedFactors hG
  obtain ⟨u, hu, huv⟩ := (v : ProductAnalyticGerm n).2
  choose P hPa hP using fun i ↦ (p i).2
  have hu0 : u 0 ≠ 0 := by
    have h := (productAnalyticGerm_isUnit_iff (v : ProductAnalyticGerm n)).mp v.isUnit
    rw [← huv, Filter.Germ.value_ofFun] at h
    convert h using 1
  have hP0 : ∀ i, P i 0 = 0 := by
    intro i
    by_contra hi
    apply (hp i).not_isUnit
    apply (productAnalyticGerm_isUnit_iff _).mpr
    rw [← hP i, Filter.Germ.value_ofFun]
    convert hi using 1
  have hPi : ∀ i, Irreducible (⟨↑(P i), P i, hPa i, rfl⟩ : ProductAnalyticGerm n) := by
    intro i
    have heq : (⟨↑(P i), P i, hPa i, rfl⟩ : ProductAnalyticGerm n) = p i :=
      Subtype.ext (hP i)
    rw [heq]
    exact (hp i).irreducible
  refine ⟨k, u, P, m, hu, hu0, (fun i ↦ ⟨hPa i, hP0 i, hm i,
    squareFreeAt_of_irreducible_productGerm (hPa i) (hPi i)⟩), ?_, ?_⟩
  · intro i j hij
    rintro ⟨q, r, s, hq, hr, hs, hq0, hqr, hqs⟩
    let Q : ProductAnalyticGerm n := ⟨↑q, q, hq, rfl⟩
    have hQu : ¬ IsUnit Q := fun h ↦ ((productAnalyticGerm_isUnit_iff Q).mp h) hq0
    have hQi : Q ∣ p i := by
      refine ⟨⟨↑r, r, hr, rfl⟩, ?_⟩
      apply Subtype.ext
      rw [← hP i]
      exact Filter.Germ.coe_eq.mpr hqr
    have hQj : Q ∣ p j := by
      refine ⟨⟨↑s, s, hs, rfl⟩, ?_⟩
      apply Subtype.ext
      rw [← hP j]
      exact Filter.Germ.coe_eq.mpr hqs
    have hiQ := ((hp i).irreducible.dvd_iff.mp hQi).resolve_left hQu
    have hjQ := ((hp j).irreducible.dvd_iff.mp hQj).resolve_left hQu
    have heq : p i = p j := UniqueFactorizationMonoid.mem_normalizedFactors_eq_of_associated
      (hmem i) (hmem j) (hiQ.trans hjQ.symm)
    exact hij (e.injective (Subtype.ext heq))
  · have hfun : (fun y ↦ u y * ∏ i, P i y ^ m i) = u * ∏ i, (P i) ^ m i := by
      ext y
      simp only [Pi.mul_apply, Finset.prod_apply, Pi.pow_apply]
    rw [hfun]
    apply Filter.Germ.coe_eq.mp
    change G.1 = _
    rw [← hv, ← hprod]
    change (productAnalyticGermSubring n).subtype (∏ i, p i ^ m i) *
      (v : ProductAnalyticGerm n).1 = _
    rw [map_prod]
    simp only [map_pow, ← huv]
    change (∏ i, (p i).1 ^ m i) * ↑u =
      (Filter.Germ.coeRingHom (nhds (0 : (Fin n → ℂ) × ℂ)))
        (u * ∏ i, (P i) ^ m i)
    rw [map_mul, map_prod]
    simp only [map_pow, Filter.Germ.coe_coeRingHom, ← hP]
    exact mul_comm _ _

private theorem monic_squarefree_fraction {R : Type*} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] {P : Polynomial R} (hP : P.Monic) (hs : Squarefree P) :
    Squarefree (P.map (algebraMap R (FractionRing R))) := by
  intro q hq
  have hqd : q ∣ P.map (algebraMap R (FractionRing R)) := (dvd_mul_right q q).trans hq
  have hq0 : q ≠ 0 := ne_zero_of_dvd_ne_zero (hP.map _).ne_zero hqd
  obtain ⟨Q, hQ⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd (FractionRing R) hP hqd
  have hQm : Q.Monic := by
    apply Polynomial.monic_of_injective (IsFractionRing.injective R (FractionRing R))
    have he : Q.map (algebraMap R (FractionRing R)) = q * C q.leadingCoeff⁻¹ := by
      calc
        _ = (Q.map (algebraMap R (FractionRing R)) * C q.leadingCoeff) * C q.leadingCoeff⁻¹ := by
          rw [mul_assoc, ← C_mul, mul_inv_cancel₀ (leadingCoeff_ne_zero.mpr hq0), C_1, mul_one]
        _ = _ := by rw [hQ]
    rw [he]
    exact monic_mul_leadingCoeff_inv hq0
  have hQQ : Q * Q ∣ P := hP.dvd_of_fraction_map_dvd_fraction_map (K := FractionRing R) (hQm.mul hQm) (by
    rw [Polynomial.map_mul]
    exact (mul_dvd_mul (show Q.map (algebraMap R (FractionRing R)) ∣ q from ⟨_, hQ.symm⟩)
      (show Q.map (algebraMap R (FractionRing R)) ∣ q from ⟨_, hQ.symm⟩)).trans hq)
  rw [← hQ]
  exact ((hs Q hQQ).map (Polynomial.mapRingHom _)).mul
    (isUnit_C.mpr (isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr hq0)))

private def fixedDiscr {R : Type*} [CommRing R] (P : Polynomial R) (d : ℕ) : R :=
  (if hd : d = 0 then (0 : Matrix (Fin (d - 1 + d)) (Fin (d - 1 + d)) R)
    else (P.derivative.sylvester P (d - 1) d).updateRow ⟨2 * d - 2, by omega⟩
      (fun j ↦ if ↑j = d - 2 then 1 else if ↑j = 2 * d - 2 then (d : R) else 0)).det *
        (-1) ^ (d * (d - 1) / 2)

private theorem fixedDiscr_eq {R : Type*} [CommRing R] (P : Polynomial R) :
    fixedDiscr P P.natDegree = P.discr := rfl

private theorem fixedDiscr_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (P : Polynomial R) (d : ℕ) :
    fixedDiscr (P.map φ) d = φ (fixedDiscr P d) := by
  unfold fixedDiscr
  rw [map_mul, map_pow, map_neg, map_one, RingHom.map_det]
  congr 2
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
  split_ifs <;> simp_all [Matrix.updateRow_apply, Polynomial.derivative_map,
    Polynomial.sylvester_map_map, RingHom.mapMatrix_apply, Matrix.map_apply]
  all_goals split_ifs <;> simp_all

private theorem monic_discr_ne_zero {K : Type*} [Field K] [CharZero K]
    {P : Polynomial K} (hP : P.Monic) (hs : Squarefree P) : P.discr ≠ 0 := by
  have hsep : P.Separable := PerfectField.separable_iff_squarefree.mpr hs
  rcases Nat.eq_zero_or_pos P.natDegree with h0 | hpos
  · have he : P = C 1 := by
      rw [eq_C_of_natDegree_eq_zero h0, ← hP.leadingCoeff, leadingCoeff, h0]
    rw [he, discr_C]
    exact one_ne_zero
  have he := resultant_deriv (natDegree_pos_iff_degree_pos.mp hpos)
  rw [← natDegree_derivative, hP.leadingCoeff, mul_one] at he
  intro hz
  have hr : P.resultant P.derivative = 0 := by rw [he, hz, mul_zero]
  exact (resultant_eq_zero_iff.mp hr).2 hsep

private theorem squarefree_productGerm_of_squareFreeAt {f : (Fin n → ℂ) × ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hsq : IsSquareFreeAt f 0) :
    Squarefree (⟨↑f, f, hf, rfl⟩ : ProductAnalyticGerm n) := by
  intro q hq
  obtain ⟨r, hr⟩ := hq
  by_contra hqu
  obtain ⟨g, hg, hgq⟩ := q.2
  obtain ⟨h, hh, hhr⟩ := r.2
  have hg0 : g 0 = 0 := by
    by_contra hn
    apply hqu
    apply (productAnalyticGerm_isUnit_iff q).mpr
    rw [← hgq, Filter.Germ.value_ofFun]
    convert hn using 1
  apply hsq g h hg hh hg0
  apply Filter.Germ.coe_eq.mp
  have he := congrArg Subtype.val hr
  change ↑f = q.1 * q.1 * r.1 at he
  rw [← hgq, ← hhr] at he
  simp only [pow_two]
  convert he using 1 <;> rfl

private theorem monicInLast_discr_not_zero_of_squareFreeAt {d : ℕ}
    {a : Fin d → (Fin n → ℂ) → ℂ} (ha : ∀ j, AnalyticAt ℂ (a j) 0)
    (ha0 : ∀ j, a j 0 = 0) (hsq : IsSquareFreeAt (monicInLast a) 0) :
    ¬ ∀ᶠ z in nhds 0, weierstrassDiscr a z = 0 := by
  classical
  letI := spec_analyticGerm_ufd_aux n
  letI : IsDomain (AnalyticGerm n) := {}
  letI : CharZero (AnalyticGerm n) := (analyticGermValue n).charZero
  let A : Fin d → AnalyticGerm n := fun j ↦ ⟨↑(a j), a j, ha j, rfl⟩
  let P := distinguishedPolynomial A
  have hPm : P.Monic := (distinguishedPolynomial_degree A).1
  have hPd : P.natDegree = d := (distinguishedPolynomial_degree A).2
  have hPs : Squarefree P := by
    by_cases hd : d = 0
    · have hP1 : P = 1 := by
        change P = C 1
        have hdeg := hPd.trans hd
        rw [eq_C_of_natDegree_eq_zero hdeg, ← hPm.leadingCoeff, leadingCoeff, hdeg]
      rw [hP1]
      exact isUnit_one.squarefree
    have hW : IsWeierstrassPolynomial P := distinguishedPolynomial_spec A (Nat.pos_of_ne_zero hd)
      (fun j ↦ ha0 j)
    have hg : Squarefree (productPolynomial n P) := by
      have he : productPolynomial n P =
          (⟨↑(monicInLast a), monicInLast a, laneC_analyticAt_monicInLast ha 0, rfl⟩ :
            ProductAnalyticGerm n) :=
        Subtype.ext (distinguishedPolynomial_rep A a (fun _ ↦ rfl))
      rw [he]
      exact squarefree_productGerm_of_squareFreeAt (laneC_analyticAt_monicInLast ha 0) hsq
    intro Q hQ
    have hqu : IsUnit (productPolynomial n Q) := hg _ (by simpa only [map_mul] using map_dvd (productPolynomial n) hQ)
    obtain ⟨R, hR⟩ := (dvd_mul_right Q Q).trans hQ
    exact canonicalEmbedding_factor_unit hW hR (hqu.map (splitGermEquiv n).symm)
  have hDn : P.discr ≠ 0 := by
    have hs := monic_squarefree_fraction hPm hPs
    have hn := monic_discr_ne_zero (hPm.map (algebraMap _ (FractionRing (AnalyticGerm n)))) hs
    intro hz
    apply hn
    rw [← fixedDiscr_eq, hPm.natDegree_map, fixedDiscr_map, fixedDiscr_eq, hz, map_zero]
  let B : Polynomial ((Fin n → ℂ) → ℂ) := X ^ d + ∑ j : Fin d, C (a j) * X ^ (j : ℕ)
  let c : ((Fin n → ℂ) → ℂ) →+* Filter.Germ (nhds (0 : Fin n → ℂ)) ℂ :=
    Filter.Germ.coeRingHom _
  have hmap : P.map (analyticGermSubring n).subtype = B.map c := by
    simp [P, distinguishedPolynomial, B, A, c, Polynomial.map_sum, Polynomial.map_pow,
      Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C]
  have hfun : fixedDiscr B d = weierstrassDiscr a := by
    funext z
    let ev : ((Fin n → ℂ) → ℂ) →+* ℂ := Pi.evalRingHom _ z
    have hB : B.map ev = monicPoly a z := by
      simp [B, monicPoly, Polynomial.map_sum, Polynomial.map_pow, Polynomial.map_add,
        Polynomial.map_mul, Polynomial.map_C, ev]
    change ev (fixedDiscr B d) = _
    rw [← fixedDiscr_map, hB]
    exact (congrArg (fixedDiscr (monicPoly a z)) (spec_monicPoly a z).2.1.symm).trans
      (fixedDiscr_eq _)
  intro hz
  apply hDn
  apply (analyticGermSubring n).subtype_injective
  rw [map_zero]
  change (analyticGermSubring n).subtype P.discr = 0
  rw [← fixedDiscr_eq, hPd, ← fixedDiscr_map, hmap, fixedDiscr_map, hfun]
  exact Filter.Germ.coe_eq.mpr hz

private theorem eventually_squareFreeAt_of_discriminant {d : ℕ}
    {a : Fin d → (Fin n → ℂ) → ℂ} (ha : ∀ j, AnalyticAt ℂ (a j) 0)
    (hD : ¬ ∀ᶠ z in nhds 0, weierstrassDiscr a z = 0) :
    ∀ᶠ y in nhds (0 : (Fin n → ℂ) × ℂ), IsSquareFreeAt (monicInLast a) y := by
  obtain ⟨ε, hε, hdense⟩ := laneC_exists_weierstrassDiscr_ne_zero ha hD
  have hnear : ∀ᶠ y in nhds (0 : (Fin n → ℂ) × ℂ), y.1 ∈ Metric.ball 0 ε :=
    continuous_fst.continuousAt.eventually (Metric.ball_mem_nhds _ hε)
  filter_upwards [hnear] with y hy
  intro g h hg hh hg0 hfac
  have ht : Tendsto (fun w : ℂ ↦ (y.1, w)) (nhds y.2) (nhds y) :=
    continuous_const.continuousAt.prodMk continuous_id.continuousAt
  have hgs : AnalyticAt ℂ (fun w ↦ g (y.1, w)) y.2 :=
    hg.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  have hgn : analyticOrderAt (fun w ↦ g (y.1, w)) y.2 ≠ ⊤ := by
    intro htop
    obtain ⟨m, hm⟩ := laneC_order_monicInLast_natCast a y.1 y.2
    have hz : ∀ᶠ w in nhds y.2, monicInLast a (y.1, w) = 0 := by
      filter_upwards [ht.eventually hfac, analyticOrderAt_eq_top.mp htop] with w hw hwg
      simp only [hw, hwg, zero_pow (by decide : 2 ≠ 0), zero_mul]
    have := (analyticOrderAt_eq_top.mpr hz)
    rw [hm] at this
    exact ENat.natCast_ne_top m this
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hgn
  have hmpos : m ≠ 0 := by
    intro hm0
    have hh0 := analyticOrderAt_ne_zero.mpr ⟨hgs, hg0⟩
    exact hh0 (hm.symm.trans (by simp [hm0]))
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    ((hg.eventually_analyticAt.and hh.eventually_analyticAt).and hfac)
  obtain ⟨r, hr, hrρ, δ, hδ, hga, -, hcount⟩ :=
    spec_exists_zeroCount_eq_order hg hm.symm hρ
  obtain ⟨z, hz, hDz⟩ := hdense y.1 hy (min δ ρ) (lt_min hδ hρ)
  have hzδ : z ∈ Metric.ball y.1 δ := Metric.ball_subset_ball (min_le_left _ _) hz
  have hzρ : z ∈ Metric.ball y.1 ρ := Metric.ball_subset_ball (min_le_right _ _) hz
  obtain ⟨w, hw, hword⟩ : ∃ w ∈ Metric.ball y.2 r,
      analyticOrderNatAt (fun w ↦ g (z, w)) w ≠ 0 := by
    apply exists_ne_zero_of_finsum_mem_ne_zero
    rw [← zeroCount, hcount z hzδ]
    exact hmpos
  have hgw : g (z, w) = 0 :=
    apply_eq_zero_of_analyticOrderNatAt_ne_zero (f := fun w ↦ g (z, w)) hword
  have hp : (z, w) ∈ Metric.ball y ρ := by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨Metric.mem_ball.mp hzρ, lt_trans (Metric.mem_ball.mp hw) hrρ⟩
  have hlocal : monicInLast a =ᶠ[nhds (z, w)] fun p ↦ g p ^ 2 * h p :=
    Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hp) fun p hp ↦ (hball p hp).2
  have hg' : AnalyticAt ℂ (fun w ↦ g (z, w)) w :=
    (hball (z, w) hp).1.1.comp₂ analyticAt_const analyticAt_id
  have hh' : AnalyticAt ℂ (fun w ↦ h (z, w)) w :=
    (hball (z, w) hp).1.2.comp₂ analyticAt_const analyticAt_id
  have ht' : Tendsto (fun w : ℂ ↦ (z, w)) (nhds w) (nhds (z, w)) :=
    continuous_const.continuousAt.prodMk continuous_id.continuousAt
  have hd0 : deriv (fun w ↦ monicInLast a (z, w)) w = 0 := by
    have hd := ((hg'.differentiableAt.hasDerivAt.pow 2).mul hh'.differentiableAt.hasDerivAt).congr_of_eventuallyEq
      (ht'.eventually hlocal)
    simpa [Pi.pow_apply, hgw] using hd.deriv
  have hP0 : monicInLast a (z, w) = 0 := by
    simpa only [hgw, zero_pow (by decide : 2 ≠ 0), zero_mul] using hlocal.self_of_nhds
  have hle := (spec_weierstrassDiscr_ne_zero_iff a z).mp hDz w
  have hne : analyticOrderAt (fun w ↦ monicInLast a (z, w)) w ≠ 0 :=
    analyticOrderAt_ne_zero.mpr ⟨by
      change AnalyticAt ℂ (fun t : ℂ ↦ t ^ d + ∑ j : Fin d, a j z * t ^ (j : ℕ)) w
      exact (analyticAt_id.pow d).add (Finset.analyticAt_fun_sum _ fun j _ ↦
        analyticAt_const.mul (analyticAt_id.pow _)), hP0⟩
  have h1 : analyticOrderAt (fun w ↦ monicInLast a (z, w)) w = 1 := by
    generalize analyticOrderAt (fun w ↦ monicInLast a (z, w)) w = k at hne hle ⊢
    induction k using ENat.recTopCoe with
    | top => simp at hle
    | coe k => norm_cast at hne hle ⊢; omega
  exact (laneC_deriv_ne_zero_of_order_one (analyticOrderAt_ne_zero.mp hne).1 h1) hd0

private theorem squareFreeAt_of_comp_unit {f P u : (Fin n → ℂ) × ℂ → ℂ}
    (L : ((Fin n → ℂ) × ℂ) ≃L[ℂ] ((Fin n → ℂ) × ℂ)) {y : (Fin n → ℂ) × ℂ}
    (hP : IsSquareFreeAt P y) (hu : AnalyticAt ℂ u y) (hu0 : u y ≠ 0)
    (hfac : (fun p ↦ f (L p)) =ᶠ[nhds y] fun p ↦ u p * P p) :
    IsSquareFreeAt f (L y) := by
  intro g h hg hh hg0 he
  apply hP (fun p ↦ g (L p)) (fun p ↦ h (L p) / u p)
    (hg.comp (L.analyticAt y)) ((hh.comp (L.analyticAt y)).div hu hu0) hg0
  filter_upwards [hfac, L.continuousAt.eventually he, hu.continuousAt.eventually_ne hu0]
    with p hp hp' hup
  rw [← mul_div_assoc, eq_div_iff hup, mul_comm (P p) (u p), ← hp, hp']

theorem spec_eventually_isSquareFreeAt_aux {f : (Fin n → ℂ) × ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hsq : IsSquareFreeAt f 0) :
    ∀ᶠ y in nhds 0, IsSquareFreeAt f y := by
  have hnz : ¬ ∀ᶠ y in nhds 0, f y = 0 := by
    intro hz
    apply hsq (fun _ ↦ 0) (fun _ ↦ 0) analyticAt_const analyticAt_const rfl
    filter_upwards [hz] with p hp
    simpa using hp
  obtain ⟨d, -, L, u, hu, hu0, a, ha, hfac⟩ := spec_exists_linearEquiv_preparation hf hnz
  have hsqP : IsSquareFreeAt (monicInLast a) 0 :=
    laneC_isSquareFreeAt_of_comp L (by simpa using hsq) hu hfac
  have hD := monicInLast_discr_not_zero_of_squareFreeAt (fun j ↦ (ha j).1)
    (fun j ↦ (ha j).2) hsqP
  have hnear : ∀ᶠ y in nhds (0 : (Fin n → ℂ) × ℂ), IsSquareFreeAt f (L y) := by
    filter_upwards [eventually_squareFreeAt_of_discriminant (fun j ↦ (ha j).1) hD,
      hu.eventually_analyticAt, hu.continuousAt.eventually_ne hu0, hfac.eventuallyEq_nhds]
      with y hy hyu hyu0 hyfac
    exact squareFreeAt_of_comp_unit L hy hyu hyu0 hyfac
  have ht : Tendsto L.symm (nhds (0 : (Fin n → ℂ) × ℂ)) (nhds 0) := by
    simpa only [ContinuousAt, map_zero] using L.symm.continuousAt (x := 0)
  simpa using ht.eventually hnear

private theorem analyticOrderAt_prod_pow_eq {k : ℕ} {Q : Fin k → ℂ → ℂ}
    (m : Fin k → ℕ) (i : Fin k) (hQ : ∀ j, AnalyticAt ℂ (Q j) 0)
    (hi : analyticOrderAt (Q i) 0 = 1) (hne : ∀ j, j ≠ i → Q j 0 ≠ 0) :
    analyticOrderAt (fun t ↦ ∏ j, (Q j t) ^ (m j)) 0 = m i := by
  have hfun : (fun t ↦ ∏ j, (Q j t) ^ (m j)) =
      (Q i) ^ (m i) * fun t ↦ ∏ j ∈ Finset.univ.erase i, (Q j t) ^ (m j) := by
    funext t
    simp only [Pi.mul_apply, Pi.pow_apply]
    exact (Finset.mul_prod_erase _ (fun j ↦ (Q j t) ^ (m j)) (Finset.mem_univ i)).symm
  have hrest : AnalyticAt ℂ (fun t ↦ ∏ j ∈ Finset.univ.erase i, (Q j t) ^ (m j)) 0 :=
    Finset.analyticAt_fun_prod _ fun j _ ↦ (hQ j).pow _
  have hrest0 :
      analyticOrderAt (fun t ↦ ∏ j ∈ Finset.univ.erase i, (Q j t) ^ (m j)) 0 = 0 := by
    apply analyticOrderAt_eq_zero.2
    right
    rw [Finset.prod_ne_zero_iff]
    intro j hj
    exact pow_ne_zero _ (hne j (Finset.ne_of_mem_erase hj))
  rw [hfun, analyticOrderAt_mul ((hQ i).pow _) hrest,
    analyticOrderAt_pow (hQ i), hi, hrest0]
  simp

theorem spec_transverseOrder_of_decomposition_aux {k : ℕ}
    {f u : (Fin n → ℂ) × ℂ → ℂ}
    {P : Fin k → (Fin n → ℂ) × ℂ → ℂ} {m : Fin k → ℕ}
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0) (hP : ∀ i, AnalyticAt ℂ (P i) 0)
    (hm : ∀ i, 0 < m i) (hfac : f =ᶠ[nhds 0] fun y ↦ u y * ∏ i, (P i y) ^ (m i)) :
    ∀ᶠ y in nhds 0, ∀ i, P i y = 0 → (∀ j, j ≠ i → P j y ≠ 0) →
      ∀ v : (Fin n → ℂ) × ℂ, fderiv ℂ (P i) y v ≠ 0 →
        analyticOrderAt (fun t : ℂ ↦ f (y + t • v)) 0 = m i := by
  obtain ⟨U, hU, hUopen, hU0⟩ := eventually_nhds_iff.mp hfac
  have hUnhds : U ∈ nhds (0 : (Fin n → ℂ) × ℂ) := hUopen.mem_nhds hU0
  have hu_ne : ∀ᶠ y in nhds 0, u y ≠ 0 := hu.continuousAt.eventually_ne hu0
  have hPa : ∀ᶠ y in nhds 0, ∀ i, AnalyticAt ℂ (P i) y :=
    eventually_all.mpr fun i ↦ (hP i).eventually_analyticAt
  filter_upwards [hUnhds, hu.eventually_analyticAt, hu_ne, hPa] with y hyU huy huy0 hPay
  intro i hPiy hother v hder
  let Q : Fin k → ℂ → ℂ := fun j t ↦ P j (y + t • v)
  have hQa : ∀ j, AnalyticAt ℂ (Q j) 0 := fun j ↦ analyticAt_line_comp (hPay j) v
  have hQi : analyticOrderAt (Q i) 0 = 1 :=
    (spec_analyticOrderAt_line_eq_one_iff_aux (hPay i) hPiy v).2 hder
  have hQne : ∀ j, j ≠ i → Q j 0 ≠ 0 := by
    intro j hji
    simpa [Q] using hother j hji
  have hua : AnalyticAt ℂ (fun t : ℂ ↦ u (y + t • v)) 0 := analyticAt_line_comp huy v
  have huord : analyticOrderAt (fun t : ℂ ↦ u (y + t • v)) 0 = 0 := by
    apply analyticOrderAt_eq_zero.2
    right
    simpa using huy0
  have hslice : (fun t : ℂ ↦ f (y + t • v)) =ᶠ[nhds 0]
      fun t ↦ u (y + t • v) * ∏ j, (Q j t) ^ (m j) := by
    have ht : Tendsto (fun t : ℂ ↦ y + t • v) (nhds 0) (nhds y) := by
      have hc : ContinuousAt (fun t : ℂ ↦ y + t • v) 0 := by fun_prop
      convert hc.tendsto using 1 <;> simp
    filter_upwards [ht.eventually (hUopen.mem_nhds hyU)] with t htU
    exact hU _ htU
  rw [analyticOrderAt_congr hslice]
  change analyticOrderAt
    ((fun t : ℂ ↦ u (y + t • v)) * (fun t ↦ ∏ j, (Q j t) ^ (m j))) 0 = m i
  have hproda : AnalyticAt ℂ (fun t ↦ ∏ j, (Q j t) ^ (m j)) 0 :=
    Finset.analyticAt_fun_prod _ fun j _ ↦ (hQa j).pow _
  rw [analyticOrderAt_mul hua hproda,
    huord, zero_add, analyticOrderAt_prod_pow_eq m i hQa hQi hQne]

end HodgeLean.Foundations.AnalyticDivisorAlgebraic6
