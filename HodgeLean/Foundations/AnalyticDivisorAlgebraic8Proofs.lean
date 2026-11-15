import HodgeLean.Foundations.AnalyticDivisorAlgebraic8Defs

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic8

open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7

theorem spec_localDivisor_one_aux (n : ℕ) : localDivisor n 1 = 0 := by
  simp [localDivisor]

theorem spec_localDivisor_zero_aux (n : ℕ) : localDivisor n 0 = 0 := by
  simp [localDivisor]

theorem spec_localDivisor_associated_aux (n : ℕ) (f g : ProductAnalyticGerm n)
    (h : Associated f g) : localDivisor n f = localDivisor n g := by
  have hm : Associates.mk f = Associates.mk g := Associates.mk_eq_mk_iff_associated.mpr h
  simp [localDivisor, hm]

theorem spec_localDivisor_unit_aux (n : ℕ) (f : ProductAnalyticGerm n) (hf : IsUnit f) :
    localDivisor n f = 0 := by
  rw [spec_localDivisor_associated_aux n f 1 (associated_one_iff_isUnit.mpr hf)]
  exact spec_localDivisor_one_aux n

theorem spec_localDivisor_mul_aux (n : ℕ) (f g : ProductAnalyticGerm n)
    (hf : f ≠ 0) (hg : g ≠ 0) :
    localDivisor n (f * g) = localDivisor n f + localDivisor n g := by
  classical
  letI : UniqueFactorizationMonoid (ProductAnalyticGerm n) := productAnalyticGermUFD n
  rw [localDivisor, localDivisor, localDivisor]
  change factorization (Associates.mk f * Associates.mk g) = _
  exact factorization_mul (Associates.mk_ne_zero.mpr hf) (Associates.mk_ne_zero.mpr hg)

theorem spec_localDivisor_pow_aux (n : ℕ) (f : ProductAnalyticGerm n) (m : ℕ) :
    localDivisor n (f ^ m) = m • localDivisor n f := by
  classical
  letI : UniqueFactorizationMonoid (ProductAnalyticGerm n) := productAnalyticGermUFD n
  rw [localDivisor, localDivisor]
  have hm : Associates.mk (f ^ m) = Associates.mk f ^ m :=
    map_pow Associates.mkMonoidHom f m
  rw [hm]
  exact factorization_pow

private theorem productAnalyticGermOf_isUnit {n : ℕ}
    {f : (Fin n → ℂ) × ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hf0 : f 0 ≠ 0) :
    IsUnit (productAnalyticGermOf f hf) := by
  let q : ProductAnalyticGerm n := productAnalyticGermOf (fun z ↦ (f z)⁻¹) (hf.inv hf0)
  apply isUnit_iff_exists_inv.mpr
  refine ⟨q, ?_⟩
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [hf.continuousAt.eventually_ne hf0] with z hz
  exact mul_inv_cancel₀ hz

private theorem productAnalyticGermOf_irreducible {n : ℕ}
    {f : (Fin n → ℂ) × ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hi : IsIrreducibleAt f 0) :
    Irreducible (productAnalyticGermOf f hf) := by
  refine ⟨fun hu ↦ (hu.map ((Filter.Germ.valueRingHom
    (X := (Fin n → ℂ) × ℂ) (E := ℂ)).comp
      (productAnalyticGermSubring n).subtype)).ne_zero hi.1, ?_⟩
  intro a b hab
  obtain ⟨g, hg, hga⟩ := a.2
  obtain ⟨h, hh, hhb⟩ := b.2
  have hfac : f =ᶠ[nhds 0] fun x ↦ g x * h x := by
    apply Filter.Germ.coe_eq.mp
    calc
      ↑f = (productAnalyticGermOf f hf).1 := rfl
      _ = (a * b).1 := congrArg Subtype.val hab
      _ = a.1 * b.1 := rfl
      _ = ↑g * ↑h := congrArg₂ (· * ·) hga.symm hhb.symm
      _ = ↑(fun x ↦ g x * h x) := rfl
  rcases hi.2 g h hg hh hfac with hg0 | hh0
  · left
    rw [isUnit_iff_exists_inv]
    let q : ProductAnalyticGerm n := productAnalyticGermOf (fun z ↦ (g z)⁻¹) (hg.inv hg0)
    refine ⟨q, Subtype.ext ?_⟩
    change a.1 * q.1 = 1
    rw [← hga]
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [hg.continuousAt.eventually_ne hg0] with z hz
    exact mul_inv_cancel₀ hz
  · right
    rw [isUnit_iff_exists_inv]
    let q : ProductAnalyticGerm n := productAnalyticGermOf (fun z ↦ (h z)⁻¹) (hh.inv hh0)
    refine ⟨q, Subtype.ext ?_⟩
    change b.1 * q.1 = 1
    rw [← hhb]
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [hh.continuousAt.eventually_ne hh0] with z hz
    exact mul_inv_cancel₀ hz

private theorem localDivisor_irreducible {n : ℕ} (f : ProductAnalyticGerm n)
    (hf : Irreducible f) :
    localDivisor n f = Finsupp.single (Associates.mk f) 1 := by
  classical
  letI : UniqueFactorizationMonoid (ProductAnalyticGerm n) := productAnalyticGermUFD n
  rw [localDivisor, factorization, UniqueFactorizationMonoid.normalizedFactors_irreducible
    (Associates.irreducible_mk.mpr hf)]
  simp only [normalize_eq, Multiset.toFinsupp_singleton]

theorem spec_localDivisor_decomposition_aux {n k : ℕ}
    {f u : (Fin n → ℂ) × ℂ → ℂ} {P : Fin k → (Fin n → ℂ) × ℂ → ℂ}
    {m : Fin k → ℕ} (hf : AnalyticAt ℂ f 0) (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hP : ∀ i, AnalyticAt ℂ (P i) 0 ∧ IsIrreducibleAt (P i) 0 ∧ 0 < m i)
    (hcP : Pairwise (fun i j ↦ IsCoprimeAt (P i) (P j) 0))
    (hfac : f =ᶠ[nhds 0] fun y ↦ u y * ∏ i, (P i y) ^ (m i)) :
    localDivisor n (productAnalyticGermOf f hf) =
      ∑ i, m i • Finsupp.single
        (Associates.mk (productAnalyticGermOf (P i) (hP i).1)) 1 := by
  classical
  letI : UniqueFactorizationMonoid (ProductAnalyticGerm n) := productAnalyticGermUFD n
  let U : ProductAnalyticGerm n := productAnalyticGermOf u hu
  let A : Fin k → ProductAnalyticGerm n := fun i ↦ productAnalyticGermOf (P i) (hP i).1
  have hU : IsUnit U := productAnalyticGermOf_isUnit hu hu0
  have hAi : ∀ i, Irreducible (A i) := fun i ↦
    productAnalyticGermOf_irreducible (hP i).1 (hP i).2.1
  have hfun : (fun y ↦ u y * ∏ i, P i y ^ m i) = u * ∏ i, (P i) ^ m i := by
    ext y
    simp only [Pi.mul_apply, Finset.prod_apply, Pi.pow_apply]
  rw [hfun] at hfac
  have heq : productAnalyticGermOf f hf = U * ∏ i, (A i) ^ (m i) := by
    apply Subtype.ext
    change (↑f : Filter.Germ (nhds (0 : (Fin n → ℂ) × ℂ)) ℂ) =
      U.1 * (productAnalyticGermSubring n).subtype (∏ i, (A i) ^ (m i))
    calc
      ↑f = (Filter.Germ.coeRingHom (nhds (0 : (Fin n → ℂ) × ℂ)))
          (u * ∏ i, (P i) ^ (m i)) := Filter.Germ.coe_eq.mpr hfac
      _ = U.1 * (productAnalyticGermSubring n).subtype (∏ i, (A i) ^ (m i)) := by
        rw [map_mul, map_prod, map_prod]
        simp only [map_pow, Filter.Germ.coe_coeRingHom]
        congr 1
  have hprod_ne : (∏ i, (A i) ^ (m i)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr fun i _ ↦ pow_ne_zero _ (hAi i).ne_zero
  have hprod : localDivisor n (∏ i, (A i) ^ (m i)) =
      ∑ i, m i • Finsupp.single (Associates.mk (A i)) 1 := by
    induction (Finset.univ : Finset (Fin k)) using Finset.induction_on with
    | empty => exact spec_localDivisor_one_aux n
    | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        spec_localDivisor_mul_aux n ((A a) ^ (m a)) (∏ i ∈ s, (A i) ^ (m i))
          (pow_ne_zero _ (hAi a).ne_zero)
          (Finset.prod_ne_zero_iff.mpr fun i _ ↦ pow_ne_zero _ (hAi i).ne_zero),
        spec_localDivisor_pow_aux, localDivisor_irreducible _ (hAi a), ih]
  rw [heq, spec_localDivisor_mul_aux n U (∏ i, (A i) ^ (m i)) hU.ne_zero hprod_ne,
    spec_localDivisor_unit_aux n U hU, hprod, zero_add]

theorem spec_localDivisor_support_and_zeroSet_aux {n k : ℕ}
    {f u : (Fin n → ℂ) × ℂ → ℂ} {P : Fin k → (Fin n → ℂ) × ℂ → ℂ}
    {m : Fin k → ℕ} (hf : AnalyticAt ℂ f 0) (hnz : ¬ ∀ᶠ y in nhds 0, f y = 0)
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hP : ∀ i, AnalyticAt ℂ (P i) 0 ∧ IsIrreducibleAt (P i) 0 ∧ 0 < m i)
    (hcP : Pairwise (fun i j ↦ IsCoprimeAt (P i) (P j) 0))
    (hfac : f =ᶠ[nhds 0] fun y ↦ u y * ∏ i, (P i y) ^ (m i)) :
    ↑(localDivisor n (productAnalyticGermOf f hf)).support =
        {c | ∃ i, c = Associates.mk (productAnalyticGermOf (P i) (hP i).1)} ∧
      ∀ᶠ y in nhds 0, f y = 0 ↔ ∃ i, P i y = 0 := by
  classical
  constructor
  · rw [spec_localDivisor_decomposition_aux hf hu hu0 hP hcP hfac]
    ext c
    simp only [Finset.mem_coe, Finsupp.mem_support_iff, ne_eq, Set.mem_ofPred_eq,
      Finsupp.sum_apply, Finsupp.smul_apply, Finsupp.single_apply]
    simp
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨i, ?_⟩
      by_contra hne
      apply hi
      simp [Finsupp.single_apply, hne]
    · rintro ⟨i, rfl⟩
      refine ⟨i, ?_⟩
      simp [Finsupp.single_apply, (hP i).2.2.ne']
  · exact spec_eventually_zero_iff_factor_zero hu hu0 (fun i ↦ (hP i).2.2) hfac

private theorem localFactorClass_ne_of_coprime {n : ℕ}
    {f g : (Fin n → ℂ) × ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (hfi : IsIrreducibleAt f 0) (hcop : IsCoprimeAt f g 0) :
    Associates.mk (productAnalyticGermOf f hf) ≠
      Associates.mk (productAnalyticGermOf g hg) := by
  intro heq
  have hassoc : Associated (productAnalyticGermOf f hf) (productAnalyticGermOf g hg) :=
    Associates.mk_eq_mk_iff_associated.mp heq
  obtain ⟨w, hw⟩ := hassoc
  obtain ⟨v, hv, hvw⟩ := (w : ProductAnalyticGerm n).2
  apply hcop
  refine ⟨f, fun _ ↦ 1, v, hf, analyticAt_const, hv, hfi.1, ?_, ?_⟩
  · filter_upwards [] with y
    simp
  · apply Filter.Germ.coe_eq.mp
    calc
      ↑g = (productAnalyticGermOf g hg).1 := rfl
      _ = (productAnalyticGermOf f hf * (w : ProductAnalyticGerm n)).1 :=
        congrArg Subtype.val hw.symm
      _ = (productAnalyticGermOf f hf).1 * (w : ProductAnalyticGerm n).1 := rfl
      _ = ↑f * ↑v := congrArg₂ (· * ·) rfl hvw.symm
      _ = ↑(fun x ↦ f x * v x) := rfl

theorem spec_localDivisor_multiplicity_eq_transverseOrder_aux {n k : ℕ}
    {f u : (Fin n → ℂ) × ℂ → ℂ} {P : Fin k → (Fin n → ℂ) × ℂ → ℂ}
    {m : Fin k → ℕ} (hf : AnalyticAt ℂ f 0) (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hP : ∀ i, AnalyticAt ℂ (P i) 0 ∧ IsIrreducibleAt (P i) 0 ∧ 0 < m i)
    (hcP : Pairwise (fun i j ↦ IsCoprimeAt (P i) (P j) 0))
    (hfac : f =ᶠ[nhds 0] fun y ↦ u y * ∏ i, (P i y) ^ (m i)) :
    ∀ᶠ y in nhds 0, ∀ i, P i y = 0 → (∀ j, j ≠ i → P j y ≠ 0) →
        ∀ a : (Fin n → ℂ) × ℂ, fderiv ℂ (P i) y a ≠ 0 →
          analyticOrderAt (fun t : ℂ ↦ f (y + t • a)) 0 =
            (localDivisor n (productAnalyticGermOf f hf))
              (Associates.mk (productAnalyticGermOf (P i) (hP i).1)) := by
  have horder := spec_transverseOrder_of_decomposition hu hu0 (fun i ↦ (hP i).1)
    (fun i ↦ (hP i).2.2) hfac
  filter_upwards [horder] with y hy
  intro i hPiy hother a hder
  rw [hy i hPiy hother a hder]
  rw [spec_localDivisor_decomposition_aux hf hu hu0 hP hcP hfac]
  classical
  simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
    Finsupp.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hne := localFactorClass_ne_of_coprime (hP j).1 (hP i).1 (hP j).2.1
      (hcP hji)
    simp only [hne, ↓reduceIte, mul_zero]
  · simp

private theorem irreducibleAt_of_fderiv_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} {y : E} (hf : AnalyticAt ℂ f y) (hf0 : f y = 0)
    (hd : fderiv ℂ f y ≠ 0) : IsIrreducibleAt f y := by
  refine ⟨hf0, ?_⟩
  intro g h hg hh hfac
  by_contra hn
  push Not at hn
  have he := hfac.fderiv_eq (𝕜 := ℂ)
  have he0 : fderiv ℂ (fun x ↦ g x * h x) y = 0 := by
    change fderiv ℂ (g * h) y = 0
    rw [fderiv_mul hg.differentiableAt hh.differentiableAt, hn.1, hn.2]
    apply ContinuousLinearMap.ext
    intro z
    simp
  exact hd (he.trans he0)

private theorem fderiv_snd_ne_zero {n : ℕ} :
    fderiv ℂ (fun y : (Fin n → ℂ) × ℂ ↦ y.2) 0 ≠ 0 := by
  have hd : HasFDerivAt (fun y : (Fin n → ℂ) × ℂ ↦ y.2)
      (ContinuousLinearMap.snd ℂ (Fin n → ℂ) ℂ) 0 := by fun_prop
  intro h
  have he := congrArg (fun L ↦ L (0, 1)) h
  rw [hd.fderiv] at he
  norm_num at he

private theorem fderiv_w_sub_z_ne_zero :
    fderiv ℂ (fun y : (Fin 1 → ℂ) × ℂ ↦ y.2 - y.1 0) 0 ≠ 0 := by
  have hd : HasFDerivAt (fun y : (Fin 1 → ℂ) × ℂ ↦ y.2 - y.1 0)
      ((ContinuousLinearMap.snd ℂ (Fin 1 → ℂ) ℂ) -
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).comp
          (ContinuousLinearMap.fst ℂ (Fin 1 → ℂ) ℂ)) 0 := by fun_prop
  intro h
  have he := congrArg (fun L ↦ L (0, 1)) h
  rw [hd.fderiv] at he
  norm_num at he

private theorem associatedAt_of_associated_productAnalyticGermOf {n : ℕ}
    {f g : (Fin n → ℂ) × ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (h : Associated (productAnalyticGermOf f hf) (productAnalyticGermOf g hg)) :
    AreAssociatedAt f g 0 := by
  obtain ⟨w, hw⟩ := h.symm
  obtain ⟨u, hu, huw⟩ := (w : ProductAnalyticGerm n).2
  refine ⟨u, hu, ?_, ?_⟩
  · have hwu : IsUnit (w : ProductAnalyticGerm n) := w.isUnit
    have hv := (hwu.map ((Filter.Germ.valueRingHom
      (X := (Fin n → ℂ) × ℂ) (E := ℂ)).comp
        (productAnalyticGermSubring n).subtype)).ne_zero
    change (w : ProductAnalyticGerm n).1.value ≠ 0 at hv
    rw [← huw, Filter.Germ.value_ofFun] at hv
    exact hv
  · apply Filter.Germ.coe_eq.mp
    calc
      ↑f = (productAnalyticGermOf f hf).1 := rfl
      _ = (productAnalyticGermOf g hg * (w : ProductAnalyticGerm n)).1 :=
        (congrArg Subtype.val hw).symm
      _ = (productAnalyticGermOf g hg).1 * (w : ProductAnalyticGerm n).1 := rfl
      _ = ↑g * ↑u := congrArg₂ (· * ·) rfl huw.symm
      _ = ↑(fun x ↦ u x * g x) := by rw [mul_comm]; rfl

private theorem w_not_associated_w_sub_z :
    let w : (Fin 1 → ℂ) × ℂ → ℂ := fun y ↦ y.2
    let q : (Fin 1 → ℂ) × ℂ → ℂ := fun y ↦ y.2 - y.1 0
    let hq : AnalyticAt ℂ q 0 := analyticAt_snd.sub
      (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).analyticAt 0).comp_of_eq
        analyticAt_fst rfl)
    Associates.mk (productAnalyticGermOf w analyticAt_snd) ≠
      Associates.mk (productAnalyticGermOf q hq) := by
  dsimp
  intro heq
  have hassoc : Associated
      (productAnalyticGermOf (fun y : (Fin 1 → ℂ) × ℂ ↦ y.2) analyticAt_snd)
      (productAnalyticGermOf (fun y : (Fin 1 → ℂ) × ℂ ↦ y.2 - y.1 0)
        (analyticAt_snd.sub
          (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).analyticAt 0).comp_of_eq
            analyticAt_fst rfl))) := Associates.mk_eq_mk_iff_associated.mp heq
  obtain ⟨u, hu, hu0, hfac⟩ :=
    associatedAt_of_associated_productAnalyticGermOf _ _ hassoc
  have hdw : HasFDerivAt (fun y : (Fin 1 → ℂ) × ℂ ↦ y.2)
      (ContinuousLinearMap.snd ℂ (Fin 1 → ℂ) ℂ) 0 := by fun_prop
  have hdq : HasFDerivAt (fun y : (Fin 1 → ℂ) × ℂ ↦ y.2 - y.1 0)
      ((ContinuousLinearMap.snd ℂ (Fin 1 → ℂ) ℂ) -
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).comp
          (ContinuousLinearMap.fst ℂ (Fin 1 → ℂ) ℂ)) 0 := by fun_prop
  have he := hfac.fderiv_eq (𝕜 := ℂ)
  have he' : fderiv ℂ (fun x ↦ u x * (x.2 - x.1 0)) 0 =
      u 0 • fderiv ℂ (fun x : (Fin 1 → ℂ) × ℂ ↦ x.2 - x.1 0) 0 := by
    have hp := hu.differentiableAt.hasFDerivAt.mul hdq
    change fderiv ℂ (u * fun x : (Fin 1 → ℂ) × ℂ ↦ x.2 - x.1 0) 0 = _
    rw [hp.fderiv, hdq.fderiv]
    norm_num
  rw [he', hdw.fderiv, hdq.fderiv] at he
  have hev := congrArg (fun L ↦ L (fun _ ↦ 1, 0)) he
  norm_num at hev
  exact hu0 hev

theorem spec_localDivisor_w_sq_mul_w_sub_z_aux :
    let w : (Fin 1 → ℂ) × ℂ → ℂ := fun y ↦ y.2
    let q : (Fin 1 → ℂ) × ℂ → ℂ := fun y ↦ y.2 - y.1 0
    localDivisor 1 (productAnalyticGermOf (fun y ↦ w y ^ 2 * q y)
      ((analyticAt_snd.pow 2).mul (analyticAt_snd.sub
        (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).analyticAt 0).comp_of_eq
          analyticAt_fst rfl)))) =
      2 • Finsupp.single (Associates.mk (productAnalyticGermOf w analyticAt_snd)) 1 +
        Finsupp.single (Associates.mk (productAnalyticGermOf q
          (analyticAt_snd.sub
            (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).analyticAt 0).comp_of_eq
              analyticAt_fst rfl)))) 1 ∧
    Associates.mk (productAnalyticGermOf w analyticAt_snd) ≠
      Associates.mk (productAnalyticGermOf q
        (analyticAt_snd.sub
          (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).analyticAt 0).comp_of_eq
            analyticAt_fst rfl))) := by
  dsimp
  letI : UniqueFactorizationMonoid (ProductAnalyticGerm 1) := productAnalyticGermUFD 1
  let hq : AnalyticAt ℂ (fun y : (Fin 1 → ℂ) × ℂ ↦ y.2 - y.1 0) 0 :=
    analyticAt_snd.sub
      (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).analyticAt 0).comp_of_eq
        analyticAt_fst rfl)
  let W : ProductAnalyticGerm 1 :=
    productAnalyticGermOf (fun y : (Fin 1 → ℂ) × ℂ ↦ y.2) analyticAt_snd
  let Q : ProductAnalyticGerm 1 :=
    productAnalyticGermOf (fun y : (Fin 1 → ℂ) × ℂ ↦ y.2 - y.1 0) hq
  have hiW : Irreducible W := productAnalyticGermOf_irreducible analyticAt_snd
    (irreducibleAt_of_fderiv_ne_zero analyticAt_snd rfl fderiv_snd_ne_zero)
  have hiQ : Irreducible Q := productAnalyticGermOf_irreducible hq
    (irreducibleAt_of_fderiv_ne_zero hq (by norm_num) fderiv_w_sub_z_ne_zero)
  have heq : productAnalyticGermOf
      (fun y : (Fin 1 → ℂ) × ℂ ↦ y.2 ^ 2 * (y.2 - y.1 0))
      ((analyticAt_snd.pow 2).mul hq) = W ^ 2 * Q := by
    apply Subtype.ext
    rfl
  refine ⟨?_, w_not_associated_w_sub_z⟩
  rw [heq, spec_localDivisor_mul_aux 1 (W ^ 2) Q (pow_ne_zero _ hiW.ne_zero) hiQ.ne_zero,
    spec_localDivisor_pow_aux, localDivisor_irreducible W hiW,
    localDivisor_irreducible Q hiQ]

theorem spec_localDivisor_one_add_z_aux :
    localDivisor 1 (productAnalyticGermOf (fun y : (Fin 1 → ℂ) × ℂ ↦ 1 + y.1 0)
      (analyticAt_const.add
        (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).analyticAt 0).comp_of_eq
          analyticAt_fst rfl))) = 0 := by
  apply spec_localDivisor_unit_aux
  apply productAnalyticGermOf_isUnit
  norm_num

theorem spec_localDivisor_zero_base_w_pow_aux :
    localDivisor 0 (productAnalyticGermOf (fun y : (Fin 0 → ℂ) × ℂ ↦ y.2 ^ 3)
      (analyticAt_snd.pow 3)) =
      3 • Finsupp.single (Associates.mk (productAnalyticGermOf (fun y : (Fin 0 → ℂ) × ℂ ↦ y.2)
        analyticAt_snd)) 1 := by
  let W : ProductAnalyticGerm 0 :=
    productAnalyticGermOf (fun y : (Fin 0 → ℂ) × ℂ ↦ y.2) analyticAt_snd
  have hiW : Irreducible W := productAnalyticGermOf_irreducible analyticAt_snd
    (irreducibleAt_of_fderiv_ne_zero analyticAt_snd rfl fderiv_snd_ne_zero)
  have heq : productAnalyticGermOf (fun y : (Fin 0 → ℂ) × ℂ ↦ y.2 ^ 3)
      (analyticAt_snd.pow 3) = W ^ 3 := by
    apply Subtype.ext
    rfl
  rw [heq, spec_localDivisor_pow_aux, localDivisor_irreducible W hiW]

theorem spec_localDivisor_distinct_and_associated_factors_aux :
    let w : (Fin 1 → ℂ) × ℂ → ℂ := fun y ↦ y.2
    let q : (Fin 1 → ℂ) × ℂ → ℂ := fun y ↦ y.2 - y.1 0
    let hw : AnalyticAt ℂ w 0 := analyticAt_snd
    let hq : AnalyticAt ℂ q 0 := analyticAt_snd.sub
      (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).analyticAt 0).comp_of_eq
        analyticAt_fst rfl)
    localDivisor 1 (productAnalyticGermOf (fun y ↦ w y * q y) (hw.mul hq)) =
        Finsupp.single (Associates.mk (productAnalyticGermOf w hw)) 1 +
          Finsupp.single (Associates.mk (productAnalyticGermOf q hq)) 1 ∧
      localDivisor 1 (productAnalyticGermOf (fun y ↦ w y * (2 * w y))
        (hw.mul (analyticAt_const.mul hw))) =
        2 • Finsupp.single (Associates.mk (productAnalyticGermOf w hw)) 1 := by
  dsimp
  letI : UniqueFactorizationMonoid (ProductAnalyticGerm 1) := productAnalyticGermUFD 1
  let hq : AnalyticAt ℂ (fun y : (Fin 1 → ℂ) × ℂ ↦ y.2 - y.1 0) 0 :=
    analyticAt_snd.sub
      (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).analyticAt 0).comp_of_eq
        analyticAt_fst rfl)
  let W : ProductAnalyticGerm 1 :=
    productAnalyticGermOf (fun y : (Fin 1 → ℂ) × ℂ ↦ y.2) analyticAt_snd
  let Q : ProductAnalyticGerm 1 :=
    productAnalyticGermOf (fun y : (Fin 1 → ℂ) × ℂ ↦ y.2 - y.1 0) hq
  let C : ProductAnalyticGerm 1 :=
    productAnalyticGermOf (fun _ : (Fin 1 → ℂ) × ℂ ↦ (2 : ℂ)) analyticAt_const
  have hiW : Irreducible W := productAnalyticGermOf_irreducible analyticAt_snd
    (irreducibleAt_of_fderiv_ne_zero analyticAt_snd rfl fderiv_snd_ne_zero)
  have hiQ : Irreducible Q := productAnalyticGermOf_irreducible hq
    (irreducibleAt_of_fderiv_ne_zero hq (by norm_num) fderiv_w_sub_z_ne_zero)
  have hC : IsUnit C := productAnalyticGermOf_isUnit analyticAt_const (by norm_num)
  have heq₁ : productAnalyticGermOf
      (fun y : (Fin 1 → ℂ) × ℂ ↦ y.2 * (y.2 - y.1 0)) (analyticAt_snd.mul hq) =
      W * Q := by
    apply Subtype.ext
    rfl
  have heq₂ : productAnalyticGermOf
      (fun y : (Fin 1 → ℂ) × ℂ ↦ y.2 * (2 * y.2))
      (analyticAt_snd.mul (analyticAt_const.mul analyticAt_snd)) = C * W ^ 2 := by
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    filter_upwards [] with y
    simp only [Function.comp_apply]
    ring
  constructor
  · rw [heq₁, spec_localDivisor_mul_aux 1 W Q hiW.ne_zero hiQ.ne_zero,
      localDivisor_irreducible W hiW, localDivisor_irreducible Q hiQ]
  · rw [heq₂, spec_localDivisor_mul_aux 1 C (W ^ 2) hC.ne_zero
        (pow_ne_zero _ hiW.ne_zero), spec_localDivisor_unit_aux 1 C hC,
      spec_localDivisor_pow_aux, localDivisor_irreducible W hiW, zero_add]

end HodgeLean.Foundations.AnalyticDivisorAlgebraic8
