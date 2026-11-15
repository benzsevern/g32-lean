import HodgeLean.Foundations.AnalyticDivisorAlgebraic14Defs

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic14

open Filter Set Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7
open HodgeLean.Foundations.AnalyticDivisorAlgebraic8

/-- Source: Griffiths--Harris, Ch. 1 §1; association by a nonvanishing germ. -/
theorem spec_zero_iff_on_overlap_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} {U : Set E} {V : ι → Set E} {f : ι → E → ℂ}
    (hD : IsLocalDivisorData U V f) (i j : ι) (x : E) (hi : x ∈ V i) (hj : x ∈ V j) :
    f i x = 0 ↔ f j x = 0 := by
  obtain ⟨u, -, hu0, hfu⟩ := hD.2.2.2.2 i j x ⟨hi, hj⟩
  rw [hfu.self_of_nhds, mul_eq_zero]
  exact ⟨fun h ↦ h.resolve_left hu0, Or.inr⟩

/-- Source: Griffiths--Harris, Ch. 1 §1. -/
theorem spec_mem_localDivisorSupport_iff_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {ι : Type*} {U : Set E} {V : ι → Set E} {f : ι → E → ℂ}
    (hD : IsLocalDivisorData U V f) (i : ι) (x : E) (hi : x ∈ V i) :
    x ∈ localDivisorSupport V f ↔ f i x = 0 := by
  constructor
  · rintro ⟨j, hj, hfj⟩
    exact (spec_zero_iff_on_overlap_aux hD i j x hi hj).mpr hfj
  · exact fun h ↦ ⟨i, hi, h⟩

/-- Source: Griffiths--Harris, Ch. 1 §1; continuity of analytic functions. -/
theorem spec_isClosed_localDivisorSupport_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {ι : Type*} {U : Set E} {V : ι → Set E} {f : ι → E → ℂ}
    (hD : IsLocalDivisorData U V f) :
    localDivisorSupport V f ⊆ U ∧
      IsClosed (((↑) : U → E) ⁻¹' localDivisorSupport V f) := by
  refine ⟨?_, ?_⟩
  · rintro x ⟨i, hi, -⟩
    rw [← hD.2.1]
    exact mem_iUnion.mpr ⟨i, hi⟩
  · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x hx
    have hxU : (x : E) ∈ ⋃ i, V i := hD.2.1.symm ▸ x.2
    obtain ⟨i, hi⟩ := mem_iUnion.mp hxU
    have hfx : f i x ≠ 0 := fun h ↦ hx ⟨i, hi, h⟩
    have hS : {y | y ∈ V i ∧ f i y ≠ 0} ∈ 𝓝 (x : E) :=
      inter_mem ((hD.1 i).mem_nhds hi)
        ((hD.2.2.1 i x hi).continuousAt.eventually_ne hfx)
    rw [nhds_subtype]
    refine mem_comap.mpr ⟨_, hS, ?_⟩
    rintro y ⟨hyi, hfy⟩ hy
    exact hfy ((spec_mem_localDivisorSupport_iff_aux hD i y hyi).mp hy)

private theorem analyticAt_translate {n : ℕ} {f : (Fin n → ℂ) × ℂ → ℂ}
    {p : (Fin n → ℂ) × ℂ} (hf : AnalyticAt ℂ f p) :
    AnalyticAt ℂ (fun y ↦ f (p + y)) 0 :=
  hf.comp_of_eq (analyticAt_const.add analyticAt_id) (by simp)

private theorem productAnalyticGermOf_isUnit_of_ne_zero {n : ℕ}
    {f : (Fin n → ℂ) × ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hf0 : f 0 ≠ 0) :
    IsUnit (productAnalyticGermOf f hf) := by
  let q : ProductAnalyticGerm n :=
    productAnalyticGermOf (fun z ↦ (f z)⁻¹) (hf.inv hf0)
  apply isUnit_iff_exists_inv.mpr
  refine ⟨q, ?_⟩
  apply Subtype.ext
  apply Filter.Germ.coe_eq.mpr
  filter_upwards [hf.continuousAt.eventually_ne hf0] with z hz
  exact mul_inv_cancel₀ hz

/-- Source: Gunning--Rossi, II.B, Definition 1; `spec_localDivisor_associated`. -/
theorem spec_localDivisorAt_eq_of_areAssociatedAt_aux {n : ℕ}
    {f g : (Fin n → ℂ) × ℂ → ℂ} {p : (Fin n → ℂ) × ℂ}
    (hf : AnalyticAt ℂ f p) (hg : AnalyticAt ℂ g p) (h : AreAssociatedAt f g p) :
    localDivisorAt n f p = localDivisorAt n g p := by
  obtain ⟨u, hu, hu0, hfg⟩ := h
  have hft := analyticAt_translate hf
  have hgt := analyticAt_translate hg
  have hut := analyticAt_translate hu
  simp only [localDivisorAt, hft, hgt, ↓reduceDIte]
  apply spec_localDivisor_associated
  let U : ProductAnalyticGerm n := productAnalyticGermOf (fun y ↦ u (p + y)) hut
  have hU : IsUnit U := productAnalyticGermOf_isUnit_of_ne_zero hut (by simpa using hu0)
  have heq : productAnalyticGermOf (fun y ↦ f (p + y)) hft =
      U * productAnalyticGermOf (fun y ↦ g (p + y)) hgt := by
    apply Subtype.ext
    apply Filter.Germ.coe_eq.mpr
    have hfg0 : f =ᶠ[𝓝 (p + 0)] fun x ↦ u x * g x := by simpa using hfg
    have hfg' := hfg0.comp_tendsto
      (analyticAt_const.add analyticAt_id :
        AnalyticAt ℂ (fun y : (Fin n → ℂ) × ℂ ↦ p + y) 0).continuousAt
    filter_upwards [hfg'] with y hy
    exact hy
  rw [heq]
  exact associated_unit_mul_left _ _ hU

/-- Source: Griffiths--Harris, Ch. 1 §1; `spec_localDivisor_unit`. -/
theorem spec_localDivisorAt_eq_zero_of_ne_zero_aux {n : ℕ}
    {f : (Fin n → ℂ) × ℂ → ℂ} {p : (Fin n → ℂ) × ℂ}
    (hf : AnalyticAt ℂ f p) (hp : f p ≠ 0) :
    localDivisorAt n f p = 0 := by
  have hft := analyticAt_translate hf
  simp only [localDivisorAt, hft, ↓reduceDIte]
  apply spec_localDivisor_unit
  exact productAnalyticGermOf_isUnit_of_ne_zero hft (by simpa using hp)

/-- Source: Griffiths--Harris, Ch. 1 §1; `spec_localDivisorAt_eq_of_areAssociatedAt`. -/
theorem spec_localDivisorAt_eq_on_overlap_aux {n : ℕ} {ι : Type*}
    {U : Set ((Fin n → ℂ) × ℂ)} {V : ι → Set ((Fin n → ℂ) × ℂ)}
    {f : ι → (Fin n → ℂ) × ℂ → ℂ} (hD : IsLocalDivisorData U V f)
    (i j : ι) (p : (Fin n → ℂ) × ℂ) (hi : p ∈ V i) (hj : p ∈ V j) :
    localDivisorAt n (f i) p = localDivisorAt n (f j) p := by
  exact spec_localDivisorAt_eq_of_areAssociatedAt_aux
    (hD.2.2.1 i p hi) (hD.2.2.1 j p hj) (hD.2.2.2.2 i j p ⟨hi, hj⟩)

/-- Source: Gunning--Rossi, II.B, Theorems 3--6; Griffiths--Harris, Ch. 1 §1. -/
theorem spec_localDivisorAt_ne_zero_iff_aux {n : ℕ} {ι : Type*}
    {U : Set ((Fin n → ℂ) × ℂ)} {V : ι → Set ((Fin n → ℂ) × ℂ)}
    {f : ι → (Fin n → ℂ) × ℂ → ℂ} (hD : IsLocalDivisorData U V f)
    (i : ι) (p : (Fin n → ℂ) × ℂ) (hi : p ∈ V i) :
    localDivisorAt n (f i) p ≠ 0 ↔ p ∈ localDivisorSupport V f := by
  classical
  have hf : AnalyticAt ℂ (f i) p := hD.2.2.1 i p hi
  have ht : AnalyticAt ℂ (fun y ↦ f i (p + y)) 0 :=
    hf.comp_of_eq (analyticAt_const.add analyticAt_id) (by simp)
  rw [spec_mem_localDivisorSupport_iff_aux hD i p hi]
  constructor
  · intro hne
    by_contra hp
    exact hne (spec_localDivisorAt_eq_zero_of_ne_zero_aux hf hp)
  · intro hp
    simp only [localDivisorAt, ht, ↓reduceDIte]
    let g : ProductAnalyticGerm n :=
      productAnalyticGermOf (fun y ↦ f i (p + y)) ht
    have hg0 : g ≠ 0 := by
      intro hg
      have he : ∀ᶠ y in 𝓝 (0 : (Fin n → ℂ) × ℂ), f i (p + y) = 0 := by
        apply Filter.Germ.coe_eq.mp
        exact congrArg Subtype.val hg
      have he' : ∀ᶠ x in 𝓝 p, f i x = 0 := by
        have hs : Tendsto (fun x ↦ x - p) (𝓝 p) (𝓝 0) := by
          simpa using (tendsto_id.sub tendsto_const_nhds :
            Tendsto (fun x ↦ x - p) (𝓝 p) (𝓝 (p - p)))
        filter_upwards [hs.eventually he] with x hx
        convert hx using 1 <;> abel
      exact hD.2.2.2.1 i p hi he'
    have hgnu : ¬ IsUnit g := by
      intro hgu
      have hv : IsUnit ((Filter.Germ.valueRingHom
          (X := (Fin n → ℂ) × ℂ) (E := ℂ)).comp
            (productAnalyticGermSubring n).subtype g) := hgu.map _
      have hval : (Filter.Germ.valueRingHom
          (X := (Fin n → ℂ) × ℂ) (E := ℂ)).comp
            (productAnalyticGermSubring n).subtype g = 0 := by
        change (@Filter.Germ.ofFun ((Fin n → ℂ) × ℂ) ℂ (𝓝 0)
          (fun y ↦ f i (p + y))).value = 0
        rw [Filter.Germ.value_ofFun]
        simpa using hp
      exact not_isUnit_zero (hval ▸ hv)
    intro hzero
    letI : UniqueFactorizationMonoid (ProductAnalyticGerm n) := productAnalyticGermUFD n
    have hfzero : factorization (Associates.mk g) = 0 := by
      simpa [localDivisor, g] using hzero
    have hmknz : Associates.mk g ≠ 0 := Associates.mk_ne_zero.mpr hg0
    have hassoc : Associated (Associates.mk g) 1 :=
      associated_of_factorization_eq _ _ hmknz one_ne_zero (by simpa using hfzero)
    exact hgnu (Associates.isUnit_mk.mp (associated_one_iff_isUnit.mp hassoc))

/-- Source: Griffiths--Harris, Ch. 1 §1 (restriction to a refinement). -/
theorem spec_refinement_isLocalDivisorData_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {ι κ : Type*} {U : Set E} {V : ι → Set E} {f : ι → E → ℂ}
    (hD : IsLocalDivisorData U V f) (W : κ → Set E) (τ : κ → ι)
    (hW : ∀ k, IsOpen (W k)) (hWU : (⋃ k, W k) = U) (hWV : ∀ k, W k ⊆ V (τ k)) :
    IsLocalDivisorData U W (fun k ↦ f (τ k)) := by
  exact ⟨hW, hWU, fun k ↦ (hD.2.2.1 (τ k)).mono (hWV k),
    fun k x hx ↦ hD.2.2.2.1 (τ k) x (hWV k hx),
    fun k l x hx ↦ hD.2.2.2.2 (τ k) (τ l) x ⟨hWV k hx.1, hWV l hx.2⟩⟩

/-- Source: Griffiths--Harris, Ch. 1 §1 (restriction to a refinement). -/
theorem spec_refinement_support_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {ι κ : Type*} {U : Set E} {V : ι → Set E} {f : ι → E → ℂ}
    (hD : IsLocalDivisorData U V f) (W : κ → Set E) (τ : κ → ι)
    (hWU : (⋃ k, W k) = U) (hWV : ∀ k, W k ⊆ V (τ k)) :
    localDivisorSupport W (fun k ↦ f (τ k)) = localDivisorSupport V f := by
  ext x
  constructor
  · rintro ⟨k, hk, hfk⟩
    exact ⟨τ k, hWV k hk, hfk⟩
  · rintro ⟨i, hi, hfi⟩
    have hxU : x ∈ ⋃ k, W k := by
      rw [hWU, ← hD.2.1]
      exact mem_iUnion.mpr ⟨i, hi⟩
    obtain ⟨k, hk⟩ := mem_iUnion.mp hxU
    exact ⟨k, hk, (spec_zero_iff_on_overlap_aux hD (τ k) i x (hWV k hk) hi).mpr hfi⟩

/-- Source: Griffiths--Harris, Ch. 1 §1 (restriction to a refinement). -/
theorem spec_refinement_localDivisorAt_aux {n : ℕ} {ι κ : Type*}
    {U : Set ((Fin n → ℂ) × ℂ)} {V : ι → Set ((Fin n → ℂ) × ℂ)}
    {f : ι → (Fin n → ℂ) × ℂ → ℂ} (hD : IsLocalDivisorData U V f)
    (W : κ → Set ((Fin n → ℂ) × ℂ)) (τ : κ → ι) (hWV : ∀ k, W k ⊆ V (τ k))
    (k : κ) (i : ι) (p : (Fin n → ℂ) × ℂ) (hk : p ∈ W k) (hi : p ∈ V i) :
    localDivisorAt n (f (τ k)) p = localDivisorAt n (f i) p := by
  exact spec_localDivisorAt_eq_on_overlap_aux hD (τ k) i p (hWV k hk) hi

/-- Irreducibility at a point descends from the translate at the origin.
Source: Gunning--Rossi, II.B, Definition 1; translation is an analytic isomorphism. -/
theorem isIrreducibleAt_of_translate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} {p : E} (h : IsIrreducibleAt (fun y ↦ f (p + y)) 0) :
    IsIrreducibleAt f p := by
  refine ⟨by simpa using h.1, fun g g' hg hg' hfac ↦ ?_⟩
  have ht : Tendsto (fun y : E ↦ p + y) (𝓝 0) (𝓝 p) :=
    (continuous_const.add continuous_id).tendsto' 0 p (add_zero p)
  have hA : AnalyticAt ℂ (fun y : E ↦ p + y) 0 := analyticAt_const.add analyticAt_id
  have := h.2 (fun y ↦ g (p + y)) (fun y ↦ g' (p + y))
    (hg.comp_of_eq hA (add_zero p)) (hg'.comp_of_eq hA (add_zero p))
    (ht.eventually hfac)
  simpa using this

/-- Coprimality at a point descends from the translates at the origin.
Source: Gunning--Rossi, II.B, Theorems 3--6; translation is an analytic isomorphism. -/
theorem isCoprimeAt_of_translate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : E → ℂ} {p : E}
    (h : IsCoprimeAt (fun y ↦ f (p + y)) (fun y ↦ g (p + y)) 0) :
    IsCoprimeAt f g p := by
  rintro ⟨q, r, s, hq, hr, hs, hq0, hfq, hgq⟩
  have ht : Tendsto (fun y : E ↦ p + y) (𝓝 0) (𝓝 p) :=
    (continuous_const.add continuous_id).tendsto' 0 p (add_zero p)
  have hA : AnalyticAt ℂ (fun y : E ↦ p + y) 0 := analyticAt_const.add analyticAt_id
  exact h ⟨fun y ↦ q (p + y), fun y ↦ r (p + y), fun y ↦ s (p + y),
    hq.comp_of_eq hA (add_zero p), hr.comp_of_eq hA (add_zero p),
    hs.comp_of_eq hA (add_zero p), by simpa using hq0, ht.eventually hfq, ht.eventually hgq⟩

/-- Source: Gunning--Rossi, II.B, Theorems 3--6, after translation to the origin. -/
theorem spec_exists_irreducible_decomposition_at_aux {n : ℕ}
    {f : (Fin n → ℂ) × ℂ → ℂ} {p : (Fin n → ℂ) × ℂ}
    (hf : AnalyticAt ℂ f p) (hf0 : f p = 0) (hnz : ¬ ∀ᶠ y in 𝓝 p, f y = 0) :
    ∃ k : ℕ, ∃ u : (Fin n → ℂ) × ℂ → ℂ,
      ∃ P : Fin k → (Fin n → ℂ) × ℂ → ℂ, ∃ m : Fin k → ℕ,
        AnalyticAt ℂ u p ∧ u p ≠ 0 ∧
        (∀ j, AnalyticAt ℂ (P j) p ∧ IsIrreducibleAt (P j) p ∧ 0 < m j) ∧
        Pairwise (fun j l ↦ IsCoprimeAt (P j) (P l) p) ∧
        f =ᶠ[𝓝 p] fun y ↦ u y * ∏ j, (P j y) ^ (m j) := by
  have hA : AnalyticAt ℂ (fun y : (Fin n → ℂ) × ℂ ↦ p + y) 0 :=
    analyticAt_const.add analyticAt_id
  have hB : AnalyticAt ℂ (fun y : (Fin n → ℂ) × ℂ ↦ y - p) p :=
    analyticAt_id.sub analyticAt_const
  have hs : Tendsto (fun y : (Fin n → ℂ) × ℂ ↦ y - p) (𝓝 p) (𝓝 0) :=
    (continuous_id.sub continuous_const).tendsto' p 0 (sub_self p)
  have hF : AnalyticAt ℂ (fun y ↦ f (p + y)) 0 := hf.comp_of_eq hA (add_zero p)
  have hF0 : (fun y ↦ f (p + y)) 0 = 0 := by simpa using hf0
  have hFnz : ¬ ∀ᶠ y in 𝓝 0, (fun y ↦ f (p + y)) y = 0 := by
    intro hev
    apply hnz
    filter_upwards [hs.eventually hev] with y hy
    simpa using hy
  obtain ⟨k, u, P, m, hu, hu0, hP, hcP, hfac⟩ :=
    spec_exists_irreducible_decomposition hF hF0 hFnz
  have hback : ∀ g : (Fin n → ℂ) × ℂ → ℂ,
      (fun y ↦ (fun y ↦ g (y - p)) (p + y)) = g := by
    intro g
    funext y
    simp
  refine ⟨k, fun y ↦ u (y - p), fun j y ↦ P j (y - p), m,
    hu.comp_of_eq hB (sub_self p), by simpa using hu0, fun j ↦ ⟨?_, ?_, (hP j).2.2⟩, ?_, ?_⟩
  · exact (hP j).1.comp_of_eq hB (sub_self p)
  · apply isIrreducibleAt_of_translate
    rw [hback]
    exact (hP j).2.1
  · intro j l hjl
    apply isCoprimeAt_of_translate
    rw [hback, hback]
    exact hcP hjl
  · filter_upwards [hs.eventually hfac] with y hy
    simpa using hy

/-- Source: Gunning--Rossi, Ch. III; Chirka, §§2--5; `spec_point_mem_closure_clean_regular_factor`. -/
theorem spec_mem_closure_clean_support_factor_aux {n k : ℕ} {ι : Type*}
    {U : Set ((Fin n → ℂ) × ℂ)} {V : ι → Set ((Fin n → ℂ) × ℂ)}
    {f : ι → (Fin n → ℂ) × ℂ → ℂ} (hD : IsLocalDivisorData U V f)
    (i : ι) (p : (Fin n → ℂ) × ℂ) (hi : p ∈ V i)
    {u : (Fin n → ℂ) × ℂ → ℂ} {P : Fin k → (Fin n → ℂ) × ℂ → ℂ} {m : Fin k → ℕ}
    (hu : AnalyticAt ℂ u p) (hu0 : u p ≠ 0)
    (hP : ∀ j, AnalyticAt ℂ (P j) p ∧ IsIrreducibleAt (P j) p ∧ 0 < m j)
    (hcP : Pairwise (fun j l ↦ IsCoprimeAt (P j) (P l) p))
    (hfac : f i =ᶠ[𝓝 p] fun y ↦ u y * ∏ j, (P j y) ^ (m j)) (j : Fin k) :
    p ∈ closure {y | y ∈ V i ∩ localDivisorSupport V f ∧ P j y = 0 ∧
      (∀ l, l ≠ j → P l y ≠ 0) ∧ fderiv ℂ (P j) y ≠ 0} := by
  have hcl := AnalyticDivisorAlgebraic13.spec_point_mem_closure_clean_regular_factor p
    (fun l ↦ ⟨(hP l).1, (hP l).2.1⟩) hcP j
  have hN : ∀ᶠ y in 𝓝 p, y ∈ V i ∧ f i y = u y * ∏ j, (P j y) ^ (m j) :=
    (eventually_mem_set.mpr ((hD.1 i).mem_nhds hi)).and hfac
  rw [mem_closure_iff_nhds] at hcl ⊢
  intro t ht
  obtain ⟨y, ⟨hyt, hyN⟩, hyP, hyl, hyd⟩ := hcl _ (inter_mem ht hN)
  refine ⟨y, hyt, ⟨hyN.1, i, hyN.1, ?_⟩, hyP, hyl, hyd⟩
  rw [hyN.2, Finset.prod_eq_zero (Finset.mem_univ j), mul_zero]
  rw [hyP, zero_pow (hP j).2.2.ne']

/-- Source: Gunning--Rossi, II.B, Theorems 3--6 and Ch. III; Chirka, §§2--5. -/
theorem spec_mem_support_exists_clean_decomposition_aux {n : ℕ} {ι : Type*}
    {U : Set ((Fin n → ℂ) × ℂ)} {V : ι → Set ((Fin n → ℂ) × ℂ)}
    {f : ι → (Fin n → ℂ) × ℂ → ℂ} (hD : IsLocalDivisorData U V f)
    (i : ι) (p : (Fin n → ℂ) × ℂ) (hi : p ∈ V i) (hp : p ∈ localDivisorSupport V f) :
    ∃ k : ℕ, ∃ u : (Fin n → ℂ) × ℂ → ℂ,
      ∃ P : Fin k → (Fin n → ℂ) × ℂ → ℂ, ∃ m : Fin k → ℕ,
        0 < k ∧ AnalyticAt ℂ u p ∧ u p ≠ 0 ∧
        (∀ j, AnalyticAt ℂ (P j) p ∧ IsIrreducibleAt (P j) p ∧ 0 < m j) ∧
        Pairwise (fun j l ↦ IsCoprimeAt (P j) (P l) p) ∧
        (f i =ᶠ[𝓝 p] fun y ↦ u y * ∏ j, (P j y) ^ (m j)) ∧
        ∀ j, p ∈ closure {y | y ∈ V i ∩ localDivisorSupport V f ∧ P j y = 0 ∧
          (∀ l, l ≠ j → P l y ≠ 0) ∧ fderiv ℂ (P j) y ≠ 0} := by
  have hf0 : f i p = 0 := (spec_mem_localDivisorSupport_iff_aux hD i p hi).1 hp
  obtain ⟨k, u, P, m, hu, hu0, hP, hcP, hfac⟩ :=
    spec_exists_irreducible_decomposition_at_aux (hD.2.2.1 i p hi) hf0 (hD.2.2.2.1 i p hi)
  refine ⟨k, u, P, m, ?_, hu, hu0, hP, hcP, hfac, fun j ↦
    spec_mem_closure_clean_support_factor_aux hD i p hi hu hu0 hP hcP hfac j⟩
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have h := hfac.self_of_nhds
    simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one] at h
    exact absurd (h ▸ hf0) hu0
  · exact hk

end HodgeLean.Foundations.AnalyticDivisorAlgebraic14
