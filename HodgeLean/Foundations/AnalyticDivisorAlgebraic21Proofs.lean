import HodgeLean.Foundations.AnalyticDivisorAlgebraic21Defs
import Mathlib.Analysis.Normed.Module.Connected

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic21

open Filter Set Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7
open HodgeLean.Foundations.AnalyticDivisorAlgebraic8
open HodgeLean.Foundations.AnalyticDivisorAlgebraic14
open HodgeLean.Foundations.AnalyticDivisorAlgebraic17

/-- Product coordinates in positive complex dimension.
Source: `ContinuousLinearEquiv.ofFinrankEq`. -/
def gaga21_br_coord {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {n : ℕ} (h : Module.finrank ℂ E = n + 1) :
    E ≃L[ℂ] (Fin n → ℂ) × ℂ :=
  ContinuousLinearEquiv.ofFinrankEq (by simpa using h)

/-- Vector coordinates in arbitrary finite complex dimension.
Source: `ContinuousLinearEquiv.ofFinrankEq`. -/
def gaga21_br_coord_fin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {n : ℕ} (h : Module.finrank ℂ E = n) :
    E ≃L[ℂ] (Fin n → ℂ) :=
  ContinuousLinearEquiv.ofFinrankEq (by simpa using h)

example {n : ℕ} : ((Fin n → ℂ) × ℂ) ≃L[ℂ] (Fin n → ℂ) × ℂ :=
  gaga21_br_coord (by simp)
example {n : ℕ} : (Fin n → ℂ) ≃L[ℂ] (Fin n → ℂ) :=
  gaga21_br_coord_fin (by simp)

section Transport
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem gaga21_br_analyticAt (e : E ≃L[ℂ] F) (f : F → ℂ) (p : E) :
    AnalyticAt ℂ (fun x ↦ f (e x)) p ↔ AnalyticAt ℂ f (e p) := by
  constructor
  · intro h
    simpa only [Filter.EventuallyEq, Function.comp_def, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply]
      using (h.comp_of_eq (e.symm.toContinuousLinearMap.analyticAt (e p)) (e.symm_apply_apply p))
  · intro h
    exact h.comp (e.toContinuousLinearMap.analyticAt p)

theorem gaga21_br_eventually (e : E ≃L[ℂ] F) (P : F → Prop) (p : E) :
    (∀ᶠ x in 𝓝 p, P (e x)) ↔ ∀ᶠ y in 𝓝 (e p), P y := by
  constructor
  · intro h
    simpa only [Filter.EventuallyEq, Function.comp_def, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using
      (show Tendsto e.symm (𝓝 (e p)) (𝓝 p) by simpa using e.symm.continuous.tendsto (e p)).eventually h
  · exact fun h ↦ (e.continuous.tendsto p).eventually h

theorem gaga21_br_irreducible (e : E ≃L[ℂ] F) (f : F → ℂ) (p : E) :
    IsIrreducibleAt (fun x ↦ f (e x)) p ↔ IsIrreducibleAt f (e p) := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro g k hg hk he
    exact h.2 (fun x ↦ g (e x)) (fun x ↦ k (e x))
      (hg.comp (e.toContinuousLinearMap.analyticAt _))
      (hk.comp (e.toContinuousLinearMap.analyticAt _))
      ((e.continuous.tendsto p).eventually he)
  · intro h
    refine ⟨h.1, ?_⟩
    intro g k hg hk he
    have he' := (show Tendsto e.symm (𝓝 (e p)) (𝓝 p) by
      simpa using e.symm.continuous.tendsto (e p)).eventually he
    simp only [ContinuousLinearEquiv.apply_symm_apply] at he'
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using
      h.2 (fun y ↦ g (e.symm y)) (fun y ↦ k (e.symm y))
        ((gaga21_br_analyticAt e.symm g (e p)).2 (by simpa using hg))
        ((gaga21_br_analyticAt e.symm k (e p)).2 (by simpa using hk)) he'

theorem gaga21_br_associated (e : E ≃L[ℂ] F) (f g : F → ℂ) (p : E) :
    AreAssociatedAt (fun x ↦ f (e x)) (fun x ↦ g (e x)) p ↔
      AreAssociatedAt f g (e p) := by
  constructor
  · rintro ⟨u, hu, hn, he⟩
    refine ⟨fun y ↦ u (e.symm y), ((gaga21_br_analyticAt e.symm u (e p)).2 (by simpa using hu)),
      by simpa using hn, ?_⟩
    simpa only [Filter.EventuallyEq, Function.comp_def, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using
      (show Tendsto e.symm (𝓝 (e p)) (𝓝 p) by simpa using e.symm.continuous.tendsto (e p)).eventually he
  · rintro ⟨u, hu, hn, he⟩
    exact ⟨fun x ↦ u (e x), hu.comp (e.toContinuousLinearMap.analyticAt _), hn,
      (e.continuous.tendsto p).eventually he⟩

theorem gaga21_br_coprime (e : E ≃L[ℂ] F) (f g : F → ℂ) (p : E) :
    IsCoprimeAt (fun x ↦ f (e x)) (fun x ↦ g (e x)) p ↔
      IsCoprimeAt f g (e p) := by
  constructor
  · intro h ⟨q, r, s, hq, hr, hs, hz, hf, hg⟩
    exact h ⟨fun x ↦ q (e x), fun x ↦ r (e x), fun x ↦ s (e x),
      hq.comp (e.toContinuousLinearMap.analyticAt _),
      hr.comp (e.toContinuousLinearMap.analyticAt _),
      hs.comp (e.toContinuousLinearMap.analyticAt _), hz,
      (e.continuous.tendsto p).eventually hf, (e.continuous.tendsto p).eventually hg⟩
  · intro h ⟨q, r, s, hq, hr, hs, hz, hf, hg⟩
    refine h ⟨fun y ↦ q (e.symm y), fun y ↦ r (e.symm y), fun y ↦ s (e.symm y),
      ((gaga21_br_analyticAt e.symm q (e p)).2 (by simpa using hq)),
      ((gaga21_br_analyticAt e.symm r (e p)).2 (by simpa using hr)),
      ((gaga21_br_analyticAt e.symm s (e p)).2 (by simpa using hs)), by simpa using hz, ?_, ?_⟩
    · simpa only [Filter.EventuallyEq, Function.comp_def, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using
        (show Tendsto e.symm (𝓝 (e p)) (𝓝 p) by simpa using e.symm.continuous.tendsto (e p)).eventually hf
    · simpa only [Filter.EventuallyEq, Function.comp_def, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using
        (show Tendsto e.symm (𝓝 (e p)) (𝓝 p) by simpa using e.symm.continuous.tendsto (e p)).eventually hg

theorem gaga21_br_fderiv_ne_zero (e : E ≃L[ℂ] F) (f : F → ℂ) (p : E) :
    fderiv ℂ (fun x ↦ f (e x)) p ≠ 0 ↔ fderiv ℂ f (e p) ≠ 0 := by
  rw [show (fun x ↦ f (e x)) = f ∘ e from rfl, e.comp_right_fderiv]
  constructor
  · intro h hz
    exact h (by rw [hz, ContinuousLinearMap.zero_comp])
  · intro h hz
    apply h
    ext y
    have he := congrArg (fun L : E →L[ℂ] ℂ ↦ L (e.symm y)) hz
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, zero_apply] using he

theorem gaga21_br_localDivisorData {ι : Type*} (e : E ≃L[ℂ] F)
    {U : Set F} {V : ι → Set F} {f : ι → F → ℂ}
    (h : IsLocalDivisorData U V f) :
    IsLocalDivisorData (e ⁻¹' U) (fun i ↦ e ⁻¹' V i) (fun i x ↦ f i (e x)) := by
  refine ⟨fun i ↦ (h.1 i).preimage e.continuous, ?_, ?_, ?_, ?_⟩
  · rw [← preimage_iUnion, h.2.1]
  · intro i x hx
    exact (gaga21_br_analyticAt e (f i) x).2 (h.2.2.1 i (e x) hx)
  · intro i x hx hz
    exact h.2.2.2.1 i (e x) hx ((gaga21_br_eventually e (fun y ↦ f i y = 0) x).1 hz)
  · intro i j x hx
    exact (gaga21_br_associated e (f i) (f j) x).2 (h.2.2.2.2 i j (e x) hx)

end Transport

theorem gaga21_br_no_occurrence_dim_zero {E ι : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] (h : Module.finrank ℂ E = 0)
    {V : ι → Set E} {f : ι → E → ℂ} (a : gaga21_LocalFactorOccurrence V f) : False := by
  let e := gaga21_br_coord_fin h
  have hi := (gaga21_br_irreducible e.symm a.factor (e a.point)).2
    (by simpa [gaga21_LocalFactorOccurrence.factor] using (a.factor_data a.selected).2.1)
  exact AnalyticDivisorAlgebraic18.gaga18_no_irreducible_zero (e a.point)
    (fun y ↦ a.factor (e.symm y)) hi

section GeneralDimension
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E]

theorem gaga21_br_decomposition {f : E → ℂ} {p : E}
    (hf : AnalyticAt ℂ f p) (hf0 : f p = 0) (hnz : ¬ ∀ᶠ y in 𝓝 p, f y = 0) :
    ∃ k : ℕ, ∃ u : E → ℂ, ∃ P : Fin k → E → ℂ, ∃ m : Fin k → ℕ,
      AnalyticAt ℂ u p ∧ u p ≠ 0 ∧
      (∀ j, AnalyticAt ℂ (P j) p ∧ IsIrreducibleAt (P j) p ∧ 0 < m j) ∧
      Pairwise (fun j l ↦ IsCoprimeAt (P j) (P l) p) ∧
      f =ᶠ[𝓝 p] fun y ↦ u y * ∏ j, P j y ^ m j := by
  have hdim : Module.finrank ℂ E ≠ 0 := by
    intro h
    let e := gaga21_br_coord_fin h
    apply hnz
    exact Eventually.of_forall fun y ↦ by
      have hy : y = p := e.injective (Subsingleton.elim _ _)
      rw [hy, hf0]
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hdim
  let e := gaga21_br_coord (E := E) hn
  have ha : AnalyticAt ℂ (fun y ↦ f (e.symm y)) (e p) :=
    (gaga21_br_analyticAt e.symm f (e p)).2 (by simpa using hf)
  obtain ⟨k, u, P, m, hu, hu0, hP, hc, he⟩ :=
    spec_exists_irreducible_decomposition_at ha (by simpa using hf0)
      (by intro hz; apply hnz; simpa only [ContinuousLinearEquiv.symm_apply_apply] using
          (e.continuous.tendsto p).eventually hz)
  refine ⟨k, fun x ↦ u (e x), fun j x ↦ P j (e x), m,
    (gaga21_br_analyticAt e u p).2 hu, hu0, ?_, ?_, ?_⟩
  · intro j
    exact ⟨(gaga21_br_analyticAt e (P j) p).2 (hP j).1,
      (gaga21_br_irreducible e (P j) p).2 (hP j).2.1, (hP j).2.2⟩
  · intro j l hjl
    exact (gaga21_br_coprime e (P j) (P l) p).2 (hc hjl)
  · simpa only [Filter.EventuallyEq, ContinuousLinearEquiv.symm_apply_apply] using
      (e.continuous.tendsto p).eventually he

theorem gaga21_br_nullstellensatz (p : E) (g h : E → ℂ)
    (hg : AnalyticAt ℂ g p) (hh : AnalyticAt ℂ h p)
    (hgi : IsIrreducibleAt g p) (hz : ∀ᶠ z in 𝓝 p, g z = 0 → h z = 0) :
    ∃ c : E → ℂ, AnalyticAt ℂ c p ∧ h =ᶠ[𝓝 p] fun z ↦ g z * c z := by
  let e := gaga21_br_coord_fin (E := E) rfl
  have ht : Tendsto e.symm (𝓝 (e p)) (𝓝 p) := by
    simpa using e.symm.continuous.tendsto (e p)
  obtain ⟨c, hc, he⟩ := AnalyticDivisorAlgebraic18.spec_hypersurface_nullstellensatz
    (Module.finrank ℂ E) (e p) (fun y ↦ g (e.symm y)) (fun y ↦ h (e.symm y))
    ((gaga21_br_analyticAt e.symm g (e p)).2 (by simpa using hg))
    ((gaga21_br_analyticAt e.symm h (e p)).2 (by simpa using hh))
    ((gaga21_br_irreducible e.symm g (e p)).2 (by simpa using hgi)) (ht.eventually hz)
  refine ⟨fun x ↦ c (e x), (gaga21_br_analyticAt e c p).2 hc, ?_⟩
  simpa only [Filter.EventuallyEq, ContinuousLinearEquiv.symm_apply_apply] using
    (e.continuous.tendsto p).eventually he

theorem gaga21_br_eventually_pairwise_coprime (r : ℕ) (p : E)
    (P : Fin r → E → ℂ) (hP : ∀ a, AnalyticAt ℂ (P a) p)
    (hiP : ∀ a, IsIrreducibleAt (P a) p)
    (hcP : Pairwise (fun a b ↦ IsCoprimeAt (P a) (P b) p)) :
    ∃ N, IsOpen N ∧ p ∈ N ∧ ∀ q ∈ N, ∀ a b, a ≠ b →
      ¬ ∃ A s t : E → ℂ, AnalyticAt ℂ A q ∧ IsIrreducibleAt A q ∧
        AnalyticAt ℂ s q ∧ (P a =ᶠ[𝓝 q] fun z ↦ A z * s z) ∧
        AnalyticAt ℂ t q ∧ (P b =ᶠ[𝓝 q] fun z ↦ A z * t z) := by
  let e := gaga21_br_coord_fin (E := E) rfl
  obtain ⟨N, hNo, hpN, hN⟩ := AnalyticDivisorAlgebraic18.spec_eventually_pairwise_coprime
    (Module.finrank ℂ E) r (e p) (fun a y ↦ P a (e.symm y))
    (fun a ↦ (gaga21_br_analyticAt e.symm (P a) (e p)).2 (by simpa using hP a))
    (fun a ↦ (gaga21_br_irreducible e.symm (P a) (e p)).2 (by simpa using hiP a))
    (fun a b hab ↦ (gaga21_br_coprime e.symm (P a) (P b) (e p)).2
      (by simpa using hcP hab))
  refine ⟨e ⁻¹' N, hNo.preimage e.continuous, hpN, ?_⟩
  intro q hq a b hab ⟨A, s, t, hA, hiA, hs, hes, ht, het⟩
  have hT : Tendsto e.symm (𝓝 (e q)) (𝓝 q) := by
    simpa using e.symm.continuous.tendsto (e q)
  exact hN (e q) hq a b hab ⟨fun y ↦ A (e.symm y), fun y ↦ s (e.symm y),
    fun y ↦ t (e.symm y),
    (gaga21_br_analyticAt e.symm A (e q)).2 (by simpa using hA),
    (gaga21_br_irreducible e.symm A (e q)).2 (by simpa using hiA),
    (gaga21_br_analyticAt e.symm s (e q)).2 (by simpa using hs), hT.eventually hes,
    (gaga21_br_analyticAt e.symm t (e q)).2 (by simpa using ht), hT.eventually het⟩

theorem gaga21_br_regular_locus (p : E) (f : E → ℂ)
    (hf : AnalyticAt ℂ f p) (hf0 : f p = 0) (hi : IsIrreducibleAt f p) :
    ∃ W ∈ 𝓝 p, IsOpen W ∧ p ∈ W ∧
      closure (AnalyticDivisorAlgebraic20.gaga20_regularZero f ∩ W) =
        {x | f x = 0} ∩ closure W ∧
      IsConnected (AnalyticDivisorAlgebraic20.gaga20_regularZero f ∩ W) := by
  let e := gaga21_br_coord_fin (E := E) rfl
  obtain ⟨W, _, hWo, hpW, hcl, hc⟩ := AnalyticDivisorAlgebraic20.gaga20_regular_locus
    (e p) (fun y ↦ f (e.symm y))
    ((gaga21_br_analyticAt e.symm f (e p)).2 (by simpa using hf))
    (by simpa using hf0)
    ((gaga21_br_irreducible e.symm f (e p)).2 (by simpa using hi))
  have hreg : e ⁻¹' AnalyticDivisorAlgebraic20.gaga20_regularZero (fun y ↦ f (e.symm y)) =
      AnalyticDivisorAlgebraic20.gaga20_regularZero f := by
    ext x
    simp only [mem_preimage, AnalyticDivisorAlgebraic20.gaga20_regularZero, mem_ofPred_eq,
      gaga21_br_fderiv_ne_zero, ContinuousLinearEquiv.symm_apply_apply]
  refine ⟨e ⁻¹' W, (hWo.preimage e.continuous).mem_nhds hpW,
    hWo.preimage e.continuous, hpW, ?_, ?_⟩
  · have hpre (S : Set (Fin (Module.finrank ℂ E) → ℂ)) :
        e ⁻¹' closure S = closure (e ⁻¹' S) := e.toHomeomorph.preimage_closure S
    have he := congrArg (fun S ↦ e ⁻¹' S) hcl
    simpa only [hpre, preimage_inter, hreg,
      preimage_ofPred_eq, ContinuousLinearEquiv.symm_apply_apply] using he
  · have he := e.toHomeomorph.isConnected_preimage.mpr hc
    change IsConnected (e ⁻¹' (_ ∩ W)) at he
    simpa only [preimage_inter, hreg] using he

theorem gaga21_br_nearby_factor_matching {r : ℕ} {ι : Type*}
    {U : Set (E)} {V : ι → Set (E)}
    {f : ι → E → ℂ} (hD : IsLocalDivisorData U V f)
    (i : ι) {p q : E} {N : Set (E)}
    (hNo : IsOpen N) (hNp : N ∈ 𝓝 p) (hNV : N ⊆ V i) (hqN : q ∈ N)
    {v : E → ℂ} {P : Fin r → E → ℂ}
    {b : Fin r → ℕ} (hv : AnalyticOnNhd ℂ v N) (hv0 : v p ≠ 0)
    (hP : ∀ a, AnalyticOnNhd ℂ (P a) N)
    (hirr : ∀ a, IsIrreducibleAt (P a) p) (hb : ∀ a, 0 < b a)
    (hcop : Pairwise (fun a c ↦ IsCoprimeAt (P a) (P c) p))
    (hfacN : ∀ y ∈ N, f i y = v y * ∏ a, P a y ^ b a)
    (a : Fin r) (hzero : P a q = 0)
    {k : ℕ} {u : E → ℂ}
    {Q : Fin k → E → ℂ} {d : Fin k → ℕ}
    (hu : AnalyticAt ℂ u q) (hu0 : u q ≠ 0)
    (hQ : ∀ j, AnalyticAt ℂ (Q j) q ∧ IsIrreducibleAt (Q j) q ∧ 0 < d j)
    (hcQ : Pairwise (fun j l ↦ IsCoprimeAt (Q j) (Q l) q))
    (hfacQ : P a =ᶠ[𝓝 q] fun y ↦ u y * ∏ j, Q j y ^ d j)
    {t : ℕ} {w : E → ℂ}
    {R : Fin t → E → ℂ} {e : Fin t → ℕ}
    (hw : AnalyticAt ℂ w q) (hw0 : w q ≠ 0)
    (hR : ∀ l, AnalyticAt ℂ (R l) q ∧ IsIrreducibleAt (R l) q ∧ 0 < e l)
    (hcR : Pairwise (fun l s ↦ IsCoprimeAt (R l) (R s) q))
    (hfacR : f i =ᶠ[𝓝 q] fun y ↦ w y * ∏ l, R l y ^ e l) :
    ∀ j, ∃ l, AreAssociatedAt (Q j) (R l) q := by
  have hdim : Module.finrank ℂ E ≠ 0 := by
    intro hz
    let c := gaga21_br_coord_fin (E := E) hz
    exact AnalyticDivisorAlgebraic18.gaga18_no_irreducible_zero (c p)
      (fun y ↦ P a (c.symm y))
      ((gaga21_br_irreducible c.symm (P a) (c p)).2 (by simpa using hirr a))
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hdim
  let c := gaga21_br_coord (E := E) hn
  have tp : Tendsto c.symm (𝓝 (c p)) (𝓝 p) := by
    simpa using c.symm.continuous.tendsto (c p)
  have tq : Tendsto c.symm (𝓝 (c q)) (𝓝 q) := by
    simpa using c.symm.continuous.tendsto (c q)
  have an (g : E → ℂ) (x : E) (h : AnalyticAt ℂ g x) :
      AnalyticAt ℂ (fun y ↦ g (c.symm y)) (c x) :=
    (gaga21_br_analyticAt c.symm g (c x)).2 (by simpa using h)
  have ir (g : E → ℂ) (x : E) (h : IsIrreducibleAt g x) :
      IsIrreducibleAt (fun y ↦ g (c.symm y)) (c x) :=
    (gaga21_br_irreducible c.symm g (c x)).2 (by simpa using h)
  have cp (g h : E → ℂ) (x : E) (hc : IsCoprimeAt g h x) :
      IsCoprimeAt (fun y ↦ g (c.symm y)) (fun y ↦ h (c.symm y)) (c x) :=
    (gaga21_br_coprime c.symm g h (c x)).2 (by simpa using hc)
  have hm := spec_nearby_factor_matching (gaga21_br_localDivisorData c.symm hD) i
    (hNo.preimage c.symm.continuous) (tp.eventually hNp)
    (fun y hy ↦ hNV hy) (show c q ∈ c.symm ⁻¹' N by simpa using hqN)
    (fun y hy ↦ (hv (c.symm y) hy).comp (c.symm.toContinuousLinearMap.analyticAt y))
    (show v (c.symm (c p)) ≠ 0 by simpa using hv0)
    (fun a y hy ↦ (hP a (c.symm y) hy).comp (c.symm.toContinuousLinearMap.analyticAt y))
    (fun a ↦ ir (P a) p (hirr a)) hb (fun a b hab ↦ cp (P a) (P b) p (hcop hab))
    (fun y hy ↦ hfacN (c.symm y) hy) a (show P a (c.symm (c q)) = 0 by simpa using hzero)
    (an u q hu) (show u (c.symm (c q)) ≠ 0 by simpa using hu0)
    (fun j ↦ ⟨an (Q j) q (hQ j).1, ir (Q j) q (hQ j).2.1, (hQ j).2.2⟩)
    (fun j l hjl ↦ cp (Q j) (Q l) q (hcQ hjl)) (tq.eventually hfacQ)
    (an w q hw) (show w (c.symm (c q)) ≠ 0 by simpa using hw0)
    (fun l ↦ ⟨an (R l) q (hR l).1, ir (R l) q (hR l).2.1, (hR l).2.2⟩)
    (fun l s hls ↦ cp (R l) (R s) q (hcR hls)) (tq.eventually hfacR)
  intro j
  obtain ⟨l, hl⟩ := hm j
  exact ⟨l, by simpa using (gaga21_br_associated c.symm (Q j) (R l) (c q)).1 hl⟩

theorem gaga21_br_pair_propagation (p : E)
    (F G : E → ℂ)
    (hF : AnalyticAt ℂ F p) (hG : AnalyticAt ℂ G p)
    (hiF : IsIrreducibleAt F p) (hiG : IsIrreducibleAt G p)
    (hc : IsCoprimeAt F G p) :
    ∀ᶠ q in nhds p, IsCoprimeAt F G q ∧
      ∀ (k l : ℕ) (u v : E → ℂ)
        (Q : Fin k → E → ℂ)
        (R : Fin l → E → ℂ)
        (d : Fin k → ℕ) (e : Fin l → ℕ),
        AnalyticAt ℂ u q → u q ≠ 0 → AnalyticAt ℂ v q → v q ≠ 0 →
        (∀ j, AnalyticAt ℂ (Q j) q ∧ IsIrreducibleAt (Q j) q ∧ 0 < d j) →
        (∀ j, AnalyticAt ℂ (R j) q ∧ IsIrreducibleAt (R j) q ∧ 0 < e j) →
        Pairwise (fun j j' ↦ IsCoprimeAt (Q j) (Q j') q) →
        Pairwise (fun j j' ↦ IsCoprimeAt (R j) (R j') q) →
        (F =ᶠ[nhds q] fun z ↦ u z * ∏ j, Q j z ^ d j) →
        (G =ᶠ[nhds q] fun z ↦ v z * ∏ j, R j z ^ e j) →
        ∀ j j', ¬ AreAssociatedAt (Q j) (R j') q := by
  let L := gaga21_br_coord_fin (E := E) rfl
  have hL (x : E) : Tendsto L (nhds x) (nhds (L x)) :=
    L.continuous.continuousAt
  have hLi (x : Fin (Module.finrank ℂ E) → ℂ) :
      Tendsto L.symm (nhds x) (nhds (L.symm x)) := L.symm.continuous.continuousAt
  have hLiL (x : E) : Tendsto L.symm (nhds (L x)) (nhds x) := by
    simpa using hLi (L x)
  have hirr_iff (f : E → ℂ) (x : E) :
      IsIrreducibleAt (fun z ↦ f (L.symm z)) (L x) ↔ IsIrreducibleAt f x := by
    simpa using gaga21_br_irreducible L.symm f (L x)
  have hcop_iff (f g : E → ℂ) (x : E) :
      IsCoprimeAt (fun z ↦ f (L.symm z)) (fun z ↦ g (L.symm z)) (L x) ↔
        IsCoprimeAt f g x := by
    simpa using gaga21_br_coprime L.symm f g (L x)
  have hassoc_iff (f g : E → ℂ) (x : E) :
      AreAssociatedAt (fun z ↦ f (L.symm z)) (fun z ↦ g (L.symm z)) (L x) ↔
        AreAssociatedAt f g x := by
    simpa using gaga21_br_associated L.symm f g (L x)
  let F' : (Fin (Module.finrank ℂ E) → ℂ) → ℂ := fun z ↦ F (L.symm z)
  let G' : (Fin (Module.finrank ℂ E) → ℂ) → ℂ := fun z ↦ G (L.symm z)
  have hnear := AnalyticDivisorAlgebraic18.gaga18_pair_propagation (Module.finrank ℂ E) (L p) F' G'
    (hF.comp_of_eq (L.symm.analyticAt (L p)) (by simp))
    (hG.comp_of_eq (L.symm.analyticAt (L p)) (by simp))
    ((hirr_iff F p).2 hiF) ((hirr_iff G p).2 hiG) ((hcop_iff F G p).2 hc)
  filter_upwards [(hL p).eventually hnear] with q hq
  refine ⟨(hcop_iff F G q).1 hq.1, ?_⟩
  intro k l u v Q R d e hu hu0 hv hv0 hQ hR hcQ hcR hfacF hfacG j j'
  let u' : (Fin (Module.finrank ℂ E) → ℂ) → ℂ := fun z ↦ u (L.symm z)
  let v' : (Fin (Module.finrank ℂ E) → ℂ) → ℂ := fun z ↦ v (L.symm z)
  let Q' (i : Fin k) : (Fin (Module.finrank ℂ E) → ℂ) → ℂ := fun z ↦ Q i (L.symm z)
  let R' (i : Fin l) : (Fin (Module.finrank ℂ E) → ℂ) → ℂ := fun z ↦ R i (L.symm z)
  have hfacF' : F' =ᶠ[nhds (L q)] fun z ↦ u' z * ∏ i, Q' i z ^ d i :=
    (hLiL q).eventually hfacF |>.mono fun z hz ↦ by simpa [F', u', Q'] using hz
  have hfacG' : G' =ᶠ[nhds (L q)] fun z ↦ v' z * ∏ i, R' i z ^ e i :=
    (hLiL q).eventually hfacG |>.mono fun z hz ↦ by simpa [G', v', R'] using hz
  have hnot := hq.2 k l u' v' Q' R' d e
    (hu.comp_of_eq (L.symm.analyticAt (L q)) (by simp)) (by simpa [u'] using hu0)
    (hv.comp_of_eq (L.symm.analyticAt (L q)) (by simp)) (by simpa [v'] using hv0)
    (fun i ↦ ⟨(hQ i).1.comp_of_eq (L.symm.analyticAt (L q)) (by simp),
      (hirr_iff (Q i) q).2 (hQ i).2.1, (hQ i).2.2⟩)
    (fun i ↦ ⟨(hR i).1.comp_of_eq (L.symm.analyticAt (L q)) (by simp),
      (hirr_iff (R i) q).2 (hR i).2.1, (hR i).2.2⟩)
    (fun i j hij ↦ (hcop_iff (Q i) (Q j) q).2 (hcQ hij))
    (fun i j hij ↦ (hcop_iff (R i) (R j) q).2 (hcR hij)) hfacF' hfacG' j j'
  change ¬ AreAssociatedAt (fun z ↦ Q j (L.symm z))
    (fun z ↦ R j' (L.symm z)) (L q) at hnot
  exact (hassoc_iff (Q j) (R j') q).not.mp hnot

theorem gaga21_br_nearby_distinct_group_matching {r : ℕ} {ι : Type*}
    {U : Set (E)} {V : ι → Set (E)}
    {f : ι → E → ℂ} (hD : IsLocalDivisorData U V f)
    (i : ι) {p : E}
    {v : E → ℂ} {P : Fin r → E → ℂ}
    {b : Fin r → ℕ} (hvP : AnalyticAt ℂ v p) (hv0P : v p ≠ 0)
    (hPp : ∀ a, AnalyticAt ℂ (P a) p) (hirr : ∀ a, IsIrreducibleAt (P a) p)
    (hb : ∀ a, 0 < b a) (hcop : Pairwise (fun a c ↦ IsCoprimeAt (P a) (P c) p)) :
    ∀ᶠ q in nhds p, ∀ (N : Set (E)), IsOpen N → N ∈ nhds p →
      N ⊆ V i → q ∈ N → AnalyticOnNhd ℂ v N →
      (∀ a, AnalyticOnNhd ℂ (P a) N) →
      (∀ y ∈ N, f i y = v y * ∏ a, P a y ^ b a) →
      ∀ (a c : Fin r), a ≠ c → P a q = 0 → P c q = 0 →
      ∀ (ka kc t : ℕ) (ua uc w : E → ℂ)
        (Qa : Fin ka → E → ℂ)
        (Qc : Fin kc → E → ℂ)
        (R : Fin t → E → ℂ)
        (da : Fin ka → ℕ) (dc : Fin kc → ℕ) (e : Fin t → ℕ),
        AnalyticAt ℂ ua q → ua q ≠ 0 →
        (∀ j, AnalyticAt ℂ (Qa j) q ∧ IsIrreducibleAt (Qa j) q ∧ 0 < da j) →
        Pairwise (fun j l ↦ IsCoprimeAt (Qa j) (Qa l) q) →
        (P a =ᶠ[nhds q] fun y ↦ ua y * ∏ j, Qa j y ^ da j) →
        AnalyticAt ℂ uc q → uc q ≠ 0 →
        (∀ j, AnalyticAt ℂ (Qc j) q ∧ IsIrreducibleAt (Qc j) q ∧ 0 < dc j) →
        Pairwise (fun j l ↦ IsCoprimeAt (Qc j) (Qc l) q) →
        (P c =ᶠ[nhds q] fun y ↦ uc y * ∏ j, Qc j y ^ dc j) →
        AnalyticAt ℂ w q → w q ≠ 0 →
        (∀ l, AnalyticAt ℂ (R l) q ∧ IsIrreducibleAt (R l) q ∧ 0 < e l) →
        Pairwise (fun l s ↦ IsCoprimeAt (R l) (R s) q) →
        (f i =ᶠ[nhds q] fun y ↦ w y * ∏ l, R l y ^ e l) →
        ∀ ja jc, ∃ la lc, AreAssociatedAt (Qa ja) (R la) q ∧
          AreAssociatedAt (Qc jc) (R lc) q ∧ la ≠ lc := by
  have hall : ∀ᶠ q in nhds p, ∀ a c, a ≠ c →
      IsCoprimeAt (P a) (P c) q ∧
        ∀ (ka kc : ℕ) (ua uc : E → ℂ)
          (Qa : Fin ka → E → ℂ)
          (Qc : Fin kc → E → ℂ)
          (da : Fin ka → ℕ) (dc : Fin kc → ℕ),
          AnalyticAt ℂ ua q → ua q ≠ 0 → AnalyticAt ℂ uc q → uc q ≠ 0 →
          (∀ j, AnalyticAt ℂ (Qa j) q ∧ IsIrreducibleAt (Qa j) q ∧ 0 < da j) →
          (∀ j, AnalyticAt ℂ (Qc j) q ∧ IsIrreducibleAt (Qc j) q ∧ 0 < dc j) →
          Pairwise (fun j j' ↦ IsCoprimeAt (Qa j) (Qa j') q) →
          Pairwise (fun j j' ↦ IsCoprimeAt (Qc j) (Qc j') q) →
          (P a =ᶠ[nhds q] fun z ↦ ua z * ∏ j, Qa j z ^ da j) →
          (P c =ᶠ[nhds q] fun z ↦ uc z * ∏ j, Qc j z ^ dc j) →
          ∀ j j', ¬ AreAssociatedAt (Qa j) (Qc j') q := by
    apply eventually_all.mpr
    intro a
    apply eventually_all.mpr
    intro c
    by_cases hac : a = c
    · exact Eventually.of_forall fun _ hne ↦ False.elim (hne hac)
    · exact (gaga21_br_pair_propagation p (P a) (P c)
        (hPp a) (hPp c) (hirr a) (hirr c) (hcop hac)).mono fun _ h _ ↦ h
  filter_upwards [hall] with q hq
  intro N hNo hNp hNV hqN hv hP hfac a c hac hza hzc ka kc t ua uc w Qa Qc R da dc e
    hua hua0 hQa hcQa hfa huc huc0 hQc hcQc hfc hw hw0 hR hcR hfR ja jc
  have hdis := (hq a c hac).2 ka kc ua uc Qa Qc da dc hua hua0 huc huc0
    hQa hQc hcQa hcQc hfa hfc
  obtain ⟨la, hla⟩ := gaga21_br_nearby_factor_matching hD i hNo hNp hNV hqN hv hv0P hP hirr hb
    hcop hfac a hza hua hua0 hQa hcQa hfa hw hw0 hR hcR hfR ja
  obtain ⟨lc, hlc⟩ := gaga21_br_nearby_factor_matching hD i hNo hNp hNV hqN hv hv0P hP hirr hb
    hcop hfac c hzc huc huc0 hQc hcQc hfc hw hw0 hR hcR hfR jc
  refine ⟨la, lc, hla, hlc, ?_⟩
  intro heq
  apply hdis ja jc
  exact AnalyticDivisorAlgebraic19.gaga19_associated_of_common_right_aux hla (heq ▸ hlc)

theorem gaga21_br_regularSupport_of_clean {ι : Type} {U : Set E}
    {V : ι → Set E} {f : ι → E → ℂ} (hD : IsLocalDivisorData U V f)
    (a : gaga21_LocalFactorOccurrence V f) :
    ∀ᶠ y in 𝓝 a.point, a.factor y = 0 → fderiv ℂ a.factor y ≠ 0 →
      (∀ j, j ≠ a.selected → a.factors j y ≠ 0) →
      y ∈ gaga21_regularSupport V f ∧
        ∀ᶠ z in 𝓝 y, z ∈ localDivisorSupport V f ↔ a.factor z = 0 := by
  classical
  have han : ∀ᶠ y in 𝓝 a.point, ∀ j, AnalyticAt ℂ (a.factors j) y :=
    eventually_all.mpr fun j ↦ (a.factor_data j).1.eventually_analyticAt
  filter_upwards [(hD.1 a.chart).mem_nhds a.mem_chart, han,
    a.unit_analytic.continuousAt.eventually_ne a.unit_ne, a.unit_analytic.eventually_analyticAt,
    a.factorization.eventually_nhds]
    with y hyV hyan hyu hyua hyfac
  intro hy0 hyd hyother
  have hothers : ∀ᶠ z in 𝓝 y, ∀ j, j ≠ a.selected → a.factors j z ≠ 0 := by
    apply eventually_all.mpr
    intro j
    by_cases hj : j = a.selected
    · exact Eventually.of_forall fun _ hne ↦ (hne hj).elim
    · exact ((hyan j).continuousAt.eventually_ne (hyother j hj)).mono fun _ hz _ ↦ hz
  have hunit : ∀ᶠ z in 𝓝 y, a.unit z ≠ 0 := hyua.continuousAt.eventually_ne hyu
  have he : ∀ᶠ z in 𝓝 y, z ∈ localDivisorSupport V f ↔ a.factor z = 0 := by
    filter_upwards [(hD.1 a.chart).mem_nhds hyV, hothers, hunit, hyfac]
      with z hzV hzother hzu hzfac
    rw [spec_mem_localDivisorSupport_iff hD a.chart z hzV, hzfac,
      mul_eq_zero, or_iff_right hzu, Finset.prod_eq_zero_iff]
    constructor
    · rintro ⟨j, _, hj⟩
      have hj0 : a.factors j z = 0 := (pow_eq_zero_iff (Nat.ne_of_gt (a.factor_data j).2.2)).mp hj
      have heq : j = a.selected := by
        by_contra hne
        exact hzother j hne hj0
      simpa only [heq, gaga21_LocalFactorOccurrence.factor] using hj0
    · intro hz
      exact ⟨a.selected, Finset.mem_univ _,
        pow_eq_zero_iff (Nat.ne_of_gt (a.factor_data a.selected).2.2) |>.mpr hz⟩
  refine ⟨⟨he.self_of_nhds.mpr hy0, a.factor, hyan a.selected, hy0, hyd, he⟩, he⟩


/-- Removing countably many points from a nonempty open convex plane domain preserves
path connectedness. -/
theorem gaga21_br_convex_diff_countable {U S : Set ℂ}
    (hU : IsOpen U) (hc : Convex ℝ U) (hne : U.Nonempty) (hS : S.Countable) :
    IsPathConnected (U \ S) := by
  obtain ⟨a, haU, haS⟩ := (hS.dense_compl ℝ).inter_open_nonempty U hU hne
  refine ⟨a, ⟨haU, haS⟩, ?_⟩
  rintro b ⟨hbU, hbS⟩
  rcases eq_or_ne a b with rfl | hab
  · exact JoinedIn.refl ⟨haU, haS⟩
  let c : ℂ := (2 : ℝ)⁻¹ • (a + b)
  let x : ℂ := (2 : ℝ)⁻¹ • (b - a)
  have hca : c - x = a := by simp only [c, x]; module
  have hcb : c + x = b := by simp only [c, x]; module
  have hx : x ≠ 0 := by simpa [x] using sub_ne_zero.mpr hab.symm
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [← Module.finrank_eq_rank, Complex.finrank_real_complex]
    norm_num
  obtain ⟨v, hv⟩ := exists_linearIndependent_pair_of_one_lt_rank hrank hx
  have hbad (z : ℂ) (hz : z ∉ S) (hlin : LinearIndependent ℝ ![z - c, v]) :
      Set.Countable {t : ℝ | (segment ℝ z (c + t • v) ∩ S).Nonempty} := by
    apply countable_ofPred_nonempty_of_disjoint _ (fun _ ↦ inter_subset_right) hS
    intro t t' htt'
    apply disjoint_iff_inter_eq_empty.mpr
    rw [inter_assoc, inter_comm S, inter_assoc, inter_self, ← inter_assoc]
    have he : segment ℝ z (c + t • v) ∩ segment ℝ z (c + t' • v) = {z} := by
      simpa only [add_sub_cancel] using
        segment_inter_eq_endpoint_of_linearIndependent_of_ne hlin htt'.symm (c := c)
    rw [he, singleton_inter_eq_empty]
    exact hz
  have hb : Set.Countable {t : ℝ | (segment ℝ b (c + t • v) ∩ S).Nonempty} := by
    apply hbad b hbS
    have he : b - c = x := by rw [← hcb]; abel
    rwa [he]
  have ha : Set.Countable {t : ℝ | (segment ℝ a (c + t • v) ∩ S).Nonempty} := by
    apply hbad a haS
    have he : a - c = -x := by rw [← hca]; abel
    rw [he]
    convert hv.units_smul ![-1, 1] using 1 <;> simp [← List.ofFn_inj]
  have hcU : c ∈ U := by simpa only [midpoint_eq_smul_add, invOf_eq_inv, c] using hc.midpoint_mem haU hbU
  have hopen : IsOpen {t : ℝ | c + t • v ∈ U} :=
    hU.preimage (by fun_prop)
  have hnonempty : {t : ℝ | c + t • v ∈ U}.Nonempty := ⟨0, by simpa using hcU⟩
  obtain ⟨t, htU, ht⟩ := ((ha.union hb).dense_compl ℝ).inter_open_nonempty _ hopen hnonempty
  have hsegA : segment ℝ a (c + t • v) ⊆ U \ S := by
    intro z hz
    refine ⟨hc.segment_subset haU htU hz, ?_⟩
    intro hzS
    exact ht (Or.inl ⟨z, hz, hzS⟩)
  have hsegB : segment ℝ b (c + t • v) ⊆ U \ S := by
    intro z hz
    refine ⟨hc.segment_subset hbU htU hz, ?_⟩
    intro hzS
    exact ht (Or.inr ⟨z, hz, hzS⟩)
  exact (JoinedIn.of_segment_subset hsegA).trans (JoinedIn.of_segment_subset hsegB).symm

/-- The complement of a proper analytic zero set in a convex open domain is path connected. -/
theorem gaga21_br_convex_analytic_complement {U : Set E} {g : E → ℂ}
    (hU : IsOpen U) (hc : Convex ℝ U) (hg : AnalyticOnNhd ℂ g U)
    (hne : {x ∈ U | g x ≠ 0}.Nonempty) :
    IsPathConnected {x ∈ U | g x ≠ 0} := by
  obtain ⟨a, haU, hag⟩ := hne
  refine ⟨a, ⟨haU, hag⟩, ?_⟩
  rintro b ⟨hbU, hbg⟩
  let L : ℂ → E := fun t ↦ a + t • (b - a)
  have hL : Continuous L := by dsimp [L]; fun_prop
  have hLa : ∀ t, AnalyticAt ℂ L t := by intro t; dsimp [L]; fun_prop
  have hL0 : L 0 = a := by simp [L]
  have hL1 : L 1 = b := by simp [L]
  let D := L ⁻¹' U
  have hDo : IsOpen D := hU.preimage hL
  have hDc : Convex ℝ D := by
    exact (hc.translate_preimage_right a).linear_preimage
      ((LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight (b - a) |>.restrictScalars ℝ)
  have h0 : (0 : ℂ) ∈ D := by simpa [D, hL0] using haU
  have h1 : (1 : ℂ) ∈ D := by simpa [D, hL1] using hbU
  have hga : AnalyticOnNhd ℂ (fun t ↦ g (L t)) D := fun t ht ↦ (hg _ ht).comp (hLa t)
  have hdisc : {t | g (L t) ≠ 0} ∈ codiscreteWithin D := by
    rcases hga.eqOn_zero_or_eventually_ne_zero_of_preconnected hDc.isPreconnected with hz | hn
    · exact (hag (by simpa only [hL0, Pi.zero_apply] using hz h0)).elim
    · exact hn
  have hcount : ({t | g (L t) = 0} ∩ D).Countable := by
    apply (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
    exact isDiscrete_of_codiscreteWithin hdisc
  have hp := gaga21_br_convex_diff_countable hDo hDc ⟨0, h0⟩ hcount
  have hj := hp.joinedIn 0 ⟨h0, fun hz ↦ hag (by simpa only [Set.mem_setOf_eq, hL0] using hz.1)⟩
    1 ⟨h1, fun hz ↦ hbg (by simpa only [Set.mem_setOf_eq, hL1] using hz.1)⟩
  have hm := hj.map hL.continuousOn
  rw [hL0, hL1] at hm
  apply hm.mono
  rintro x ⟨t, ht, rfl⟩
  exact ⟨ht.1, fun hz ↦ ht.2 ⟨hz, ht.1⟩⟩

theorem gaga21_br_regular_graph_chart {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {U : Set E} {P : E → ℂ}
    (hU : IsOpen U) (hP : AnalyticOnNhd ℂ P U) {x : E}
    (hx : x ∈ AnalyticDivisorAlgebraic20.gaga20_regularZero P ∩ U) :
    ∃ (g : LinearMap.ker (fderiv ℂ P x : E →ₗ[ℂ] ℂ) → E)
      (k : E → LinearMap.ker (fderiv ℂ P x : E →ₗ[ℂ] ℂ)) (r : ℝ),
      0 < r ∧ g 0 = x ∧ Continuous k ∧ k x = 0 ∧
      AnalyticOnNhd ℂ g (Metric.ball 0 r) ∧
      MapsTo g (Metric.ball 0 r) (AnalyticDivisorAlgebraic20.gaga20_regularZero P ∩ U) ∧
      ∀ᶠ y in nhds x, k y ∈ Metric.ball 0 r ∧
        (y ∈ AnalyticDivisorAlgebraic20.gaga20_regularZero P ∩ U → g (k y) = y) := by
  classical
  obtain ⟨v, hv⟩ : ∃ v, fderiv ℂ P x v ≠ 0 := by
    by_contra hn
    apply hx.1.2
    ext v
    simpa only [zero_apply] using not_exists_not.mp hn v
  obtain ⟨e, he⟩ := AnalyticDivisorAlgebraic3.spec_exists_prodKerEquiv (fderiv ℂ P x) hv
  obtain ⟨ψ, hψ, hψ0, hgraph⟩ :=
    AnalyticDivisorAlgebraic3.spec_exists_analytic_graph (hP x hx.2) hx.1.1 hv
  let K := LinearMap.ker (fderiv ℂ P x : E →ₗ[ℂ] ℂ)
  let g : K → E := fun t ↦ x + (t : E) + ψ t • v
  let k : E → K := fun y ↦ (e.symm (y - x)).1
  have hg0 : g 0 = x := by simp [g, hψ0]
  have hk : Continuous k := continuous_fst.comp (e.symm.continuous.comp (continuous_id.sub continuous_const))
  have hk0 : k x = 0 := by simp [k]
  have hga : AnalyticAt ℂ g 0 :=
    (analyticAt_const.add (K.subtypeL.analyticAt 0)).add (hψ.smul analyticAt_const)
  have hpair : Tendsto (fun t : K ↦ (t, ψ t)) (nhds 0) (nhds 0) := by
    simpa only [ContinuousAt, id_eq, hψ0, Prod.mk_zero_zero] using continuousAt_id.prodMk hψ.continuousAt
  have hgt : Tendsto g (nhds 0) (nhds x) := by
    simpa only [ContinuousAt, hg0] using hga.continuousAt
  have hreg : ∀ᶠ y in nhds x, fderiv ℂ P y ≠ 0 :=
    (hP x hx.2).fderiv.continuousAt.eventually_ne hx.1.2
  have hgood : ∀ᶠ t in nhds (0 : K),
      AnalyticAt ℂ g t ∧ g t ∈ AnalyticDivisorAlgebraic20.gaga20_regularZero P ∩ U := by
    filter_upwards [hga.eventually_analyticAt, hpair.eventually hgraph,
      hgt.eventually hreg,
      hgt.eventually (hU.mem_nhds hx.2)] with t ha hz hr hu
    exact ⟨ha, ⟨(hz.mpr rfl), hr⟩, hu⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hgood
  refine ⟨g, k, r, hr, hg0, hk, hk0, fun t ht ↦ (hball ht).1,
    fun t ht ↦ (hball ht).2, ?_⟩
  have hevent : Tendsto (fun y ↦ e.symm (y - x)) (nhds x) (nhds 0) := by
    have ht : ContinuousAt (fun y ↦ e.symm (y - x)) x :=
      (e.symm.continuous.comp (continuous_id.sub continuous_const)).continuousAt
    simpa only [ContinuousAt, sub_self, map_zero] using ht
  filter_upwards [(hk.tendsto' _ _ hk0).eventually (Metric.ball_mem_nhds 0 hr),
    hevent.eventually hgraph] with y hy hz
  refine ⟨hy, fun hyR ↦ ?_⟩
  have hrep : x + ((e.symm (y - x)).1 : E) + (e.symm (y - x)).2 • v = y := by
    rw [add_assoc, ← he, e.apply_symm_apply, add_sub_cancel]
  have hψy := hz.mp (hrep.symm ▸ hyR.1.1)
  change x + ((e.symm (y - x)).1 : E) + ψ ((e.symm (y - x)).1) • v = y
  rw [hψy, hrep]

/-- A proper analytic zero set has dense complement in an open convex domain. -/
theorem gaga21_br_convex_analytic_complement_dense {U : Set E} {g : E → ℂ}
    (hU : IsOpen U) (hc : Convex ℝ U) (hg : AnalyticOnNhd ℂ g U)
    (hne : {x ∈ U | g x ≠ 0}.Nonempty) :
    U ⊆ closure {x ∈ U | g x ≠ 0} := by
  intro x hx
  rw [mem_closure_iff_frequently]
  by_contra hn
  have hz : g =ᶠ[𝓝 x] 0 := by
    filter_upwards [Filter.not_frequently.mp hn, hU.mem_nhds hx] with y hy hyU
    simpa only [Pi.zero_apply] using not_not.mp (fun h ↦ hy ⟨hyU, h⟩)
  have hall := hg.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc.isPreconnected hx hz
  obtain ⟨y, hyU, hy⟩ := hne
  exact hy (hall hyU)

/-- Local preconnected pieces with dense intersection propagate connectedness of a subset. -/
theorem gaga21_br_connected_dense_of_local {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] {S : Set X} (hne : S.Nonempty)
    (hloc : ∀ x : X, ∃ T ∈ 𝓝 x, IsPreconnected (T ∩ S) ∧
      ((T ∩ S).Nonempty → T ⊆ closure (T ∩ S))) : IsConnected S ∧ Dense S := by
  obtain ⟨a, ha⟩ := hne
  let C := connectedComponentIn S a
  have haC : a ∈ C := mem_connectedComponentIn ha
  have hCS : C ⊆ S := connectedComponentIn_subset S a
  have hclosed : IsClosed (closure C) := isClosed_closure
  have hopen : IsOpen (closure C) := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    obtain ⟨T, hT, hc, hd⟩ := hloc x
    obtain ⟨z, hzC, hzT⟩ := ((mem_closure_iff_frequently.mp hx).and_eventually hT).exists
    have hzTS : z ∈ T ∩ S := ⟨hzT, hCS hzC⟩
    have hsub : T ∩ S ⊆ C := by
      have hh := hc.subset_connectedComponentIn hzTS inter_subset_right
      rwa [← connectedComponentIn_eq hzC] at hh
    exact Filter.mem_of_superset hT ((hd ⟨z, hzTS⟩).trans (closure_mono hsub))
  have heq : closure C = univ := (show IsClopen (closure C) from ⟨hclosed, hopen⟩).eq_univ
    ⟨a, subset_closure haC⟩
  have hp : IsPreconnected (closure C ∩ S) :=
    isPreconnected_connectedComponentIn.subset_closure
      (fun x hx ↦ ⟨subset_closure hx, hCS hx⟩) inter_subset_left
  refine ⟨⟨⟨a, ha⟩, by simpa only [heq, univ_inter] using hp⟩, ?_⟩
  intro x
  exact closure_mono hCS (heq.symm ▸ mem_univ x)

/-- Removing an analytic zero set from a connected regular hypersurface preserves
connectedness whenever the complement is nonempty. -/
theorem gaga21_br_regular_complement_connected_dense {U : Set E} {P Q : E → ℂ}
    (hU : IsOpen U) (hP : AnalyticOnNhd ℂ P U) (hQ : AnalyticOnNhd ℂ Q U)
    (hc : IsConnected (AnalyticDivisorAlgebraic20.gaga20_regularZero P ∩ U))
    (hne : {x ∈ AnalyticDivisorAlgebraic20.gaga20_regularZero P ∩ U | Q x ≠ 0}.Nonempty) :
    IsConnected {x ∈ AnalyticDivisorAlgebraic20.gaga20_regularZero P ∩ U | Q x ≠ 0} ∧
      AnalyticDivisorAlgebraic20.gaga20_regularZero P ∩ U ⊆
        closure {x ∈ AnalyticDivisorAlgebraic20.gaga20_regularZero P ∩ U | Q x ≠ 0} := by
  let R := AnalyticDivisorAlgebraic20.gaga20_regularZero P ∩ U
  let S : Set R := {x | Q x ≠ 0}
  haveI : PreconnectedSpace R := isPreconnected_iff_preconnectedSpace.mp hc.2
  have hS : IsConnected S ∧ Dense S := by
    apply gaga21_br_connected_dense_of_local
    · obtain ⟨x, hx, hn⟩ := hne
      exact ⟨⟨x, hx⟩, hn⟩
    intro x
    obtain ⟨g, k, r, hr, hg0, hk, hk0, hga, hgR, hrecover⟩ :=
      gaga21_br_regular_graph_chart hU hP x.property
    let B := Metric.ball (0 : LinearMap.ker (fderiv ℂ P x : E →ₗ[ℂ] ℂ)) r
    let A := {t ∈ B | Q (g t) ≠ 0}
    let T : Set R := ((↑) : R → E) ⁻¹' (g '' B)
    have hT : T ∈ 𝓝 x := by
      filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds hrecover] with y hy
      exact ⟨k y, hy.1, hy.2 y.property⟩
    have hqa : AnalyticOnNhd ℂ (fun t ↦ Q (g t)) B :=
      fun t ht ↦ (hQ _ (hgR ht).2).comp (hga _ ht)
    have himage : ((↑) : R → E) '' (T ∩ S) = g '' A := by
      ext y
      constructor
      · rintro ⟨z, ⟨⟨t, ht, htz⟩, hz⟩, rfl⟩
        exact ⟨t, ⟨ht, by simpa only [S, Set.mem_setOf_eq, htz] using hz⟩, htz⟩
      · rintro ⟨t, ⟨ht, hqt⟩, rfl⟩
        exact ⟨⟨g t, hgR ht⟩, ⟨⟨t, ht, rfl⟩, hqt⟩, rfl⟩
    refine ⟨T, hT, ?_, ?_⟩
    · apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
      rw [himage]
      by_cases hA : A.Nonempty
      · exact (gaga21_br_convex_analytic_complement Metric.isOpen_ball
          (convex_ball _ _) hqa hA).isConnected.2.image g
          (hga.continuousOn.mono (fun _ ht ↦ ht.1))
      · rw [Set.not_nonempty_iff_eq_empty.mp hA, image_empty]
        exact isPreconnected_empty
    · intro hTS y hy
      have hA : A.Nonempty := by
        have hn := hTS.image ((↑) : R → E)
        rw [himage] at hn
        exact hn.of_image
      obtain ⟨t, ht, hty⟩ := hy
      rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, himage]
      change (y : E) ∈ closure (g '' A)
      rw [← hty]
      exact mem_closure_image (hga t ht).continuousAt
        (gaga21_br_convex_analytic_complement_dense Metric.isOpen_ball
          (convex_ball _ _) hqa hA ht)
  have himage : ((↑) : R → E) '' S = {x ∈ R | Q x ≠ 0} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · rintro ⟨hx, hn⟩
      exact ⟨⟨x, hx⟩, hn, rfl⟩
  refine ⟨?_, ?_⟩
  · simpa only [himage] using hS.1.image ((↑) : R → E) continuous_subtype_val.continuousOn
  · intro x hx
    have hd := hS.2 (⟨x, hx⟩ : R)
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, himage] at hd
    exact hd

/-- The connected regular-locus neighborhood may be chosen inside any prescribed open
neighborhood of the anchor; density is stated relative to that neighborhood. -/
theorem gaga21_br_regular_locus_within (p : E) (f : E → ℂ)
    (hf : AnalyticAt ℂ f p) (hi : IsIrreducibleAt f p)
    {O : Set E} (hO : IsOpen O) (hpO : p ∈ O) :
    ∃ W, IsOpen W ∧ p ∈ W ∧ W ⊆ O ∧
      IsConnected (AnalyticDivisorAlgebraic20.gaga20_regularZero f ∩ W) ∧
      {x ∈ W | f x = 0} ⊆
        closure (AnalyticDivisorAlgebraic20.gaga20_regularZero f ∩ W) := by
  classical
  let F : E → ℂ := fun x ↦ if x ∈ O then f x else 1
  have he (x : E) (hx : x ∈ O) : F =ᶠ[𝓝 x] f := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact if_pos hy
  have hFp : F p = 0 := (he p hpO).self_of_nhds.trans hi.1
  have hFi : IsIrreducibleAt F p :=
    ⟨hFp, fun g h hg hh hfac ↦ hi.2 g h hg hh ((he p hpO).symm.trans hfac)⟩
  obtain ⟨W, _, hWo, hpW, hd, hc⟩ :=
    gaga21_br_regular_locus p F (hf.congr (he p hpO).symm) hFp hFi
  have hreg : AnalyticDivisorAlgebraic20.gaga20_regularZero F ∩ W =
      AnalyticDivisorAlgebraic20.gaga20_regularZero f ∩ (W ∩ O) := by
    ext x
    constructor
    · rintro ⟨⟨hx0, hxd⟩, hxW⟩
      have hxO : x ∈ O := by
        by_contra hn
        have hh : F x = 1 := if_neg hn
        exact one_ne_zero (hh.symm.trans hx0)
      exact ⟨⟨(he x hxO).self_of_nhds.symm.trans hx0,
        (he x hxO).fderiv_eq (𝕜 := ℂ) ▸ hxd⟩, hxW, hxO⟩
    · rintro ⟨⟨hx0, hxd⟩, hxW, hxO⟩
      exact ⟨⟨(he x hxO).self_of_nhds.trans hx0,
        ((he x hxO).fderiv_eq (𝕜 := ℂ)).symm ▸ hxd⟩, hxW⟩
  refine ⟨W ∩ O, hWo.inter hO, ⟨hpW, hpO⟩, inter_subset_right, hreg ▸ hc, ?_⟩
  intro x hx
  rw [← hreg, hd]
  exact ⟨(he x hx.1.2).self_of_nhds.trans hx.2, subset_closure hx.1.1⟩

/-- Near an irreducible germ, its regular part off a coprime analytic germ is connected
and dense in its zero set. -/
theorem gaga21_br_regular_locus_off (p : E) (a g : E → ℂ)
    (ha : AnalyticAt ℂ a p) (hi : IsIrreducibleAt a p)
    (hg : AnalyticAt ℂ g p) (hcop : IsCoprimeAt a g p) :
    ∃ W, IsOpen W ∧ p ∈ W ∧
      IsConnected {x ∈ AnalyticDivisorAlgebraic20.gaga20_regularZero a ∩ W | g x ≠ 0} ∧
      {x ∈ W | a x = 0} ⊆
        closure {x ∈ AnalyticDivisorAlgebraic20.gaga20_regularZero a ∩ W | g x ≠ 0} := by
  obtain ⟨O, hO, hOo, hpO⟩ :=
    eventually_nhds_iff.mp (ha.eventually_analyticAt.and hg.eventually_analyticAt)
  obtain ⟨W, hWo, hpW, hWO, hc, hd⟩ := gaga21_br_regular_locus_within p a ha hi hOo hpO
  have hga : AnalyticOnNhd ℂ g W := fun x hx ↦ (hO x (hWO hx)).2
  have hne : {x ∈ AnalyticDivisorAlgebraic20.gaga20_regularZero a ∩ W | g x ≠ 0}.Nonempty := by
    by_contra hn
    have hzero : ∀ x ∈ AnalyticDivisorAlgebraic20.gaga20_regularZero a ∩ W, g x = 0 := by
      intro x hx
      by_contra hxg
      exact hn ⟨x, hx, hxg⟩
    have he : ∀ᶠ x in 𝓝 p, a x = 0 → g x = 0 := by
      filter_upwards [hWo.mem_nhds hpW] with x hx hxa
      exact tendsto_nhds_unique_of_frequently_eq (hga x hx).continuousAt tendsto_const_nhds
        ((mem_closure_iff_frequently.mp (hd ⟨hx, hxa⟩)).mono fun y hy ↦ hzero y hy)
    obtain ⟨c, hc, hdiv⟩ := gaga21_br_nullstellensatz p a g ha hg hi he
    exact hcop ⟨a, (fun _ ↦ 1), c, ha, analyticAt_const, hc, hi.1,
      Eventually.of_forall (fun x ↦ (mul_one (a x)).symm), hdiv⟩
  obtain ⟨hconn, hdense⟩ := gaga21_br_regular_complement_connected_dense hWo
    (fun x hx ↦ (hO x (hWO hx)).1) hga hc hne
  exact ⟨W, hWo, hpW, hconn, hd.trans (closure_minimal hdense isClosed_closure)⟩

open AnalyticDivisorAlgebraic5 in
theorem gaga21_br_squarefree_of_irreducible {f : E → ℂ} {p : E}
    (hi : IsIrreducibleAt f p) : IsSquareFreeAt f p := by
  intro r s hr hs hr0 hfac
  have he : f =ᶠ[𝓝 p] fun y ↦ r y * (r y * s y) := by
    filter_upwards [hfac] with y hy
    simpa only [pow_two, mul_assoc] using hy
  rcases hi.2 r (fun y ↦ r y * s y) hr (hr.mul hs) he with hn | hn
  · exact hn hr0
  · exact hn (by rw [hr0, zero_mul])

open AnalyticDivisorAlgebraic5 in
theorem gaga21_br_eventually_squarefree {p : E} {f : E → ℂ}
    (hf : AnalyticAt ℂ f p) (hi : IsIrreducibleAt f p) :
    ∀ᶠ q in 𝓝 p, IsSquareFreeAt f q := by
  have hn : Module.finrank ℂ E ≠ 0 := by
    intro hn
    let e := gaga21_br_coord_fin hn
    have hi' := (gaga21_br_irreducible e.symm f (e p)).2 (by simpa using hi)
    exact AnalyticDivisorAlgebraic18.gaga18_no_irreducible_zero (e p)
      (fun y ↦ f (e.symm y)) hi'
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn
  let L := gaga21_br_coord hm
  let T : ((Fin m → ℂ) × ℂ) → E := fun y ↦ p + L.symm y
  have hT (y) : AnalyticAt ℂ T y := analyticAt_const.add (L.symm.analyticAt y)
  have hfT : AnalyticAt ℂ (fun y ↦ f (T y)) 0 :=
    hf.comp_of_eq (hT 0) (by simp [T])
  have hsf := gaga21_br_squarefree_of_irreducible hi
  have hsfT : IsSquareFreeAt (fun y ↦ f (T y)) 0 := by
    intro a b ha hb ha0 hab
    let A : E → ℂ := fun z ↦ a (L (z - p))
    let B : E → ℂ := fun z ↦ b (L (z - p))
    have hS : AnalyticAt ℂ (fun z ↦ L (z - p)) p :=
      (L.analyticAt _).comp (analyticAt_id.sub analyticAt_const)
    apply hsf A B (ha.comp_of_eq hS (by simp)) (hb.comp_of_eq hS (by simp))
      (by simp [A, ha0])
    have ht : Tendsto (fun z ↦ L (z - p)) (𝓝 p) (𝓝 0) := by
      simpa only [ContinuousAt, sub_self, map_zero] using hS.continuousAt
    filter_upwards [ht.eventually hab] with z hz
    simpa [T, A, B] using hz
  have hnear := spec_eventually_isSquareFreeAt hfT hsfT
  have hS : Tendsto (fun q : E ↦ L (q - p)) (𝓝 p) (𝓝 0) := by
    have ha : AnalyticAt ℂ (fun q ↦ L (q - p)) p :=
      (L.analyticAt _).comp (analyticAt_id.sub analyticAt_const)
    simpa only [ContinuousAt, sub_self, map_zero] using ha.continuousAt
  filter_upwards [hS.eventually hnear] with q hq
  intro A B hA hB hA0 hab
  let a : ((Fin m → ℂ) × ℂ) → ℂ := fun y ↦ A (T y)
  let b : ((Fin m → ℂ) × ℂ) → ℂ := fun y ↦ B (T y)
  have hqT : T (L (q - p)) = q := by simp [T]
  apply hq a b (hA.comp_of_eq (hT _) hqT) (hB.comp_of_eq (hT _) hqT)
    (by change A (T (L (q - p))) = 0; rw [hqT, hA0])
  have ht : Tendsto T (𝓝 (L (q - p))) (𝓝 q) := by
    simpa only [ContinuousAt, hqT] using (hT (L (q - p))).continuousAt
  filter_upwards [ht.eventually hab] with y hy
  simpa [a, b] using hy

open AnalyticDivisorAlgebraic5 in
theorem gaga21_br_squarefree_comp {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (e : E ≃L[ℂ] F) (f : F → ℂ) (p : E) (hs : IsSquareFreeAt f (e p)) :
    IsSquareFreeAt (fun x ↦ f (e x)) p := by
  intro a b ha hb ha0 hab
  have ht : Tendsto e.symm (𝓝 (e p)) (𝓝 p) := by
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using e.symm.continuous.tendsto (e p)
  apply hs (fun y ↦ a (e.symm y)) (fun y ↦ b (e.symm y))
    (ha.comp_of_eq (e.symm.analyticAt _) (e.symm_apply_apply p))
    (hb.comp_of_eq (e.symm.analyticAt _) (e.symm_apply_apply p))
    (by simpa only [ContinuousLinearEquiv.symm_apply_apply] using ha0)
  simpa only [Filter.EventuallyEq, ContinuousLinearEquiv.apply_symm_apply] using ht.eventually hab

open AnalyticDivisorAlgebraic5 AnalyticDivisorAlgebraic11 in
theorem gaga21_br_squarefree_germ {n : ℕ} {p : Fin n → ℂ} {f : (Fin n → ℂ) → ℂ}
    (hf : AnalyticAt ℂ f p) (hs : IsSquareFreeAt f p) :
    Squarefree (⟨Filter.Germ.ofFun f, f, hf, rfl⟩ : AnalyticGermAt n p) := by
  intro q ⟨r, hr⟩
  by_contra hqu
  obtain ⟨g, hg, hgq⟩ := q.2
  obtain ⟨h, hh, hhr⟩ := r.2
  have hg0 : g p = 0 := by
    by_contra hn
    apply hqu
    let v : AnalyticGermAt n p :=
      ⟨Filter.Germ.ofFun (fun z ↦ (g z)⁻¹), fun z ↦ (g z)⁻¹, hg.inv hn, rfl⟩
    refine isUnit_iff_exists_inv.mpr ⟨v, Subtype.ext ?_⟩
    change q.1 * v.1 = 1
    rw [← hgq]
    exact Filter.Germ.coe_eq.mpr ((hg.continuousAt.eventually_ne hn).mono
      fun z hz ↦ mul_inv_cancel₀ hz)
  apply hs g h hg hh hg0
  apply Filter.Germ.coe_eq.mp
  have he := congrArg Subtype.val hr
  change Filter.Germ.ofFun f = q.1 * q.1 * r.1 at he
  rw [← hgq, ← hhr] at he
  simp only [pow_two]
  convert he using 1 <;> rfl

open AnalyticDivisorAlgebraic5 in
theorem gaga21_br_reduced_associated (p : E) (f g : E → ℂ)
    (hf : AnalyticAt ℂ f p) (hg : AnalyticAt ℂ g p)
    (hsf : IsSquareFreeAt f p) (hsg : IsSquareFreeAt g p)
    (hz : ∀ᶠ z in 𝓝 p, f z = 0 ↔ g z = 0) : AreAssociatedAt f g p := by
  let e := gaga21_br_coord_fin (E := E) rfl
  have hf' : AnalyticAt ℂ (fun y ↦ f (e.symm y)) (e p) :=
    hf.comp_of_eq (e.symm.analyticAt _) (e.symm_apply_apply p)
  have hg' : AnalyticAt ℂ (fun y ↦ g (e.symm y)) (e p) :=
    hg.comp_of_eq (e.symm.analyticAt _) (e.symm_apply_apply p)
  have hsf' := gaga21_br_squarefree_comp e.symm f (e p) (by simpa only
    [ContinuousLinearEquiv.symm_apply_apply] using hsf)
  have hsg' := gaga21_br_squarefree_comp e.symm g (e p) (by simpa only
    [ContinuousLinearEquiv.symm_apply_apply] using hsg)
  have ht : Tendsto e.symm (𝓝 (e p)) (𝓝 p) := by
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using e.symm.continuous.tendsto (e p)
  have hh := AnalyticDivisorAlgebraic18.spec_reduced_zero_germs_associated
    (Module.finrank ℂ E) (e p) _ _ hf' hg'
    (gaga21_br_squarefree_germ hf' hsf') (gaga21_br_squarefree_germ hg' hsg')
    (ht.eventually hz)
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using
    (gaga21_br_associated e.symm f g (e p)).mp hh

theorem gaga21_br_irreducible_of_regular {f : E → ℂ} {p : E}
    (hf : AnalyticAt ℂ f p) (hf0 : f p = 0) (hd : fderiv ℂ f p ≠ 0) :
    IsIrreducibleAt f p := by
  refine ⟨hf0, ?_⟩
  intro g h hg hh hfac
  by_contra hn
  push Not at hn
  have he := hfac.fderiv_eq (𝕜 := ℂ)
  have he0 : fderiv ℂ (fun x ↦ g x * h x) p = 0 := by
    change fderiv ℂ (g * h) p = 0
    rw [fderiv_mul hg.differentiableAt hh.differentiableAt, hn.1, hn.2]
    ext z
    simp
  exact hd (he.trans he0)

open AnalyticDivisorAlgebraic5 in
theorem gaga21_br_reduced_of_regular_containment {a h : E → ℂ} {p : E}
    (ha : AnalyticAt ℂ a p) (ha0 : a p = 0) (hs : IsSquareFreeAt a p)
    (hh : AnalyticAt ℂ h p) (hh0 : h p = 0) (hhd : fderiv ℂ h p ≠ 0)
    (hz : ∀ᶠ z in 𝓝 p, a z = 0 → h z = 0) : AreAssociatedAt a h p := by
  classical
  have hnz : ¬ ∀ᶠ z in 𝓝 p, a z = 0 := by
    intro he
    exact hs (fun _ ↦ 0) (fun _ ↦ 1) analyticAt_const analyticAt_const rfl
      (by simpa only [Filter.EventuallyEq, zero_pow (by decide : 2 ≠ 0), zero_mul] using he)
  obtain ⟨k, u, P, m, hu, hu0, hP, _, hfac⟩ := gaga21_br_decomposition ha ha0 hnz
  have hp : ∏ j, P j p ^ m j = 0 :=
    (mul_eq_zero.mp (hfac.self_of_nhds.symm.trans ha0)).resolve_left hu0
  obtain ⟨j, _, _⟩ := Finset.prod_eq_zero_iff.mp hp
  have hPa : ∀ᶠ z in 𝓝 p, P j z = 0 → a z = 0 := by
    filter_upwards [hfac] with z hz hPz
    rw [hz]
    have hpz : ∏ i, P i z ^ m i = 0 := Finset.prod_eq_zero (Finset.mem_univ j)
      (by rw [hPz, zero_pow (Nat.ne_of_gt (hP j).2.2)])
    rw [hpz, mul_zero]
  have hPh : ∀ᶠ z in 𝓝 p, P j z = 0 → h z = 0 := by
    filter_upwards [hPa, hz] with z hza hzh
    exact fun hx ↦ hzh (hza hx)
  obtain ⟨c, hc, hdiv⟩ := gaga21_br_nullstellensatz p (P j) h (hP j).1 hh (hP j).2.1 hPh
  have hi := gaga21_br_irreducible_of_regular hh hh0 hhd
  have hc0 : c p ≠ 0 := (hi.2 (P j) c (hP j).1 hc hdiv).resolve_left
    (not_not.mpr (hP j).2.1.1)
  have he : ∀ᶠ z in 𝓝 p, a z = 0 ↔ h z = 0 := by
    filter_upwards [hz, hPa, hdiv, hc.continuousAt.eventually_ne hc0] with z haz hza hzdiv hcz
    refine ⟨haz, fun hhz ↦ hza ?_⟩
    exact (mul_eq_zero.mp (hzdiv.symm.trans hhz)).resolve_right hcz
  exact gaga21_br_reduced_associated p a h ha hh hs
    (gaga21_br_squarefree_of_irreducible hi) he

theorem gaga21_br_regular_of_associated {a h : E → ℂ} {p : E}
    (hh : AnalyticAt ℂ h p) (hh0 : h p = 0) (hhd : fderiv ℂ h p ≠ 0)
    (has : AreAssociatedAt a h p) : fderiv ℂ a p ≠ 0 := by
  obtain ⟨u, hu, hu0, he⟩ := has
  rw [he.fderiv_eq (𝕜 := ℂ)]
  change fderiv ℂ (u * h) p ≠ 0
  rw [fderiv_mul hu.differentiableAt hh.differentiableAt, hh0, zero_smul, add_zero]
  exact smul_ne_zero hu0 hhd

/-- Every selected-factor zero at a regular-support point is regular, after shrinking.
The conclusion also supplies its association with any reduced regular support equation. -/
theorem gaga21_br_regular_of_regularSupport {ι : Type} {U : Set E}
    {V : ι → Set E} {f : ι → E → ℂ} (hD : IsLocalDivisorData U V f)
    (a : gaga21_LocalFactorOccurrence V f) :
    ∀ᶠ y in 𝓝 a.point, a.factor y = 0 → y ∈ gaga21_regularSupport V f →
      y ∈ AnalyticDivisorAlgebraic20.gaga20_regularZero a.factor := by
  classical
  have ha : AnalyticAt ℂ a.factor a.point := (a.factor_data a.selected).1
  have hi : IsIrreducibleAt a.factor a.point := (a.factor_data a.selected).2.1
  filter_upwards [ha.eventually_analyticAt, gaga21_br_eventually_squarefree ha hi,
    (hD.1 a.chart).mem_nhds a.mem_chart, a.factorization.eventually_nhds]
    with y hya hys hyV hyfac
  intro hy0 ⟨_, h, hh, hh0, hhd, hzero⟩
  have hz : ∀ᶠ z in 𝓝 y, a.factor z = 0 → h z = 0 := by
    filter_upwards [hzero, hyfac, (hD.1 a.chart).mem_nhds hyV] with z hz hzfac hzV hza
    apply hz.mp
    apply (spec_mem_localDivisorSupport_iff hD a.chart z hzV).mpr
    rw [hzfac]
    have hp : ∏ j, a.factors j z ^ a.exponents j = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ a.selected)
        (pow_eq_zero_iff (Nat.ne_of_gt (a.factor_data a.selected).2.2) |>.mpr hza)
    rw [hp, mul_zero]
  exact ⟨hy0, gaga21_br_regular_of_associated hh hh0 hhd
    (gaga21_br_reduced_of_regular_containment hya hy0 hys hh hh0 hhd hz)⟩

/-- Finitely many proper analytic zero sets can be removed from a connected regular locus. -/
theorem gaga21_br_regular_complement_finite {k : ℕ} {U : Set E} {P : E → ℂ}
    (Q : Fin k → E → ℂ) (hU : IsOpen U) (hP : AnalyticOnNhd ℂ P U)
    (hQ : ∀ j, AnalyticOnNhd ℂ (Q j) U)
    (hc : IsConnected (AnalyticDivisorAlgebraic20.gaga20_regularZero P ∩ U))
    (hne : ∀ j, {x ∈ AnalyticDivisorAlgebraic20.gaga20_regularZero P ∩ U | Q j x ≠ 0}.Nonempty) :
    IsConnected {x ∈ AnalyticDivisorAlgebraic20.gaga20_regularZero P ∩ U | ∀ j, Q j x ≠ 0} ∧
      AnalyticDivisorAlgebraic20.gaga20_regularZero P ∩ U ⊆
        closure {x ∈ AnalyticDivisorAlgebraic20.gaga20_regularZero P ∩ U | ∀ j, Q j x ≠ 0} := by
  classical
  let R := AnalyticDivisorAlgebraic20.gaga20_regularZero P ∩ U
  have hDense (j : Fin k) : Dense {x : R | Q j x ≠ 0} := by
    have hd := (gaga21_br_regular_complement_connected_dense hU hP (hQ j) hc (hne j)).2
    apply Topology.IsInducing.subtypeVal.dense_iff.mpr
    intro x
    have he : ((↑) : R → E) '' {x : R | Q j x ≠ 0} = {x ∈ R | Q j x ≠ 0} := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩; exact ⟨z.property, hz⟩
      · rintro ⟨hy, hz⟩; exact ⟨⟨y, hy⟩, hz, rfl⟩
    rw [he]
    exact hd x.property
  have hOpen (j : Fin k) : IsOpen {x : R | Q j x ≠ 0} := by
    apply isOpen_ne.preimage
    exact continuous_iff_continuousAt.mpr fun x ↦
      (hQ j x x.property.2).continuousAt.comp continuous_subtype_val.continuousAt
  have hfin (s : Finset (Fin k)) : Dense {x : R | ∀ j ∈ s, Q j x ≠ 0} := by
    induction s using Finset.induction_on with
    | empty => simpa using (dense_univ : Dense (Set.univ : Set R))
    | @insert j s hjs ih =>
      simpa only [Finset.mem_insert, forall_eq_or_imp, setOf_and] using
        (hDense j).inter_of_isOpen_left ih (hOpen j)
  haveI : Nonempty R := hc.1.to_subtype
  obtain ⟨x, hx⟩ := (hfin Finset.univ).nonempty
  have hprod : {x ∈ R | (∏ j, Q j x) ≠ 0}.Nonempty :=
    ⟨x, x.property, Finset.prod_ne_zero_iff.mpr fun j hj ↦ hx j hj⟩
  have hh := gaga21_br_regular_complement_connected_dense hU hP
    (fun x hx ↦ Finset.analyticAt_fun_prod _ fun j _ ↦ hQ j x hx) hc hprod
  simpa only [Finset.prod_ne_zero_iff, Finset.mem_univ, forall_const] using hh

theorem gaga21_br_regularSupport_clean {ι : Type} {U : Set E}
    {V : ι → Set E} {f : ι → E → ℂ} (hD : IsLocalDivisorData U V f)
    (a : gaga21_LocalFactorOccurrence V f) :
    ∀ᶠ y in 𝓝 a.point, a.factor y = 0 → y ∈ gaga21_regularSupport V f →
      ∀ j, j ≠ a.selected → a.factors j y ≠ 0 := by
  classical
  have han : ∀ᶠ y in 𝓝 a.point, ∀ j, AnalyticAt ℂ (a.factors j) y :=
    eventually_all.mpr fun j ↦ (a.factor_data j).1.eventually_analyticAt
  have hsq : ∀ᶠ y in 𝓝 a.point, ∀ j, AnalyticDivisorAlgebraic5.IsSquareFreeAt (a.factors j) y :=
    eventually_all.mpr fun j ↦ gaga21_br_eventually_squarefree
      (a.factor_data j).1 (a.factor_data j).2.1
  have hcop : ∀ᶠ y in 𝓝 a.point, ∀ j, j ≠ a.selected → IsCoprimeAt a.factor (a.factors j) y := by
    apply eventually_all.mpr
    intro j
    by_cases hj : j = a.selected
    · exact Eventually.of_forall fun _ hn ↦ (hn hj).elim
    · exact (gaga21_br_pair_propagation a.point a.factor (a.factors j)
        (a.factor_data a.selected).1 (a.factor_data j).1
        (a.factor_data a.selected).2.1 (a.factor_data j).2.1
        (a.coprime (Ne.symm hj))).mono fun _ hy _ ↦ hy.1
  filter_upwards [han, hsq, hcop, (hD.1 a.chart).mem_nhds a.mem_chart,
    a.factorization.eventually_nhds] with y hya hys hyc hyV hyfac
  intro hy0 ⟨_, h, hh, hh0, hhd, hz⟩ j hj hj0
  have hcontain (i : Fin a.count) : ∀ᶠ z in 𝓝 y, a.factors i z = 0 → h z = 0 := by
    filter_upwards [hz, hyfac, (hD.1 a.chart).mem_nhds hyV] with z hzh hzf hzV hzi
    apply hzh.mp
    apply (spec_mem_localDivisorSupport_iff hD a.chart z hzV).mpr
    rw [hzf]
    have hp : ∏ l, a.factors l z ^ a.exponents l = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i)
        (pow_eq_zero_iff (Nat.ne_of_gt (a.factor_data i).2.2) |>.mpr hzi)
    rw [hp, mul_zero]
  obtain ⟨u, hu, _, heu⟩ := gaga21_br_reduced_of_regular_containment
    (hya a.selected) hy0 (hys a.selected) hh hh0 hhd (hcontain a.selected)
  obtain ⟨v, hv, _, hev⟩ := gaga21_br_reduced_of_regular_containment
    (hya j) hj0 (hys j) hh hh0 hhd (hcontain j)
  apply hyc j hj
  refine ⟨h, u, v, hh, hu, hv, hh0, ?_, ?_⟩
  · exact heu.mono fun z hz ↦ hz.trans (mul_comm _ _)
  · exact hev.mono fun z hz ↦ hz.trans (mul_comm _ _)

/-- A connected regular piece capturing the selected branch germ, inside any prescribed
open neighborhood. -/
theorem gaga21_br_branch_piece {ι : Type} {U : Set E}
    {V : ι → Set E} {f : ι → E → ℂ} (hD : IsLocalDivisorData U V f)
    (a : gaga21_LocalFactorOccurrence V f) {O : Set E} (hOo : IsOpen O) (hpO : a.point ∈ O) :
    ∃ W R : Set E, IsOpen W ∧ a.point ∈ W ∧ W ⊆ O ∧ IsConnected R ∧
      R ⊆ gaga21_regularSupport V f ∧ R ⊆ W ∧
      {x ∈ W | a.factor x = 0} ⊆ closure R ∧
      ∀ y ∈ W, a.factor y = 0 → y ∈ gaga21_regularSupport V f → y ∈ R := by
  classical
  have han : ∀ᶠ y in 𝓝 a.point, ∀ j, AnalyticAt ℂ (a.factors j) y :=
    eventually_all.mpr fun j ↦ (a.factor_data j).1.eventually_analyticAt
  have hdata : ∀ᶠ y in 𝓝 a.point, y ∈ O ∧ (∀ j, AnalyticAt ℂ (a.factors j) y) ∧
      (a.factor y = 0 → fderiv ℂ a.factor y ≠ 0 →
        (∀ j, j ≠ a.selected → a.factors j y ≠ 0) → y ∈ gaga21_regularSupport V f) ∧
      (a.factor y = 0 → y ∈ gaga21_regularSupport V f →
        y ∈ AnalyticDivisorAlgebraic20.gaga20_regularZero a.factor) ∧
      (a.factor y = 0 → y ∈ gaga21_regularSupport V f →
        ∀ j, j ≠ a.selected → a.factors j y ≠ 0) := by
    filter_upwards [hOo.mem_nhds hpO, han, gaga21_br_regularSupport_of_clean hD a,
      gaga21_br_regular_of_regularSupport hD a, gaga21_br_regularSupport_clean hD a]
      with y hyO hya hyf hyr hyc
    exact ⟨hyO, hya, fun hz hd ho ↦ (hyf hz hd ho).1, hyr, hyc⟩
  obtain ⟨N, hN, hNo, hpN⟩ := eventually_nhds_iff.mp hdata
  obtain ⟨W, hWo, hpW, hWN, hc, hd⟩ := gaga21_br_regular_locus_within a.point a.factor
    (a.factor_data a.selected).1 (a.factor_data a.selected).2.1 hNo hpN
  let Q (j : Fin a.count) (x : E) : ℂ := if j = a.selected then 1 else a.factors j x
  have hQa : ∀ j, AnalyticOnNhd ℂ (Q j) W := by
    intro j x hx
    by_cases hj : j = a.selected
    · simpa only [Q, if_pos hj] using (analyticAt_const : AnalyticAt ℂ (fun _ : E ↦ (1 : ℂ)) x)
    · simpa only [Q, if_neg hj] using (hN x (hWN hx)).2.1 j
  have hne (j : Fin a.count) :
      {x ∈ AnalyticDivisorAlgebraic20.gaga20_regularZero a.factor ∩ W | Q j x ≠ 0}.Nonempty := by
    by_cases hj : j = a.selected
    · obtain ⟨x, hx⟩ := hc.1
      exact ⟨x, hx, by simp only [Q, if_pos hj, ne_eq, one_ne_zero, not_false_eq_true]⟩
    · by_contra hn
      have hzero : ∀ x ∈ AnalyticDivisorAlgebraic20.gaga20_regularZero a.factor ∩ W,
          a.factors j x = 0 := by
        intro x hx
        by_contra hz
        exact hn ⟨x, hx, by simpa only [Q, if_neg hj] using hz⟩
      have he : ∀ᶠ x in 𝓝 a.point, a.factor x = 0 → a.factors j x = 0 := by
        filter_upwards [hWo.mem_nhds hpW] with x hx hxa
        exact tendsto_nhds_unique_of_frequently_eq ((hN x (hWN hx)).2.1 j).continuousAt
          tendsto_const_nhds ((mem_closure_iff_frequently.mp (hd ⟨hx, hxa⟩)).mono
            fun y hy ↦ hzero y hy)
      obtain ⟨c, hca, hdiv⟩ := gaga21_br_nullstellensatz a.point a.factor (a.factors j)
        (a.factor_data a.selected).1 (a.factor_data j).1
        (a.factor_data a.selected).2.1 he
      exact a.coprime (Ne.symm hj) ⟨a.factor, (fun _ ↦ 1), c,
        (a.factor_data a.selected).1, analyticAt_const, hca, a.selected_zero,
        Eventually.of_forall (fun x ↦ (mul_one (a.factor x)).symm), hdiv⟩
  obtain ⟨hcR, hdR⟩ := gaga21_br_regular_complement_finite Q hWo
    (fun x hx ↦ (hN x (hWN hx)).2.1 a.selected) hQa hc hne
  let R := {x ∈ AnalyticDivisorAlgebraic20.gaga20_regularZero a.factor ∩ W | ∀ j, Q j x ≠ 0}
  refine ⟨W, R, hWo, hpW, fun x hx ↦ (hN x (hWN hx)).1, hcR, ?_,
    (fun x hx ↦ hx.1.2), hd.trans (closure_minimal hdR isClosed_closure), ?_⟩
  · intro x hx
    apply (hN x (hWN hx.1.2)).2.2.1 hx.1.1.1 hx.1.1.2
    intro j hj
    simpa only [Q, if_neg hj] using hx.2 j
  · intro y hy hy0 hyR
    have hdy := hN y (hWN hy)
    refine ⟨⟨hdy.2.2.2.1 hy0 hyR, hy⟩, ?_⟩
    intro j
    by_cases hj : j = a.selected
    · simp only [Q, if_pos hj, ne_eq, one_ne_zero, not_false_eq_true]
    · simpa only [Q, if_neg hj] using hdy.2.2.2.2 hy0 hyR j hj

theorem gaga21_br_associated_symm {f g : E → ℂ} {p : E}
    (h : AreAssociatedAt f g p) : AreAssociatedAt g f p := by
  obtain ⟨u, hu, hu0, he⟩ := h
  refine ⟨fun x ↦ (u x)⁻¹, hu.inv hu0, inv_ne_zero hu0, ?_⟩
  filter_upwards [he, hu.continuousAt.eventually_ne hu0] with x hx hxu
  rw [hx, ← mul_assoc, inv_mul_cancel₀ hxu, one_mul]

open AnalyticDivisorAlgebraic5 in
theorem gaga21_br_squarefree_not_zero {a : E → ℂ} {p : E} (hs : IsSquareFreeAt a p) :
    ¬ ∀ᶠ z in 𝓝 p, a z = 0 := by
  intro he
  exact hs (fun _ ↦ 0) (fun _ ↦ 1) analyticAt_const analyticAt_const rfl
    (by simpa only [Filter.EventuallyEq, zero_pow (by decide : 2 ≠ 0), zero_mul] using he)

/-- A nearby zero of a certified factor has a certified occurrence in the same quotient
class and chart, associated to an irreducible analytic divisor of that factor's germ. -/
theorem gaga21_br_reanchor {ι : Type} {U : Set E}
    {V : ι → Set E} {f : ι → E → ℂ} (hD : IsLocalDivisorData U V f)
    (a : gaga21_LocalFactorOccurrence V f) :
    ∀ᶠ y in 𝓝 a.point, a.factor y = 0 →
      ∃ b : gaga21_LocalFactorOccurrence V f,
        b.point = y ∧ b.chart = a.chart ∧
        Quotient.mk (gaga21_componentSetoid V f) b = Quotient.mk (gaga21_componentSetoid V f) a ∧
        ∃ Q c : E → ℂ, AnalyticAt ℂ Q y ∧ IsIrreducibleAt Q y ∧
          AreAssociatedAt b.factor Q y ∧ AnalyticAt ℂ c y ∧
          a.factor =ᶠ[𝓝 y] fun z ↦ Q z * c z := by
  classical
  have han : ∀ᶠ y in 𝓝 a.point, ∀ j, AnalyticAt ℂ (a.factors j) y :=
    eventually_all.mpr fun j ↦ (a.factor_data j).1.eventually_analyticAt
  have hV : ∀ᶠ y in 𝓝 a.point, y ∈ V a.chart := (hD.1 a.chart).mem_nhds a.mem_chart
  have hdata := hV.and
    (a.unit_analytic.eventually_analyticAt.and (han.and
      (a.factorization.and (gaga21_br_eventually_squarefree
        (a.factor_data a.selected).1 (a.factor_data a.selected).2.1))))
  obtain ⟨N, hN, hNo, hpN⟩ := eventually_nhds_iff.mp hdata
  obtain ⟨W, R, hWo, hpW, hWN, hcR, hRreg, _, _, hcapture⟩ :=
    gaga21_br_branch_piece hD a hNo hpN
  filter_upwards [hWo.mem_nhds hpW] with y hyW hy0
  have hyN := hWN hyW
  have hdy := hN y hyN
  have hya : AnalyticAt ℂ a.factor y := hdy.2.2.1 a.selected
  obtain ⟨k, u, Q, d, hu, hu0, hQ, hcQ, hfacQ⟩ :=
    gaga21_br_decomposition hya hy0 (gaga21_br_squarefree_not_zero hdy.2.2.2.2)
  have hp : ∏ j, Q j y ^ d j = 0 :=
    (mul_eq_zero.mp (hfacQ.self_of_nhds.symm.trans hy0)).resolve_left hu0
  obtain ⟨j, _, _⟩ := Finset.prod_eq_zero_iff.mp hp
  have hfy : f a.chart y = 0 := by
    rw [hdy.2.2.2.1]
    change a.unit y * (∏ i, a.factors i y ^ a.exponents i) = 0
    have hz : ∏ i, a.factors i y ^ a.exponents i = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ a.selected)
        (pow_eq_zero_iff (Nat.ne_of_gt (a.factor_data a.selected).2.2) |>.mpr hy0)
    rw [hz, mul_zero]
  obtain ⟨t, w, P, e, hw, hw0, hP, hcP, hfacP⟩ :=
    gaga21_br_decomposition (hD.2.2.1 a.chart y hdy.1) hfy (hD.2.2.2.1 a.chart y hdy.1)
  obtain ⟨l, hl⟩ := gaga21_br_nearby_factor_matching hD a.chart hNo (hNo.mem_nhds hpN)
    (fun z hz ↦ (hN z hz).1) hyN (fun z hz ↦ (hN z hz).2.1) a.unit_ne
    (fun i z hz ↦ (hN z hz).2.2.1 i) (fun i ↦ (a.factor_data i).2.1)
    (fun i ↦ (a.factor_data i).2.2) a.coprime (fun z hz ↦ (hN z hz).2.2.2.1)
    a.selected hy0 hu hu0 hQ hcQ hfacQ hw hw0 hP hcP hfacP j
  let b : gaga21_LocalFactorOccurrence V f :=
    { chart := a.chart, point := y, mem_chart := hdy.1, count := t, unit := w,
      factors := P, exponents := e, selected := l, unit_analytic := hw, unit_ne := hw0,
      factor_data := hP, coprime := hcP, factorization := hfacP, selected_zero := (hP l).2.1.1 }
  have hQa : ∀ᶠ z in 𝓝 y, Q j z = 0 → a.factor z = 0 := by
    filter_upwards [hfacQ] with z hz hqz
    rw [hz]
    have hpz : ∏ i, Q i z ^ d i = 0 := Finset.prod_eq_zero (Finset.mem_univ j)
      (pow_eq_zero_iff (Nat.ne_of_gt (hQ j).2.2) |>.mpr hqz)
    rw [hpz, mul_zero]
  have hba : ∀ᶠ z in 𝓝 y, b.factor z = 0 → a.factor z = 0 := by
    obtain ⟨v, _, _, hev⟩ := hl
    filter_upwards [hQa, hev] with z hza hz hzb
    apply hza
    change P l z = 0 at hzb
    rw [hz, hzb, mul_zero]
  have hcont : gaga21_continuation a b := by
    refine ⟨R, hcR, hRreg, ?_, ?_⟩
    · filter_upwards [hWo.mem_nhds hpW] with z hz hza hzr
      exact hcapture z hz hza hzr
    · change ∀ᶠ z in 𝓝 y, b.factor z = 0 → z ∈ gaga21_regularSupport V f → z ∈ R
      filter_upwards [hWo.mem_nhds hyW, hba] with z hz hza hzb hzr
      exact hcapture z hz (hza hzb) hzr
  obtain ⟨c, hca, hdiv⟩ := gaga21_br_nullstellensatz y (Q j) a.factor
    (hQ j).1 hya (hQ j).2.1 hQa
  exact ⟨b, rfl, rfl, (Quotient.sound (Relation.EqvGen.rel a b hcont)).symm,
    Q j, c, (hQ j).1, (hQ j).2.1, gaga21_br_associated_symm hl, hca, hdiv⟩

/-- The zero germ of each certified factor lies in its constructed quotient carrier. -/
theorem gaga21_br_germ_in_carrier {ι : Type} {U : Set E}
    {V : ι → Set E} {f : ι → E → ℂ} (hD : IsLocalDivisorData U V f)
    (a : gaga21_LocalFactorOccurrence V f) :
    ∀ᶠ y in 𝓝 a.point, a.factor y = 0 →
      y ∈ gaga21_componentCarrier (Quotient.mk (gaga21_componentSetoid V f) a) := by
  filter_upwards [gaga21_br_reanchor hD a] with y hy hya
  obtain ⟨b, hb, _, hclass, _⟩ := hy hya
  exact ⟨b, hclass, hb⟩

theorem gaga21_br_product_order {k : ℕ} {Q : Fin k → ℂ → ℂ}
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

/-- Clean transverse multiplicity at an arbitrary anchor in a finite-dimensional complex
space, with nearby pairwise coprimality. -/
theorem gaga21_br_clean_multiplicity {k : ℕ} {p : E} {f u : E → ℂ}
    {P : Fin k → E → ℂ} {b : Fin k → ℕ}
    (hu : AnalyticAt ℂ u p) (hu0 : u p ≠ 0)
    (hP : ∀ a, AnalyticAt ℂ (P a) p) (hiP : ∀ a, IsIrreducibleAt (P a) p)
    (hb : ∀ a, 0 < b a) (hcop : Pairwise (fun a c ↦ IsCoprimeAt (P a) (P c) p))
    (hfac : f =ᶠ[𝓝 p] fun y ↦ u y * ∏ a, P a y ^ b a) :
    ∃ N, IsOpen N ∧ p ∈ N ∧
      (∀ q ∈ N, Pairwise (fun a c ↦ IsCoprimeAt (P a) (P c) q)) ∧
      ∀ q ∈ N, ∀ a, P a q = 0 → (∀ c, c ≠ a → P c q ≠ 0) →
        ∀ v : E, fderiv ℂ (P a) q v ≠ 0 →
          analyticOrderAt (fun t : ℂ ↦ f (q + t • v)) 0 = b a := by
  have hc : ∀ᶠ q in 𝓝 p, Pairwise (fun a c ↦ IsCoprimeAt (P a) (P c) q) := by
    apply eventually_all.mpr
    intro a
    apply eventually_all.mpr
    intro c
    by_cases hac : a = c
    · exact Eventually.of_forall fun _ hne ↦ (hne hac).elim
    · exact (gaga21_br_pair_propagation p (P a) (P c)
        (hP a) (hP c) (hiP a) (hiP c) (hcop hac)).mono fun _ h _ ↦ h.1
  have hPa : ∀ᶠ y in 𝓝 p, ∀ i, AnalyticAt ℂ (P i) y :=
    eventually_all.mpr fun i ↦ (hP i).eventually_analyticAt
  obtain ⟨N, hN, hNo, hpN⟩ := eventually_nhds_iff.mp
    (hc.and (hu.eventually_analyticAt.and ((hu.continuousAt.eventually_ne hu0).and
      (hPa.and hfac.eventually_nhds))))
  refine ⟨N, hNo, hpN, fun q hq ↦ (hN q hq).1, ?_⟩
  intro y hy i hPiy hother v hder
  have huy := (hN y hy).2.1
  have huy0 := (hN y hy).2.2.1
  have hPay := (hN y hy).2.2.2.1
  have hyfac := (hN y hy).2.2.2.2
  let L : ℂ → E := fun t ↦ y + t • v
  have hLa : AnalyticAt ℂ L 0 := analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hL0 : L 0 = y := by simp [L]
  have hLt : Tendsto L (𝓝 0) (𝓝 y) := by simpa only [ContinuousAt, hL0] using hLa.continuousAt
  let Q : Fin k → ℂ → ℂ := fun j t ↦ P j (L t)
  have hQa : ∀ j, AnalyticAt ℂ (Q j) 0 := fun j ↦ (hPay j).comp_of_eq hLa hL0
  have hline : HasDerivAt L v 0 := by
    simpa only [L, Pi.add_apply, id_eq, zero_add, one_smul] using
      ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add y
  have hFD : HasFDerivAt (P i) (fderiv ℂ (P i) y) (L 0) :=
    by simpa only [hL0] using (hPay i).differentiableAt.hasFDerivAt
  have hQD : HasDerivAt (Q i) (fderiv ℂ (P i) y v) 0 := hFD.comp_hasDerivAt 0 hline
  have hQi : analyticOrderAt (Q i) 0 = 1 :=
    (hQa i).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
      (by simpa only [Q, hL0] using hPiy) (hQD.deriv.symm ▸ hder)
  have hQne : ∀ j, j ≠ i → Q j 0 ≠ 0 := by
    intro j hji
    simpa only [Q, hL0] using hother j hji
  have hua : AnalyticAt ℂ (fun t ↦ u (L t)) 0 := huy.comp_of_eq hLa hL0
  have huord : analyticOrderAt (fun t ↦ u (L t)) 0 = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (by simpa only [hL0] using huy0))
  have hslice : (fun t ↦ f (L t)) =ᶠ[𝓝 0] fun t ↦ u (L t) * ∏ j, Q j t ^ b j :=
    hLt.eventually hyfac
  change analyticOrderAt (fun t ↦ f (L t)) 0 = b i
  rw [analyticOrderAt_congr hslice]
  change analyticOrderAt ((fun t ↦ u (L t)) * (fun t ↦ ∏ j, Q j t ^ b j)) 0 = b i
  have hproda : AnalyticAt ℂ (fun t ↦ ∏ j, Q j t ^ b j) 0 :=
    Finset.analyticAt_fun_prod _ fun j _ ↦ (hQa j).pow _
  rw [analyticOrderAt_mul hua hproda, huord, zero_add,
    gaga21_br_product_order b i hQa hQi hQne]

end GeneralDimension

theorem gaga21_carrier_nonempty_contained_aux {E ι : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {U : Set E} {V : ι → Set E} {f : ι → E → ℂ}
    (hD : IsLocalDivisorData U V f) (C : gaga21_GlobalComponent V f) :
    (gaga21_componentCarrier C).Nonempty ∧ gaga21_componentCarrier C ⊆ U := by
  constructor
  · exact ⟨(Quotient.out C).point, Quotient.out C, Quotient.out_eq C, rfl⟩
  · rintro q ⟨a, -, rfl⟩
    rw [← hD.2.1]
    exact mem_iUnion_of_mem a.chart a.mem_chart

theorem gaga21_a2_connected_factor {E : Type} [TopologicalSpace E]
    {k : ℕ} (P : Fin k → E → ℂ) {R : Set E} (hR : IsConnected R)
    (hP : ∀ j, ContinuousOn (P j) R)
    (hz : ∀ x ∈ R, ∃ j, P j x = 0)
    (hu : ∀ x ∈ R, ∀ j l, P j x = 0 → P l x = 0 → j = l) :
    ∃ j, ∀ x ∈ R, P j x = 0 := by
  classical
  letI : ConnectedSpace R := isConnected_iff_connectedSpace.mp hR
  obtain ⟨x, hx⟩ := hR.nonempty
  obtain ⟨j, hj⟩ := hz x hx
  have hc (l : Fin k) : IsClosed {y : R | P l y = 0} :=
    isClosed_eq (continuousOn_iff_continuous_domRestrict.mp (hP l)) continuous_const
  have he : {y : R | P j y = 0}ᶜ = ⋃ l : {l : Fin k // l ≠ j},
      {y : R | P l.val y = 0} := by
    ext y
    constructor
    · intro hy
      obtain ⟨l, hl⟩ := hz y y.property
      exact mem_iUnion.mpr ⟨⟨l, fun h ↦ hy (h ▸ hl)⟩, hl⟩
    · intro hy hjy
      obtain ⟨l, hl⟩ := mem_iUnion.mp hy
      exact l.property (hu y y.property l j hl hjy)
  have ho : IsOpen {y : R | P j y = 0} := by
    rw [← isClosed_compl_iff, he]
    exact isClosed_iUnion_of_finite fun l ↦ hc l.val
  have hall := (show IsClopen {y : R | P j y = 0} from ⟨hc j, ho⟩).eq_univ
    ⟨⟨x, hx⟩, hj⟩
  exact ⟨j, fun y hy ↦ Set.eq_univ_iff_forall.mp hall ⟨y, hy⟩⟩

theorem gaga21_a2_nearby_classes {E ι : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {U : Set E} {V : ι → Set E}
    {f : ι → E → ℂ} (hD : IsLocalDivisorData U V f) {p : E}
    (hp : p ∈ localDivisorSupport V f) :
    ∀ᶠ y in 𝓝 p, ∀ a : gaga21_LocalFactorOccurrence V f, a.point = y →
      p ∈ gaga21_componentCarrier (Quotient.mk (gaga21_componentSetoid V f) a) := by
  classical
  obtain ⟨i, hpi, hfi⟩ := hp
  obtain ⟨k, u, P, m, hu, hu0, hP, hc, hfac⟩ :=
    gaga21_br_decomposition (hD.2.2.1 i p hpi) hfi (hD.2.2.2.1 i p hpi)
  let b (j : Fin k) : gaga21_LocalFactorOccurrence V f :=
    { chart := i, point := p, mem_chart := hpi, count := k, unit := u,
      factors := P, exponents := m, selected := j, unit_analytic := hu, unit_ne := hu0,
      factor_data := hP, coprime := hc, factorization := hfac,
      selected_zero := (hP j).2.1.1 }
  choose W R hWo hpW hWU hRc hRreg hRW hdense hcap using
    (fun j ↦ gaga21_br_branch_piece hD (b j) isOpen_univ (mem_univ _))
  have hdata : ∀ᶠ y in 𝓝 p, y ∈ V i ∧ (∀ j, y ∈ W j) ∧
      (∀ j, AnalyticAt ℂ (P j) y) ∧ u y ≠ 0 ∧
      f i y = u y * ∏ j, P j y ^ m j ∧
      ∀ j, P j y = 0 → y ∈ gaga21_regularSupport V f →
        ∀ l, l ≠ j → P l y ≠ 0 := by
    filter_upwards [(hD.1 i).mem_nhds hpi,
      eventually_all.mpr (fun j ↦ (hWo j).mem_nhds (hpW j)),
      eventually_all.mpr (fun j ↦ (hP j).1.eventually_analyticAt),
      hu.continuousAt.eventually_ne hu0, hfac,
      eventually_all.mpr (fun j ↦ gaga21_br_regularSupport_clean hD (b j))]
      with y hyV hyW hya hyu hyf hyc
    exact ⟨hyV, hyW, hya, hyu, hyf, hyc⟩
  obtain ⟨N, hN, hNo, hpN⟩ := eventually_nhds_iff.mp hdata
  filter_upwards [hNo.mem_nhds hpN] with y hy a hay
  have haN : a.point ∈ N := hay.symm ▸ hy
  obtain ⟨O, S, hOo, haO, hON, hSc, hSreg, hSO, _, hScap⟩ :=
    gaga21_br_branch_piece hD a hNo haN
  have hSN : S ⊆ N := hSO.trans hON
  have hz : ∀ x ∈ S, ∃ j, P j x = 0 := by
    intro x hx
    have hdx := hN x (hSN hx)
    have hfx := (spec_mem_localDivisorSupport_iff hD i x hdx.1).mp (hSreg hx).1
    rw [hdx.2.2.2.2.1, mul_eq_zero, or_iff_right hdx.2.2.2.1,
      Finset.prod_eq_zero_iff] at hfx
    obtain ⟨j, _, hj⟩ := hfx
    exact ⟨j, (pow_eq_zero_iff (Nat.ne_of_gt (hP j).2.2)).mp hj⟩
  obtain ⟨j, hj⟩ := gaga21_a2_connected_factor P hSc
    (fun j x hx ↦ ((hN x (hSN hx)).2.2.1 j).continuousAt.continuousWithinAt) hz
    (by
      intro x hx j l hj hl
      by_contra hne
      exact (hN x (hSN hx)).2.2.2.2.2 j hj (hSreg hx) l (Ne.symm hne) hl)
  have hcont : gaga21_continuation (b j) a := by
    refine ⟨R j, hRc j, hRreg j, ?_, ?_⟩
    · filter_upwards [(hWo j).mem_nhds (hpW j)] with x hx hx0 hxr
      exact hcap j x hx hx0 hxr
    · filter_upwards [hOo.mem_nhds haO] with x hx hx0 hxr
      have hxS := hScap x hx hx0 hxr
      exact hcap j x ((hN x (hSN hxS)).2.1 j) (hj x hxS) hxr
  exact ⟨b j, Quotient.sound (Relation.EqvGen.rel _ _ hcont), rfl⟩

theorem gaga21_carrier_closed_aux {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {U : Set E} {V : ι → Set E} {f : ι → E → ℂ}
    (hD : IsLocalDivisorData U V f) (C : gaga21_GlobalComponent V f) :
    IsClosed (((↑) : U → E) ⁻¹' gaga21_componentCarrier C) := by
  classical
  have hs : gaga21_componentCarrier C ⊆ localDivisorSupport V f := by
    rintro x ⟨a, _, rfl⟩
    refine ⟨a.chart, a.mem_chart, ?_⟩
    rw [a.factorization.self_of_nhds]
    have hz : ∏ j, a.factors j a.point ^ a.exponents j = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ a.selected)
        ((pow_eq_zero_iff (Nat.ne_of_gt (a.factor_data a.selected).2.2)).mpr a.selected_zero)
    exact mul_eq_zero.mpr (Or.inr hz)
  apply isClosed_iff_frequently.mpr
  intro p hp
  have hpS : (p : E) ∈ localDivisorSupport V f :=
    isClosed_iff_frequently.mp (spec_isClosed_localDivisorSupport hD).2 p
      (hp.mono fun y hy ↦ hs hy)
  have hn := (continuous_subtype_val.tendsto p).eventually (gaga21_a2_nearby_classes hD hpS)
  obtain ⟨y, hy, hny⟩ := (hp.and_eventually hn).exists
  obtain ⟨a, ha, hay⟩ := hy
  have hm := hny a hay
  rwa [ha] at hm

section RegularCarrier
variable {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {U : Set E} {V : ι → Set E} {f : ι → E → ℂ}

theorem gaga21_b2_factor_support (hD : IsLocalDivisorData U V f)
    (a : gaga21_LocalFactorOccurrence V f) :
    ∀ᶠ y in 𝓝 a.point, a.factor y = 0 → y ∈ localDivisorSupport V f := by
  filter_upwards [(hD.1 a.chart).mem_nhds a.mem_chart, a.factorization] with y hy he hz
  apply (spec_mem_localDivisorSupport_iff hD a.chart y hy).mpr
  have hprod : ∏ j, a.factors j y ^ a.exponents j = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ a.selected)
      (pow_eq_zero_iff (Nat.ne_of_gt (a.factor_data a.selected).2.2) |>.mpr hz)
  rw [he, hprod, mul_zero]

theorem gaga21_b2_carrier_support (hD : IsLocalDivisorData U V f)
    (C : gaga21_GlobalComponent V f) :
    gaga21_componentCarrier C ⊆ localDivisorSupport V f := by
  rintro p ⟨a, _, rfl⟩
  exact (gaga21_b2_factor_support hD a).self_of_nhds a.selected_zero

theorem gaga21_b2_occurrence (hD : IsLocalDivisorData U V f)
    {p : E} (hp : p ∈ localDivisorSupport V f) :
    ∃ a : gaga21_LocalFactorOccurrence V f, a.point = p := by
  obtain ⟨i, hi, hz⟩ := hp
  obtain ⟨k, u, P, m, hu, hu0, hP, hcop, hfac⟩ :=
    gaga21_br_decomposition (hD.2.2.1 i p hi) hz (hD.2.2.2.1 i p hi)
  have hp : ∏ j, P j p ^ m j = 0 :=
    (mul_eq_zero.mp (hfac.self_of_nhds.symm.trans hz)).resolve_left hu0
  obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp hp
  exact ⟨⟨i, p, hi, k, u, P, m, j, hu, hu0, hP, hcop, hfac,
    eq_zero_of_pow_eq_zero hj⟩, rfl⟩

theorem gaga21_b2_regular_equation (hD : IsLocalDivisorData U V f)
    (a : gaga21_LocalFactorOccurrence V f) (hp : a.point ∈ gaga21_regularSupport V f) :
    ∀ᶠ y in 𝓝 a.point, y ∈ localDivisorSupport V f ↔ a.factor y = 0 := by
  exact ((gaga21_br_regularSupport_of_clean hD a).self_of_nhds a.selected_zero
    ((gaga21_br_regular_of_regularSupport hD a).self_of_nhds a.selected_zero hp).2
    ((gaga21_br_regularSupport_clean hD a).self_of_nhds a.selected_zero hp)).2

theorem gaga21_b2_regular_nearby_class (hD : IsLocalDivisorData U V f)
    (a : gaga21_LocalFactorOccurrence V f) (hp : a.point ∈ gaga21_regularSupport V f) :
    ∀ᶠ y in 𝓝 a.point, ∀ b : gaga21_LocalFactorOccurrence V f, b.point = y →
      Quotient.mk (gaga21_componentSetoid V f) b = Quotient.mk (gaga21_componentSetoid V f) a := by
  obtain ⟨O, hO, hOo, hpO⟩ := eventually_nhds_iff.mp (gaga21_b2_regular_equation hD a hp)
  obtain ⟨W, R, hWo, hpW, hWO, hc, hRS, hRW, hd, hcap⟩ :=
    gaga21_br_branch_piece hD a hOo hpO
  filter_upwards [hWo.mem_nhds hpW] with y hy b hb
  apply Quotient.sound
  apply Relation.EqvGen.symm
  apply Relation.EqvGen.rel
  refine ⟨R, hc, hRS, ?_, ?_⟩
  · exact Filter.Eventually.mono (hWo.mem_nhds hpW) fun z hz hza hzs ↦ hcap z hz hza hzs
  · have hbW : b.point ∈ W := hb ▸ hy
    filter_upwards [hWo.mem_nhds hbW, gaga21_b2_factor_support hD b] with z hz hzb hzero hzs
    exact hcap z hz ((hO z (hWO hz)).mp (hzb hzero)) hzs

theorem gaga21_b2_branch_piece {ι : Type} {U : Set E}
    {V : ι → Set E} {f : ι → E → ℂ} (hD : IsLocalDivisorData U V f)
    (a : gaga21_LocalFactorOccurrence V f) {O : Set E} (hOo : IsOpen O) (hpO : a.point ∈ O) :
    ∃ W R : Set E, IsOpen W ∧ a.point ∈ W ∧ W ⊆ O ∧ IsConnected R ∧
      R ⊆ gaga21_regularSupport V f ∧ R ⊆ W ∧ (∀ x ∈ R, a.factor x = 0) ∧
      {x ∈ W | a.factor x = 0} ⊆ closure R ∧
      ∀ y ∈ W, a.factor y = 0 → y ∈ gaga21_regularSupport V f → y ∈ R := by
  classical
  have han : ∀ᶠ y in 𝓝 a.point, ∀ j, AnalyticAt ℂ (a.factors j) y :=
    eventually_all.mpr fun j ↦ (a.factor_data j).1.eventually_analyticAt
  have hdata : ∀ᶠ y in 𝓝 a.point, y ∈ O ∧ (∀ j, AnalyticAt ℂ (a.factors j) y) ∧
      (a.factor y = 0 → fderiv ℂ a.factor y ≠ 0 →
        (∀ j, j ≠ a.selected → a.factors j y ≠ 0) → y ∈ gaga21_regularSupport V f) ∧
      (a.factor y = 0 → y ∈ gaga21_regularSupport V f →
        y ∈ AnalyticDivisorAlgebraic20.gaga20_regularZero a.factor) ∧
      (a.factor y = 0 → y ∈ gaga21_regularSupport V f →
        ∀ j, j ≠ a.selected → a.factors j y ≠ 0) := by
    filter_upwards [hOo.mem_nhds hpO, han, gaga21_br_regularSupport_of_clean hD a,
      gaga21_br_regular_of_regularSupport hD a, gaga21_br_regularSupport_clean hD a]
      with y hyO hya hyf hyr hyc
    exact ⟨hyO, hya, fun hz hd ho ↦ (hyf hz hd ho).1, hyr, hyc⟩
  obtain ⟨N, hN, hNo, hpN⟩ := eventually_nhds_iff.mp hdata
  obtain ⟨W, hWo, hpW, hWN, hc, hd⟩ := gaga21_br_regular_locus_within a.point a.factor
    (a.factor_data a.selected).1 (a.factor_data a.selected).2.1 hNo hpN
  let Q (j : Fin a.count) (x : E) : ℂ := if j = a.selected then 1 else a.factors j x
  have hQa : ∀ j, AnalyticOnNhd ℂ (Q j) W := by
    intro j x hx
    by_cases hj : j = a.selected
    · simpa only [Q, if_pos hj] using (analyticAt_const : AnalyticAt ℂ (fun _ : E ↦ (1 : ℂ)) x)
    · simpa only [Q, if_neg hj] using (hN x (hWN hx)).2.1 j
  have hne (j : Fin a.count) :
      {x ∈ AnalyticDivisorAlgebraic20.gaga20_regularZero a.factor ∩ W | Q j x ≠ 0}.Nonempty := by
    by_cases hj : j = a.selected
    · obtain ⟨x, hx⟩ := hc.1
      exact ⟨x, hx, by simp only [Q, if_pos hj, ne_eq, one_ne_zero, not_false_eq_true]⟩
    · by_contra hn
      have hzero : ∀ x ∈ AnalyticDivisorAlgebraic20.gaga20_regularZero a.factor ∩ W,
          a.factors j x = 0 := by
        intro x hx
        by_contra hz
        exact hn ⟨x, hx, by simpa only [Q, if_neg hj] using hz⟩
      have he : ∀ᶠ x in 𝓝 a.point, a.factor x = 0 → a.factors j x = 0 := by
        filter_upwards [hWo.mem_nhds hpW] with x hx hxa
        exact tendsto_nhds_unique_of_frequently_eq ((hN x (hWN hx)).2.1 j).continuousAt
          tendsto_const_nhds ((mem_closure_iff_frequently.mp (hd ⟨hx, hxa⟩)).mono
            fun y hy ↦ hzero y hy)
      obtain ⟨c, hca, hdiv⟩ := gaga21_br_nullstellensatz a.point a.factor (a.factors j)
        (a.factor_data a.selected).1 (a.factor_data j).1
        (a.factor_data a.selected).2.1 he
      exact a.coprime (Ne.symm hj) ⟨a.factor, (fun _ ↦ 1), c,
        (a.factor_data a.selected).1, analyticAt_const, hca, a.selected_zero,
        Eventually.of_forall (fun x ↦ (mul_one (a.factor x)).symm), hdiv⟩
  obtain ⟨hcR, hdR⟩ := gaga21_br_regular_complement_finite Q hWo
    (fun x hx ↦ (hN x (hWN hx)).2.1 a.selected) hQa hc hne
  let R := {x ∈ AnalyticDivisorAlgebraic20.gaga20_regularZero a.factor ∩ W | ∀ j, Q j x ≠ 0}
  refine ⟨W, R, hWo, hpW, fun x hx ↦ (hN x (hWN hx)).1, hcR, ?_,
    (fun x hx ↦ hx.1.2), (fun x hx ↦ hx.1.1.1), hd.trans (closure_minimal hdR isClosed_closure), ?_⟩
  · intro x hx
    apply (hN x (hWN hx.1.2)).2.2.1 hx.1.1.1 hx.1.1.2
    intro j hj
    simpa only [Q, if_neg hj] using hx.2 j
  · intro y hy hy0 hyR
    have hdy := hN y (hWN hy)
    refine ⟨⟨hdy.2.2.2.1 hy0 hyR, hy⟩, ?_⟩
    intro j
    by_cases hj : j = a.selected
    · simp only [Q, if_pos hj, ne_eq, one_ne_zero, not_false_eq_true]
    · simpa only [Q, if_neg hj] using hdy.2.2.2.2 hy0 hyR j hj

theorem gaga21_b2_regular_carrier_local (hD : IsLocalDivisorData U V f)
    (C : gaga21_GlobalComponent V f) {p : E} (hp : p ∈ gaga21_regularSupport V f) :
    ∀ᶠ y in 𝓝 p, y ∈ gaga21_regularSupport V f →
      (y ∈ gaga21_componentCarrier C ↔ p ∈ gaga21_componentCarrier C) := by
  obtain ⟨a, rfl⟩ := gaga21_b2_occurrence hD hp.1
  have hn := gaga21_b2_regular_nearby_class hD a hp
  filter_upwards [hn] with y hy hys
  constructor
  · rintro ⟨b, hb, hby⟩
    exact ⟨a, (hy b hby).symm.trans hb, rfl⟩
  · rintro ⟨b, hb, hbp⟩
    obtain ⟨c, hc⟩ := gaga21_b2_occurrence hD hys.1
    exact ⟨c, (hy c hc).trans ((hn.self_of_nhds b hbp).symm.trans hb), hc⟩

theorem gaga21_b2_regular_carrier_clopen (hD : IsLocalDivisorData U V f)
    (C : gaga21_GlobalComponent V f) :
    IsClopen (((↑) : gaga21_regularSupport V f → E) ⁻¹' gaga21_componentCarrier C) := by
  constructor
  · apply isOpen_compl_iff.mp
    rw [isOpen_iff_mem_nhds]
    intro p hp
    filter_upwards [continuous_subtype_val.continuousAt.eventually
      (gaga21_b2_regular_carrier_local hD C p.property)] with y hy
    exact fun hm ↦ hp ((hy y.property).mp hm)
  · rw [isOpen_iff_mem_nhds]
    intro p hp
    filter_upwards [continuous_subtype_val.continuousAt.eventually
      (gaga21_b2_regular_carrier_local hD C p.property)] with y hy
    exact (hy y.property).mpr hp

theorem gaga21_b2_connected_carrier (hD : IsLocalDivisorData U V f)
    (C : gaga21_GlobalComponent V f) {R : Set E} (hc : IsPreconnected R)
    (hRS : R ⊆ gaga21_regularSupport V f)
    (hm : (R ∩ gaga21_componentCarrier C).Nonempty) : R ⊆ gaga21_componentCarrier C := by
  have hc' : IsPreconnected (((↑) : gaga21_regularSupport V f → E) ⁻¹' R) := by
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rwa [Subtype.image_preimage_coe, inter_eq_right.mpr hRS]
  obtain ⟨p, hpR, hpC⟩ := hm
  have hh := hc'.subset_isClopen (gaga21_b2_regular_carrier_clopen hD C)
    ⟨⟨p, hRS hpR⟩, hpR, hpC⟩
  exact fun y hy ↦ hh (show (⟨y, hRS hy⟩ : gaga21_regularSupport V f) ∈
    ((↑) : gaga21_regularSupport V f → E) ⁻¹' R from hy)

theorem gaga21_b2_frequent_regular (hD : IsLocalDivisorData U V f)
    (a : gaga21_LocalFactorOccurrence V f) :
    ∃ᶠ y in 𝓝 a.point, a.factor y = 0 ∧ y ∈ gaga21_regularSupport V f := by
  obtain ⟨W, R, _, hpW, _, _, hRS, _, hRzero, hd, _⟩ :=
    gaga21_b2_branch_piece hD a isOpen_univ (mem_univ _)
  exact (mem_closure_iff_frequently.mp (hd ⟨hpW, a.selected_zero⟩)).mono
    fun y hy ↦ ⟨hRzero y hy, hRS hy⟩

theorem gaga21_b2_edge_component (hD : IsLocalDivisorData U V f)
    {a b : gaga21_LocalFactorOccurrence V f} (hab : gaga21_continuation a b) (x : E)
    (ha : ∀ᶠ y in 𝓝 a.point, a.factor y = 0 → y ∈ gaga21_regularSupport V f →
      y ∈ connectedComponentIn (gaga21_regularSupport V f) x) :
    ∀ᶠ y in 𝓝 b.point, b.factor y = 0 → y ∈ gaga21_regularSupport V f →
      y ∈ connectedComponentIn (gaga21_regularSupport V f) x := by
  obtain ⟨R, hc, hRS, hRa, hRb⟩ := hab
  obtain ⟨y, hy, hya, hyr⟩ :=
    ((gaga21_b2_frequent_regular hD a).and_eventually (ha.and hRa)).exists
  have hyK := hya hy.1 hy.2
  have hyR := hyr hy.1 hy.2
  have hRK : R ⊆ connectedComponentIn (gaga21_regularSupport V f) x := by
    rw [connectedComponentIn_eq hyK]
    exact hc.2.subset_connectedComponentIn hyR hRS
  exact hRb.mono fun z hz hz0 hzS ↦ hRK (hz hz0 hzS)

theorem gaga21_b2_equiv_component (hD : IsLocalDivisorData U V f)
    {a b : gaga21_LocalFactorOccurrence V f}
    (hab : Relation.EqvGen gaga21_continuation a b) (x : E) :
    (∀ᶠ y in 𝓝 a.point, a.factor y = 0 → y ∈ gaga21_regularSupport V f →
      y ∈ connectedComponentIn (gaga21_regularSupport V f) x) ↔
    (∀ᶠ y in 𝓝 b.point, b.factor y = 0 → y ∈ gaga21_regularSupport V f →
      y ∈ connectedComponentIn (gaga21_regularSupport V f) x) := by
  induction hab with
  | rel a b hab =>
    refine ⟨gaga21_b2_edge_component hD hab x, ?_⟩
    obtain ⟨R, hc, hRS, ha, hb⟩ := hab
    exact gaga21_b2_edge_component hD ⟨R, hc, hRS, hb, ha⟩ x
  | refl a => exact Iff.rfl
  | symm a b hab ih => exact ih.symm
  | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc

theorem gaga21_b2_regular_connected (hD : IsLocalDivisorData U V f)
    (C : gaga21_GlobalComponent V f) :
    IsConnected (gaga21_regularSupport V f ∩ gaga21_componentCarrier C) := by
  let a := Quotient.out C
  have haC : Quotient.mk (gaga21_componentSetoid V f) a = C := Quotient.out_eq C
  obtain ⟨O, hO, hOo, hpO⟩ := eventually_nhds_iff.mp (gaga21_br_germ_in_carrier hD a)
  obtain ⟨W, R, hWo, hpW, hWO, hc, hRS, hRW, hz, hd, hcap⟩ :=
    gaga21_b2_branch_piece hD a hOo hpO
  obtain ⟨x, hx⟩ := hc.1
  have hxC : x ∈ gaga21_componentCarrier C := by
    rw [← haC]
    exact hO x (hWO (hRW hx)) (hz x hx)
  have hRK := hc.2.subset_connectedComponentIn hx hRS
  have hKC := gaga21_b2_connected_carrier hD C isPreconnected_connectedComponentIn
    (connectedComponentIn_subset (gaga21_regularSupport V f) x)
    ⟨x, mem_connectedComponentIn (hRS hx), hxC⟩
  have haK : ∀ᶠ y in 𝓝 a.point, a.factor y = 0 → y ∈ gaga21_regularSupport V f →
      y ∈ connectedComponentIn (gaga21_regularSupport V f) x := by
    filter_upwards [hWo.mem_nhds hpW] with y hy hy0 hyS
    exact hRK (hcap y hy hy0 hyS)
  have he : gaga21_regularSupport V f ∩ gaga21_componentCarrier C =
      connectedComponentIn (gaga21_regularSupport V f) x := by
    apply Subset.antisymm
    · rintro p ⟨hpS, b, hbC, rfl⟩
      have hab : Relation.EqvGen gaga21_continuation a b :=
        Quotient.exact (haC.trans hbC.symm)
      exact ((gaga21_b2_equiv_component hD hab x).mp haK).self_of_nhds b.selected_zero hpS
    · exact fun p hp ↦ ⟨connectedComponentIn_subset _ _ hp, hKC hp⟩
  rw [he]
  exact isConnected_connectedComponentIn_iff.mpr (hRS hx)

theorem gaga21_b2_carrier_approximation (hD : IsLocalDivisorData U V f)
    (C : gaga21_GlobalComponent V f) :
    gaga21_componentCarrier C ⊆ closure (gaga21_regularSupport V f ∩ gaga21_componentCarrier C) := by
  rintro p ⟨a, haC, rfl⟩
  apply mem_closure_iff_frequently.mpr
  apply ((gaga21_b2_frequent_regular hD a).and_eventually
    (gaga21_br_germ_in_carrier hD a)).mono
  intro y hy
  exact ⟨hy.1.2, haC ▸ hy.2 hy.1.1⟩

end RegularCarrier

theorem gaga21_carrier_regular_connected_aux {E ι : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {U : Set E} {V : ι → Set E} {f : ι → E → ℂ}
    (hD : IsLocalDivisorData U V f) (C : gaga21_GlobalComponent V f) :
    IsConnected (gaga21_regularSupport V f ∩ gaga21_componentCarrier C) ∧
    IsConnected {p | p ∈ gaga21_componentCarrier C ∧ ∃ h : E → ℂ,
      AnalyticAt ℂ h p ∧ h p = 0 ∧ fderiv ℂ h p ≠ 0 ∧
      ∀ᶠ y in 𝓝 p, y ∈ gaga21_componentCarrier C ↔ h y = 0} := by
  have hc := gaga21_b2_regular_connected hD C
  refine ⟨hc, hc.subset_closure ?_ ?_⟩
  · rintro p ⟨hpS, a, haC, hpa⟩
    obtain ⟨hsupport, h, hh, hh0, hhd, hheq⟩ := hpS
    refine ⟨⟨a, haC, hpa⟩, h, hh, hh0, hhd, ?_⟩
    have hpS : a.point ∈ gaga21_regularSupport V f :=
      by
        rw [hpa]
        exact ⟨hsupport, h, hh, hh0, hhd, hheq⟩
    have he := gaga21_b2_regular_equation hD a hpS
    have hg := gaga21_br_germ_in_carrier hD a
    rw [hpa] at he hg
    filter_upwards [hheq, he, hg] with y hyh hye hyg
    constructor
    · intro hyC
      exact hyh.mp (gaga21_b2_carrier_support hD C hyC)
    · intro hy0
      exact haC ▸ hyg (hye.mp (hyh.mpr hy0))
  · intro p hp
    exact gaga21_b2_carrier_approximation hD C hp.1

theorem gaga21_carrier_density_aux {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {U : Set E} {V : ι → Set E} {f : ι → E → ℂ}
    (hD : IsLocalDivisorData U V f) (C : gaga21_GlobalComponent V f) :
    closure (gaga21_regularSupport V f ∩ gaga21_componentCarrier C) ∩ U =
      gaga21_componentCarrier C := by
  classical
  have hCU := (gaga21_carrier_nonempty_contained_aux hD C).2
  apply Subset.antisymm
  · obtain ⟨F, hF, he⟩ := isClosed_induced_iff.mp (gaga21_carrier_closed_aux hD C)
    have hCF : gaga21_componentCarrier C ⊆ F := by
      intro x hx
      have hx' : (⟨x, hCU hx⟩ : U) ∈ ((↑) : U → E) ⁻¹' gaga21_componentCarrier C := hx
      rw [← he] at hx'
      exact hx'
    rintro x ⟨hx, hxU⟩
    have hxF := closure_minimal (inter_subset_right.trans hCF) hF hx
    have hx' : (⟨x, hxU⟩ : U) ∈ ((↑) : U → E) ⁻¹' F := hxF
    rw [he] at hx'
    exact hx'
  · intro q hq
    refine ⟨?_, hCU hq⟩
    obtain ⟨a, haC, rfl⟩ := hq
    have han : ∀ᶠ y in 𝓝 a.point, ∀ j, AnalyticAt ℂ (a.factors j) y :=
      eventually_all.mpr fun j ↦ (a.factor_data j).1.eventually_analyticAt
    obtain ⟨N, hN, hNo, hpN⟩ := eventually_nhds_iff.mp
      (han.and ((gaga21_br_regularSupport_of_clean hD a).and
        (gaga21_br_germ_in_carrier hD a)))
    obtain ⟨W, hWo, hpW, hWN, hc, hd⟩ := gaga21_br_regular_locus_within a.point a.factor
      (a.factor_data a.selected).1 (a.factor_data a.selected).2.1 hNo hpN
    let Q (j : Fin a.count) (x : E) : ℂ := if j = a.selected then 1 else a.factors j x
    have hQa : ∀ j, AnalyticOnNhd ℂ (Q j) W := by
      intro j x hx
      by_cases hj : j = a.selected
      · simpa only [Q, if_pos hj] using
          (analyticAt_const : AnalyticAt ℂ (fun _ : E ↦ (1 : ℂ)) x)
      · simpa only [Q, if_neg hj] using (hN x (hWN hx)).1 j
    have hne (j : Fin a.count) :
        {x ∈ AnalyticDivisorAlgebraic20.gaga20_regularZero a.factor ∩ W | Q j x ≠ 0}.Nonempty := by
      by_cases hj : j = a.selected
      · obtain ⟨x, hx⟩ := hc.1
        exact ⟨x, hx, by simp only [Q, if_pos hj, ne_eq, one_ne_zero, not_false_eq_true]⟩
      · by_contra hn
        have hzero : ∀ x ∈ AnalyticDivisorAlgebraic20.gaga20_regularZero a.factor ∩ W,
            a.factors j x = 0 := by
          intro x hx
          by_contra hz
          exact hn ⟨x, hx, by simpa only [Q, if_neg hj] using hz⟩
        have he : ∀ᶠ x in 𝓝 a.point, a.factor x = 0 → a.factors j x = 0 := by
          filter_upwards [hWo.mem_nhds hpW] with x hx hxa
          exact tendsto_nhds_unique_of_frequently_eq ((hN x (hWN hx)).1 j).continuousAt
            tendsto_const_nhds ((mem_closure_iff_frequently.mp (hd ⟨hx, hxa⟩)).mono
              fun y hy ↦ hzero y hy)
        obtain ⟨c, hca, hdiv⟩ := gaga21_br_nullstellensatz a.point a.factor (a.factors j)
          (a.factor_data a.selected).1 (a.factor_data j).1
          (a.factor_data a.selected).2.1 he
        exact a.coprime (Ne.symm hj) ⟨a.factor, (fun _ ↦ 1), c,
          (a.factor_data a.selected).1, analyticAt_const, hca, a.selected_zero,
          Eventually.of_forall (fun x ↦ (mul_one (a.factor x)).symm), hdiv⟩
    have hdR := (gaga21_br_regular_complement_finite Q hWo
      (fun x hx ↦ (hN x (hWN hx)).1 a.selected) hQa hc hne).2
    apply closure_mono (s := {x ∈ AnalyticDivisorAlgebraic20.gaga20_regularZero a.factor ∩ W |
      ∀ j, Q j x ≠ 0}) ?_ ((hd.trans (closure_minimal hdR isClosed_closure))
        ⟨hpW, a.selected_zero⟩)
    intro x hx
    have hxN := hN x (hWN hx.1.2)
    refine ⟨(hxN.2.1 hx.1.1.1 hx.1.1.2 ?_).1, ?_⟩
    · intro j hj
      simpa only [Q, if_neg hj] using hx.2 j
    · rw [← haC]
      exact hxN.2.2 hx.1.1.1

section FiniteBranches

variable {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {U : Set E} {V : ι → Set E} {f : ι → E → ℂ}

theorem gaga21_d2_prime_factor {t : ℕ} {F A w s : E → ℂ} {q : E}
    {P : Fin t → E → ℂ} {m : Fin t → ℕ}
    (hA : AnalyticAt ℂ A q) (hiA : IsIrreducibleAt A q)
    (hs : AnalyticAt ℂ s q) (hdiv : F =ᶠ[𝓝 q] fun y ↦ A y * s y)
    (hw : AnalyticAt ℂ w q) (hw0 : w q ≠ 0)
    (hP : ∀ j, AnalyticAt ℂ (P j) q)
    (hfac : F =ᶠ[𝓝 q] fun y ↦ w y * ∏ j, P j y ^ m j) :
    ∃ j, ∃ c : E → ℂ, AnalyticAt ℂ c q ∧
      P j =ᶠ[𝓝 q] fun y ↦ A y * c y := by
  have hdim : Module.finrank ℂ E ≠ 0 := by
    intro hz
    let e := gaga21_br_coord_fin (E := E) hz
    exact AnalyticDivisorAlgebraic18.gaga18_no_irreducible_zero (e q)
      (fun y ↦ A (e.symm y))
      ((gaga21_br_irreducible e.symm A (e q)).2 (by simpa using hiA))
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hdim
  let e := gaga21_br_coord (E := E) hn
  have ht : Tendsto e.symm (𝓝 (e q)) (𝓝 q) := by
    simpa using e.symm.continuous.tendsto (e q)
  have an (g : E → ℂ) (hg : AnalyticAt ℂ g q) :
      AnalyticAt ℂ (fun z ↦ g (e.symm z)) (e q) :=
    hg.comp_of_eq (e.symm.analyticAt _) (e.symm_apply_apply q)
  obtain ⟨j, c, hc, he⟩ := gaga17_prime_divides_factor (an A hA)
    ((gaga21_br_irreducible e.symm A (e q)).2 (by simpa using hiA))
    (an s hs) (ht.eventually hdiv) (an w hw) (by simpa using hw0)
    (fun j ↦ an (P j) (hP j)) (ht.eventually hfac)
  refine ⟨j, fun z ↦ c (e z), (gaga21_br_analyticAt e c q).2 hc, ?_⟩
  simpa only [Filter.EventuallyEq, ContinuousLinearEquiv.symm_apply_apply] using
    (e.continuous.tendsto q).eventually he

theorem gaga21_d2_class_of_containment (hD : IsLocalDivisorData U V f)
    (a : gaga21_LocalFactorOccurrence V f) :
    ∀ᶠ y in 𝓝 a.point, ∀ b : gaga21_LocalFactorOccurrence V f, b.point = y →
      (∀ᶠ z in 𝓝 y, b.factor z = 0 → a.factor z = 0) →
      Quotient.mk (gaga21_componentSetoid V f) b = Quotient.mk (gaga21_componentSetoid V f) a := by
  obtain ⟨W, R, hWo, hpW, _, hc, hreg, _, _, hcap⟩ :=
    gaga21_br_branch_piece hD a isOpen_univ (mem_univ _)
  filter_upwards [hWo.mem_nhds hpW] with y hy b hb hba
  apply Eq.symm
  apply Quotient.sound
  apply Relation.EqvGen.rel
  refine ⟨R, hc, hreg, ?_, ?_⟩
  · filter_upwards [hWo.mem_nhds hpW] with z hz hza hzr
    exact hcap z hz hza hzr
  · rw [hb]
    filter_upwards [hWo.mem_nhds hy, hba] with z hz hza hzb hzr
    exact hcap z hz (hza hzb) hzr

theorem gaga21_d2_factor_zero_chart (hD : IsLocalDivisorData U V f)
    (b : gaga21_LocalFactorOccurrence V f) (i : ι) (hi : b.point ∈ V i) :
    ∀ᶠ z in 𝓝 b.point, b.factor z = 0 → f i z = 0 := by
  obtain ⟨u, _, _, he⟩ := hD.2.2.2.2 i b.chart b.point ⟨hi, b.mem_chart⟩
  filter_upwards [he, b.factorization] with z hz hfac hzero
  have hp : ∏ j, b.factors j z ^ b.exponents j = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ b.selected)
      (pow_eq_zero_iff (Nat.ne_of_gt (b.factor_data b.selected).2.2) |>.mpr hzero)
  rw [hz, hfac, hp, mul_zero, mul_zero]

theorem gaga21_d2_local_classification (hD : IsLocalDivisorData U V f)
    (q : E) (i : ι) (hqi : q ∈ V i) (hfq : f i q = 0) :
    ∃ k : ℕ, ∃ a : Fin k → gaga21_LocalFactorOccurrence V f,
      (∀ j, (a j).point = q ∧ (a j).chart = i) ∧
      ∀ᶠ y in 𝓝 q, ∀ b : gaga21_LocalFactorOccurrence V f, b.point = y →
        ∃ j, Quotient.mk (gaga21_componentSetoid V f) b =
            Quotient.mk (gaga21_componentSetoid V f) (a j) ∧
          ∃ c : E → ℂ, AnalyticAt ℂ c y ∧
            (a j).factor =ᶠ[𝓝 y] fun z ↦ b.factor z * c z := by
  obtain ⟨k, u, P, m, hu, hu0, hP, hc, hfac⟩ :=
    gaga21_br_decomposition (hD.2.2.1 i q hqi) hfq (hD.2.2.2.1 i q hqi)
  let a (j : Fin k) : gaga21_LocalFactorOccurrence V f :=
    { chart := i, point := q, mem_chart := hqi, count := k, unit := u,
      factors := P, exponents := m, selected := j, unit_analytic := hu, unit_ne := hu0,
      factor_data := hP, coprime := hc, factorization := hfac, selected_zero := (hP j).2.1.1 }
  refine ⟨k, a, fun _ ↦ ⟨rfl, rfl⟩, ?_⟩
  have hclasses : ∀ᶠ y in 𝓝 q, ∀ j, ∀ b : gaga21_LocalFactorOccurrence V f,
      b.point = y → (∀ᶠ z in 𝓝 y, b.factor z = 0 → (a j).factor z = 0) →
      Quotient.mk (gaga21_componentSetoid V f) b =
        Quotient.mk (gaga21_componentSetoid V f) (a j) :=
    eventually_all.mpr fun j ↦ gaga21_d2_class_of_containment hD (a j)
  have hans : ∀ᶠ y in 𝓝 q, ∀ j, AnalyticAt ℂ (P j) y :=
    eventually_all.mpr fun j ↦ (hP j).1.eventually_analyticAt
  filter_upwards [(hD.1 i).mem_nhds hqi, hu.eventually_analyticAt,
    hu.continuousAt.eventually_ne hu0, hans, hfac.eventually_nhds, hclasses]
    with y hyi huy huy0 hPy hfacy hclass b hb
  have hba : AnalyticAt ℂ b.factor y := hb ▸ (b.factor_data b.selected).1
  have hbi : IsIrreducibleAt b.factor y := hb ▸ (b.factor_data b.selected).2.1
  have hbz : ∀ᶠ z in 𝓝 y, b.factor z = 0 → f i z = 0 := by
    simpa only [hb] using gaga21_d2_factor_zero_chart hD b i (hb ▸ hyi)
  obtain ⟨s, hs, hdiv⟩ := gaga21_br_nullstellensatz y b.factor (f i) hba
    (hD.2.2.1 i y hyi) hbi hbz
  obtain ⟨j, c, hca, he⟩ := gaga21_d2_prime_factor hba hbi hs hdiv huy huy0 hPy hfacy
  refine ⟨j, hclass j b hb ?_, c, hca, he⟩
  filter_upwards [he] with z hz hzb
  change P j z = 0
  rw [hz, hzb, zero_mul]

theorem gaga21_d2_associated_of_divides {A B c : E → ℂ} {q : E}
    (hA : AnalyticAt ℂ A q) (hiA : IsIrreducibleAt A q)
    (hiB : IsIrreducibleAt B q) (hc : AnalyticAt ℂ c q)
    (hdiv : B =ᶠ[𝓝 q] fun z ↦ A z * c z) : AreAssociatedAt A B q := by
  have hc0 : c q ≠ 0 := (hiB.2 A c hA hc hdiv).resolve_left (not_not.mpr hiA.1)
  apply gaga21_br_associated_symm
  refine ⟨c, hc, hc0, ?_⟩
  filter_upwards [hdiv] with z hz
  exact hz.trans (mul_comm _ _)

theorem gaga21_d2_selected_branches (hD : IsLocalDivisorData U V f)
    (C : gaga21_GlobalComponent V f) (q : E) (hq : q ∈ gaga21_componentCarrier C)
    (i : ι) (hqi : q ∈ V i) :
    ∃ k : ℕ, ∃ a : Fin k → gaga21_LocalFactorOccurrence V f,
      0 < k ∧ (∀ j, (a j).point = q ∧ (a j).chart = i ∧
        Quotient.mk (gaga21_componentSetoid V f) (a j) = C) ∧
      (∀ᶠ y in 𝓝 q, y ∈ gaga21_componentCarrier C ↔ ∃ j, (a j).factor y = 0) ∧
      (∀ b : gaga21_LocalFactorOccurrence V f, b.point = q → b.chart = i →
        (Quotient.mk (gaga21_componentSetoid V f) b = C ↔
          ∃ j, AreAssociatedAt b.factor (a j).factor q)) := by
  classical
  obtain ⟨b₀, hb₀C, hb₀q⟩ := hq
  have hfq : f i q = 0 := by
    have hz := (gaga21_d2_factor_zero_chart hD b₀ i (hb₀q ▸ hqi)).self_of_nhds
      b₀.selected_zero
    simpa only [hb₀q] using hz
  obtain ⟨r, A, hA, hmatch⟩ := gaga21_d2_local_classification hD q i hqi hfq
  let J := {j : Fin r // Quotient.mk (gaga21_componentSetoid V f) (A j) = C}
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let a (j : Fin (Fintype.card J)) := A (e j).val
  have hnon : Nonempty J := by
    obtain ⟨j, hj, _⟩ := hmatch.self_of_nhds b₀ hb₀q
    exact ⟨⟨j, hj.symm.trans hb₀C⟩⟩
  have ha (j : Fin (Fintype.card J)) : (a j).point = q ∧ (a j).chart = i ∧
      Quotient.mk (gaga21_componentSetoid V f) (a j) = C :=
    ⟨(hA _).1, (hA _).2, (e j).property⟩
  refine ⟨Fintype.card J, a, Fintype.card_pos_iff.mpr hnon, ha, ?_, ?_⟩
  · have hz : ∀ᶠ y in 𝓝 q, ∀ j, (a j).factor y = 0 →
        y ∈ gaga21_componentCarrier C := by
      apply eventually_all.mpr
      intro j
      simpa only [(ha j).1, (ha j).2.2] using gaga21_br_germ_in_carrier hD (a j)
    filter_upwards [hmatch, hz] with y hym hyz
    constructor
    · rintro ⟨b, hbC, hby⟩
      obtain ⟨j, hj, c, _, he⟩ := hym b hby
      let jC : J := ⟨j, hj.symm.trans hbC⟩
      refine ⟨e.symm jC, ?_⟩
      have hab : a (e.symm jC) = A j := by simp only [a, Equiv.apply_symm_apply, jC]
      rw [hab, he.self_of_nhds]
      have hbz : b.factor y = 0 := hby ▸ b.selected_zero
      exact mul_eq_zero_of_left hbz _
    · rintro ⟨j, hj⟩
      exact hyz j hj
  · intro b hbq _
    constructor
    · intro hbC
      obtain ⟨j, hj, c, hc, he⟩ := hmatch.self_of_nhds b hbq
      let jC : J := ⟨j, hj.symm.trans hbC⟩
      refine ⟨e.symm jC, ?_⟩
      have hab : a (e.symm jC) = A j := by simp only [a, Equiv.apply_symm_apply, jC]
      rw [hab]
      exact gaga21_d2_associated_of_divides
        (hbq ▸ (b.factor_data b.selected).1)
        (hbq ▸ (b.factor_data b.selected).2.1)
        ((hA j).1 ▸ ((A j).factor_data (A j).selected).2.1) hc he
    · rintro ⟨j, hj⟩
      have hcontain : ∀ᶠ z in 𝓝 q, b.factor z = 0 → (a j).factor z = 0 := by
        obtain ⟨u, hu, hu0, he⟩ := hj
        filter_upwards [he, hu.continuousAt.eventually_ne hu0] with z hz hzu hzb
        exact (mul_eq_zero.mp (hz.symm.trans hzb)).resolve_left hzu
      have hclass := (gaga21_d2_class_of_containment hD (a j)).self_of_nhds b
        (hbq.trans (ha j).1.symm) (by simpa only [(ha j).1] using hcontain)
      exact hclass.trans (ha j).2.2

end FiniteBranches

theorem gaga21_carrier_finite_local_branches_aux {E ι : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {U : Set E} {V : ι → Set E} {f : ι → E → ℂ}
    (hD : IsLocalDivisorData U V f) (C : gaga21_GlobalComponent V f) :
    gaga21_FiniteLocalBranches V f (gaga21_componentCarrier C) ∧
    ∀ q ∈ gaga21_componentCarrier C, ∀ i, q ∈ V i →
      ∃ k : ℕ, ∃ a : Fin k → gaga21_LocalFactorOccurrence V f,
        0 < k ∧ (∀ j, (a j).point = q ∧ (a j).chart = i ∧
          Quotient.mk (gaga21_componentSetoid V f) (a j) = C) ∧
        (∀ᶠ y in 𝓝 q, y ∈ gaga21_componentCarrier C ↔ ∃ j, (a j).factor y = 0) ∧
        (∀ b : gaga21_LocalFactorOccurrence V f, b.point = q → b.chart = i →
          (Quotient.mk (gaga21_componentSetoid V f) b = C ↔
            ∃ j, AreAssociatedAt b.factor (a j).factor q)) := by
  have h := gaga21_d2_selected_branches hD C
  refine ⟨?_, h⟩
  intro q hq i hi
  obtain ⟨k, a, hk, ha, hz, _⟩ := h q hq i hi
  exact ⟨k, a, hk, fun j ↦ ⟨(ha j).1, (ha j).2.1⟩, hz⟩

section MultiplicityComparison
variable {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {U : Set E} {V : ι → Set E} {f : ι → E → ℂ}

theorem gaga21_e2_order_associated {g h : E → ℂ} {p : E}
    (hh : AnalyticAt ℂ h p) (has : AreAssociatedAt g h p) (v : E) :
    analyticOrderAt (fun t : ℂ ↦ g (p + t • v)) 0 =
      analyticOrderAt (fun t : ℂ ↦ h (p + t • v)) 0 := by
  obtain ⟨u, hu, hu0, he⟩ := has
  have hL : AnalyticAt ℂ (fun t : ℂ ↦ p + t • v) 0 :=
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hL0 : p + (0 : ℂ) • v = p := by simp
  have ht : Tendsto (fun t : ℂ ↦ p + t • v) (𝓝 0) (𝓝 p) :=
    by simpa only [ContinuousAt, zero_smul, add_zero] using hL.continuousAt
  have hs : (fun t : ℂ ↦ g (p + t • v)) =ᶠ[𝓝 0]
      (fun t : ℂ ↦ u (p + t • v) * h (p + t • v)) := ht.eventually he
  rw [analyticOrderAt_congr hs]
  change analyticOrderAt ((fun t : ℂ ↦ u (p + t • v)) *
    (fun t : ℂ ↦ h (p + t • v))) 0 = _
  have hua : AnalyticAt ℂ (fun t : ℂ ↦ u (p + t • v)) 0 := hu.comp_of_eq hL hL0
  have hha : AnalyticAt ℂ (fun t : ℂ ↦ h (p + t • v)) 0 := hh.comp_of_eq hL hL0
  rw [analyticOrderAt_mul hua hha,
    analyticOrderAt_eq_zero.mpr (Or.inr (by simpa using hu0)), zero_add]

theorem gaga21_e2_transverse_associated {g h : E → ℂ} {p v : E}
    (hh : AnalyticAt ℂ h p) (hh0 : h p = 0)
    (has : AreAssociatedAt g h p) (hv : fderiv ℂ h p v ≠ 0) :
    fderiv ℂ g p v ≠ 0 := by
  obtain ⟨u, hu, hu0, he⟩ := has
  rw [he.fderiv_eq (𝕜 := ℂ)]
  change fderiv ℂ (u * h) p v ≠ 0
  rw [fderiv_mul hu.differentiableAt hh.differentiableAt, hh0,
    zero_smul, add_zero]
  exact mul_ne_zero hu0 hv

theorem gaga21_e2_order_near (hD : IsLocalDivisorData U V f)
    (a : gaga21_LocalFactorOccurrence V f) :
    ∀ᶠ y in 𝓝 a.point, y ∈ V a.chart ∧
      (a.factor y = 0 → y ∈ gaga21_regularSupport V f →
        ∀ h : E → ℂ, AnalyticAt ℂ h y → h y = 0 → fderiv ℂ h y ≠ 0 →
        (∀ᶠ z in 𝓝 y, z ∈ localDivisorSupport V f ↔ h z = 0) →
        ∀ v : E, fderiv ℂ h y v ≠ 0 →
          analyticOrderAt (fun t : ℂ ↦ f a.chart (y + t • v)) 0 =
            a.exponents a.selected) := by
  obtain ⟨N, hNo, hpN, _, horder⟩ := gaga21_br_clean_multiplicity
    a.unit_analytic a.unit_ne (fun j ↦ (a.factor_data j).1)
    (fun j ↦ (a.factor_data j).2.1) (fun j ↦ (a.factor_data j).2.2)
    a.coprime a.factorization
  have ha := (a.factor_data a.selected).1
  filter_upwards [hNo.mem_nhds hpN, (hD.1 a.chart).mem_nhds a.mem_chart,
    ha.eventually_analyticAt,
    gaga21_br_eventually_squarefree ha (a.factor_data a.selected).2.1,
    a.factorization.eventually_nhds, gaga21_br_regularSupport_clean hD a]
    with y hyN hyV hya hys hyfac hyclean
  refine ⟨hyV, ?_⟩
  intro hy0 hyr h hh hh0 hhd hz v hv
  have hzh : ∀ᶠ z in 𝓝 y, a.factor z = 0 → h z = 0 := by
    filter_upwards [hz, hyfac, (hD.1 a.chart).mem_nhds hyV] with z hze hzf hzV hza
    apply hze.mp
    apply (spec_mem_localDivisorSupport_iff hD a.chart z hzV).mpr
    rw [hzf]
    have hp : ∏ j, a.factors j z ^ a.exponents j = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ a.selected)
        (pow_eq_zero_iff (Nat.ne_of_gt (a.factor_data a.selected).2.2) |>.mpr hza)
    rw [hp, mul_zero]
  have has := gaga21_br_reduced_of_regular_containment hya hy0 hys hh hh0 hhd hzh
  exact horder y hyN a.selected hy0 (hyclean hy0 hyr) v
    (gaga21_e2_transverse_associated hh hh0 has hv)

theorem gaga21_e2_compare_near (hD : IsLocalDivisorData U V f)
    (a : gaga21_LocalFactorOccurrence V f) :
    ∀ᶠ y in 𝓝 a.point, a.factor y = 0 → y ∈ gaga21_regularSupport V f →
      ∀ b : gaga21_LocalFactorOccurrence V f, b.point = y →
        a.exponents a.selected = b.exponents b.selected := by
  filter_upwards [gaga21_e2_order_near hD a] with y hy
  intro hy0 hyr b hby
  obtain ⟨h, hh, hh0, hhd, hz⟩ := hyr.2
  have hex : ∃ v, fderiv ℂ h y v ≠ 0 := by
    by_contra! hn
    exact hhd (ContinuousLinearMap.ext fun v ↦ hn v)
  obtain ⟨v, hv⟩ := hex
  have hb := (gaga21_e2_order_near hD b).self_of_nhds
  rw [hby] at hb
  have hb0 : b.factor y = 0 := hby ▸ b.selected_zero
  have h1 := hy.2 hy0 hyr h hh hh0 hhd hz v hv
  have h2 := hb.2 hb0 hyr h hh hh0 hhd hz v hv
  have he := gaga21_e2_order_associated (hD.2.2.1 b.chart y hb.1)
    (hD.2.2.2.2 a.chart b.chart y ⟨hy.1, hb.1⟩) v
  exact_mod_cast h1.symm.trans (he.trans h2)

theorem gaga21_e2_occurrence (hD : IsLocalDivisorData U V f)
    {p : E} (hp : p ∈ localDivisorSupport V f) :
    ∃ a : gaga21_LocalFactorOccurrence V f, a.point = p := by
  obtain ⟨i, hpi, hz⟩ := hp
  obtain ⟨k, u, P, m, hu, hu0, hP, hcop, hfac⟩ :=
    gaga21_br_decomposition (hD.2.2.1 i p hpi) hz (hD.2.2.2.1 i p hpi)
  have hp : ∏ j, P j p ^ m j = 0 :=
    (mul_eq_zero.mp (hfac.self_of_nhds.symm.trans hz)).resolve_left hu0
  obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp hp
  exact ⟨⟨i, p, hpi, k, u, P, m, j, hu, hu0, hP, hcop, hfac,
    eq_zero_of_pow_eq_zero hj⟩, rfl⟩

theorem gaga21_e2_multiplicity_function (hD : IsLocalDivisorData U V f) :
    ∃ m : E → ℕ, ∀ a : gaga21_LocalFactorOccurrence V f,
      ∀ᶠ y in 𝓝 a.point, a.factor y = 0 → y ∈ gaga21_regularSupport V f →
        m y = a.exponents a.selected := by
  classical
  have hex : ∀ y : gaga21_regularSupport V f,
      ∃ a : gaga21_LocalFactorOccurrence V f, a.point = y.1 :=
    fun y ↦ gaga21_e2_occurrence hD y.property.1
  choose c hc using hex
  let m : E → ℕ := fun y ↦ if hy : y ∈ gaga21_regularSupport V f then
    (c ⟨y, hy⟩).exponents (c ⟨y, hy⟩).selected else 0
  refine ⟨m, fun a ↦ ?_⟩
  filter_upwards [gaga21_e2_compare_near hD a] with y hy
  intro hy0 hyr
  simp only [m, dite_eq_left hyr]
  exact (hy hy0 hyr (c ⟨y, hyr⟩) (hc ⟨y, hyr⟩)).symm

theorem gaga21_e2_support_near_regular (hD : IsLocalDivisorData U V f)
    (a : gaga21_LocalFactorOccurrence V f) (hr : a.point ∈ gaga21_regularSupport V f) :
    ∀ᶠ y in 𝓝 a.point, y ∈ localDivisorSupport V f → a.factor y = 0 := by
  classical
  have hclean := (gaga21_br_regularSupport_clean hD a).self_of_nhds a.selected_zero hr
  have hother : ∀ᶠ y in 𝓝 a.point, ∀ j, j ≠ a.selected → a.factors j y ≠ 0 := by
    apply eventually_all.mpr
    intro j
    by_cases hj : j = a.selected
    · exact Eventually.of_forall fun _ hne ↦ (hne hj).elim
    · exact ((a.factor_data j).1.continuousAt.eventually_ne (hclean j hj)).mono
        fun _ h _ ↦ h
  filter_upwards [a.factorization, a.unit_analytic.continuousAt.eventually_ne a.unit_ne,
    (hD.1 a.chart).mem_nhds a.mem_chart, hother] with y hyfac hyu hyV hyo
  intro hys
  have hz := (spec_mem_localDivisorSupport_iff hD a.chart y hyV).mp hys
  have hp : ∏ j, a.factors j y ^ a.exponents j = 0 :=
    (mul_eq_zero.mp (hyfac.symm.trans hz)).resolve_left hyu
  obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp hp
  have hj0 := eq_zero_of_pow_eq_zero hj
  by_cases hjs : j = a.selected
  · simpa only [gaga21_LocalFactorOccurrence.factor, hjs] using hj0
  · exact (hyo j hjs hj0).elim

theorem gaga21_e2_locally_constant (hD : IsLocalDivisorData U V f) (m : E → ℕ)
    (hm : ∀ a : gaga21_LocalFactorOccurrence V f,
      ∀ᶠ y in 𝓝 a.point, a.factor y = 0 → y ∈ gaga21_regularSupport V f →
        m y = a.exponents a.selected)
    {x : E} (hx : x ∈ gaga21_regularSupport V f) :
    ∀ᶠ y in 𝓝 x, y ∈ gaga21_regularSupport V f → m y = m x := by
  obtain ⟨a, ha⟩ := gaga21_e2_occurrence hD hx.1
  subst x
  have hmx := (hm a).self_of_nhds a.selected_zero hx
  filter_upwards [hm a, gaga21_e2_support_near_regular hD a hx] with y hy hz
  intro hyr
  exact (hy (hz hyr.1) hyr).trans hmx.symm

theorem gaga21_e2_regular_zero_in (hD : IsLocalDivisorData U V f)
    (a : gaga21_LocalFactorOccurrence V f) {O : Set E} (hOo : IsOpen O) (hpO : a.point ∈ O) :
    ∃ y ∈ O, a.factor y = 0 ∧ y ∈ gaga21_regularSupport V f := by
  classical
  have han : ∀ᶠ y in 𝓝 a.point, ∀ j, AnalyticAt ℂ (a.factors j) y :=
    eventually_all.mpr fun j ↦ (a.factor_data j).1.eventually_analyticAt
  have hdata : ∀ᶠ y in 𝓝 a.point, y ∈ O ∧ (∀ j, AnalyticAt ℂ (a.factors j) y) ∧
      (a.factor y = 0 → fderiv ℂ a.factor y ≠ 0 →
        (∀ j, j ≠ a.selected → a.factors j y ≠ 0) → y ∈ gaga21_regularSupport V f) := by
    filter_upwards [hOo.mem_nhds hpO, han, gaga21_br_regularSupport_of_clean hD a]
      with y hyO hya hyf
    exact ⟨hyO, hya, fun hz hd ho ↦ (hyf hz hd ho).1⟩
  obtain ⟨N, hN, hNo, hpN⟩ := eventually_nhds_iff.mp hdata
  obtain ⟨W, hWo, hpW, hWN, hc, hd⟩ := gaga21_br_regular_locus_within a.point a.factor
    (a.factor_data a.selected).1 (a.factor_data a.selected).2.1 hNo hpN
  let Q (j : Fin a.count) (x : E) : ℂ := if j = a.selected then 1 else a.factors j x
  have hQa : ∀ j, AnalyticOnNhd ℂ (Q j) W := by
    intro j x hx
    by_cases hj : j = a.selected
    · simpa only [Q, ite_eq_left hj] using (analyticAt_const : AnalyticAt ℂ (fun _ : E ↦ (1 : ℂ)) x)
    · simpa only [Q, ite_eq_right hj] using (hN x (hWN hx)).2.1 j
  have hne (j : Fin a.count) :
      {x ∈ AnalyticDivisorAlgebraic20.gaga20_regularZero a.factor ∩ W | Q j x ≠ 0}.Nonempty := by
    by_cases hj : j = a.selected
    · obtain ⟨x, hx⟩ := hc.1
      exact ⟨x, hx, by simp only [Q, ite_eq_left hj, ne_eq, one_ne_zero, not_false_eq_true]⟩
    · by_contra hn
      have hzero : ∀ x ∈ AnalyticDivisorAlgebraic20.gaga20_regularZero a.factor ∩ W,
          a.factors j x = 0 := by
        intro x hx
        by_contra hz
        exact hn ⟨x, hx, by simpa only [Q, ite_eq_right hj] using hz⟩
      have he : ∀ᶠ x in 𝓝 a.point, a.factor x = 0 → a.factors j x = 0 := by
        filter_upwards [hWo.mem_nhds hpW] with x hx hxa
        exact tendsto_nhds_unique_of_frequently_eq ((hN x (hWN hx)).2.1 j).continuousAt
          tendsto_const_nhds ((mem_closure_iff_frequently.mp (hd ⟨hx, hxa⟩)).mono
            fun y hy ↦ hzero y hy)
      obtain ⟨c, hca, hdiv⟩ := gaga21_br_nullstellensatz a.point a.factor (a.factors j)
        (a.factor_data a.selected).1 (a.factor_data j).1
        (a.factor_data a.selected).2.1 he
      exact a.coprime (Ne.symm hj) ⟨a.factor, (fun _ ↦ 1), c,
        (a.factor_data a.selected).1, analyticAt_const, hca, a.selected_zero,
        Eventually.of_forall (fun x ↦ (mul_one (a.factor x)).symm), hdiv⟩
  obtain ⟨hcR, _⟩ := gaga21_br_regular_complement_finite Q hWo
    (fun x hx ↦ (hN x (hWN hx)).2.1 a.selected) hQa hc hne
  obtain ⟨y, hy⟩ := hcR.nonempty
  refine ⟨y, (hN y (hWN hy.1.2)).1, hy.1.1.1, ?_⟩
  apply (hN y (hWN hy.1.2)).2.2 hy.1.1.1 hy.1.1.2
  intro j hj
  simpa only [Q, ite_eq_right hj] using hy.2 j

end MultiplicityComparison

theorem gaga21_multiplicity_invariance_aux {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {U : Set E} {V : ι → Set E} {f : ι → E → ℂ}
    (hD : IsLocalDivisorData U V f)
    (a b : gaga21_LocalFactorOccurrence V f)
    (hab : Quotient.mk (gaga21_componentSetoid V f) a = Quotient.mk (gaga21_componentSetoid _ _) b) :
    a.exponents a.selected = b.exponents b.selected := by
  obtain ⟨m, hm⟩ := gaga21_e2_multiplicity_function hD
  have hedge (a b : gaga21_LocalFactorOccurrence V f) (hab : gaga21_continuation a b) :
      a.exponents a.selected = b.exponents b.selected := by
    obtain ⟨R, hconn, hR, ha, hb⟩ := hab
    have hconst := AnalyticDivisorAlgebraic20.gaga20_multiplicity_constancy
      (fun _ : Unit ↦ m) (fun _ ↦ R) (fun _ ↦ hconn) (by
        intro _ x hx
        obtain ⟨W, hW, hWo, hxW⟩ := eventually_nhds_iff.mp
          (gaga21_e2_locally_constant hD m hm (hR hx))
        exact ⟨W, hWo.mem_nhds hxW, fun y hy ↦ hW y hy.1 (hR hy.2)⟩)
    have hend (c : gaga21_LocalFactorOccurrence V f)
        (hc : ∀ᶠ y in 𝓝 c.point,
          c.factor y = 0 → y ∈ gaga21_regularSupport V f → y ∈ R) :
        ∃ y ∈ R, m y = c.exponents c.selected := by
      obtain ⟨O, hO, hOo, hpO⟩ := eventually_nhds_iff.mp ((hm c).and hc)
      obtain ⟨y, hyO, hy0, hyr⟩ := gaga21_e2_regular_zero_in hD c hOo hpO
      exact ⟨y, (hO y hyO).2 hy0 hyr, (hO y hyO).1 hy0 hyr⟩
    obtain ⟨x, hx, hmx⟩ := hend a ha
    obtain ⟨y, hy, hmy⟩ := hend b hb
    exact hmx.symm.trans ((hconst () x hx y hy).symm.trans hmy)
  have he : Relation.EqvGen gaga21_continuation a b := Quotient.exact hab
  clear hab
  induction he with
  | rel a b h => exact hedge a b h
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ hab hbc => exact hab.trans hbc

/-- At a regular support point, every certified branch defines the support germ. -/
theorem gaga21_f2_regular_germ {E ι : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {U : Set E} {V : ι → Set E}
    {f : ι → E → ℂ} (hD : IsLocalDivisorData U V f)
    (a : gaga21_LocalFactorOccurrence V f)
    (hr : a.point ∈ gaga21_regularSupport V f) :
    ∀ᶠ z in 𝓝 a.point, a.factor z = 0 ↔ z ∈ localDivisorSupport V f := by
  obtain ⟨_, h, hh, hh0, hhd, hz⟩ := hr
  have haz : ∀ᶠ z in 𝓝 a.point, a.factor z = 0 → h z = 0 := by
    filter_upwards [hz, a.factorization, (hD.1 a.chart).mem_nhds a.mem_chart]
      with z hz hf hzV ha
    apply hz.mp
    apply (spec_mem_localDivisorSupport_iff hD a.chart z hzV).mpr
    rw [hf]
    have hp : ∏ j, a.factors j z ^ a.exponents j = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ a.selected)
        (by rw [show a.factors a.selected z = 0 from ha,
          zero_pow (Nat.ne_of_gt (a.factor_data a.selected).2.2)])
    rw [hp, mul_zero]
  obtain ⟨u, hu, hu0, he⟩ := gaga21_br_reduced_of_regular_containment
    (a.factor_data a.selected).1 a.selected_zero
    (gaga21_br_squarefree_of_irreducible (a.factor_data a.selected).2.1)
    hh hh0 hhd haz
  filter_upwards [he, hu.continuousAt.eventually_ne hu0, hz] with z he hu hz
  change a.factors a.selected z = 0 ↔ z ∈ localDivisorSupport V f
  rw [he, mul_eq_zero, or_iff_right hu]
  exact hz.symm

/-- Two certified branches at the same regular support point have the same class. -/
theorem gaga21_f2_regular_class {E ι : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E] {U : Set E} {V : ι → Set E}
    {f : ι → E → ℂ} (hD : IsLocalDivisorData U V f)
    (a b : gaga21_LocalFactorOccurrence V f) (hp : b.point = a.point)
    (hr : a.point ∈ gaga21_regularSupport V f) :
    Quotient.mk (gaga21_componentSetoid V f) a =
      Quotient.mk (gaga21_componentSetoid V f) b := by
  have hb := gaga21_f2_regular_germ hD b (hp.symm ▸ hr)
  rw [hp] at hb
  have ha := gaga21_f2_regular_germ hD a hr
  obtain ⟨W, R, hWo, hpW, _, hc, hR, _, _, hcap⟩ :=
    gaga21_br_branch_piece hD a isOpen_univ (mem_univ _)
  apply Quotient.sound
  apply Relation.EqvGen.rel
  refine ⟨R, hc, hR, ?_, ?_⟩
  · filter_upwards [hWo.mem_nhds hpW] with z hz hza hzr
    exact hcap z hz hza hzr
  · rw [hp]
    filter_upwards [hWo.mem_nhds hpW, ha, hb] with z hz ha hb hzb hzr
    exact hcap z hz (ha.mpr (hb.mp hzb)) hzr
private theorem gaga21_quotient_eq_of_continuation {E ι : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {V : ι → Set E} {f : ι → E → ℂ}
    {a b : gaga21_LocalFactorOccurrence V f} (h : gaga21_continuation a b) :
    Quotient.mk (gaga21_componentSetoid V f) a =
      Quotient.mk (gaga21_componentSetoid V f) b := by
  exact Quotient.sound (Relation.EqvGen.rel a b h)

theorem gaga21_finite_incidence_aux {E ι : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {U : Set E} {V : ι → Set E} {f : ι → E → ℂ}
    (hD : IsLocalDivisorData U V f)
    (q : E) (hq : q ∈ U) : ∃ W ∈ 𝓝 q,
      {C : gaga21_GlobalComponent V f | (gaga21_componentCarrier C ∩ W).Nonempty}.Finite := by
  classical
  obtain ⟨i, hqi⟩ := mem_iUnion.mp (hD.2.1.symm ▸ hq)
  have hcover : ∃ S : Set (gaga21_GlobalComponent V f), S.Finite ∧
      ∀ᶠ z in 𝓝 q, z ∈ localDivisorSupport V f →
        ∃ C ∈ S, z ∈ gaga21_componentCarrier C := by
    by_cases hf0 : f i q = 0
    · obtain ⟨k, u, P, m, hu, hu0, hP, hc, he⟩ :=
        gaga21_br_decomposition (hD.2.2.1 i q hqi) hf0 (hD.2.2.2.1 i q hqi)
      let a (j : Fin k) : gaga21_LocalFactorOccurrence V f :=
        { chart := i, point := q, mem_chart := hqi, count := k, unit := u,
          factors := P, exponents := m, selected := j, unit_analytic := hu,
          unit_ne := hu0, factor_data := hP, coprime := hc,
          factorization := he, selected_zero := (hP j).2.1.1 }
      let c (j : Fin k) : gaga21_GlobalComponent V f :=
        Quotient.mk (gaga21_componentSetoid V f) (a j)
      refine ⟨Set.range c, Set.finite_range c, ?_⟩
      have hg : ∀ᶠ z in 𝓝 q, ∀ j, P j z = 0 →
          z ∈ gaga21_componentCarrier (c j) :=
        eventually_all.mpr fun j ↦ gaga21_br_germ_in_carrier hD (a j)
      filter_upwards [hg, he, hu.continuousAt.eventually_ne hu0,
        (hD.1 i).mem_nhds hqi] with z hg he hu hzV hzs
      have hfz := (spec_mem_localDivisorSupport_iff hD i z hzV).mp hzs
      have hp : ∏ j, P j z ^ m j = 0 :=
        (mul_eq_zero.mp (he.symm.trans hfz)).resolve_left hu
      obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp hp
      have hj0 : P j z = 0 := (pow_eq_zero_iff (Nat.ne_of_gt (hP j).2.2)).mp hj
      exact ⟨c j, ⟨j, rfl⟩, hg j hj0⟩
    · refine ⟨∅, Set.finite_empty, ?_⟩
      filter_upwards [(hD.2.2.1 i q hqi).continuousAt.eventually_ne hf0,
        (hD.1 i).mem_nhds hqi] with z hz hzV hzs
      exact (hz ((spec_mem_localDivisorSupport_iff hD i z hzV).mp hzs)).elim
  obtain ⟨S, hS, hcover⟩ := hcover
  obtain ⟨W, hW, hWo, hqW⟩ := eventually_nhds_iff.mp hcover
  refine ⟨W, hWo.mem_nhds hqW, hS.subset ?_⟩
  rintro C ⟨y, hyC, hyW⟩
  have hycl : y ∈ closure (gaga21_regularSupport V f ∩ gaga21_componentCarrier C) := by
    have hy : y ∈ closure (gaga21_regularSupport V f ∩ gaga21_componentCarrier C) ∩ U := by
      rw [gaga21_carrier_density_aux hD C]
      exact hyC
    exact hy.1
  obtain ⟨z, hzW, hzr, hzC⟩ := mem_closure_iff.mp hycl W hWo hyW
  obtain ⟨D, hDS, hzD⟩ := hW z hzW hzr.1
  obtain ⟨a, haC, haz⟩ := hzC
  obtain ⟨b, hbD, hbz⟩ := hzD
  have hCD : C = D := by
    rw [← haC, ← hbD]
    exact gaga21_f2_regular_class hD a b (hbz.trans haz.symm) (haz.symm ▸ hzr)
  exact hCD.symm ▸ hDS

private theorem gaga21_g2_irreducible_in_finite_union {n k : ℕ}
    {q : (Fin n → ℂ) × ℂ} {h : (Fin n → ℂ) × ℂ → ℂ}
    {P : Fin k → (Fin n → ℂ) × ℂ → ℂ}
    (hh : AnalyticAt ℂ h q) (hi : IsIrreducibleAt h q)
    (hP : ∀ j, AnalyticAt ℂ (P j) q ∧ IsIrreducibleAt (P j) q)
    (hz : ∀ᶠ y in nhds q, h y = 0 → ∃ j, P j y = 0) :
    ∃ j, AreAssociatedAt h (P j) q := by
  let R : (Fin n → ℂ) × ℂ → ℂ := fun y ↦ ∏ j, P j y
  have hR : AnalyticAt ℂ R q := Finset.analyticAt_fun_prod _ fun j _ ↦ (hP j).1
  have hzR : ∀ᶠ y in nhds q, h y = 0 → R y = 0 := hz.mono fun y hy hy0 ↦ by
    obtain ⟨j, hj⟩ := hy hy0
    exact Finset.prod_eq_zero (Finset.mem_univ j) hj
  obtain ⟨c, hc, hdiv⟩ := gaga21_br_nullstellensatz q h R hh hR hi hzR
  obtain ⟨j, d, hd, hj⟩ := gaga17_prime_divides_factor
    (e := fun _ ↦ 1) hh hi hc hdiv analyticAt_const one_ne_zero (fun j ↦ (hP j).1)
    (Eventually.of_forall fun y ↦ by simp [R])
  exact ⟨j, gaga17_associated_of_irreducible_divides hh hi (hP j).1 (hP j).2 hd hj⟩

private theorem gaga21_g2_carrier_germ {n : ℕ} {ι : Type}
    {U : Set ((Fin n → ℂ) × ℂ)} {V : ι → Set ((Fin n → ℂ) × ℂ)}
    {f : ι → (Fin n → ℂ) × ℂ → ℂ} (hD : IsLocalDivisorData U V f)
    (i : ι) (q : (Fin n → ℂ) × ℂ) (hq : q ∈ V i)
    (h : (Fin n → ℂ) × ℂ → ℂ) (hh : AnalyticAt ℂ h q)
    (hi : IsIrreducibleAt h q) (C : gaga21_GlobalComponent V f) :
    (∀ᶠ y in 𝓝 q, h y = 0 → y ∈ gaga21_componentCarrier C) ↔
      ∃ a : gaga21_LocalFactorOccurrence V f, a.point = q ∧ a.chart = i ∧
        Quotient.mk (gaga21_componentSetoid V f) a = C ∧ AreAssociatedAt h a.factor q := by
  constructor
  · intro hz
    obtain ⟨k, a, _, ha, he, _⟩ :=
      (gaga21_carrier_finite_local_branches_aux hD C).2 q (hz.self_of_nhds hi.1) i hq
    obtain ⟨j, hj⟩ := gaga21_g2_irreducible_in_finite_union hh hi
      (fun j ↦ by simpa only [← (ha j).1] using
        ⟨((a j).factor_data (a j).selected).1, ((a j).factor_data (a j).selected).2.1⟩)
      (hz.and he |>.mono fun y hy hy0 ↦ (hy.2).mp (hy.1 hy0))
    exact ⟨a j, (ha j).1, (ha j).2.1, (ha j).2.2, hj⟩
  · rintro ⟨a, ha, _, hc, u, hu, hu0, he⟩
    have hz := gaga21_br_germ_in_carrier hD a
    rw [ha, hc] at hz
    filter_upwards [hz, he, hu.continuousAt.eventually_ne hu0] with y hy hey huy hy0
    exact hy ((mul_eq_zero.mp (hey.symm.trans hy0)).resolve_left huy)

private theorem gaga21_g2_carrier_unique {n : ℕ} {ι : Type}
    {U : Set ((Fin n → ℂ) × ℂ)} {V : ι → Set ((Fin n → ℂ) × ℂ)}
    {f : ι → (Fin n → ℂ) × ℂ → ℂ} (hD : IsLocalDivisorData U V f)
    (a : gaga21_LocalFactorOccurrence V f) (C : gaga21_GlobalComponent V f)
    (hz : ∀ᶠ y in 𝓝 a.point, a.factor y = 0 → y ∈ gaga21_componentCarrier C) :
    Quotient.mk (gaga21_componentSetoid V f) a = C := by
  obtain ⟨k, b, _, hb, he, hmatch⟩ :=
    (gaga21_carrier_finite_local_branches_aux hD C).2 a.point
      (hz.self_of_nhds a.selected_zero) a.chart a.mem_chart
  apply (hmatch a rfl rfl).mpr
  exact gaga21_g2_irreducible_in_finite_union (a.factor_data a.selected).1
    (a.factor_data a.selected).2.1
    (fun j ↦ by simpa only [← (hb j).1] using
      ⟨((b j).factor_data (b j).selected).1, ((b j).factor_data (b j).selected).2.1⟩)
    (hz.and he |>.mono fun y hy hy0 ↦ hy.2.mp (hy.1 hy0))

private theorem gaga21_g2_translate_analytic {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : E → ℂ} {q : E} (hf : AnalyticAt ℂ f q) :
    AnalyticAt ℂ (fun y ↦ f (q + y)) 0 :=
  hf.comp_of_eq (analyticAt_const.add analyticAt_id) (add_zero q)

private theorem gaga21_g2_translate_irreducible {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : E → ℂ} {q : E} (hi : IsIrreducibleAt f q) :
    IsIrreducibleAt (fun y ↦ f (q + y)) 0 := by
  refine ⟨by simpa only [add_zero] using hi.1, ?_⟩
  intro g h hg hh he
  have ht := (continuous_id.sub continuous_const).tendsto' q 0 (sub_self q)
  have ha : AnalyticAt ℂ (fun y : E ↦ y - q) q := analyticAt_id.sub analyticAt_const
  have he' : f =ᶠ[𝓝 q] fun y ↦ g (y - q) * h (y - q) := by
    simpa [Filter.EventuallyEq, Function.comp_def, add_comm] using ht.eventually he
  simpa only [Function.comp_apply, sub_self] using hi.2 _ _ (hg.comp_of_eq ha (sub_self q))
    (hh.comp_of_eq ha (sub_self q)) he'

private theorem gaga21_g2_translate_coprime {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f g : E → ℂ} {q : E} (hc : IsCoprimeAt f g q) :
    IsCoprimeAt (fun y ↦ f (q + y)) (fun y ↦ g (q + y)) 0 := by
  rintro ⟨a, b, c, ha, hb, hd, hz, he, hf⟩
  have ht := (continuous_id.sub continuous_const).tendsto' q 0 (sub_self q)
  have han : AnalyticAt ℂ (fun y : E ↦ y - q) q := analyticAt_id.sub analyticAt_const
  apply hc
  refine ⟨fun y ↦ a (y - q), fun y ↦ b (y - q), fun y ↦ c (y - q),
    ha.comp_of_eq han (sub_self q), hb.comp_of_eq han (sub_self q),
    hd.comp_of_eq han (sub_self q), by simpa only [sub_self] using hz, ?_, ?_⟩
  · simpa [Filter.EventuallyEq, Function.comp_def, add_comm] using ht.eventually he
  · simpa [Filter.EventuallyEq, Function.comp_def, add_comm] using ht.eventually hf

private theorem gaga21_g2_associated_of_germ {n : ℕ}
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

private theorem gaga21_g2_germ_class_iff {n : ℕ}
    {f g : (Fin n → ℂ) × ℂ → ℂ} {q : (Fin n → ℂ) × ℂ}
    (hf : AnalyticAt ℂ (fun y ↦ f (q + y)) 0)
    (hg : AnalyticAt ℂ (fun y ↦ g (q + y)) 0) :
    Associates.mk (productAnalyticGermOf (fun y ↦ f (q + y)) hf) =
      Associates.mk (productAnalyticGermOf (fun y ↦ g (q + y)) hg) ↔
      AreAssociatedAt f g q := by
  rw [Associates.mk_eq_mk_iff_associated]
  constructor
  · intro he
    obtain ⟨u, hu, hu0, he⟩ := gaga21_g2_associated_of_germ hf hg he
    refine ⟨fun y ↦ u (y - q), hu.comp_of_eq
      (analyticAt_id.sub analyticAt_const) (sub_self q),
      by simpa only [sub_self] using hu0, ?_⟩
    simpa [Filter.EventuallyEq, Function.comp_def, add_comm] using
      ((continuous_id.sub continuous_const).tendsto' q 0 (sub_self q)).eventually he
  · rintro ⟨u, hu, hu0, he⟩
    have hut := gaga21_g2_translate_analytic hu
    let ug := productAnalyticGermOf (fun y ↦ u (q + y)) hut
    have hunit : IsUnit ug := by
      apply isUnit_iff_exists_inv.mpr
      refine ⟨productAnalyticGermOf (fun y ↦ (u (q + y))⁻¹)
        (hut.inv (by simpa only [add_zero] using hu0)), Subtype.ext ?_⟩
      apply Filter.Germ.coe_eq.mpr
      filter_upwards [hut.continuousAt.eventually_ne (by simpa only [add_zero] using hu0)]
        with y hy
      exact mul_inv_cancel₀ hy
    have heq : productAnalyticGermOf (fun y ↦ f (q + y)) hf =
        ug * productAnalyticGermOf (fun y ↦ g (q + y)) hg := by
      apply Subtype.ext
      apply Filter.Germ.coe_eq.mpr
      exact ((continuous_const.add continuous_id).tendsto' 0 q (add_zero q)).eventually he
    rw [heq]
    exact associated_unit_mul_left _ _ hunit

private theorem gaga21_g2_class_ne_of_coprime {n : ℕ}
    {f g : (Fin n → ℂ) × ℂ → ℂ} {q : (Fin n → ℂ) × ℂ}
    (hf : AnalyticAt ℂ f q) (hg : AnalyticAt ℂ g q)
    (hi : IsIrreducibleAt f q) (hc : IsCoprimeAt f g q) :
    Associates.mk (productAnalyticGermOf (fun y ↦ f (q + y))
      (gaga21_g2_translate_analytic hf)) ≠
      Associates.mk (productAnalyticGermOf (fun y ↦ g (q + y))
        (gaga21_g2_translate_analytic hg)) := by
  intro he
  obtain ⟨u, hu, _, he⟩ := gaga21_br_associated_symm
    ((gaga21_g2_germ_class_iff _ _).mp he)
  exact hc ⟨f, fun _ ↦ 1, u, hf, analyticAt_const, hu, hi.1,
    Eventually.of_forall (fun y ↦ (mul_one (f y)).symm),
    he.mono fun y hy ↦ hy.trans (mul_comm _ _)⟩

private theorem gaga21_g2_carrier_support {E ι : Type} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {V : ι → Set E} {f : ι → E → ℂ}
    (C : gaga21_GlobalComponent V f) :
    gaga21_componentCarrier C ⊆ localDivisorSupport V f := by
  rintro q ⟨a, _, rfl⟩
  refine ⟨a.chart, a.mem_chart, ?_⟩
  rw [a.factorization.self_of_nhds]
  have hz : ∏ j, a.factors j a.point ^ a.exponents j = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ a.selected)
      (pow_eq_zero_iff (Nat.ne_of_gt (a.factor_data a.selected).2.2) |>.mpr a.selected_zero)
  change a.unit a.point * (∏ j, a.factors j a.point ^ a.exponents j) = 0
  rw [hz, mul_zero]

private theorem gaga21_g2_restrict_of_associated {n : ℕ} {ι : Type}
    {U : Set ((Fin n → ℂ) × ℂ)} {V : ι → Set ((Fin n → ℂ) × ℂ)}
    {f : ι → (Fin n → ℂ) × ℂ → ℂ} (hD : IsLocalDivisorData U V f)
    (a : gaga21_LocalFactorOccurrence V f) (h : (Fin n → ℂ) × ℂ → ℂ)
    (ha : AreAssociatedAt h a.factor a.point) :
    gaga21_restrictMultiplicity (gaga21_gluedDivisor V f) a.point h =
      a.exponents a.selected := by
  classical
  have he : ∀ᶠ y in 𝓝 a.point, h y = 0 ↔ a.factor y = 0 := by
    obtain ⟨u, hu, hu0, he⟩ := ha
    filter_upwards [he, hu.continuousAt.eventually_ne hu0] with y hy huy
    rw [hy, mul_eq_zero]
    exact or_iff_right (huy)
  have hz : ∀ᶠ y in 𝓝 a.point, h y = 0 →
      y ∈ gaga21_componentCarrier (Quotient.mk (gaga21_componentSetoid V f) a) := by
    filter_upwards [he, gaga21_br_germ_in_carrier hD a] with y hey hy hh
    exact hy (hey.mp hh)
  change (∑ᶠ C : gaga21_GlobalComponent V f,
    if (∀ᶠ y in 𝓝 a.point, h y = 0 → y ∈ gaga21_componentCarrier C)
    then (Quotient.out C).exponents (Quotient.out C).selected else 0) = _
  rw [finsum_eq_single _ (Quotient.mk (gaga21_componentSetoid V f) a)]
  · rw [if_pos hz]
    exact gaga21_multiplicity_invariance_aux hD _ a (Quotient.out_eq _)
  · intro C hC
    apply if_neg
    intro hc
    apply hC
    apply Eq.symm
    apply gaga21_g2_carrier_unique hD a C
    filter_upwards [he, hc] with y hey hy hh
    exact hy (hey.mpr hh)

private theorem gaga21_g2_divisor_decomposition {n k : ℕ}
    {q : (Fin n → ℂ) × ℂ} {f u : (Fin n → ℂ) × ℂ → ℂ}
    {P : Fin k → (Fin n → ℂ) × ℂ → ℂ} {m : Fin k → ℕ}
    (hf : AnalyticAt ℂ f q) (hu : AnalyticAt ℂ u q) (hu0 : u q ≠ 0)
    (hP : ∀ j, AnalyticAt ℂ (P j) q ∧ IsIrreducibleAt (P j) q ∧ 0 < m j)
    (hc : Pairwise (fun j l ↦ IsCoprimeAt (P j) (P l) q))
    (he : f =ᶠ[𝓝 q] fun y ↦ u y * ∏ j, P j y ^ m j) :
    localDivisorAt n f q = ∑ j, m j • Finsupp.single
      (Associates.mk (productAnalyticGermOf (fun y ↦ P j (q + y))
        (gaga21_g2_translate_analytic (hP j).1))) 1 := by
  have hft := gaga21_g2_translate_analytic hf
  simp only [localDivisorAt, hft, ↓reduceDIte]
  apply spec_localDivisor_decomposition hft (gaga21_g2_translate_analytic hu)
    (by simpa only [add_zero] using hu0)
    (fun j ↦ ⟨gaga21_g2_translate_analytic (hP j).1,
      gaga21_g2_translate_irreducible (hP j).2.1, (hP j).2.2⟩)
    (fun j l hjl ↦ gaga21_g2_translate_coprime (hc hjl))
  exact ((continuous_const.add continuous_id).tendsto' 0 q (add_zero q)).eventually he

theorem gaga21_restriction_multiplicity_aux {n : ℕ} {ι : Type} {U : Set ((Fin n → ℂ) × ℂ)}
    {V : ι → Set ((Fin n → ℂ) × ℂ)} {f : ι → (Fin n → ℂ) × ℂ → ℂ}
    (hD : IsLocalDivisorData U V f) (i : ι) (q : (Fin n → ℂ) × ℂ) (hq : q ∈ V i)
    (h : (Fin n → ℂ) × ℂ → ℂ)
    (hh : AnalyticAt ℂ (fun y ↦ h (q + y)) 0) (hi : IsIrreducibleAt h q) :
    gaga21_restrictMultiplicity (gaga21_gluedDivisor V f) q h =
      localDivisorAt n (f i) q (Associates.mk (productAnalyticGermOf (fun y ↦ h (q + y)) hh)) := by
  classical
  have hf := hD.2.2.1 i q hq
  have hhq : AnalyticAt ℂ h q := by
    convert hh.comp_of_eq (analyticAt_id.sub analyticAt_const) (sub_self q) using 1
    ext y
    simp [Function.comp_def, add_comm]
  by_cases hf0 : f i q = 0
  · obtain ⟨k, u, P, m, hu, hu0, hP, hc, he⟩ :=
      spec_exists_irreducible_decomposition_at hf hf0 (hD.2.2.2.1 i q hq)
    let K := fun j ↦ Associates.mk (productAnalyticGermOf (fun y ↦ P j (q + y))
      (gaga21_g2_translate_analytic (hP j).1))
    let H := Associates.mk (productAnalyticGermOf (fun y ↦ h (q + y)) hh)
    have hdiv := gaga21_g2_divisor_decomposition hf hu hu0 hP hc he
    change localDivisorAt n (f i) q = ∑ j, m j • Finsupp.single (K j) 1 at hdiv
    change gaga21_restrictMultiplicity (gaga21_gluedDivisor V f) q h =
      localDivisorAt n (f i) q H
    by_cases hm : ∃ j, K j = H
    · obtain ⟨j, hj⟩ := hm
      let a : gaga21_LocalFactorOccurrence V f :=
        { chart := i, point := q, mem_chart := hq, count := k, unit := u,
          factors := P, exponents := m, selected := j, unit_analytic := hu,
          unit_ne := hu0, factor_data := hP, coprime := hc, factorization := he,
          selected_zero := (hP j).2.1.1 }
      have ha : AreAssociatedAt h a.factor q :=
        (gaga21_g2_germ_class_iff hh (gaga21_g2_translate_analytic (hP j).1)).mp hj.symm
      have hleft := gaga21_g2_restrict_of_associated hD a h ha
      change gaga21_restrictMultiplicity (gaga21_gluedDivisor V f) q h = m j at hleft
      rw [hleft, hdiv]
      simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
      rw [← hj, Finset.sum_eq_single j]
      · simp only [↓reduceIte, mul_one]
      · intro l _ hlj
        have hne : K l ≠ K j :=
          gaga21_g2_class_ne_of_coprime (hP l).1 (hP j).1 (hP l).2.1 (hc hlj)
        simp only [hne, ↓reduceIte, mul_zero]
      · simp only [Finset.mem_univ, not_true_eq_false, false_implies]
    · have hright : localDivisorAt n (f i) q H = 0 := by
        rw [hdiv]
        simp only [Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
        apply Finset.sum_eq_zero
        intro j _
        have hj : K j ≠ H := fun hj ↦ hm ⟨j, hj⟩
        simp only [hj, ↓reduceIte, mul_zero]
      rw [hright]
      change (∑ᶠ C : gaga21_GlobalComponent V f,
        if (∀ᶠ y in 𝓝 q, h y = 0 → y ∈ gaga21_componentCarrier C)
        then (Quotient.out C).exponents (Quotient.out C).selected else 0) = 0
      apply finsum_eq_zero_of_forall_eq_zero
      intro C
      apply if_neg
      intro hC
      have hz : ∀ᶠ y in 𝓝 q, h y = 0 → ∃ j, P j y = 0 := by
        filter_upwards [hC, (hD.1 i).mem_nhds hq, he,
          hu.continuousAt.eventually_ne hu0] with y hy hVy hey huy hhy
        have hfy := (spec_mem_localDivisorSupport_iff hD i y hVy).mp
          (gaga21_g2_carrier_support C (hy hhy))
        have hp : ∏ j, P j y ^ m j = 0 :=
          (mul_eq_zero.mp (hey.symm.trans hfy)).resolve_left huy
        obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp hp
        exact ⟨j, (pow_eq_zero_iff (Nat.ne_of_gt (hP j).2.2)).mp hj⟩
      obtain ⟨j, hj⟩ := gaga21_g2_irreducible_in_finite_union hhq hi
        (fun j ↦ ⟨(hP j).1, (hP j).2.1⟩) hz
      exact hm ⟨j, ((gaga21_g2_germ_class_iff hh
        (gaga21_g2_translate_analytic (hP j).1)).mpr hj).symm⟩
  · rw [spec_localDivisorAt_eq_zero_of_ne_zero hf hf0, Finsupp.zero_apply]
    change (∑ᶠ C : gaga21_GlobalComponent V f,
      if (∀ᶠ y in 𝓝 q, h y = 0 → y ∈ gaga21_componentCarrier C)
      then (Quotient.out C).exponents (Quotient.out C).selected else 0) = 0
    apply finsum_eq_zero_of_forall_eq_zero
    intro C
    apply if_neg
    intro hC
    exact hf0 ((spec_mem_localDivisorSupport_iff hD i q hq).mp
      (gaga21_g2_carrier_support C (hC.self_of_nhds hi.1)))

private theorem gaga21_crossing_origin_not_regular :
    (0 : (Fin 1 → ℂ) × ℂ) ∉ gaga21_regularSupport
      (fun _ : Fin 2 ↦ (univ : Set ((Fin 1 → ℂ) × ℂ)))
      (fun _ y ↦ y.1 0 * y.2) := by
  rintro ⟨-, h, hh, hh0, hd, hzero⟩
  have hz := hzero
  simp only [localDivisorSupport, mem_iUnion, mem_setOf_eq, mem_univ, true_and,
    exists_const, mul_eq_zero] at hz
  let v₁ : (Fin 1 → ℂ) × ℂ := (fun _ ↦ 1, 0)
  let v₂ : (Fin 1 → ℂ) × ℂ := (0, 1)
  let e₁ : ℂ → (Fin 1 → ℂ) × ℂ := fun t ↦ t • v₁
  let e₂ : ℂ → (Fin 1 → ℂ) × ℂ := fun t ↦ t • v₂
  have he₁ : HasFDerivAt e₁ ((1 : ℂ →L[ℂ] ℂ).smulRight v₁) 0 := by fun_prop
  have he₂ : HasFDerivAt e₂ ((1 : ℂ →L[ℂ] ℂ).smulRight v₂) 0 := by fun_prop
  have hz₁ : (fun t ↦ h (e₁ t)) =ᶠ[𝓝 0] 0 := by
    filter_upwards [he₁.continuousAt.eventually (by simpa [e₁] using hz)] with t ht
    exact ht.mp (Or.inr (by simp [e₁, v₁]))
  have hz₂ : (fun t ↦ h (e₂ t)) =ᶠ[𝓝 0] 0 := by
    filter_upwards [he₂.continuousAt.eventually (by simpa [e₂] using hz)] with t ht
    exact ht.mp (Or.inl (by simp [e₂, v₂]))
  have hd₁ : (fderiv ℂ h 0).comp ((1 : ℂ →L[ℂ] ℂ).smulRight v₁) = 0 := by
    have hh' : HasFDerivAt h (fderiv ℂ h 0) (e₁ 0) := by
      simpa [e₁] using hh.differentiableAt.hasFDerivAt
    have hc := hh'.comp 0 he₁
    have hc' : HasFDerivAt (fun t ↦ h (e₁ t))
        ((fderiv ℂ h 0).comp ((1 : ℂ →L[ℂ] ℂ).smulRight v₁)) 0 := by
      change HasFDerivAt (h ∘ e₁) _ 0
      exact hc
    exact (hc'.congr_of_eventuallyEq hz₁.symm).unique
      (hasFDerivAt_const (x := 0) (c := (0 : ℂ)))
  have hd₂ : (fderiv ℂ h 0).comp ((1 : ℂ →L[ℂ] ℂ).smulRight v₂) = 0 := by
    have hh' : HasFDerivAt h (fderiv ℂ h 0) (e₂ 0) := by
      simpa [e₂] using hh.differentiableAt.hasFDerivAt
    have hc := hh'.comp 0 he₂
    have hc' : HasFDerivAt (fun t ↦ h (e₂ t))
        ((fderiv ℂ h 0).comp ((1 : ℂ →L[ℂ] ℂ).smulRight v₂)) 0 := by
      change HasFDerivAt (h ∘ e₂) _ 0
      exact hc
    exact (hc'.congr_of_eventuallyEq hz₂.symm).unique
      (hasFDerivAt_const (x := 0) (c := (0 : ℂ)))
  apply hd
  apply ContinuousLinearMap.ext
  rintro ⟨z, w⟩
  have h1 := DFunLike.congr_fun hd₁ (z 0)
  have h2 := DFunLike.congr_fun hd₂ w
  have hzfun : z = fun _ ↦ z 0 := by
    funext i
    fin_cases i
    rfl
  rw [hzfun] at h1
  rw [hzfun]
  have h1' : (fderiv ℂ h 0) ((fun _ ↦ z 0), 0) = 0 := by
    rw [← show (z 0 • v₁) = ((fun _ ↦ z 0), 0) by ext <;> simp [v₁]]
    simpa using h1
  have h2' : (fderiv ℂ h 0) (0, w) = 0 := by
    simpa [v₂] using h2
  rw [show ((fun _ ↦ z 0), w) = ((fun _ ↦ z 0), 0) + (0, w) by ext <;> simp,
    map_add, h1', h2', add_zero]
  rfl

private theorem gaga21_crossing_occurrence_associated
    (a : gaga21_LocalFactorOccurrence
      (fun _ : Fin 2 ↦ (univ : Set ((Fin 1 → ℂ) × ℂ)))
      (fun _ y ↦ y.1 0 * y.2)) :
    ∃ l : Fin 2, AreAssociatedAt a.factor (gaga17_crossingFactors l) a.point := by
  let s : (Fin 1 → ℂ) × ℂ → ℂ := fun y ↦
    a.unit y * (a.factors a.selected y ^ (a.exponents a.selected - 1)) *
      ∏ j ∈ Finset.univ.erase a.selected, a.factors j y ^ a.exponents j
  have hs : AnalyticAt ℂ s a.point := by
    have hp : AnalyticAt ℂ (fun y ↦
        ∏ j ∈ Finset.univ.erase a.selected, a.factors j y ^ a.exponents j) a.point :=
      by
        convert Finset.analyticAt_prod (Finset.univ.erase a.selected)
          (fun j _ ↦ (a.factor_data j).1.pow (a.exponents j)) using 1
        ext y
        simp
    exact (a.unit_analytic.mul
      ((a.factor_data a.selected).1.pow (a.exponents a.selected - 1))).mul hp
  have hdiv : (fun y ↦ y.1 0 * y.2) =ᶠ[nhds a.point] fun y ↦ a.factor y * s y := by
    filter_upwards [a.factorization] with y hy
    rw [hy]
    simp only [gaga21_LocalFactorOccurrence.factor, s]
    rw [Finset.prod_eq_mul_prod_diff_singleton a.selected _ (by simp)]
    rw [← mul_pow_sub_one (a.factor_data a.selected).2.2.ne']
    simp only [Finset.sdiff_singleton_eq_erase]
    ring
  have hcross : (fun y : (Fin 1 → ℂ) × ℂ ↦ y.1 0 * y.2) =ᶠ[nhds a.point]
      fun y ↦ (1 : ℂ) * ∏ l : Fin 2, gaga17_crossingFactors l y ^ (1 : ℕ) :=
    Eventually.of_forall fun y ↦ by simp [gaga17_crossingFactors, Fin.prod_univ_two]
  obtain ⟨l, c, hc, hl⟩ := gaga17_prime_divides_factor
    (a.factor_data a.selected).1 (a.factor_data a.selected).2.1 hs hdiv
    analyticAt_const one_ne_zero
    (fun l ↦ gaga17_crossing_data.2.1 l a.point (mem_univ _))
    hcross
  exact ⟨l, gaga17_associated_of_irreducible_divides
    (a.factor_data a.selected).1 (a.factor_data a.selected).2.1
    (gaga17_crossing_data.2.1 l a.point (mem_univ _))
    (by
      fin_cases l
      · have hp : a.point.1 = 0 := by
          funext i
          fin_cases i
          have hz := hl.self_of_nhds
          simp [gaga17_crossingFactors, a.selected_zero] at hz
          exact hz
        rw [show a.point = (0, a.point.2) by ext i <;> simp [hp]]
        exact gaga17_crossing_data.2.2.2.2 a.point.2
      · simpa [gaga17_crossingFactors] using
          (gaga17_axis_power_data 1 1 (by decide)).2 a.point
            (by
              have hz := hl.self_of_nhds
              simpa [gaga17_crossingFactors, a.selected_zero] using hz))
    hc hl⟩

private theorem gaga21_crossing_axis_regular (l : Fin 2) :
    let R : Set ((Fin 1 → ℂ) × ℂ) :=
      if l = 0 then {q | q.1 0 = 0 ∧ q ≠ 0} else {q | q.2 = 0 ∧ q ≠ 0}
    IsConnected R ∧ R ⊆ gaga21_regularSupport
      (fun _ : Fin 2 ↦ (univ : Set ((Fin 1 → ℂ) × ℂ)))
      (fun _ y ↦ y.1 0 * y.2) := by
  fin_cases l
  · dsimp
    let e : ℂ → (Fin 1 → ℂ) × ℂ := fun t ↦ (0, t)
    have he : Continuous e := continuous_const.prodMk continuous_id
    have hconn : IsConnected (e '' ({0}ᶜ : Set ℂ)) :=
      (isConnected_compl_singleton_of_one_lt_rank (by simp) 0).image e he.continuousOn
    have hR : {q : (Fin 1 → ℂ) × ℂ | q.1 0 = 0 ∧ q ≠ 0} =
        e '' ({0}ᶜ : Set ℂ) := by
      ext q
      constructor
      · rintro ⟨hq, hq0⟩
        refine ⟨q.2, ?_, ?_⟩
        · intro hq2
          have hq2' : q.2 = 0 := by simpa using hq2
          apply hq0
          ext i <;> simp [hq2']
          fin_cases i
          exact hq
        · ext i <;> simp [e]
          fin_cases i
          exact hq.symm
      · rintro ⟨t, ht, rfl⟩
        refine ⟨by simp [e], ?_⟩
        intro hzero
        have : t = 0 := by simpa [e] using congrArg Prod.snd hzero
        exact ht (by simpa [this])
    rw [hR]
    refine ⟨hconn, ?_⟩
    rintro q ⟨t, ht, rfl⟩
    have ht0 : t ≠ 0 := by simpa using ht
    refine ⟨⟨0, mem_univ _, by simp [e]⟩, (fun y ↦ y.1 0), ?_, by simp [e], ?_, ?_⟩
    · exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ)
        (i := (0 : Fin 1))).analyticAt _).comp analyticAt_fst
    · have hd : HasFDerivAt (fun y : (Fin 1 → ℂ) × ℂ ↦ y.1 0)
          ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ)
            (i := (0 : Fin 1))).comp
            (ContinuousLinearMap.fst ℂ (Fin 1 → ℂ) ℂ)) (e t) := by fun_prop
      rw [hd.fderiv]
      intro hz
      have := congrArg (fun L : ((Fin 1 → ℂ) × ℂ) →L[ℂ] ℂ ↦ L (fun _ ↦ 1, 0)) hz
      simpa using this
    · filter_upwards [(isOpen_ne.preimage continuous_snd).mem_nhds ht0] with y hy
      simp only [localDivisorSupport, mem_iUnion, mem_setOf_eq, mem_univ, true_and]
      constructor
      · rintro ⟨_, h⟩
        exact (mul_eq_zero.mp h).resolve_right hy
      · intro h
        exact ⟨0, by simp [h]⟩
  · dsimp
    let e : ℂ → (Fin 1 → ℂ) × ℂ := fun t ↦ (fun _ ↦ t, 0)
    have he : Continuous e := (continuous_pi fun _ ↦ continuous_id).prodMk continuous_const
    have hconn : IsConnected (e '' ({0}ᶜ : Set ℂ)) :=
      (isConnected_compl_singleton_of_one_lt_rank (by simp) 0).image e he.continuousOn
    have hR : {q : (Fin 1 → ℂ) × ℂ | q.2 = 0 ∧ q ≠ 0} =
        e '' ({0}ᶜ : Set ℂ) := by
      ext q
      constructor
      · rintro ⟨hq, hq0⟩
        refine ⟨q.1 0, ?_, ?_⟩
        · intro hq1
          apply hq0
          ext i <;> simp [hq]
          fin_cases i
          exact hq1
        · ext i <;> simp [e, hq]
          fin_cases i
          rfl
      · rintro ⟨t, ht, rfl⟩
        refine ⟨by simp [e], ?_⟩
        intro hzero
        have : t = 0 := by
          have := congrArg (fun q : (Fin 1 → ℂ) × ℂ ↦ q.1 0) hzero
          simpa [e] using this
        exact ht (by simpa [this])
    rw [hR]
    refine ⟨hconn, ?_⟩
    rintro q ⟨t, ht, rfl⟩
    have ht0 : t ≠ 0 := by simpa using ht
    refine ⟨⟨0, mem_univ _, by simp [e]⟩, (fun y ↦ y.2), analyticAt_snd, by simp [e], ?_, ?_⟩
    · have hd : HasFDerivAt (fun y : (Fin 1 → ℂ) × ℂ ↦ y.2)
          (ContinuousLinearMap.snd ℂ (Fin 1 → ℂ) ℂ) (e t) := by fun_prop
      rw [hd.fderiv]
      intro hz
      have := congrArg (fun L : ((Fin 1 → ℂ) × ℂ) →L[ℂ] ℂ ↦ L (0, 1)) hz
      simpa using this
    · have hfst : Continuous (fun y : (Fin 1 → ℂ) × ℂ ↦ y.1 0) := by fun_prop
      filter_upwards [(isOpen_ne.preimage hfst).mem_nhds ht0] with y hy
      simp only [localDivisorSupport, mem_iUnion, mem_setOf_eq, mem_univ, true_and]
      constructor
      · rintro ⟨_, h⟩
        exact (mul_eq_zero.mp h).resolve_left hy
      · intro h
        exact ⟨0, by simp [h]⟩

private theorem gaga21_crossing_continuation_of_associated
    (a : gaga21_LocalFactorOccurrence
      (fun _ : Fin 2 ↦ (univ : Set ((Fin 1 → ℂ) × ℂ)))
      (fun _ y ↦ y.1 0 * y.2)) (l : Fin 2)
    (ha : AreAssociatedAt a.factor (gaga17_crossingFactors l) a.point) :
    gaga21_continuation a (gaga21_crossingOccurrence l l) := by
  let R : Set ((Fin 1 → ℂ) × ℂ) :=
    if l = 0 then {q | q.1 0 = 0 ∧ q ≠ 0} else {q | q.2 = 0 ∧ q ≠ 0}
  refine ⟨R, (gaga21_crossing_axis_regular l).1,
    (gaga21_crossing_axis_regular l).2, ?_, ?_⟩
  · obtain ⟨u, hu, hu0, hau⟩ := ha
    filter_upwards [hau, hu.continuousAt.eventually_ne hu0] with y hy huy hzero hreg
    have hcoord : gaga17_crossingFactors l y = 0 := by
      rw [hy] at hzero
      exact (mul_eq_zero.mp hzero).resolve_left huy
    have hy0 : y ≠ 0 := by
      intro hyzero
      subst y
      exact gaga21_crossing_origin_not_regular hreg
    fin_cases l
    · exact ⟨by simpa [R, gaga17_crossingFactors] using hcoord, hy0⟩
    · exact ⟨by simpa [R, gaga17_crossingFactors] using hcoord, hy0⟩
  · exact Eventually.of_forall fun y hzero hreg ↦ by
      have hy0 : y ≠ 0 := by
        intro hyzero
        subst y
        exact gaga21_crossing_origin_not_regular hreg
      fin_cases l
      · exact ⟨by simpa [R, gaga21_LocalFactorOccurrence.factor,
            gaga21_crossingOccurrence, gaga17_crossingFactors] using hzero, hy0⟩
      · exact ⟨by simpa [R, gaga21_LocalFactorOccurrence.factor,
            gaga21_crossingOccurrence, gaga17_crossingFactors] using hzero, hy0⟩

theorem gaga21_crossing_classes_aux :
    Quotient.mk (gaga21_componentSetoid _ _) (gaga21_crossingOccurrence 0 0) ≠
      Quotient.mk (gaga21_componentSetoid _ _) (gaga21_crossingOccurrence 1 1) ∧
    ∀ C : gaga21_GlobalComponent
      (fun _ : Fin 2 ↦ (univ : Set ((Fin 1 → ℂ) × ℂ)))
      (fun _ y ↦ y.1 0 * y.2),
      C = Quotient.mk (gaga21_componentSetoid _ _) (gaga21_crossingOccurrence 0 0) ∨
      C = Quotient.mk (gaga21_componentSetoid _ _) (gaga21_crossingOccurrence 1 1) := by
  let V := fun _ : Fin 2 ↦ (univ : Set ((Fin 1 → ℂ) × ℂ))
  let f := fun _ : Fin 2 ↦ fun y : (Fin 1 → ℂ) × ℂ ↦ y.1 0 * y.2
  have hD : IsLocalDivisorData (univ : Set ((Fin 1 → ℂ) × ℂ)) V f := by
    refine ⟨fun _ ↦ isOpen_univ, iUnion_const _,
      fun _ ↦ gaga17_crossing_data.1.2.2.1 (),
      fun _ ↦ gaga17_crossing_data.1.2.2.2.1 (), ?_⟩
    intro i j q _
    exact ⟨fun _ ↦ 1, analyticAt_const, one_ne_zero,
      Eventually.of_forall fun _ ↦ by simp [f]⟩
  let b0 : gaga21_LocalFactorOccurrence V f := {
    chart := 0
    point := (0, 1)
    mem_chart := mem_univ _
    count := 1
    unit := fun y ↦ y.2
    factors := fun _ y ↦ y.1 0
    exponents := fun _ ↦ 1
    selected := 0
    unit_analytic := analyticAt_snd
    unit_ne := one_ne_zero
    factor_data := fun _ ↦ ⟨
      gaga17_crossing_data.2.1 0 _ (mem_univ _),
      gaga17_crossing_data.2.2.2.2 1, Nat.zero_lt_one⟩
    coprime := fun i j h ↦ (h (Subsingleton.elim i j)).elim
    factorization := Eventually.of_forall fun y ↦ by simp [V, f, mul_comm]
    selected_zero := rfl }
  let b1 : gaga21_LocalFactorOccurrence V f := {
    chart := 0
    point := (fun _ ↦ 1, 0)
    mem_chart := mem_univ _
    count := 1
    unit := fun y ↦ y.1 0
    factors := fun _ y ↦ y.2
    exponents := fun _ ↦ 1
    selected := 0
    unit_analytic := ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ)
      (i := (0 : Fin 1))).analyticAt _).comp analyticAt_fst
    unit_ne := one_ne_zero
    factor_data := fun _ ↦ ⟨analyticAt_snd,
      (gaga17_axis_power_data 1 1 (by decide)).2 _ rfl, Nat.zero_lt_one⟩
    coprime := fun i j h ↦ (h (Subsingleton.elim i j)).elim
    factorization := Eventually.of_forall fun y ↦ by simp [V, f]
    selected_zero := rfl }
  constructor
  · intro heq
    have hb0 : Quotient.mk (gaga21_componentSetoid V f) b0 =
        Quotient.mk (gaga21_componentSetoid V f) (gaga21_crossingOccurrence 0 0) := by
      apply gaga21_quotient_eq_of_continuation
      apply gaga21_crossing_continuation_of_associated b0 0
      exact ⟨fun _ ↦ 1, analyticAt_const, one_ne_zero,
        Eventually.of_forall fun _ ↦ by
          simp [b0, gaga21_LocalFactorOccurrence.factor, gaga17_crossingFactors]⟩
    have hb1 : Quotient.mk (gaga21_componentSetoid V f) b1 =
        Quotient.mk (gaga21_componentSetoid V f) (gaga21_crossingOccurrence 1 1) := by
      apply gaga21_quotient_eq_of_continuation
      apply gaga21_crossing_continuation_of_associated b1 1
      exact ⟨fun _ ↦ 1, analyticAt_const, one_ne_zero,
        Eventually.of_forall fun _ ↦ by
          simp [b1, gaga21_LocalFactorOccurrence.factor, gaga17_crossingFactors]⟩
    let C : gaga21_GlobalComponent V f :=
      Quotient.mk (gaga21_componentSetoid V f) (gaga21_crossingOccurrence 0 0)
    let S := gaga21_regularSupport V f ∩ gaga21_componentCarrier C
    have hconn : IsConnected S := (gaga21_carrier_regular_connected_aux hD C).1
    let A : Set ((Fin 1 → ℂ) × ℂ) := {q | q.1 0 = 0}
    let B : Set ((Fin 1 → ℂ) × ℂ) := {q | q.2 = 0}
    have hSA : ((0, 1) : (Fin 1 → ℂ) × ℂ) ∈ S ∩ A := by
      refine ⟨⟨(gaga21_crossing_axis_regular 0).2 ⟨rfl, by simp⟩, ?_⟩, rfl⟩
      exact ⟨b0, hb0, rfl⟩
    have hSB : (((fun _ ↦ 1), 0) : (Fin 1 → ℂ) × ℂ) ∈ S ∩ B := by
      refine ⟨⟨(gaga21_crossing_axis_regular 1).2 ⟨rfl, ?_⟩, ?_⟩, rfl⟩
      · intro h
        have := congrFun (congrArg Prod.fst h) 0
        simp at this
      exact ⟨b1, hb1.trans heq.symm, rfl⟩
    have hsub : S ⊆ A ∪ B := by
      rintro q ⟨hreg, -⟩
      rcases hreg.1 with ⟨i, -, hi⟩
      exact (mul_eq_zero.mp hi).imp (fun h ↦ h) (fun h ↦ h)
    have hinter : S ∩ (A ∩ B) = ∅ := by
      ext q
      constructor
      · rintro ⟨⟨hreg, -⟩, ha, hb⟩
        have hq : q = 0 := by
          apply Prod.ext
          · funext i
            fin_cases i
            exact ha
          · exact hb
        subst q
        exact (gaga21_crossing_origin_not_regular hreg).elim
      · simp
    rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hconn.isPreconnected)
        A B (isClosed_eq (by fun_prop) continuous_const)
        (isClosed_eq continuous_snd continuous_const) hsub hinter with h | h
    · have hz := h hSB.1
      exact (one_ne_zero : (1 : ℂ) ≠ 0) (by simpa [A] using hz)
    · have hw := h hSA.1
      exact (one_ne_zero : (1 : ℂ) ≠ 0) (by simpa [B] using hw)
  · intro C
    refine Quotient.inductionOn C fun a ↦ ?_
    obtain ⟨l, hl⟩ := gaga21_crossing_occurrence_associated a
    have hq := gaga21_quotient_eq_of_continuation
      (gaga21_crossing_continuation_of_associated a l hl)
    fin_cases l
    · exact Or.inl hq
    · exact Or.inr hq

theorem gaga21_axis_classes_aux (n : ℕ) :
    ∀ C : gaga21_GlobalComponent
      (fun _ : Unit ↦ (univ : Set ((Fin n → ℂ) × ℂ))) (fun _ y ↦ y.2),
      C = Quotient.mk (gaga21_componentSetoid _ _) (gaga21_axisOccurrence n 0 rfl) := by
  intro C
  refine Quotient.inductionOn C fun a ↦ Quotient.sound ?_
  apply Relation.EqvGen.rel
  let R : Set ((Fin n → ℂ) × ℂ) := {q | q.2 = 0}
  have hRconn : IsConnected R := by
    have hconn : IsConnected (range (fun x : Fin n → ℂ ↦ (x, (0 : ℂ)))) :=
      isConnected_range (continuous_id.prodMk continuous_const)
    rw [show R = range (fun x : Fin n → ℂ ↦ (x, 0)) by
      ext q
      constructor
      · intro hq
        change q.2 = 0 at hq
        exact ⟨q.1, Prod.ext rfl hq.symm⟩
      · rintro ⟨x, rfl⟩
        rfl]
    exact hconn
  have hRreg : R ⊆ gaga21_regularSupport
      (fun _ : Unit ↦ (univ : Set ((Fin n → ℂ) × ℂ))) (fun _ y ↦ y.2) := by
    intro q hq
    refine ⟨⟨(), mem_univ _, hq⟩, (fun y ↦ y.2), analyticAt_snd, hq, ?_, ?_⟩
    · have hd : HasFDerivAt (fun y : (Fin n → ℂ) × ℂ ↦ y.2)
          (ContinuousLinearMap.snd ℂ (Fin n → ℂ) ℂ) q := by fun_prop
      rw [hd.fderiv]
      intro hz
      have := congrArg (fun L : ((Fin n → ℂ) × ℂ) →L[ℂ] ℂ ↦ L (0, 1)) hz
      simpa using this
    · exact Eventually.of_forall fun y ↦ by
        simp only [localDivisorSupport, mem_iUnion, mem_setOf_eq, mem_univ, true_and]
        constructor
        · rintro ⟨_, hy⟩
          exact hy
        · intro hy
          exact ⟨(), hy⟩
  refine ⟨R, hRconn, hRreg, ?_, ?_⟩
  · filter_upwards [a.factorization] with y hy hzero _
    change y.2 = 0
    rw [hy]
    apply mul_eq_zero_of_right
    apply Finset.prod_eq_zero (Finset.mem_univ a.selected)
    change a.factors a.selected y = 0 at hzero
    rw [hzero]
    exact zero_pow (a.factor_data a.selected).2.2.ne'
  · exact Eventually.of_forall fun y hy _ ↦ hy

theorem gaga21_node_data_aux  :
    IsLocalDivisorData (univ : Set ((Fin 1 → ℂ) × ℂ))
      (fun _ : Unit ↦ univ) (fun _ ↦ gaga21_node) := by
  have hx : ∀ q : (Fin 1 → ℂ) × ℂ, AnalyticAt ℂ (fun y ↦ y.1 0) q := fun q ↦
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ ↦ ℂ) 0).analyticAt q.1).comp
      analyticAt_fst
  have han : AnalyticOnNhd ℂ gaga21_node univ := fun q _ ↦
    (analyticAt_snd.pow 2).sub (((hx q).pow 2).mul ((hx q).add analyticAt_const))
  refine ⟨fun _ ↦ isOpen_univ, iUnion_const _, fun _ ↦ han, ?_, ?_⟩
  · intro _ q _ hzero
    have hall := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ q) hzero
    have hone := hall (mem_univ (0, 1))
    norm_num [gaga21_node] at hone
  · intro _ _ q _
    exact ⟨fun _ ↦ 1, analyticAt_const, one_ne_zero,
      Eventually.of_forall fun _ ↦ by simp⟩

private theorem gaga21_node_parameter_domain_connected :
    IsConnected ({1, -1} : Set ℂ)ᶜ := by
  apply Set.Countable.isConnected_compl_of_one_lt_rank
  · rw [Complex.rank_real_complex]
    norm_num
  · exact Set.toFinite _ |>.countable

private def gaga21_nodeNormalization (t : ℂ) : (Fin 1 → ℂ) × ℂ :=
  (fun _ ↦ t ^ 2 - 1, t * (t ^ 2 - 1))

private theorem gaga21_node_support_iff (p : (Fin 1 → ℂ) × ℂ) :
    p ∈ localDivisorSupport (fun _ : Unit ↦ univ) (fun _ ↦ gaga21_node) ↔
      gaga21_node p = 0 := by
  exact spec_mem_localDivisorSupport_iff gaga21_node_data_aux () p (mem_univ _)

private theorem gaga21_nodeNormalization_zero (t : ℂ) :
    gaga21_node (gaga21_nodeNormalization t) = 0 := by
  simp only [gaga21_nodeNormalization, gaga21_node]
  ring

private theorem gaga21_node_zero_parametrized (p : (Fin 1 → ℂ) × ℂ)
    (hp : gaga21_node p = 0) (hp0 : p ≠ 0) :
    ∃ t ∈ ({1, -1} : Set ℂ)ᶜ, gaga21_nodeNormalization t = p := by
  have hx : p.1 0 ≠ 0 := by
    intro hx
    have hy : p.2 = 0 := by
      have : p.2 ^ 2 = 0 := by simpa [gaga21_node, hx] using hp
      simpa [pow_two] using (mul_self_eq_zero.mp (by simpa [pow_two] using this))
    apply hp0
    apply Prod.ext
    · funext i
      simp [hx, Fin.eq_zero i]
    · exact hy
  let t : ℂ := p.2 / p.1 0
  have ht_sq : t ^ 2 = p.1 0 + 1 := by
    dsimp [t]
    simp only [gaga21_node] at hp
    field_simp [hx]
    linear_combination hp
  have heq : gaga21_nodeNormalization t = p := by
    ext i
    · simp only [gaga21_nodeNormalization]
      rw [ht_sq]
      simp [Fin.eq_zero i]
    · simp only [gaga21_nodeNormalization]
      rw [ht_sq]
      dsimp [t]
      field_simp [hx]
      ring
  refine ⟨t, ?_, heq⟩
  simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
  constructor
  · intro ht
    apply hp0
    rw [← heq, ht]
    apply Prod.ext
    · funext i
      simp [gaga21_nodeNormalization]
    · simp [gaga21_nodeNormalization]
  · intro ht
    apply hp0
    rw [← heq, ht]
    apply Prod.ext
    · funext i
      simp [gaga21_nodeNormalization]
    · simp [gaga21_nodeNormalization]

private def gaga21_nodeCoordinates :
    ((Fin 1 → ℂ) × ℂ) ≃L[ℂ] (Fin 2 → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toEquiv := (Equiv.prodComm _ _).trans
        (Fin.snocEquiv (fun _ : Fin 2 ↦ ℂ))
      map_add' := by
        intro x y
        ext i
        fin_cases i <;> rfl
      map_smul' := by
        intro c x
        ext i
        fin_cases i <;> rfl }

private theorem gaga21_irreducible_comp_coordinates_iff
    (f : (Fin 2 → ℂ) → ℂ) :
    IsIrreducibleAt (fun z ↦ f (gaga21_nodeCoordinates z)) 0 ↔
      IsIrreducibleAt f 0 := by
  let L := gaga21_nodeCoordinates
  constructor
  · intro hf
    refine ⟨by simpa using hf.1, ?_⟩
    intro a b ha hb hab
    have ha' := ha.comp_of_eq (L.analyticAt 0) (by simp)
    have hb' := hb.comp_of_eq (L.analyticAt 0) (by simp)
    have hL : Tendsto L (𝓝 (0 : (Fin 1 → ℂ) × ℂ)) (𝓝 (0 : Fin 2 → ℂ)) := by
      rw [← map_zero L]
      exact L.continuous.continuousAt
    have hab' : (fun z ↦ f (L z)) =ᶠ[𝓝 0] fun z ↦ a (L z) * b (L z) :=
      hL.eventually hab |>.mono fun z hz ↦ by simpa using hz
    simpa [L] using hf.2 (fun z ↦ a (L z)) (fun z ↦ b (L z)) ha' hb' hab'
  · intro hf
    refine ⟨by simpa using hf.1, ?_⟩
    intro a b ha hb hab
    have ha' := ha.comp_of_eq (L.symm.analyticAt 0) (by simp)
    have hb' := hb.comp_of_eq (L.symm.analyticAt 0) (by simp)
    have hLi : Tendsto L.symm (𝓝 (0 : Fin 2 → ℂ))
        (𝓝 (0 : (Fin 1 → ℂ) × ℂ)) := by
      change ContinuousAt L.symm 0
      exact L.symm.continuous.continuousAt
    have hab' : f =ᶠ[𝓝 0] fun z ↦ a (L.symm z) * b (L.symm z) :=
      hLi.eventually hab |>.mono fun z hz ↦ by simpa [L] using hz
    exact hf.2 (fun z ↦ a (L.symm z)) (fun z ↦ b (L.symm z)) ha' hb' hab'

private theorem gaga21_node_two_factors :
    ∃ P : Fin 2 → ((Fin 1 → ℂ) × ℂ) → ℂ,
      (∀ j, AnalyticAt ℂ (P j) 0 ∧ IsIrreducibleAt (P j) 0 ∧ P j 0 = 0) ∧
      Pairwise (fun j k ↦ IsCoprimeAt (P j) (P k) 0) ∧
      gaga21_node =ᶠ[𝓝 0] fun z ↦ ∏ j, P j z := by
  let L := gaga21_nodeCoordinates
  obtain ⟨s, hs, hs0, -, hfac, hm, hp, -⟩ :=
    AnalyticDivisorAlgebraic18.gaga18_node_factorization
  let P : Fin 2 → ((Fin 1 → ℂ) × ℂ) → ℂ := fun j z ↦
    if j = 0 then (L z) 1 - (L z) 0 * s (L z)
    else (L z) 1 + (L z) 0 * s (L z)
  have hL0 : L (0 : (Fin 1 → ℂ) × ℂ) = 0 := map_zero L
  have hPa (j) : AnalyticAt ℂ (P j) 0 := by
    have h0 := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 0).analyticAt 0
    have h1 := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 1).analyticAt 0
    fin_cases j
    · change AnalyticAt ℂ ((fun z ↦ z 1 - z 0 * s z) ∘ L) 0
      exact (h1.sub (h0.mul hs)).comp_of_eq (L.analyticAt 0) hL0
    · change AnalyticAt ℂ ((fun z ↦ z 1 + z 0 * s z) ∘ L) 0
      exact (h1.add (h0.mul hs)).comp_of_eq (L.analyticAt 0) hL0
  have hPi (j) : IsIrreducibleAt (P j) 0 := by
    fin_cases j
    · simpa [P, hL0] using
        (gaga21_irreducible_comp_coordinates_iff
          (fun z ↦ z 1 - z 0 * s z)).2 hm
    · simpa [P, hL0] using
        (gaga21_irreducible_comp_coordinates_iff
          (fun z ↦ z 1 + z 0 * s z)).2 hp
  refine ⟨P, fun j ↦ ⟨hPa j, hPi j, ?_⟩, ?_, ?_⟩
  · fin_cases j <;> simp [P, hL0, hs0]
  · intro j k hjk
    let Dx : ((Fin 1 → ℂ) × ℂ) →L[ℂ] ℂ :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).comp
        (ContinuousLinearMap.fst ℂ (Fin 1 → ℂ) ℂ)
    let Dy : ((Fin 1 → ℂ) × ℂ) →L[ℂ] ℂ :=
      ContinuousLinearMap.snd ℂ (Fin 1 → ℂ) ℂ
    have hmD : HasFDerivAt (P 0) (Dy - Dx) 0 := by
      have h : HasFDerivAt (fun z : Fin 2 → ℂ ↦ z 1 - z 0 * s z)
          ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 1) -
            (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 0)) 0 := by
        have h0 := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 0).hasFDerivAt (x := 0)
        have h1 := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 1).hasFDerivAt (x := 0)
        have hsD := hs.differentiableAt.hasFDerivAt
        convert h1.sub (h0.mul hsD) using 1 <;> ext z <;> simp [hs0]
      have h' : HasFDerivAt (fun z : Fin 2 → ℂ ↦ z 1 - z 0 * s z)
          ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 1) -
            (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 0))
          (L 0) := by simpa only [hL0] using h
      have hc := h'.comp 0 L.hasFDerivAt
      convert hc using 1 <;> first | rfl | (ext z; simp [P, Dx, Dy, L,
        gaga21_nodeCoordinates, Fin.snoc_apply_zero])
    have hpD : HasFDerivAt (P 1) (Dy + Dx) 0 := by
      have h : HasFDerivAt (fun z : Fin 2 → ℂ ↦ z 1 + z 0 * s z)
          ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 1) +
            (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 0)) 0 := by
        have h0 := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 0).hasFDerivAt (x := 0)
        have h1 := (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 1).hasFDerivAt (x := 0)
        have hsD := hs.differentiableAt.hasFDerivAt
        convert h1.add (h0.mul hsD) using 1 <;> ext z <;> simp [hs0]
      have h' : HasFDerivAt (fun z : Fin 2 → ℂ ↦ z 1 + z 0 * s z)
          ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 1) +
            (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 2 ↦ ℂ) 0))
          (L 0) := by simpa only [hL0] using h
      have hc := h'.comp 0 L.hasFDerivAt
      convert hc using 1 <;> first | rfl | (ext z; simp [P, Dx, Dy, L,
        gaga21_nodeCoordinates, Fin.snoc_apply_zero])
    have hnot01 : ¬ AreAssociatedAt (P 0) (P 1) 0 := by
      rintro ⟨u, hu, hu0, hassoc⟩
      have hprod := hu.differentiableAt.hasFDerivAt.mul hpD
      have hd := hassoc.fderiv_eq (𝕜 := ℂ)
      rw [hmD.fderiv] at hd
      change HasFDerivAt (fun x ↦ u x * P 1 x) _ 0 at hprod
      rw [hprod.fderiv] at hd
      have he := congrArg (fun D : ((Fin 1 → ℂ) × ℂ) →L[ℂ] ℂ ↦ D (0, 1)) hd
      have he' := congrArg (fun D : ((Fin 1 → ℂ) × ℂ) →L[ℂ] ℂ ↦
        D (fun _ ↦ 1, 0)) hd
      have hpzero : P 1 0 = 0 := by simp [P, hL0, hs0]
      simp [hpzero, Dx, Dy] at he he'
      rw [← he] at he'
      norm_num at he'
    have hnot : ¬ AreAssociatedAt (P j) (P k) 0 := by
      fin_cases j <;> fin_cases k <;> try contradiction
      · exact hnot01
      · rintro ⟨u, hu, hu0, h⟩
        apply hnot01
        refine ⟨fun z ↦ (u z)⁻¹, hu.inv hu0, inv_ne_zero hu0, ?_⟩
        filter_upwards [h, hu.continuousAt.eventually_ne hu0] with z hz huz
        calc
          P 0 z = (u z)⁻¹ * (u z * P 0 z) := by
            rw [← mul_assoc, inv_mul_cancel₀ huz, one_mul]
          _ = (u z)⁻¹ * P 1 z := congrArg (fun w ↦ (u z)⁻¹ * w) hz.symm
    rintro ⟨q, r, t, hq, hr, ht, hq0, hj, hk⟩
    have hr0 : r 0 ≠ 0 := (hPi j).2 q r hq hr hj |>.resolve_left (fun h ↦ h hq0)
    have ht0 : t 0 ≠ 0 := (hPi k).2 q t hq ht hk |>.resolve_left (fun h ↦ h hq0)
    apply hnot
    refine ⟨fun z ↦ r z / t z, hr.div ht ht0, div_ne_zero hr0 ht0, ?_⟩
    filter_upwards [hj, hk, ht.continuousAt.eventually_ne ht0] with z hjz hkz htz
    rw [hjz, hkz]
    field_simp
  · have hT : Tendsto L (𝓝 (0 : (Fin 1 → ℂ) × ℂ)) (𝓝 (0 : Fin 2 → ℂ)) := by
      rw [← map_zero L]
      exact L.continuous.continuousAt
    filter_upwards [hT.eventually hfac] with z hz
    have h0 : (L z) 0 = z.1 0 := by rfl
    have h1 : (L z) 1 = z.2 := by rfl
    simpa [gaga21_node, AnalyticDivisorAlgebraic18.gaga18_node, P,
      Fin.prod_univ_two, h0, h1, add_comm] using hz

private theorem gaga21_node_nonzero_regular (p : (Fin 1 → ℂ) × ℂ)
    (hp : gaga21_node p = 0) (hp0 : p ≠ 0) :
    p ∈ gaga21_regularSupport (fun _ : Unit ↦ univ) (fun _ ↦ gaga21_node) := by
  have hx : AnalyticAt ℂ (fun y : (Fin 1 → ℂ) × ℂ ↦ y.1 0) p :=
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ ↦ ℂ) 0).analyticAt p.1).comp
      analyticAt_fst
  have han : AnalyticAt ℂ gaga21_node p :=
    (analyticAt_snd.pow 2).sub ((hx.pow 2).mul (hx.add analyticAt_const))
  refine ⟨(gaga21_node_support_iff p).2 hp, gaga21_node, han, hp, ?_, ?_⟩
  · intro hd
    have hxFD : HasFDerivAt (fun y : (Fin 1 → ℂ) × ℂ ↦ y.1 0)
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).comp
          (ContinuousLinearMap.fst ℂ (Fin 1 → ℂ) ℂ)) p :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0).hasFDerivAt).comp
        p (ContinuousLinearMap.fst ℂ (Fin 1 → ℂ) ℂ).hasFDerivAt
    have hyFD : HasFDerivAt (fun y : (Fin 1 → ℂ) × ℂ ↦ y.2)
        (ContinuousLinearMap.snd ℂ (Fin 1 → ℂ) ℂ) p :=
      (ContinuousLinearMap.snd ℂ (Fin 1 → ℂ) ℂ).hasFDerivAt
    have hFD := (hyFD.pow 2).sub
      ((hxFD.pow 2).mul (hxFD.add_const (1 : ℂ)))
    have hfun : ((fun x : (Fin 1 → ℂ) × ℂ ↦ x.2 ^ 2) -
        (fun x ↦ x.1 0 ^ 2) * fun x ↦ x.1 0 + 1) = gaga21_node := by
      funext z
      rfl
    rw [hfun] at hFD
    rw [hFD.fderiv] at hd
    have hdy := congrArg (fun D : ((Fin 1 → ℂ) × ℂ) →L[ℂ] ℂ ↦ D (0, 1)) hd
    have hdx := congrArg (fun D : ((Fin 1 → ℂ) × ℂ) →L[ℂ] ℂ ↦
      D (fun _ ↦ 1, 0)) hd
    simp at hdy hdx
    have hy : p.2 = 0 := by linear_combination hdy
    have hx0 : p.1 0 = 0 ∨ p.1 0 = -1 := by
      have hp' : p.1 0 ^ 2 * (p.1 0 + 1) = 0 := by
        simp only [gaga21_node] at hp
        rw [hy] at hp
        norm_num at hp ⊢
        exact hp
      rcases mul_eq_zero.mp hp' with h | h
      · left
        simpa using h
      · right
        linear_combination h
    rcases hx0 with hx0 | hx1
    · apply hp0
      apply Prod.ext
      · funext i
        simpa [Fin.eq_zero i] using hx0
      · exact hy
    · rw [hx1] at hdx
      norm_num at hdx
  · exact Eventually.of_forall fun y ↦ gaga21_node_support_iff y

private theorem gaga21_node_origin_not_regular :
    (0 : (Fin 1 → ℂ) × ℂ) ∉
      gaga21_regularSupport (fun _ : Unit ↦ univ) (fun _ ↦ gaga21_node) := by
  rintro ⟨-, h, hh, hh0, hder, hzero⟩
  have hν1 : gaga21_nodeNormalization (1 : ℂ) = 0 := by
    apply Prod.ext
    · funext i
      simp [gaga21_nodeNormalization]
    · simp [gaga21_nodeNormalization]
  have hνm1 : gaga21_nodeNormalization (-1 : ℂ) = 0 := by
    apply Prod.ext
    · funext i
      simp [gaga21_nodeNormalization]
    · simp [gaga21_nodeNormalization]
  have hνFD (t : ℂ) : HasFDerivAt gaga21_nodeNormalization
      ((ContinuousLinearMap.pi fun _ : Fin 1 ↦
          (2 * t) • ContinuousLinearMap.id ℂ ℂ).prod
        ((3 * t ^ 2 - 1) • ContinuousLinearMap.id ℂ ℂ)) t := by
    unfold gaga21_nodeNormalization
    apply HasFDerivAt.prodMk
    · rw [hasFDerivAt_pi]
      intro i
      simpa using ((hasFDerivAt_id t).pow 2).sub_const 1
    · convert (hasFDerivAt_id t).mul (((hasFDerivAt_id t).pow 2).sub_const 1) using 1
      · rfl
      · apply ContinuousLinearMap.ext
        intro z
        simp
        ring
  have hcomp (t : ℂ) (ht : gaga21_nodeNormalization t = 0) :
      (fun s ↦ h (gaga21_nodeNormalization s)) =ᶠ[𝓝 t] 0 := by
    have hT : Tendsto gaga21_nodeNormalization (𝓝 t) (𝓝 0) := by
      simpa only [ContinuousAt, ht] using (hνFD t).continuousAt
    filter_upwards [hT.eventually hzero] with s hs
    exact hs.mp (gaga21_node_support_iff _ |>.2 (gaga21_nodeNormalization_zero s))
  have hkill (t : ℂ) (ht : gaga21_nodeNormalization t = 0) :
      (fderiv ℂ h 0) (fun _ ↦ 2 * t, 3 * t ^ 2 - 1) = 0 := by
    have hh' : AnalyticAt ℂ h (gaga21_nodeNormalization t) := by simpa [ht] using hh
    have hc := hh'.differentiableAt.hasFDerivAt.comp t (hνFD t)
    have hz := (hcomp t ht).fderiv_eq (𝕜 := ℂ)
    change fderiv ℂ (h ∘ gaga21_nodeNormalization) t = _ at hz
    rw [hc.fderiv] at hz
    have hz' := congrArg (fun D : ℂ →L[ℂ] ℂ ↦ D 1) hz
    simpa [ht] using hz'
  have hp := hkill 1 hν1
  have hm := hkill (-1) hνm1
  have hx : (fderiv ℂ h 0) (fun _ ↦ 1, 0) = 0 := by
    have hs := congrArg (fun z : (Fin 1 → ℂ) × ℂ ↦ (fderiv ℂ h 0) z)
      (show (fun _ : Fin 1 ↦ 4, 0) =
          (fun _ ↦ 2 * (1 : ℂ), 3 * (1 : ℂ) ^ 2 - 1) -
            (fun _ ↦ 2 * (-1 : ℂ), 3 * (-1 : ℂ) ^ 2 - 1) by ext <;> norm_num)
    rw [map_sub, hp, hm, sub_zero] at hs
    have he : (fun _ : Fin 1 ↦ (4 : ℂ), 0) =
        (4 : ℂ) • (fun _ : Fin 1 ↦ (1 : ℂ), (0 : ℂ)) := by ext <;> norm_num
    rw [he, map_smul] at hs
    exact (smul_eq_zero.mp hs).resolve_left (by norm_num)
  have hy : (fderiv ℂ h 0) (0, 1) = 0 := by
    have hs := congrArg (fun z : (Fin 1 → ℂ) × ℂ ↦ (fderiv ℂ h 0) z)
      (show (0, (4 : ℂ)) =
          (fun _ ↦ 2 * (1 : ℂ), 3 * (1 : ℂ) ^ 2 - 1) +
            (fun _ ↦ 2 * (-1 : ℂ), 3 * (-1 : ℂ) ^ 2 - 1) by ext <;> norm_num)
    rw [map_add, hp, hm, add_zero] at hs
    have he : ((0 : Fin 1 → ℂ), (4 : ℂ)) =
        (4 : ℂ) • ((0 : Fin 1 → ℂ), (1 : ℂ)) := by ext <;> norm_num
    rw [he, map_smul] at hs
    exact (smul_eq_zero.mp hs).resolve_left (by norm_num)
  apply hder
  apply ContinuousLinearMap.ext
  intro z
  have hz : z = z.1 0 • (fun _ ↦ 1, 0) + z.2 • (0, 1) := by
    apply Prod.ext
    · funext i
      simp [Fin.eq_zero i]
    · simp
  rw [hz, map_add, map_smul, map_smul, hx, hy]
  simp

theorem gaga21_node_branches_aux  :
    ∃ a b : gaga21_LocalFactorOccurrence
      (fun _ : Unit ↦ (univ : Set ((Fin 1 → ℂ) × ℂ))) (fun _ ↦ gaga21_node),
      a.point = 0 ∧ b.point = 0 ∧ ¬ AreAssociatedAt a.factor b.factor 0 ∧
      (∀ c : gaga21_LocalFactorOccurrence
        (fun _ : Unit ↦ (univ : Set ((Fin 1 → ℂ) × ℂ))) (fun _ ↦ gaga21_node),
        c.point = 0 → AreAssociatedAt c.factor a.factor 0 ∨
          AreAssociatedAt c.factor b.factor 0) ∧
      ∀ C : gaga21_GlobalComponent
        (fun _ : Unit ↦ (univ : Set ((Fin 1 → ℂ) × ℂ))) (fun _ ↦ gaga21_node),
        C = Quotient.mk (gaga21_componentSetoid _ _) a := by
  classical
  obtain ⟨P, hP, hcop, hfac⟩ := gaga21_node_two_factors
  let occ : Fin 2 → gaga21_LocalFactorOccurrence
      (fun _ : Unit ↦ (univ : Set ((Fin 1 → ℂ) × ℂ))) (fun _ ↦ gaga21_node) := fun j ↦
    { chart := ()
      point := 0
      mem_chart := mem_univ _
      count := 2
      unit := fun _ ↦ 1
      factors := P
      exponents := fun _ ↦ 1
      selected := j
      unit_analytic := analyticAt_const
      unit_ne := one_ne_zero
      factor_data := fun l ↦ ⟨(hP l).1, (hP l).2.1, zero_lt_one⟩
      coprime := hcop
      factorization := hfac.mono fun z hz ↦ by simpa using hz
      selected_zero := (hP j).2.2 }
  have hclass (c : gaga21_LocalFactorOccurrence
      (fun _ : Unit ↦ (univ : Set ((Fin 1 → ℂ) × ℂ))) (fun _ ↦ gaga21_node))
      (hc : c.point = 0) :
      AreAssociatedAt c.factor (occ 0).factor 0 ∨
        AreAssociatedAt c.factor (occ 1).factor 0 := by
    obtain ⟨e, he⟩ := spec_irreducible_decomposition_unique
      (u := fun _ ↦ 1) (v := c.unit) (P := P) (Q := c.factors)
      (m := fun _ ↦ 1) (r := c.exponents)
      analyticAt_const one_ne_zero (by simpa [hc] using c.unit_analytic)
      (by simpa [hc] using c.unit_ne)
      (fun j ↦ ⟨(hP j).1, (hP j).2.1, zero_lt_one⟩)
      (by simpa [hc] using c.factor_data) hcop (by simpa [hc] using c.coprime)
      (hfac.mono fun z hz ↦ by simpa using hz) (by simpa [hc] using c.factorization)
    let j : Fin 2 := e.symm c.selected
    have hj : e j = c.selected := e.apply_symm_apply c.selected
    have hassoc : AreAssociatedAt (occ j).factor c.factor 0 := by
      simpa [occ, gaga21_LocalFactorOccurrence.factor, hj] using (he j).1
    have hassoc' : AreAssociatedAt c.factor (occ j).factor 0 :=
      by
        obtain ⟨u, hu, hu0, heq⟩ := hassoc
        refine ⟨fun z ↦ (u z)⁻¹, hu.inv hu0, inv_ne_zero hu0, ?_⟩
        filter_upwards [heq, hu.continuousAt.eventually_ne hu0] with z hz huz
        rw [hz, ← mul_assoc, inv_mul_cancel₀ huz, one_mul]
    have hj_cases : j = 0 ∨ j = 1 := by omega
    rcases hj_cases with hj0 | hj1
    · rw [hj0] at hassoc'
      exact Or.inl hassoc'
    · rw [hj1] at hassoc'
      exact Or.inr hassoc'
  have hnormalization_continuous : Continuous gaga21_nodeNormalization := by
    unfold gaga21_nodeNormalization
    fun_prop
  let T : Set ℂ := ({1, -1} : Set ℂ)ᶜ
  let R : Set ((Fin 1 → ℂ) × ℂ) := gaga21_nodeNormalization '' T
  have hR_connected : IsConnected R := by
    exact gaga21_node_parameter_domain_connected.image gaga21_nodeNormalization
      hnormalization_continuous.continuousOn
  have hnormalization_ne_zero {t : ℂ} (ht : t ∈ T) :
      gaga21_nodeNormalization t ≠ 0 := by
    intro h0
    have hx := congrArg (fun z : (Fin 1 → ℂ) × ℂ ↦ z.1 0) h0
    simp only [gaga21_nodeNormalization, Prod.fst_zero, Pi.zero_apply] at hx
    have hprod : (t - 1) * (t + 1) = 0 := by linear_combination hx
    rcases mul_eq_zero.mp hprod with h | h
    · apply ht
      simp only [T, mem_compl_iff, mem_insert_iff, mem_singleton_iff]
      exact Or.inl (sub_eq_zero.mp h)
    · apply ht
      simp only [T, mem_compl_iff, mem_insert_iff, mem_singleton_iff]
      exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hcontinuation (c d : gaga21_LocalFactorOccurrence
      (fun _ : Unit ↦ (univ : Set ((Fin 1 → ℂ) × ℂ))) (fun _ ↦ gaga21_node)) :
      gaga21_continuation c d := by
    refine ⟨R, hR_connected, ?_, ?_, ?_⟩
    · rintro p ⟨t, ht, rfl⟩
      exact gaga21_node_nonzero_regular _ (gaga21_nodeNormalization_zero t)
        (hnormalization_ne_zero ht)
    · exact Eventually.of_forall fun p _ hreg ↦ by
        have hp0 : p ≠ 0 := fun hp ↦ by
          subst p
          exact gaga21_node_origin_not_regular hreg
        obtain ⟨t, ht, rfl⟩ := gaga21_node_zero_parametrized p
          ((gaga21_node_support_iff p).mp hreg.1) hp0
        exact ⟨t, ht, rfl⟩
    · exact Eventually.of_forall fun p _ hreg ↦ by
        have hp0 : p ≠ 0 := fun hp ↦ by
          subst p
          exact gaga21_node_origin_not_regular hreg
        obtain ⟨t, ht, rfl⟩ := gaga21_node_zero_parametrized p
          ((gaga21_node_support_iff p).mp hreg.1) hp0
        exact ⟨t, ht, rfl⟩
  refine ⟨occ 0, occ 1, rfl, rfl, ?_, hclass, ?_⟩
  · intro hassoc
    obtain ⟨u, hu, hu0, huEq⟩ := hassoc
    apply (hcop (show (0 : Fin 2) ≠ 1 by decide))
    refine ⟨P 1, u, fun _ ↦ 1, (hP 1).1, hu, analyticAt_const,
      (hP 1).2.2, ?_, ?_⟩
    · simpa [occ, gaga21_LocalFactorOccurrence.factor, mul_comm] using huEq
    · exact Eventually.of_forall fun z ↦ by simp
  · intro C
    induction C using Quotient.inductionOn with
    | _ c =>
      apply Quotient.sound
      exact Relation.EqvGen.rel _ _ (hcontinuation c (occ 0))

end HodgeLean.Foundations.AnalyticDivisorAlgebraic21
