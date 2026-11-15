import HodgeLean.Foundations.AnalyticStratificationDefs
import HodgeLean.Foundations.AnalyticDivisorAlgebraic3

/-! Proof obligations for countable holomorphic parametrization. -/

noncomputable section
open Set Filter Topology
namespace HodgeLean.Foundations

private def astrat_wordDirs {n : ℕ} : (s : List (Fin n)) → Fin s.length → (Fin n → ℂ)
  | [], j => Fin.elim0 j
  | i :: s, j => Fin.cases (Pi.single i 1) (astrat_wordDirs s) j

private lemma astrat_wordDirs_eq {n : ℕ} (s : List (Fin n)) :
    astrat_wordDirs s = fun j ↦ Pi.single (s.get j) 1 := by
  induction s with
  | nil => funext j; exact Fin.elim0 j
  | cons i s ih =>
    funext j
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · rfl
    · simp [astrat_wordDirs, ih]

private lemma astrat_iterated_cast {n a b : ℕ} (f : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ)
    (h : a = b) (v : Fin b → (Fin n → ℂ)) :
    iteratedFDeriv ℂ a f z (fun j ↦ v (Fin.cast h j)) = iteratedFDeriv ℂ b f z v := by
  cases h
  rfl

private lemma astrat_partial_eq_iterated {n : ℕ} (f : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ)
    (s : List (Fin n)) (hf : AnalyticAt ℂ f z) :
    astrat_partial n f s z = iteratedFDeriv ℂ s.length f z (astrat_wordDirs s) := by
  induction s generalizing z with
  | nil => simp [astrat_partial, astrat_wordDirs, iteratedFDeriv_zero_apply]
  | cons i s ih =>
    rw [astrat_partial]
    have heq : EventuallyEq (nhds z) (astrat_partial n f s)
        (fun x ↦ iteratedFDeriv ℂ s.length f x (astrat_wordDirs s)) := by
      filter_upwards [hf.eventually_analyticAt] with x hx
      exact ih x hx
    change fderiv ℂ (astrat_partial n f s) z (Pi.single i 1) = _
    rw [heq.fderiv_eq]
    have ha : AnalyticOnNhd ℂ f ({z} : Set (Fin n → ℂ)) := by
      intro x hx
      simpa only [mem_singleton_iff] using hx ▸ hf
    have hd := ((ha.iteratedFDeriv s.length) z (mem_singleton z)).differentiableAt
    simp only [List.length_cons]
    rw [DifferentiableAt.iteratedFDeriv_succ_apply_left' hd]
    rfl

private lemma astrat_exists_iterated_ne_zero {n : ℕ} (f : (Fin n → ℂ) → ℂ)
    (z : Fin n → ℂ) (hf : AnalyticAt ℂ f z) (
      hne : ¬ EventuallyEq (nhds z) f 0) :
    ∃ k, iteratedFDeriv ℂ k f z ≠ 0 := by
  by_contra h
  push Not at h
  rcases hf with ⟨p, r, hp⟩
  apply hne
  filter_upwards [Metric.eball_mem_nhds z hp.r_pos] with x hx
  have hy : x - z ∈ Metric.eball (0 : Fin n → ℂ) r := by
    simpa [edist_eq_enorm_sub] using hx
  have hs := hp.hasSum_iteratedFDeriv hy
  have hzsum : HasSum (fun _ : ℕ ↦ (0 : ℂ)) 0 := hasSum_zero
  have hzsum' : HasSum
      (fun k ↦ (k.factorial : ℂ)⁻¹ • iteratedFDeriv ℂ k f z (fun _ ↦ x - z)) 0 := by
    simp [h]
  have heq := hs.unique hzsum'
  simpa using heq

private lemma astrat_exists_partial_ne_zero {n : ℕ} (f : (Fin n → ℂ) → ℂ)
    (z : Fin n → ℂ) (hf : AnalyticAt ℂ f z) (
      hne : ¬ EventuallyEq (nhds z) f 0) :
    ∃ s : List (Fin n), astrat_partial n f s z ≠ 0 := by
  obtain ⟨k, hk⟩ := astrat_exists_iterated_ne_zero f z hf hne
  have hb : ∃ v : Fin k → Fin n,
      iteratedFDeriv ℂ k f z (fun j ↦ Pi.single (v j) 1) ≠ 0 := by
    by_contra h
    push Not at h
    apply hk
    apply ContinuousMultilinearMap.ext
    intro x
    have hm : (iteratedFDeriv ℂ k f z).toMultilinearMap = 0 := by
      apply Module.Basis.ext_multilinear (fun _ ↦ Pi.basisFun ℂ (Fin n))
      intro v
      simpa using h v
    exact DFunLike.congr_fun hm x
  obtain ⟨v, hv⟩ := hb
  cases k with
  | zero =>
      refine ⟨[], ?_⟩
      rw [astrat_partial_eq_iterated f z [] hf]
      simpa [astrat_wordDirs] using hv
  | succ k =>
      refine ⟨List.ofFn v, ?_⟩
      rw [astrat_partial_eq_iterated f z (List.ofFn v) hf]
      intro hzero
      have hlen : (List.ofFn v).length = k + 1 := List.length_ofFn
      have hdirs : astrat_wordDirs (List.ofFn v) = fun j ↦
          Pi.single (v (Fin.cast hlen j)) 1 := by
        funext j
        rw [astrat_wordDirs_eq]
        change Pi.single ((List.ofFn v).get j) 1 = _
        congr 2
        apply Fin.ext
        exact congrArg Fin.val (List.get_ofFn v j)
      rw [hdirs] at hzero
      have hvcast : iteratedFDeriv ℂ (List.ofFn v).length f z
          (fun j ↦ Pi.single (v (Fin.cast hlen j)) 1) ≠ 0 := by
        intro hz'
        apply hv
        rw [← astrat_iterated_cast f z hlen (fun j ↦ Pi.single (v j) 1)]
        exact hz'
      exact hvcast hzero

private lemma astrat_partial_analyticAt {n : ℕ} (f : (Fin n → ℂ) → ℂ)
    (z : Fin n → ℂ) (s : List (Fin n)) (hf : AnalyticAt ℂ f z) :
    AnalyticAt ℂ (astrat_partial n f s) z := by
  induction s with
  | nil => exact hf
  | cons i s ih =>
      rw [astrat_partial]
      let e : ((Fin n → ℂ) →L[ℂ] ℂ) →L[ℂ] ℂ :=
        ContinuousLinearMap.apply ℂ ℂ (Pi.single i (1 : ℂ))
      exact (e.analyticAt _).comp ih.fderiv

/-- A nonzero holomorphic germ vanishing at the anchor has a derivative with a regular zero there.
Source: Gunning--Rossi, Chapter I, §A (Taylor expansion and uniqueness);
Chirka, *Complex Analytic Sets*, §2 (local equations). -/
theorem astrat_finite_derivative_aux (n : ℕ) (f : (Fin n → ℂ) → ℂ)
    (z : Fin n → ℂ) (hf : AnalyticAt ℂ f z) (hz : f z = 0)
    (hne : ¬ f =ᶠ[𝓝 z] 0) :
    ∃ s : List (Fin n), AnalyticAt ℂ (astrat_partial n f s) z ∧
      astrat_partial n f s z = 0 ∧ fderiv ℂ (astrat_partial n f s) z ≠ 0 := by
  classical
  have hex := astrat_exists_partial_ne_zero f z hf hne
  let P : ℕ → Prop := fun k ↦ ∃ s : List (Fin n),
    s.length = k ∧ astrat_partial n f s z ≠ 0
  have hP : ∃ k, P k := by
    obtain ⟨s, hs⟩ := hex
    exact ⟨s.length, s, rfl, hs⟩
  let m := Nat.find hP
  have hm : ∃ s : List (Fin n), s.length = m ∧ astrat_partial n f s z ≠ 0 :=
    Nat.find_spec hP
  obtain ⟨s, hslen, hsne⟩ := hm
  cases s with
  | nil =>
      simp only [List.length_nil] at hslen
      subst m
      exact (hsne hz).elim
  | cons i t =>
      refine ⟨t, astrat_partial_analyticAt f z t hf, ?_, ?_⟩
      · by_contra ht
        have hlt : t.length < m := by simp [← hslen]
        exact (not_le_of_gt hlt) (Nat.find_min' hP ⟨t, rfl, ht⟩)
      · intro hd
        apply hsne
        simp only [astrat_partial]
        rw [hd]
        rfl

/-- A regular hypersurface has an anchored parametrization on an open parameter domain.
Source: Gunning--Rossi, Chapter I, §B, Theorem 4; the kernel chart in
AnalyticDivisorAlgebraic3.spec_exists_analytic_graph, followed by finite-dimensional coordinates. -/
theorem astrat_regular_parametrization_aux (n : ℕ)
    (W : Set (Fin (n + 1) → ℂ)) (hW : IsOpen W)
    (f : (Fin (n + 1) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f W)
    (z : Fin (n + 1) → ℂ) (hz : z ∈ W) (hzero : f z = 0)
    (hreg : fderiv ℂ f z ≠ 0) :
    ∃ (U : Set (Fin n → ℂ)) (V : Set (Fin (n + 1) → ℂ))
      (g : (Fin n → ℂ) → (Fin (n + 1) → ℂ)),
      IsOpen U ∧ (0 : Fin n → ℂ) ∈ U ∧ IsOpen V ∧ z ∈ V ∧ V ⊆ W ∧
      AnalyticOnNhd ℂ g U ∧ g 0 = z ∧ g '' U = V ∩ {x | f x = 0} := by
  classical
  let E := Fin (n + 1) → ℂ
  let D := fderiv ℂ f z
  let K := LinearMap.ker (D : E →ₗ[ℂ] ℂ)
  obtain ⟨v, hv⟩ : ∃ v : E, D v ≠ 0 := by
    by_contra h
    apply hreg
    ext w
    simpa only [zero_apply] using not_exists_not.mp h w
  obtain ⟨q, hq⟩ :=
    AnalyticDivisorAlgebraic3.spec_exists_prodKerEquiv D hv
  obtain ⟨ψ, hψ, hψ0, hgraph⟩ :=
    AnalyticDivisorAlgebraic3.spec_exists_analytic_graph (hf z hz) hzero hv
  have hdimK : Module.finrank ℂ K = n := by
    have hd := Module.Dual.finrank_ker_add_one_of_ne_zero
      (show (D : E →ₗ[ℂ] ℂ) ≠ 0 from fun h => by
        apply hreg
        exact ContinuousLinearMap.coe_injective (by simpa [D] using h))
    have hdE : Module.finrank ℂ E = n + 1 := by
      simp [E]
    have hd' : Module.finrank ℂ K + 1 = n + 1 := by
      simpa [K, D, E, hdE] using hd
    omega
  let e : (Fin n → ℂ) ≃L[ℂ] K := ContinuousLinearEquiv.ofFinrankEq (by
    simpa [Module.finrank_pi] using hdimK.symm)
  let gK : K → E := fun t => z + (t : E) + ψ t • v
  let k : E → K := fun y => (q.symm (y - z)).1
  let g : (Fin n → ℂ) → E := fun t => gK (e t)
  have hgK0 : gK 0 = z := by simp [gK, hψ0]
  have hk0 : k z = 0 := by simp [k]
  have hkg : ∀ t, k (gK t) = t := by
    intro t
    have hrep : gK t - z = q (t, ψ t) := by
      rw [hq]
      dsimp [gK]
      abel
    change (q.symm (gK t - z)).1 = t
    rw [hrep, q.symm_apply_apply]
  have hgKa : AnalyticAt ℂ gK 0 :=
    (analyticAt_const.add (K.subtypeL.analyticAt 0)).add
      (hψ.smul analyticAt_const)
  have hka : AnalyticAt ℂ k z := by
    exact analyticAt_fst.comp
      ((q.symm.analyticAt _).comp (analyticAt_id.sub analyticAt_const))
  have hk : Continuous k :=
    continuous_fst.comp (q.symm.continuous.comp (continuous_id.sub continuous_const))
  have hgk : ∀ᶠ y in 𝓝 z, f y = 0 → gK (k y) = y := by
    have hqevent : Tendsto (fun y => q.symm (y - z)) (𝓝 z) (𝓝 0) := by
      have ht : ContinuousAt (fun y => q.symm (y - z)) z :=
        (q.symm.continuous.comp (continuous_id.sub continuous_const)).continuousAt
      simpa only [ContinuousAt, sub_self, map_zero] using ht
    filter_upwards [hqevent.eventually hgraph] with y hy
    intro hfy
    have hrep : z + ((q.symm (y - z)).1 : E) + (q.symm (y - z)).2 • v = y := by
      rw [add_assoc, ← hq, q.apply_symm_apply, add_sub_cancel]
    have hψy := hy.mp (hrep.symm ▸ hfy)
    change z + ((q.symm (y - z)).1 : E) + ψ ((q.symm (y - z)).1) • v = y
    rw [hψy, hrep]
  have hPg : ∀ᶠ t in 𝓝 (0 : K), f (gK t) = 0 := by
    have ht : Tendsto (fun t : K => (t, ψ t)) (𝓝 0) (𝓝 0) := by
      simpa only [hψ0, id_eq, Prod.mk_zero_zero] using
        (continuousAt_id.prodMk hψ.continuousAt).tendsto
    filter_upwards [ht.eventually hgraph] with t ht
    exact ht.mpr rfl
  obtain ⟨O, hOo, hzO, hOW, hrecover⟩ :
      ∃ O : Set E, IsOpen O ∧ z ∈ O ∧ O ⊆ W ∧ ∀ y ∈ O, f y = 0 → gK (k y) = y := by
    have hevent : ∀ᶠ y in 𝓝 z, y ∈ W ∧ (f y = 0 → gK (k y) = y) :=
      Filter.Eventually.and (hW.mem_nhds hz) hgk
    rw [eventually_iff_exists_mem] at hevent
    obtain ⟨O, hOz, hO⟩ := hevent
    obtain ⟨O', hO'sub, hO'o, hzO'⟩ := mem_nhds_iff.mp hOz
    exact ⟨O', hO'o, hzO', fun y hy => (hO _ (hO'sub hy)).1,
      fun y hy => (hO _ (hO'sub hy)).2⟩
  have hgood : ∀ᶠ t in 𝓝 (0 : K),
      AnalyticAt ℂ gK t ∧ gK t ∈ O ∧ f (gK t) = 0 := by
    filter_upwards [hgKa.eventually_analyticAt, hgKa.continuousAt.tendsto.eventually
      (hOo.mem_nhds (hgK0 ▸ hzO)), hPg] with t ha ho hp
    exact ⟨ha, ho, hp⟩
  obtain ⟨A, hAo, h0A, hAgood⟩ : ∃ A : Set K, IsOpen A ∧ 0 ∈ A ∧
      ∀ t ∈ A, AnalyticAt ℂ gK t ∧ gK t ∈ O ∧ f (gK t) = 0 := by
    rw [eventually_iff_exists_mem] at hgood
    obtain ⟨A, hA0, hA⟩ := hgood
    obtain ⟨A', hA'sub, hA'o, h0A'⟩ := mem_nhds_iff.mp hA0
    exact ⟨A', hA'o, h0A', fun t ht => hA _ (hA'sub ht)⟩
  let U : Set (Fin n → ℂ) := e ⁻¹' A
  let V : Set E := O ∩ k ⁻¹' A
  refine ⟨U, V, g, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hAo.preimage e.continuous
  · simpa [U] using h0A
  · exact hOo.inter (hAo.preimage hk)
  · exact ⟨hzO, by simpa [hk0] using h0A⟩
  · exact fun _ hx => hOW hx.1
  · intro t ht
    exact (hAgood (e t) ht).1.comp (e.analyticAt t)
  · simp [g, hgK0]
  · ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨(hAgood (e t) ht).2.1, by
        change k (gK (e t)) ∈ A
        rw [hkg]
        exact ht⟩,
        (hAgood (e t) ht).2.2⟩
    · rintro ⟨⟨hyO, hyA⟩, hfy⟩
      refine ⟨e.symm (k y), ?_, ?_⟩
      · simpa [U] using hyA
      · simp only [g, e.apply_symm_apply]
        exact hrecover y hyO hfy

private theorem astrat_partial_analyticOnNhd (n : ℕ)
    (W : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → ℂ)
    (hf : AnalyticOnNhd ℂ f W) (s : List (Fin n)) :
    AnalyticOnNhd ℂ (astrat_partial n f s) W := by
  induction s with
  | nil => exact hf
  | cons i s ih =>
      exact (ContinuousLinearMap.apply ℂ ℂ (Pi.single i 1)).comp_analyticOnNhd ih.fderiv

/-- A nonzero equation on a connected open domain has a countable hypersurface cover.
The chart images may contain points where the original equation is nonzero.
Source: Gunning--Rossi, Chapter I, §§A--B (derivatives and implicit functions);
second countability applied separately to the regular zero locus of each derivative. -/
theorem astrat_zero_set_cover_aux (n : ℕ)
    (W : Set (Fin (n + 1) → ℂ)) (hW : IsOpen W) (hc : IsPreconnected W)
    (f : (Fin (n + 1) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f W)
    (a : Fin (n + 1) → ℂ) (ha : a ∈ W) (hne : f a ≠ 0) :
    ∃ (U : ℕ → Set (Fin n → ℂ))
      (g : ℕ → (Fin n → ℂ) → (Fin (n + 1) → ℂ)),
      (∀ j, IsOpen (U j)) ∧ (∀ j, AnalyticOnNhd ℂ (g j) (U j)) ∧
      (∀ j, MapsTo (g j) (U j) W) ∧
      W ∩ {x | f x = 0} ⊆ ⋃ j, g j '' U j := by
  classical
  let R : List (Fin (n + 1)) → Set (Fin (n + 1) → ℂ) := fun s ↦
    W ∩ {z | astrat_partial (n + 1) f s z = 0 ∧
      fderiv ℂ (astrat_partial (n + 1) f s) z ≠ 0}
  have hchart : ∀ (s : List (Fin (n + 1))) (z : Fin (n + 1) → ℂ), z ∈ R s →
      ∃ (U : Set (Fin n → ℂ)) (V : Set (Fin (n + 1) → ℂ))
        (g : (Fin n → ℂ) → (Fin (n + 1) → ℂ)),
        IsOpen U ∧ (0 : Fin n → ℂ) ∈ U ∧ IsOpen V ∧ z ∈ V ∧ V ⊆ W ∧
        AnalyticOnNhd ℂ g U ∧ g 0 = z ∧
        g '' U = V ∩ {x | astrat_partial (n + 1) f s x = 0} := by
    intro s z hz
    exact astrat_regular_parametrization_aux n W hW _
      (astrat_partial_analyticOnNhd (n + 1) W f hf s) z hz.1 hz.2.1 hz.2.2
  choose Uc Vc gc hUc h0c hVc hzc hVWc hgc hg0c himgc using hchart
  let Vall : List (Fin (n + 1)) → (Fin (n + 1) → ℂ) → Set (Fin (n + 1) → ℂ) :=
    fun s z ↦ if hz : z ∈ R s then Vc s z hz else ∅
  have hsubcover : ∀ s : List (Fin (n + 1)),
      ∃ T : Set (Fin (n + 1) → ℂ), T ⊆ R s ∧ T.Countable ∧
        R s ⊆ ⋃ z ∈ T, Vall s z := by
    intro s
    apply TopologicalSpace.countable_cover_nhdsWithin
    intro z hz
    simp only [Vall, dif_pos hz]
    exact mem_nhdsWithin_of_mem_nhds ((hVc s z hz).mem_nhds (hzc s z hz))
  choose T hTR hTc hTcover using hsubcover
  let I := Σ s : List (Fin (n + 1)), {z // z ∈ T s}
  let Ui : I → Set (Fin n → ℂ) := fun q ↦ Uc q.1 q.2.1 (hTR q.1 q.2.2)
  let gi : I → (Fin n → ℂ) → (Fin (n + 1) → ℂ) := fun q ↦
    gc q.1 q.2.1 (hTR q.1 q.2.2)
  have hIcount : Countable I := by
    letI (s : List (Fin (n + 1))) : Countable {z // z ∈ T s} := (hTc s).to_subtype
    infer_instance
  letI : Countable I := hIcount
  by_cases hIn : Nonempty I
  · let e : ℕ → I := (exists_surjective_nat I).choose
    have he : Function.Surjective e := (exists_surjective_nat I).choose_spec
    refine ⟨fun j ↦ Ui (e j), fun j ↦ gi (e j), ?_, ?_, ?_, ?_⟩
    · intro j
      exact hUc _ _ _
    · intro j
      exact hgc _ _ _
    · intro j x hx
      have him : gi (e j) x ∈ gc (e j).1 (e j).2.1 (hTR _ (e j).2.2) ''
          Uc (e j).1 (e j).2.1 (hTR _ (e j).2.2) := ⟨x, hx, rfl⟩
      rw [himgc] at him
      exact hVWc _ _ _ him.1
    · rintro z ⟨hzW, hzf⟩
      have hng : ¬ Filter.EventuallyEq (nhds z) f 0 := by
        intro hlocal
        exact hne (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hzW hlocal ha)
      obtain ⟨s, hsana, hszero, hsreg⟩ :=
        astrat_finite_derivative_aux (n + 1) f z (hf z hzW) hzf hng
      have hzR : z ∈ R s := ⟨hzW, hszero, hsreg⟩
      obtain ⟨w, hwT, hzw⟩ := mem_iUnion₂.mp (hTcover s hzR)
      have hwR := hTR s hwT
      simp only [Vall, dif_pos hwR] at hzw
      let q : I := ⟨s, ⟨w, hwT⟩⟩
      obtain ⟨j, hj⟩ := he q
      apply mem_iUnion.mpr
      refine ⟨j, ?_⟩
      change z ∈ gi (e j) '' Ui (e j)
      rw [hj]
      change z ∈ gc s w (hTR s hwT) '' Uc s w (hTR s hwT)
      rw [himgc]
      exact ⟨hzw, hszero⟩
  · refine ⟨fun _ ↦ ∅, fun _ _ ↦ 0, fun _ ↦ isOpen_empty,
        fun _ ↦ analyticOnNhd_empty, fun _ ↦ mapsTo_empty _ _, ?_⟩
    rintro z ⟨hzW, hzf⟩
    have hng : ¬ Filter.EventuallyEq (nhds z) f 0 := by
      intro hlocal
      exact hne (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hzW hlocal ha)
    obtain ⟨s, hsana, hszero, hsreg⟩ :=
      astrat_finite_derivative_aux (n + 1) f z (hf z hzW) hzf hng
    have hzR : z ∈ R s := ⟨hzW, hszero, hsreg⟩
    obtain ⟨w, hwT, _⟩ := mem_iUnion₂.mp (hTcover s hzR)
    exact (hIn ⟨⟨s, ⟨w, hwT⟩⟩⟩).elim

/-- Local finite equations pull back along a holomorphic map on an open domain.
Source: Gunning--Rossi, Chapter II, local analytic sets and inverse images;
Chirka, *Complex Analytic Sets*, §2. -/
theorem astrat_pullback_equations_aux (n k : ℕ) (Z : Set (Fin n → ℂ))
    (hZ : ∀ z ∈ Z, ∃ (V : Set (Fin n → ℂ)), IsOpen V ∧ z ∈ V ∧
      ∃ (r : ℕ) (F : Fin r → (Fin n → ℂ) → ℂ),
        (∀ i, AnalyticOnNhd ℂ (F i) V) ∧
        ∀ x ∈ V, (x ∈ Z ↔ ∀ i, F i x = 0))
    (U : Set (Fin k → ℂ)) (hU : IsOpen U)
    (g : (Fin k → ℂ) → (Fin n → ℂ)) (hg : AnalyticOnNhd ℂ g U) :
    ∀ z ∈ U ∩ g ⁻¹' Z, ∃ (V : Set (Fin k → ℂ)), IsOpen V ∧ z ∈ V ∧
      ∃ (r : ℕ) (F : Fin r → (Fin k → ℂ) → ℂ),
        (∀ i, AnalyticOnNhd ℂ (F i) V) ∧
        ∀ x ∈ V, (x ∈ U ∩ g ⁻¹' Z ↔ ∀ i, F i x = 0) := by
  intro z hz
  obtain ⟨V₀, hV₀, hgzV₀, r, F, hF, hzero⟩ := hZ (g z) hz.2
  let V := U ∩ g ⁻¹' V₀
  refine ⟨V, hg.continuousOn.isOpen_inter_preimage hU hV₀, ⟨hz.1, hgzV₀⟩,
    r, fun i ↦ F i ∘ g, ?_, ?_⟩
  · intro i
    exact (hF i).comp (hg.mono inter_subset_left) fun _ hx ↦ hx.2
  · intro x hx
    constructor
    · intro hxZ i
      exact (hzero (g x) hx.2).mp hxZ.2 i
    · intro hFzero
      exact ⟨hx.1, (hzero (g x) hx.2).mpr fun i ↦ hFzero i⟩

private theorem astrat_boundary_equation (n : ℕ) (Z : Set (Fin n → ℂ))
    (hZ : ∀ z ∈ Z, ∃ (V : Set (Fin n → ℂ)), IsOpen V ∧ z ∈ V ∧
      ∃ (r : ℕ) (F : Fin r → (Fin n → ℂ) → ℂ),
        (∀ i, AnalyticOnNhd ℂ (F i) V) ∧
        ∀ x ∈ V, (x ∈ Z ↔ ∀ i, F i x = 0))
    (z : Fin n → ℂ) (hz : z ∈ Z) (hzint : z ∉ interior Z) :
    ∃ (W : Set (Fin n → ℂ)) (f : (Fin n → ℂ) → ℂ) (a : Fin n → ℂ),
      IsOpen W ∧ IsPreconnected W ∧ z ∈ W ∧ AnalyticOnNhd ℂ f W ∧
      a ∈ W ∧ f a ≠ 0 ∧ W ∩ Z ⊆ {x | f x = 0} := by
  classical
  obtain ⟨V, hVo, hzV, r, F, hFa, hdef⟩ := hZ z hz
  have hsome : ∃ i : Fin r, ¬ F i =ᶠ[nhds z] 0 := by
    by_contra h
    push_neg at h
    have hall : ∀ᶠ x in nhds z, ∀ i, F i x = 0 := Filter.eventually_all.2 h
    have hznhd : Z ∈ nhds z := by
      filter_upwards [hVo.mem_nhds hzV, hall] with x hxV hxF
      exact (hdef x hxV).2 hxF
    exact hzint (mem_interior_iff_mem_nhds.2 hznhd)
  obtain ⟨i, hi⟩ := hsome
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hVo.mem_nhds hzV)
  have ha : ∃ a ∈ Metric.ball z ε, F i a ≠ 0 := by
    by_contra h
    push_neg at h
    apply hi
    filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε)] with x hx
    exact h x hx
  obtain ⟨a, haW, hane⟩ := ha
  refine ⟨Metric.ball z ε, F i, a, Metric.isOpen_ball,
    (convex_ball z ε).isPreconnected, Metric.mem_ball_self hε, ?_, haW, hane, ?_⟩
  · exact (hFa i).mono hball
  · rintro x ⟨hxW, hxZ⟩
    exact (hdef x (hball hxW)).1 hxZ i

/-- Sets with local finite holomorphic equations at their own points have countable charts.
Only charts whose images lie in the interior may have full ambient parameter dimension.
Source: Gunning--Rossi, Chapter III (local parametrization); Chirka, §2;
dimension induction using derivative hypersurface covers and pullback equations. -/
theorem astrat_local_parametrization_aux (n : ℕ) (Z : Set (Fin n → ℂ))
    (hZ : ∀ z ∈ Z, ∃ (V : Set (Fin n → ℂ)), IsOpen V ∧ z ∈ V ∧
      ∃ (r : ℕ) (F : Fin r → (Fin n → ℂ) → ℂ),
        (∀ i, AnalyticOnNhd ℂ (F i) V) ∧
        ∀ x ∈ V, (x ∈ Z ↔ ∀ i, F i x = 0)) :
    ∃ (d : ℕ → ℕ) (U : ∀ j, Set (Fin (d j) → ℂ))
      (f : ∀ j, (Fin (d j) → ℂ) → (Fin n → ℂ)),
      (∀ j, d j ≤ n) ∧ (∀ j, IsOpen (U j)) ∧
      (∀ j, AnalyticOnNhd ℂ (f j) (U j)) ∧
      (∀ j, d j = n → f j '' U j ⊆ interior Z) ∧ Z = ⋃ j, f j '' U j := by
  classical
  induction n with
  | zero =>
      have hZo : IsOpen Z := isOpen_discrete Z
      refine ⟨fun _ ↦ 0, fun _ ↦ Z, fun _ ↦ id, ?_, ?_, ?_, ?_, ?_⟩
      · intro j
        exact le_rfl
      · intro j
        exact hZo
      · intro j
        exact analyticOnNhd_id
      · intro j hj
        simpa only [image_id, hZo.interior_eq] using (Subset.rfl : Z ⊆ Z)
      · simp only [image_id, iUnion_const]
  | succ m ih =>
      let B : Set (Fin (m + 1) → ℂ) := Z \ interior Z
      have hlocal : ∀ z : B,
          ∃ (W : Set (Fin (m + 1) → ℂ)) (q : (Fin (m + 1) → ℂ) → ℂ)
            (a : Fin (m + 1) → ℂ),
            IsOpen W ∧ IsPreconnected W ∧ (z : Fin (m + 1) → ℂ) ∈ W ∧
            AnalyticOnNhd ℂ q W ∧ a ∈ W ∧ q a ≠ 0 ∧
            W ∩ Z ⊆ {x | q x = 0} := by
        intro z
        exact astrat_boundary_equation (m + 1) Z hZ z z.2.1 z.2.2
      choose W q a hWo hWc hzW hqa haW hane hWZ using hlocal
      obtain ⟨S, hSc, hScover⟩ := TopologicalSpace.countable_cover_nhds
        (fun z : B ↦ preimage_coe_mem_nhds_subtype.2
          (mem_nhdsWithin_of_mem_nhds ((hWo z).mem_nhds (hzW z))))
      let I := {z : B // z ∈ S}
      letI : Countable I := hSc.to_subtype
      have hcover : ∀ t : I,
          ∃ (A : ℕ → Set (Fin m → ℂ))
            (g : ℕ → (Fin m → ℂ) → (Fin (m + 1) → ℂ)),
            (∀ j, IsOpen (A j)) ∧ (∀ j, AnalyticOnNhd ℂ (g j) (A j)) ∧
            (∀ j, MapsTo (g j) (A j) (W t.1)) ∧
            W t.1 ∩ {x | q t.1 x = 0} ⊆ ⋃ j, g j '' A j := by
        intro t
        exact astrat_zero_set_cover_aux m (W t.1) (hWo t.1) (hWc t.1)
          (q t.1) (hqa t.1) (a t.1) (haW t.1) (hane t.1)
      choose A g hAo hga hgm hgcov using hcover
      let P : I → ℕ → Set (Fin m → ℂ) := fun t j ↦ A t j ∩ g t j ⁻¹' Z
      have hPeq : ∀ (t : I) (j : ℕ) (x : Fin m → ℂ),
          x ∈ P t j ↔ x ∈ A t j ∩ g t j ⁻¹' Z := by
        intros
        rfl
      have hPlocal : ∀ (t : I) (j : ℕ) (x : Fin m → ℂ), x ∈ P t j →
          ∃ (V : Set (Fin m → ℂ)), IsOpen V ∧ x ∈ V ∧
            ∃ (r : ℕ) (F : Fin r → (Fin m → ℂ) → ℂ),
              (∀ i, AnalyticOnNhd ℂ (F i) V) ∧
              ∀ y ∈ V, (y ∈ P t j ↔ ∀ i, F i y = 0) := by
        intro t j
        simpa only [P] using astrat_pullback_equations_aux (m + 1) m Z hZ
          (A t j) (hAo t j) (g t j) (hga t j)
      have hrec : ∀ (t : I) (j : ℕ),
          ∃ (d : ℕ → ℕ) (U : ∀ l, Set (Fin (d l) → ℂ))
            (f : ∀ l, (Fin (d l) → ℂ) → (Fin m → ℂ)),
            (∀ l, d l ≤ m) ∧ (∀ l, IsOpen (U l)) ∧
            (∀ l, AnalyticOnNhd ℂ (f l) (U l)) ∧
            (∀ l, d l = m → f l '' U l ⊆ interior (P t j)) ∧
            P t j = ⋃ l, f l '' U l := by
        intro t j
        exact ih (P t j) (hPlocal t j)
      choose d' U' f' hd' hU' hf' hfull' hEq' using hrec
      let K := Unit ⊕ (I × ℕ × ℕ)
      let e : ℕ → K := (exists_surjective_nat K).choose
      have he : Function.Surjective e := (exists_surjective_nat K).choose_spec
      let dk : K → ℕ := fun k ↦ match k with
        | Sum.inl _ => m + 1
        | Sum.inr t => d' t.1 t.2.1 t.2.2
      let Uk : ∀ k : K, Set (Fin (dk k) → ℂ) := fun k ↦ match k with
        | Sum.inl _ => interior Z
        | Sum.inr t => U' t.1 t.2.1 t.2.2
      let fk : ∀ k : K, (Fin (dk k) → ℂ) → (Fin (m + 1) → ℂ) := fun k ↦
        match k with
        | Sum.inl _ => id
        | Sum.inr t => g t.1 t.2.1 ∘ f' t.1 t.2.1 t.2.2
      refine ⟨fun j ↦ dk (e j), fun j ↦ Uk (e j), fun j ↦ fk (e j), ?_, ?_, ?_, ?_, ?_⟩
      · intro j
        change dk (e j) ≤ m + 1
        rcases hje : e j with _ | t
        · exact le_rfl
        · simp only [dk]
          exact (hd' t.1 t.2.1 t.2.2).trans (Nat.le_succ m)
      · intro j
        change IsOpen (Uk (e j))
        rcases hje : e j with _ | t
        · simpa only [Uk, dk] using isOpen_interior (s := Z)
        · simpa only [Uk, dk] using hU' t.1 t.2.1 t.2.2
      · intro j
        change AnalyticOnNhd ℂ (fk (e j)) (Uk (e j))
        rcases hje : e j with _ | t
        · simp only [fk, Uk, dk]
          change AnalyticOnNhd ℂ (fun x : Fin (m + 1) → ℂ ↦ x) (interior Z)
          exact analyticOnNhd_id
        · simp only [fk, Uk, dk]
          apply (hga t.1 t.2.1).comp (hf' t.1 t.2.1 t.2.2)
          intro x hx
          have hxP : f' t.1 t.2.1 t.2.2 x ∈ P t.1 t.2.1 := by
            rw [hEq' t.1 t.2.1]
            exact mem_iUnion.2 ⟨t.2.2, ⟨x, hx, rfl⟩⟩
          exact hxP.1
      · intro j hj
        rcases hje : e j with _ | t
        · change fk (e j) '' Uk (e j) ⊆ interior Z
          rw [hje]
          simpa only [fk, Uk, dk, image_id] using
            (Subset.rfl : interior Z ⊆ interior Z)
        · exfalso
          have hle := hd' t.1 t.2.1 t.2.2
          simp only [dk, hje] at hj
          omega
      · apply Set.Subset.antisymm
        · intro z hz
          by_cases hzint : z ∈ interior Z
          · obtain ⟨j, hj⟩ := he (Sum.inl ())
            apply mem_iUnion.2
            refine ⟨j, ?_⟩
            change z ∈ fk (e j) '' Uk (e j)
            rw [hj]
            exact ⟨z, hzint, rfl⟩
          · let zb : B := ⟨z, hz, hzint⟩
            have hzbU : zb ∈ ⋃ x ∈ S, ((↑) : B → (Fin (m + 1) → ℂ)) ⁻¹' W x := by
              rw [hScover]
              exact mem_univ zb
            obtain ⟨x, hxS, hzx⟩ := mem_iUnion₂.mp hzbU
            let t : I := ⟨x, hxS⟩
            have hzzero : z ∈ W t.1 ∩ {y | q t.1 y = 0} := by
              refine ⟨hzx, ?_⟩
              exact hWZ t.1 ⟨hzx, hz⟩
            obtain ⟨j, y, hyA, hyz⟩ := mem_iUnion.mp (hgcov t hzzero)
            have hyP : y ∈ P t j := ⟨hyA, by
              change g t j y ∈ Z
              rw [hyz]
              exact hz⟩
            rw [hEq' t j] at hyP
            obtain ⟨l, u, huU, hul⟩ := mem_iUnion.mp hyP
            obtain ⟨k, hk⟩ := he (Sum.inr (t, j, l))
            apply mem_iUnion.2
            refine ⟨k, ?_⟩
            change z ∈ fk (e k) '' Uk (e k)
            rw [hk]
            exact ⟨u, huU, by simp only [fk, Function.comp_apply, hul, hyz]⟩
        · intro z hz
          obtain ⟨j, hzj⟩ := mem_iUnion.mp hz
          rcases hje : e j with _ | t
          · change z ∈ fk (e j) '' Uk (e j) at hzj
            rw [hje] at hzj
            apply interior_subset
            simpa only [fk, Uk, dk, image_id] using hzj
          · change z ∈ fk (e j) '' Uk (e j) at hzj
            rw [hje] at hzj
            obtain ⟨u, huU, rfl⟩ := hzj
            have huP : f' t.1 t.2.1 t.2.2 u ∈ P t.1 t.2.1 := by
              rw [hEq' t.1 t.2.1]
              exact mem_iUnion.2 ⟨t.2.2, ⟨u, huU, rfl⟩⟩
            exact huP.2

/-- Countably many holomorphic images of strictly smaller dimension equal a proper analytic set.
Source: Gunning--Rossi, Chapter III, regular loci and stratification by complex dimension;
Chirka, *Complex Analytic Sets*, §2. -/
theorem astrat_analytic_stratification_aux (n : ℕ) (hn : 0 < n)
    (Z : Set (Fin n → ℂ)) (hZ : IsClosedAnalytic (Fin n → ℂ) Z) (hp : Z ≠ univ) :
    ∃ (d : ℕ → ℕ) (U : ∀ j, Set (Fin (d j) → ℂ))
      (f : ∀ j, (Fin (d j) → ℂ) → (Fin n → ℂ)),
      (∀ j, d j < n) ∧ (∀ j, IsOpen (U j)) ∧
      (∀ j, DifferentiableOn ℂ (f j) (U j)) ∧ Z = ⋃ j, f j '' U j := by
  have hinterior : interior Z = ∅ := by
    ext z
    simp only [mem_interior_iff_mem_nhds, mem_empty_iff_false, iff_false]
    intro hz
    exact hp (hZ.eq_univ_of_nonempty_interior ⟨z, mem_interior_iff_mem_nhds.mpr hz⟩)
  have hlocal : ∀ z ∈ Z, ∃ (V : Set (Fin n → ℂ)), IsOpen V ∧ z ∈ V ∧
      ∃ (r : ℕ) (F : Fin r → (Fin n → ℂ) → ℂ),
        (∀ i, AnalyticOnNhd ℂ (F i) V) ∧
        ∀ x ∈ V, (x ∈ Z ↔ ∀ i, F i x = 0) := by
    intro z hz
    obtain ⟨V, hVo, hzV, hVt, r, F, hF, hzero⟩ := hZ.2 z hz
    refine ⟨V, hVo, ?_, r, F, hF, ?_⟩
    · simpa using hzV
    · intro x hx
      simpa using hzero x hx
  obtain ⟨d, U, f, hd, hU, hf, hfull, hcover⟩ :=
    astrat_local_parametrization_aux n Z hlocal
  have hcharts : ∀ j, ∃ (k : ℕ), k < n ∧
      ∃ (V : Set (Fin k → ℂ)) (g : (Fin k → ℂ) → (Fin n → ℂ)),
        IsOpen V ∧ DifferentiableOn ℂ g V ∧ f j '' U j = g '' V := by
    intro j
    by_cases h : d j < n
    · exact ⟨d j, h, U j, f j, hU j, (hf j).differentiableOn, rfl⟩
    · have heq : d j = n := Nat.le_antisymm (hd j) (Nat.le_of_not_gt h)
      have himage : f j '' U j = ∅ := by
        rw [← subset_empty_iff, ← hinterior]
        exact hfull j heq
      refine ⟨0, hn, ∅, fun _ => 0, isOpen_empty, ?_, ?_⟩
      · intro x hx
        exact False.elim (by simpa using hx)
      · simpa [himage]
  choose d' hd' U' f' hU' hf' himage using hcharts
  refine ⟨d', U', f', hd', hU', hf', ?_⟩
  rw [hcover]
  apply iUnion_congr
  exact himage

end HodgeLean.Foundations
