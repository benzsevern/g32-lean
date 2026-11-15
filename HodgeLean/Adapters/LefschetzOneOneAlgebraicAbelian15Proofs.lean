import HodgeLean.Foundations.AnalyticDivisorAlgebraic18
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.Complemented
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian12Proofs
import HodgeLean.Foundations.AnalyticStratification

/-! # Codimension-two analytic cover primitives

Implications from reduced analytic equations and from local biholomorphisms.
These interfaces separate immersion charts, the second dimension drop, and
countable assembly. The Boundary modules supply the algebraic coheight transfer.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
open HodgeLean.Foundations
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic11
namespace HodgeLean.Adapters

/-- A regular hypersurface has an anchored chart with injective derivative.
Source: Gunning–Rossi, Chapter I.B; the graph and left inverse in
`astrat_regular_parametrization_aux`. -/
theorem bh15_regular_immersion_chart_aux (n : ℕ)
    (W : Set (Fin (n + 1) → ℂ)) (hW : IsOpen W)
    (f : (Fin (n + 1) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f W)
    (z : Fin (n + 1) → ℂ) (hz : z ∈ W) (hzero : f z = 0)
    (hreg : fderiv ℂ f z ≠ 0) :
    ∃ (U : Set (Fin n → ℂ)) (V : Set (Fin (n + 1) → ℂ))
      (g : (Fin n → ℂ) → (Fin (n + 1) → ℂ)),
      IsOpen U ∧ (0 : Fin n → ℂ) ∈ U ∧ IsOpen V ∧ z ∈ V ∧ V ⊆ W ∧
      AnalyticOnNhd ℂ g U ∧ (∀ t ∈ U, Function.Injective (fderiv ℂ g t)) ∧
      g 0 = z ∧ g '' U = V ∩ {x | f x = 0} := by
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
  refine ⟨U, V, g, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hAo.preimage e.continuous
  · simpa [U] using h0A
  · exact hOo.inter (hAo.preimage hk)
  · exact ⟨hzO, by simpa [hk0] using h0A⟩
  · exact fun _ hx => hOW hx.1
  · intro t ht
    exact (hAgood (e t) ht).1.comp (e.analyticAt t)
  · intro t ht
    have hgAt : DifferentiableAt ℂ g t :=
      ((hAgood (e t) ht).1.comp (e.analyticAt t)).differentiableAt
    have hkAt : DifferentiableAt ℂ k (g t) := by
      exact (analyticAt_fst.comp
        ((q.symm.analyticAt _).comp (analyticAt_id.sub analyticAt_const))).differentiableAt
    have hcomp := fderiv_comp t hkAt hgAt
    have heq : k ∘ g = e := by
      funext s
      exact hkg (e s)
    have hleft : (fderiv ℂ k (g t)).comp (fderiv ℂ g t) = e := by
      rw [← hcomp, heq]
      exact e.fderiv
    intro x y hxy
    apply e.injective
    change (e : (Fin n → ℂ) →L[ℂ] K) x = (e : (Fin n → ℂ) →L[ℂ] K) y
    rw [← hleft, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hxy]
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

/-- A proper equation has a countable covering by immersed hypersurface charts.
The images can contain points outside the zero set.
Source: `astrat_finite_derivative`, `bh15_regular_immersion_chart`, and the
countable extraction in `astrat_zero_set_cover_aux`. -/
theorem bh15_zero_set_immersion_cover_aux (n : ℕ)
    (W : Set (Fin (n + 1) → ℂ)) (hW : IsOpen W) (hc : IsPreconnected W)
    (f : (Fin (n + 1) → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f W)
    (a : Fin (n + 1) → ℂ) (ha : a ∈ W) (hne : f a ≠ 0) :
    ∃ (U : ℕ → Set (Fin n → ℂ))
      (g : ℕ → (Fin n → ℂ) → (Fin (n + 1) → ℂ)),
      (∀ j, IsOpen (U j)) ∧ (∀ j, AnalyticOnNhd ℂ (g j) (U j)) ∧
      (∀ j t, t ∈ U j → Function.Injective (fderiv ℂ (g j) t)) ∧
      (∀ j, MapsTo (g j) (U j) W) ∧
      W ∩ {x | f x = 0} ⊆ ⋃ j, g j '' U j := by
  classical
  let R : List (Fin (n + 1)) → Set (Fin (n + 1) → ℂ) := fun s ↦
    W ∩ {z | astrat_partial (n + 1) f s z = 0 ∧
      fderiv ℂ (astrat_partial (n + 1) f s) z ≠ 0}
  have hpartial : ∀ s : List (Fin (n + 1)),
      AnalyticOnNhd ℂ (astrat_partial (n + 1) f s) W := by
    intro s
    induction s with
    | nil => exact hf
    | cons i s ih =>
        exact (ContinuousLinearMap.apply ℂ ℂ (Pi.single i 1)).comp_analyticOnNhd ih.fderiv
  have hchart : ∀ (s : List (Fin (n + 1))) (z : Fin (n + 1) → ℂ), z ∈ R s →
      ∃ (U : Set (Fin n → ℂ)) (V : Set (Fin (n + 1) → ℂ))
        (g : (Fin n → ℂ) → (Fin (n + 1) → ℂ)),
        IsOpen U ∧ (0 : Fin n → ℂ) ∈ U ∧ IsOpen V ∧ z ∈ V ∧ V ⊆ W ∧
        AnalyticOnNhd ℂ g U ∧ (∀ t ∈ U, Function.Injective (fderiv ℂ g t)) ∧
        g 0 = z ∧ g '' U = V ∩ {x | astrat_partial (n + 1) f s x = 0} := by
    intro s z hz
    exact bh15_regular_immersion_chart_aux n W hW _
      (hpartial s) z hz.1 hz.2.1 hz.2.2
  choose Uc Vc gc hUc h0c hVc hzc hVWc hgc hinjc hg0c himgc using hchart
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
    refine ⟨fun j ↦ Ui (e j), fun j ↦ gi (e j), ?_, ?_, ?_, ?_, ?_⟩
    · intro j
      exact hUc _ _ _
    · intro j
      exact hgc _ _ _
    · intro j t ht
      exact hinjc _ _ _ t ht
    · intro j x hx
      have him : gi (e j) x ∈ gc (e j).1 (e j).2.1 (hTR _ (e j).2.2) ''
          Uc (e j).1 (e j).2.1 (hTR _ (e j).2.2) := ⟨x, hx, rfl⟩
      rw [himgc] at him
      exact hVWc _ _ _ him.1
    · rintro z ⟨hzW, hzf⟩
      have hng : ¬ Filter.EventuallyEq (nhds z) f 0 := by
        intro hlocal
        exact hne (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hzW hlocal ha)
      obtain ⟨s, _, hszero, hsreg⟩ :=
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
        fun _ ↦ analyticOnNhd_empty, fun _ _ ht ↦ (ht.elim),
        fun _ ↦ mapsTo_empty _ _, ?_⟩
    rintro z ⟨hzW, hzf⟩
    have hng : ¬ Filter.EventuallyEq (nhds z) f 0 := by
      intro hlocal
      exact hne (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hzW hlocal ha)
    obtain ⟨s, _, hszero, hsreg⟩ :=
      astrat_finite_derivative_aux (n + 1) f z (hf z hzW) hzf hng
    have hzR : z ∈ R s := ⟨hzW, hszero, hsreg⟩
    obtain ⟨w, hwT, _⟩ := mem_iUnion₂.mp (hTcover s hzR)
    exact (hIn ⟨⟨s, ⟨w, hwT⟩⟩⟩).elim

private theorem bh15_irreducibleAt_of_fderiv_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} {y : E} (_hf : AnalyticAt ℂ f y) (hf0 : f y = 0)
    (hd : fderiv ℂ f y ≠ 0) : IsIrreducibleAt f y := by
  refine ⟨hf0, ?_⟩
  intro a b ha hb hab
  by_contra hn
  push Not at hn
  have he := hab.fderiv_eq (𝕜 := ℂ)
  have hz : fderiv ℂ (fun x ↦ a x * b x) y = 0 := by
    change fderiv ℂ (a * b) y = 0
    rw [fderiv_mul ha.differentiableAt hb.differentiableAt, hn.1, hn.2]
    ext z
    simp
  exact hd (he.trans hz)

/-- An immersed hypersurface contains the germ of a regular irreducible hypersurface at each parameter anchor.
Source: the holomorphic inverse function theorem applied to an injective derivative minor;
Gunning–Rossi, Chapter I.B and II.B. -/
theorem bh15_immersion_hypersurface_germ_aux (n : ℕ) (U : Set (Fin n → ℂ)) (hU : IsOpen U)
    (g : (Fin n → ℂ) → (Fin (n + 1) → ℂ)) (t : Fin n → ℂ)
    (ht : t ∈ U) (hg : AnalyticAt ℂ g t)
    (hi : Function.Injective (fderiv ℂ g t)) :
    ∃ q : (Fin (n + 1) → ℂ) → ℂ,
      AnalyticAt ℂ q (g t) ∧ IsIrreducibleAt q (g t) ∧
      fderiv ℂ q (g t) ≠ 0 ∧
      ∀ᶠ p in 𝓝 (g t), q p = 0 → p ∈ g '' U := by
  let D := fderiv ℂ g t
  have hleft : D.HasLeftInverse :=
    ContinuousLinearMap.HasLeftInverse.of_injective_of_finiteDimensional hi
  let C := hleft.complement
  have hclosed : IsClosed (Set.range D) := hleft.isClosed_range
  let eR : (Fin n → ℂ) ≃L[ℂ] D.range := D.equivRange hi hclosed
  let eRC : (D.range × C) ≃L[ℂ] (Fin (n + 1) → ℂ) :=
    D.range.prodEquivOfIsTopCompl C
      (Submodule.IsCompl.isTopCompl_of_isClosed hleft.isCompl_complement
        hclosed hleft.isClosed_complement)
  let e : ((Fin n → ℂ) × C) ≃L[ℂ] (Fin (n + 1) → ℂ) :=
    (eR.prodCongr (ContinuousLinearEquiv.refl ℂ C)).trans eRC
  have he_apply (x : Fin n → ℂ) (c : C) : e (x, c) = D x + c.1 := by
    rfl
  have hfinC : Module.finrank ℂ C = 1 := by
    have hd := e.finrank_eq
    simp only [Module.finrank_prod, Module.finrank_fin_fun] at hd
    omega
  let cE : C ≃L[ℂ] ℂ := ContinuousLinearEquiv.ofFinrankEq (by simpa using hfinC)
  let Φ : ((Fin n → ℂ) × C) → (Fin (n + 1) → ℂ) :=
    fun x ↦ g x.1 + x.2.1
  have hΦ : AnalyticAt ℂ Φ (t, 0) := by
    dsimp [Φ]
    exact (hg.comp analyticAt_fst).add
      ((C.subtypeL.analyticAt ((t, (0 : C))).2).comp analyticAt_snd)
  have hdΦ : HasFDerivAt Φ
      (e : ((Fin n → ℂ) × C) →L[ℂ] (Fin (n + 1) → ℂ)) (t, 0) := by
    convert ((hg.differentiableAt.hasFDerivAt.comp (t, 0)
      (hasFDerivAt_fst (p := (t, (0 : C))))).add (ContinuousLinearMap.hasFDerivAt
      (C.subtypeL.comp (ContinuousLinearMap.snd ℂ (Fin n → ℂ) C)))) using 1 <;>
      ext <;> simp [Φ, e, eR, eRC, D, he_apply]
  let hr := hΦ.contDiffAt.hasStrictFDerivAt' hdΦ
    (show (ω : WithTop ℕ∞) ≠ 0 by simp)
  let inv := hr.localInverse Φ e (t, 0)
  let q : (Fin (n + 1) → ℂ) → ℂ := fun p ↦ cE (inv p).2
  have hΦbase : Φ (t, 0) = g t := by simp [Φ]
  have hinv : AnalyticAt ℂ inv (g t) := by
    rw [← hΦbase]
    let R := hr.toOpenPartialHomeomorph Φ
    have hs : R.symm (Φ (t, 0)) = (t, 0) :=
      R.left_inv hr.mem_toOpenPartialHomeomorph_source
    apply R.analyticAt_symm hr.image_mem_toOpenPartialHomeomorph_target
    · rw [hr.toOpenPartialHomeomorph_coe]
      simpa only [hs] using hΦ
    · rw [hr.toOpenPartialHomeomorph_coe]
      simpa only [hs] using hdΦ.fderiv
  have hq : AnalyticAt ℂ q (g t) := by
    have hsnd : AnalyticAt ℂ (fun x : (Fin n → ℂ) × C ↦ x.2) (inv (g t)) :=
      analyticAt_snd
    have hcS : AnalyticAt ℂ (fun x : (Fin n → ℂ) × C ↦ cE x.2) (inv (g t)) :=
      (cE.toContinuousLinearMap.analyticAt (inv (g t)).2).comp hsnd
    exact (hcS.comp hinv).congr (by rfl)
  have hinv_gt : inv (g t) = (t, 0) := by
    rw [← hΦbase]
    dsimp [inv]
    exact hr.localInverse_apply_image
  have hq0 : q (g t) = 0 := by simp [q, hinv_gt]
  have hqd : fderiv ℂ q (g t) ≠ 0 := by
    intro hz
    have hcomp : HasFDerivAt (q ∘ Φ)
        ((fderiv ℂ q (g t)).comp (e : _ →L[ℂ] _)) (t, 0) := by
      have hq' : AnalyticAt ℂ q (Φ (t, 0)) := by simpa only [hΦbase] using hq
      have hh := hq'.differentiableAt.hasFDerivAt.comp (t, 0) hdΦ
      have hdq : fderiv ℂ q (Φ (t, 0)) = fderiv ℂ q (g t) :=
        congrArg (fderiv ℂ q) hΦbase
      simpa only [hdq] using hh
    have heq : q ∘ Φ =ᶠ[𝓝 (t, 0)] fun x ↦ cE x.2 := by
      filter_upwards [hr.eventually_left_inverse] with x hx
      simp only [Function.comp_apply, q, inv]
      rw [hx]
    have hcderiv : fderiv ℂ (fun x : (Fin n → ℂ) × C ↦ cE x.2) (t, 0) = 0 := by
      rw [← heq.fderiv_eq, hcomp.fderiv, hz]
      simp
    have hone := congrArg (fun L ↦ L (0, cE.symm 1)) hcderiv
    have hcHas : HasFDerivAt (fun x : (Fin n → ℂ) × C ↦ cE x.2)
        (cE.toContinuousLinearMap.comp (ContinuousLinearMap.snd ℂ (Fin n → ℂ) C))
        (t, 0) := cE.toContinuousLinearMap.hasFDerivAt.comp (t, 0) hasFDerivAt_snd
    rw [hcHas.fderiv] at hone
    simp at hone
  refine ⟨q, hq, bh15_irreducibleAt_of_fderiv_ne_zero hq hq0 hqd, hqd, ?_⟩
  have hfirst : ∀ᶠ p in 𝓝 (g t), (inv p).1 ∈ U := by
    have hmem : (inv (g t)).1 ∈ U := by rw [hinv_gt]; exact ht
    exact hinv.continuousAt.fst.tendsto.eventually (hU.mem_nhds hmem)
  have hright : ∀ᶠ p in 𝓝 (g t), Φ (inv p) = p := by
    rw [← hΦbase]
    dsimp [inv]
    exact hr.eventually_right_inverse
  filter_upwards [hright, hfirst] with p hp hpu
  intro hzero
  have hc : (inv p).2 = 0 := cE.injective (by simpa [q] using hzero)
  refine ⟨(inv p).1, hpu, ?_⟩
  simpa [Φ, hc] using hp

/-- The critical zeros of a reduced equation have empty interior in an immersed hypersurface.
Source: `bh12_no_critical_hypersurface`, `bh15_immersion_hypersurface_germ`,
and Gunning–Rossi, Chapter I.B. -/
theorem bh15_critical_pullback_interior_aux (n : ℕ) (f : (Fin (n + 1) → ℂ) → ℂ)
    (hf : AnalyticOnNhd ℂ f univ)
    (hred : ∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
      AnalyticGermAt (n + 1) p))
    (U : Set (Fin n → ℂ)) (hU : IsOpen U)
    (g : (Fin n → ℂ) → (Fin (n + 1) → ℂ)) (hg : AnalyticOnNhd ℂ g U)
    (hi : ∀ t ∈ U, Function.Injective (fderiv ℂ g t)) :
    interior (U ∩ g ⁻¹' {p | f p = 0 ∧ fderiv ℂ f p = 0}) = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro t ht
  have ht' : t ∈ U ∩ g ⁻¹' {p | f p = 0 ∧ fderiv ℂ f p = 0} :=
    interior_subset ht
  obtain ⟨q, hq, hqi, -, hqg⟩ :=
    bh15_immersion_hypersurface_germ_aux n
      (interior (U ∩ g ⁻¹' {p | f p = 0 ∧ fderiv ℂ f p = 0})) isOpen_interior
      g t ht (hg t ht'.1) (hi t ht'.1)
  apply bh12_no_critical_hypersurface_aux (n + 1) (g t) f q
    (hf (g t) (mem_univ _)) hq (hred (g t)) hqi
  filter_upwards [hqg] with p hp hqp
  obtain ⟨s, hs, rfl⟩ := hp hqp
  exact (interior_subset hs).2

/-- Local analytic equations and empty interior give strictly smaller nonempty charts.
The guard also covers ambient dimension zero.
Source: `astrat_local_parametrization` and removal of empty full-dimensional charts. -/
theorem bh15_thin_local_cover_aux (n : ℕ) (Z : Set (Fin n → ℂ))
    (hZ : ∀ z ∈ Z, ∃ (V : Set (Fin n → ℂ)), IsOpen V ∧ z ∈ V ∧
      ∃ (r : ℕ) (F : Fin r → (Fin n → ℂ) → ℂ),
        (∀ i, AnalyticOnNhd ℂ (F i) V) ∧
        ∀ x ∈ V, (x ∈ Z ↔ ∀ i, F i x = 0))
    (hi : interior Z = ∅) :
    ∃ (d : ℕ → ℕ) (U : ∀ j, Set (Fin (d j) → ℂ))
      (g : ∀ j, (Fin (d j) → ℂ) → (Fin n → ℂ)),
      (∀ j, (U j).Nonempty → d j < n) ∧ (∀ j, IsOpen (U j)) ∧
      (∀ j, AnalyticOnNhd ℂ (g j) (U j)) ∧ Z = ⋃ j, g j '' U j := by
  obtain ⟨d, U, g, hd, hU, hg, hfull, hcover⟩ :=
    astrat_local_parametrization n Z hZ
  refine ⟨d, U, g, ?_, hU, hg, hcover⟩
  intro j hUne
  exact (hd j).lt_of_ne fun hdn ↦ by
    obtain ⟨t, ht⟩ := hUne
    have hgt : g j t ∈ interior Z := hfull j hdn ⟨t, ht, rfl⟩
    rw [hi] at hgt
    exact hgt

/-- Reduced entire equations have countable critical-zero covers of codimension at least two.
Source: `bh15_zero_set_immersion_cover`, `bh15_critical_pullback_interior`,
`astrat_pullback_equations`, and `bh15_thin_local_cover`. -/
theorem bh15_critical_stratification_aux (n : ℕ) (f : (Fin n → ℂ) → ℂ)
    (hf : AnalyticOnNhd ℂ f univ)
    (hred : ∀ p, Squarefree (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
      AnalyticGermAt n p)) :
    ∃ (d : ℕ → ℕ) (U : ∀ j, Set (Fin (d j) → ℂ))
      (g : ∀ j, (Fin (d j) → ℂ) → (Fin n → ℂ)),
      (∀ j, (U j).Nonempty → d j + 2 ≤ n) ∧
      (∀ j, IsOpen (U j)) ∧ (∀ j, DifferentiableOn ℂ (g j) (U j)) ∧
      {p | f p = 0 ∧ fderiv ℂ f p = 0} = ⋃ j, g j '' U j := by
  classical
  cases n with
  | zero =>
      have hcrit : {p : Fin 0 → ℂ | f p = 0 ∧ fderiv ℂ f p = 0} = ∅ := by
        ext p
        constructor
        · intro hp
          have hfzero : f = 0 := by
            funext q
            rw [Subsingleton.elim q p, hp.1]
            rfl
          have hgerm :
              (⟨Filter.Germ.ofFun f, f, hf p (mem_univ p), rfl⟩ :
                AnalyticGermAt 0 p) = 0 := by
            subst f
            rfl
          exact (hred p).ne_zero hgerm |>.elim
        · exact False.elim
      refine ⟨fun _ ↦ 0, fun _ ↦ ∅, fun _ _ ↦ 0, ?_, ?_, ?_, ?_⟩
      · intro j hj
        exact hj.ne_empty rfl |>.elim
      · exact fun _ ↦ isOpen_empty
      · exact fun _ ↦ differentiableOn_empty
      · rw [hcrit]
        simp only [image_empty, iUnion_empty]
  | succ m =>
      let C : Set (Fin (m + 1) → ℂ) :=
        {p | f p = 0 ∧ fderiv ℂ f p = 0}
      have hnonzero : ∃ a : Fin (m + 1) → ℂ, f a ≠ 0 := by
        by_contra h
        push_neg at h
        have hfzero : f = 0 := funext h
        have hgerm :
            (⟨Filter.Germ.ofFun f, f, hf 0 (mem_univ 0), rfl⟩ :
              AnalyticGermAt (m + 1) 0) = 0 := by
          subst f
          rfl
        exact (hred 0).ne_zero hgerm
      obtain ⟨a, ha⟩ := hnonzero
      obtain ⟨U₀, g₀, hU₀, hg₀, hi₀, hm₀, hcover₀⟩ :=
        bh15_zero_set_immersion_cover_aux m univ isOpen_univ isPreconnected_univ
          f hf a (mem_univ a) ha
      have hCeq : ∀ z ∈ C, ∃ (V : Set (Fin (m + 1) → ℂ)), IsOpen V ∧ z ∈ V ∧
          ∃ (r : ℕ) (F : Fin r → (Fin (m + 1) → ℂ) → ℂ),
            (∀ i, AnalyticOnNhd ℂ (F i) V) ∧
            ∀ x ∈ V, (x ∈ C ↔ ∀ i, F i x = 0) := by
        intro z hz
        let F : Fin (m + 2) → (Fin (m + 1) → ℂ) → ℂ := fun i ↦
          Fin.cases f (fun k x ↦ fderiv ℂ f x (Pi.single k 1)) i
        refine ⟨univ, isOpen_univ, mem_univ z, m + 2, F, ?_, ?_⟩
        · intro i
          refine Fin.cases hf (fun k ↦ ?_) i
          exact (ContinuousLinearMap.apply ℂ ℂ (Pi.single k 1)).comp_analyticOnNhd hf.fderiv
        · intro x hx
          constructor
          · rintro ⟨hfx, hdf⟩ i
            refine Fin.cases hfx (fun k ↦ ?_) i
            change fderiv ℂ f x (Pi.single k 1) = 0
            rw [hdf]
            rfl
          · intro hF
            refine ⟨hF 0, ?_⟩
            apply ContinuousLinearMap.coe_injective
            apply (Pi.basisFun ℂ (Fin (m + 1))).ext
            intro k
            simpa [F] using hF (Fin.succ k)
      have hthin : ∀ j, ∃ (d : ℕ → ℕ) (U : ∀ k, Set (Fin (d k) → ℂ))
          (g : ∀ k, (Fin (d k) → ℂ) → (Fin m → ℂ)),
          (∀ k, (U k).Nonempty → d k < m) ∧ (∀ k, IsOpen (U k)) ∧
          (∀ k, AnalyticOnNhd ℂ (g k) (U k)) ∧
          U₀ j ∩ g₀ j ⁻¹' C = ⋃ k, g k '' U k := by
        intro j
        apply bh15_thin_local_cover_aux m (U₀ j ∩ g₀ j ⁻¹' C)
        · exact astrat_pullback_equations (m + 1) m C hCeq (U₀ j) (hU₀ j)
            (g₀ j) (hg₀ j)
        · exact bh15_critical_pullback_interior_aux m f hf hred (U₀ j) (hU₀ j)
            (g₀ j) (hg₀ j) (hi₀ j)
      choose d U g hd hU hg hEq using hthin
      let d' : ℕ → ℕ := fun q ↦ d q.unpair.1 q.unpair.2
      let U' : ∀ q, Set (Fin (d' q) → ℂ) := fun q ↦ U q.unpair.1 q.unpair.2
      let g' : ∀ q, (Fin (d' q) → ℂ) → (Fin (m + 1) → ℂ) := fun q ↦
        g₀ q.unpair.1 ∘ g q.unpair.1 q.unpair.2
      refine ⟨d', U', g', ?_, ?_, ?_, ?_⟩
      · intro q hq
        dsimp [d', U'] at hq ⊢
        have := hd q.unpair.1 q.unpair.2 hq
        omega
      · intro q
        exact hU q.unpair.1 q.unpair.2
      · intro q
        apply AnalyticOnNhd.differentiableOn
        apply (hg₀ q.unpair.1).comp (hg q.unpair.1 q.unpair.2)
        intro t ht
        have ht' : g q.unpair.1 q.unpair.2 t ∈
            ⋃ k, g q.unpair.1 k '' U q.unpair.1 k :=
          mem_iUnion_of_mem q.unpair.2 ⟨t, ht, rfl⟩
        rw [← hEq q.unpair.1] at ht'
        exact ht'.1
      · apply Set.Subset.antisymm
        · intro x hx
          have hxzero : x ∈ univ ∩ {x | f x = 0} := ⟨mem_univ x, hx.1⟩
          obtain ⟨j, t, ht, hgt⟩ := mem_iUnion.mp (hcover₀ hxzero)
          have htC : t ∈ U₀ j ∩ g₀ j ⁻¹' C := ⟨ht, by simpa [C, hgt] using hx⟩
          rw [hEq j] at htC
          obtain ⟨k, s, hs, hgs⟩ := mem_iUnion.mp htC
          refine mem_iUnion.mpr ⟨Nat.pair j k, ?_⟩
          change x ∈ (g₀ (Nat.pair j k).unpair.1 ∘
            g (Nat.pair j k).unpair.1 (Nat.pair j k).unpair.2) ''
              U (Nat.pair j k).unpair.1 (Nat.pair j k).unpair.2
          rw [Nat.unpair_pair]
          refine ⟨s, hs, ?_⟩
          exact (congrArg (g₀ j) hgs).trans hgt
        · intro x hx
          obtain ⟨q, t, ht, rfl⟩ := mem_iUnion.mp hx
          have ht' : t ∈ U q.unpair.1 q.unpair.2 := by simpa [U', d'] using ht
          have hmem : g q.unpair.1 q.unpair.2 t ∈
              ⋃ k, g q.unpair.1 k '' U q.unpair.1 k :=
            mem_iUnion_of_mem q.unpair.2 ⟨t, ht', rfl⟩
          rw [← hEq q.unpair.1] at hmem
          exact hmem.2

/-- A locally biholomorphic map pulls back a countable holomorphic cover without increasing parameter dimensions.
Source: local inverse composition and second countability of complex affine space;
`spec_complexExponential_localBiholomorph` supplies the intended local inverses. -/
theorem bh15_lift_cover_aux (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (Fin n → ℂ) M] (F : (Fin n → ℂ) → M)
    (hloc : ∀ p, ∃ e : OpenPartialHomeomorph (Fin n → ℂ) M,
      p ∈ e.source ∧ EqOn F e e.source ∧
      ContMDiffOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) ω e.symm e.target)
    (d : ℕ → ℕ) (U : ∀ j, Set (Fin (d j) → ℂ))
    (g : ∀ j, (Fin (d j) → ℂ) → M)
    (hU : ∀ j, IsOpen (U j))
    (hg : ∀ j, ContMDiffOn 𝓘(ℂ, Fin (d j) → ℂ) 𝓘(ℂ, Fin n → ℂ) ω (g j) (U j)) :
    ∃ (σ : ℕ → ℕ) (V : ∀ j, Set (Fin (d (σ j)) → ℂ))
      (h : ∀ j, (Fin (d (σ j)) → ℂ) → (Fin n → ℂ)),
      (∀ j, V j ⊆ U (σ j)) ∧ (∀ j, IsOpen (V j)) ∧
      (∀ j, DifferentiableOn ℂ (h j) (V j)) ∧
      (∀ j t, t ∈ V j → F (h j t) = g (σ j) t) ∧
      F ⁻¹' (⋃ j, g j '' U j) = ⋃ j, h j '' V j := by
  choose e hp heF heSmooth using hloc
  obtain ⟨S, hSc, hScover⟩ := TopologicalSpace.countable_cover_nhds
    (fun p ↦ (e p).open_source.mem_nhds (hp p))
  have hSne : S.Nonempty := by
    have hz : (0 : Fin n → ℂ) ∈ ⋃ q ∈ S, (e q).source := by
      rw [hScover]
      exact mem_univ _
    simp only [mem_iUnion] at hz
    obtain ⟨q, hq, -⟩ := hz
    exact ⟨q, hq⟩
  obtain ⟨a, ha⟩ := hSc.exists_surjective hSne
  let pair : ℕ → ℕ × ℕ := Nat.unpair
  let σ : ℕ → ℕ := fun j ↦ (pair j).1
  let p : ℕ → Fin n → ℂ := fun j ↦ (a ((pair j).2) : Fin n → ℂ)
  let V : ∀ j, Set (Fin (d (σ j)) → ℂ) :=
    fun j ↦ U (σ j) ∩ g (σ j) ⁻¹' (e (p j)).target
  let h : ∀ j, (Fin (d (σ j)) → ℂ) → (Fin n → ℂ) :=
    fun j ↦ (e (p j)).symm ∘ g (σ j)
  refine ⟨σ, V, h, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun j ↦ inter_subset_left
  · intro j
    exact (hg (σ j)).continuousOn.isOpen_inter_preimage
      (hU (σ j)) (e (p j)).open_target
  · intro j
    apply MDifferentiableOn.differentiableOn
    exact (heSmooth (p j)).mdifferentiableOn (by simp) |>.comp
      ((hg (σ j)).mdifferentiableOn (by simp) |>.mono inter_subset_left) inter_subset_right
  · intro j t ht
    change t ∈ U (σ j) ∩ g (σ j) ⁻¹' (e (p j)).target at ht
    exact (heF (p j) ((e (p j)).map_target ht.2)).trans
      ((e (p j)).right_inv ht.2)
  · ext x
    constructor
    · intro hx
      simp only [mem_preimage, mem_iUnion, mem_image] at hx ⊢
      obtain ⟨i, t, htU, hgt⟩ := hx
      have hxs : x ∈ ⋃ q ∈ S, (e q).source := by rw [hScover]; exact mem_univ x
      simp only [mem_iUnion] at hxs
      obtain ⟨q, hqS, hxq⟩ := hxs
      obtain ⟨k, hk⟩ := ha ⟨q, hqS⟩
      let j := Nat.pair i k
      have htarget : g i t ∈ (e q).target := by
        rw [hgt, heF q hxq]
        exact (e q).map_source hxq
      have hlift : (e q).symm (g i t) = x := by
        rw [hgt, heF q hxq]
        exact (e q).left_inv hxq
      refine ⟨j, ?_⟩
      have himage : x ∈ ((e q).symm ∘ g i) ''
          (U i ∩ g i ⁻¹' (e q).target) := ⟨t, ⟨htU, htarget⟩, hlift⟩
      have hu : (Nat.unpair (Nat.pair i k)).1 = i := by
        exact congrArg Prod.fst (Nat.unpair_pair i k)
      have hv : (Nat.unpair (Nat.pair i k)).2 = k := by
        exact congrArg Prod.snd (Nat.unpair_pair i k)
      have himage' : x ∈ ((e q).symm ∘ g (Nat.unpair (Nat.pair i k)).1) ''
          (U (Nat.unpair (Nat.pair i k)).1 ∩
            g (Nat.unpair (Nat.pair i k)).1 ⁻¹' (e q).target) := hu.symm ▸ himage
      dsimp [V, h, σ, p, pair, j]
      rw [hv, hk]
      exact himage'
    · intro hx
      simp only [mem_iUnion, mem_image] at hx
      obtain ⟨j, t, htV, htx⟩ := hx
      change t ∈ U (σ j) ∩ g (σ j) ⁻¹' (e (p j)).target at htV
      simp only [mem_preimage, mem_iUnion, mem_image]
      refine ⟨σ j, t, inter_subset_left htV, ?_⟩
      rw [← htx]
      exact ((heF (p j) ((e (p j)).map_target htV.2)).trans
        ((e (p j)).right_inv htV.2)).symm

/-- Two countable codimension-two covers interleave to cover their union.
Source: reindexing the disjoint union of two copies of the natural numbers. -/
theorem bh15_union_cover_aux (n : ℕ) (A B : Set (Fin n → ℂ))
    (d₀ d₁ : ℕ → ℕ) (U₀ : ∀ j, Set (Fin (d₀ j) → ℂ))
    (U₁ : ∀ j, Set (Fin (d₁ j) → ℂ))
    (g₀ : ∀ j, (Fin (d₀ j) → ℂ) → (Fin n → ℂ))
    (g₁ : ∀ j, (Fin (d₁ j) → ℂ) → (Fin n → ℂ))
    (hd₀ : ∀ j, (U₀ j).Nonempty → d₀ j + 2 ≤ n)
    (hd₁ : ∀ j, (U₁ j).Nonempty → d₁ j + 2 ≤ n)
    (hU₀ : ∀ j, IsOpen (U₀ j)) (hU₁ : ∀ j, IsOpen (U₁ j))
    (hg₀ : ∀ j, DifferentiableOn ℂ (g₀ j) (U₀ j))
    (hg₁ : ∀ j, DifferentiableOn ℂ (g₁ j) (U₁ j))
    (hA : A = ⋃ j, g₀ j '' U₀ j) (hB : B = ⋃ j, g₁ j '' U₁ j) :
    ∃ (d : ℕ → ℕ) (U : ∀ j, Set (Fin (d j) → ℂ))
      (g : ∀ j, (Fin (d j) → ℂ) → (Fin n → ℂ)),
      (∀ j, (U j).Nonempty → d j + 2 ≤ n) ∧
      (∀ j, IsOpen (U j)) ∧ (∀ j, DifferentiableOn ℂ (g j) (U j)) ∧
      A ∪ B = ⋃ j, g j '' U j := by
  let e : ℕ ≃ ℕ ⊕ ℕ := Equiv.natSumNatEquivNat.symm
  let d' : ℕ ⊕ ℕ → ℕ := Sum.elim d₀ d₁
  let U' : ∀ s, Set (Fin (d' s) → ℂ) := fun s =>
    match s with
    | Sum.inl k => U₀ k
    | Sum.inr k => U₁ k
  let g' : ∀ s, (Fin (d' s) → ℂ) → (Fin n → ℂ) := fun s =>
    match s with
    | Sum.inl k => g₀ k
    | Sum.inr k => g₁ k
  let d : ℕ → ℕ := fun j => d' (e j)
  let U : ∀ j, Set (Fin (d j) → ℂ) := fun j => U' (e j)
  let g : ∀ j, (Fin (d j) → ℂ) → (Fin n → ℂ) := fun j => g' (e j)
  refine ⟨d, U, g, ?_, ?_, ?_, ?_⟩
  · intro j hj
    change (U' (e j)).Nonempty at hj
    change d' (e j) + 2 ≤ n
    rcases h : e j with k | k
    · rw [h] at hj
      simp only [U', d'] at hj ⊢
      exact hd₀ k hj
    · rw [h] at hj
      simp only [U', d'] at hj ⊢
      exact hd₁ k hj
  · intro j
    change IsOpen (U' (e j))
    rcases h : e j with k | k
    · simp only [U']
      exact hU₀ k
    · simp only [U']
      exact hU₁ k
  · intro j
    change DifferentiableOn ℂ (g' (e j)) (U' (e j))
    rcases h : e j with k | k
    · simp only [g', U']
      exact hg₀ k
    · simp only [g', U']
      exact hg₁ k
  · rw [hA, hB]
    have himage (j : ℕ) : g j '' U j =
        match e j with
        | Sum.inl k => g₀ k '' U₀ k
        | Sum.inr k => g₁ k '' U₁ k := by
      change g' (e j) '' U' (e j) = _
      rcases h : e j with k | k
      · rfl
      · rfl
    ext x
    simp only [mem_union, mem_iUnion]
    constructor
    · rintro (⟨k, hx⟩ | ⟨k, hx⟩)
      · refine ⟨Equiv.natSumNatEquivNat (Sum.inl k), ?_⟩
        have he : e (Equiv.natSumNatEquivNat (Sum.inl k)) = Sum.inl k := by
          simp [e]
        rw [himage, he]
        exact hx
      · refine ⟨Equiv.natSumNatEquivNat (Sum.inr k), ?_⟩
        have he : e (Equiv.natSumNatEquivNat (Sum.inr k)) = Sum.inr k := by
          simp [e]
        rw [himage, he]
        exact hx
    · rintro ⟨j, hx⟩
      rw [himage] at hx
      rcases h : e j with k | k
      · left
        rw [h] at hx
        exact ⟨k, hx⟩
      · right
        rw [h] at hx
        exact ⟨k, hx⟩

end HodgeLean.Adapters
