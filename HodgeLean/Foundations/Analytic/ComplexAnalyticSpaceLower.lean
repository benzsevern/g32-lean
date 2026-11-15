import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceUpper

/-! # Manifold pieces of top dimension near a point

Helpers prefixed `anb_` for the existence, arbitrarily near a point `p` of a locally analytic set
`B ⊆ ℂⁿ`, of manifold pieces of `B` of dimension the Krull dimension `D` of its germ at `p`:

* ring theory: a minimal prime of the vanishing ideal with `dim 𝒪/P = D`, and the drop of dimension
  when an element outside a prime is added;
* elements of an ideal vanish near the origin on the common zeros of representatives of its
  generators.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped ContDiff

namespace HodgeLean.Foundations.Analytic

open HodgeLean.Foundations HodgeLean.Foundations.AnalyticDivisorAlgebraic6

section Ring

variable {R : Type*} [CommRing R]

/-- A minimal prime of `I` realizing the (finite) Krull dimension of `R ⧸ I`. -/
theorem anb_exists_minimalPrime_dim (I : Ideal R) {D : ℕ}
    (hD : ringKrullDim (R ⧸ I) = ((D : ℕ∞) : WithBot ℕ∞)) :
    ∃ P ∈ I.minimalPrimes, ringKrullDim (R ⧸ P) = ((D : ℕ∞) : WithBot ℕ∞) := by
  rw [ringKrullDim_quotient] at hD
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.1 (hD.symm ▸ le_rfl :
    ((D : ℕ) : WithBot ℕ∞) ≤ Order.krullDim (PrimeSpectrum.zeroLocus (R := R) I))
  obtain ⟨P, hP, hPq⟩ := Ideal.exists_minimalPrimes_le
    ((PrimeSpectrum.mem_zeroLocus _ _).1 l.head.2 : (I : Set R) ⊆ l.head.1.asIdeal)
  refine ⟨P, hP, le_antisymm ?_ ?_⟩
  · rw [← hD, ← ringKrullDim_quotient]
    exact ringKrullDim_le_of_surjective (Ideal.Quotient.factor hP.1.2)
      (Ideal.Quotient.factor_surjective _)
  · rw [ringKrullDim_quotient]
    let T := {x : PrimeSpectrum.zeroLocus (R := R) I | l.head ≤ x}
    let l' : LTSeries T :=
      { length := l.length
        toFun := fun i ↦ ⟨l i, l.monotone (Fin.zero_le i)⟩
        step := fun i ↦ l.step i }
    have h1 : ((D : ℕ) : WithBot ℕ∞) ≤ Order.krullDim T :=
      hl ▸ Order.LTSeries.length_le_krullDim l'
    refine le_trans (by exact_mod_cast h1) (Order.krullDim_le_of_strictMono
      (fun x : T ↦ (⟨x.1.1, (PrimeSpectrum.mem_zeroLocus _ _).2 (hPq.trans x.2)⟩ :
        PrimeSpectrum.zeroLocus (R := R) P)) fun x y hxy ↦ hxy)

/-- Adding an element outside a prime drops the dimension. -/
theorem anb_dim_sup_lt {P J : Ideal R} [hP : P.IsPrime] {h : R} (hhJ : h ∈ J) (hhP : h ∉ P) :
    ringKrullDim (R ⧸ (P ⊔ J)) + 1 ≤ ringKrullDim (R ⧸ P) := by
  have hne : Ideal.Quotient.mk P h ≠ 0 := fun h0 ↦ hhP (Ideal.Quotient.eq_zero_iff_mem.1 h0)
  have hreg : Ideal.Quotient.mk P h ∈ nonZeroDivisors (R ⧸ P) :=
    mem_nonZeroDivisors_of_ne_zero hne
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hreg
  have h2 : ringKrullDim (R ⧸ (P ⊔ J)) ≤
      ringKrullDim ((R ⧸ P) ⧸ Ideal.span {Ideal.Quotient.mk P h}) := by
    have h3 : ringKrullDim (R ⧸ (P ⊔ J)) ≤ ringKrullDim (R ⧸ (P ⊔ Ideal.span {h})) :=
      ringKrullDim_le_of_surjective (Ideal.Quotient.factor
        (sup_le_sup_left ((Ideal.span_singleton_le_iff_mem J).2 hhJ) P))
        (Ideal.Quotient.factor_surjective _)
    refine h3.trans (le_of_eq ?_)
    have := ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotSup P (Ideal.span {h}))
    rw [Ideal.map_span, Set.image_singleton] at this
    exact this.symm
  calc ringKrullDim (R ⧸ (P ⊔ J)) + 1
      ≤ ringKrullDim ((R ⧸ P) ⧸ Ideal.span {Ideal.Quotient.mk P h}) + 1 := by gcongr
    _ ≤ _ := h1

end Ring

/-- The value of a sum of products of analytic germs is the germ of the pointwise sum. -/
theorem anb_val_sum_mul {n m : ℕ} (c g : Fin m → AnalyticGerm n) (f : Fin m → (Fin n → ℂ) → ℂ)
    (hrep : ∀ j, Filter.Germ.ofFun (f j) = (g j).val) :
    (∑ j, c j * g j).val = Filter.Germ.ofFun (fun z ↦ ∑ j, anb_rep (c j) z * f j z) := by
  have h1 : (∑ j, c j * g j).val = ∑ j, (c j).val * (g j).val := by
    rw [AddSubmonoidClass.coe_finsetSum]; rfl
  rw [h1]
  have h2 : (fun z ↦ ∑ j, anb_rep (c j) z * f j z) = ∑ j, anb_rep (c j) * f j := by
    funext z; simp
  rw [h2]
  change _ = Filter.Germ.coeRingHom _ (∑ j, anb_rep (c j) * f j)
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_mul]
  change _ = Filter.Germ.ofFun (anb_rep (c j)) * Filter.Germ.ofFun (f j)
  rw [anb_rep_germ, hrep]

/-- Elements of an ideal vanish near the origin on the common zeros of representatives of its
generators. -/
theorem anb_vanish_of_mem {n m : ℕ} {P : Ideal (AnalyticGerm n)} {g : Fin m → AnalyticGerm n}
    (hgen : Ideal.span (Set.range g) = P) {f : Fin m → (Fin n → ℂ) → ℂ}
    (hrep : ∀ j, Filter.Germ.ofFun (f j) = (g j).val) {h : AnalyticGerm n} (hh : h ∈ P)
    {H : (Fin n → ℂ) → ℂ} (hH : Filter.Germ.ofFun H = h.val) :
    ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), (∀ j, f j z = 0) → H z = 0 := by
  rw [← hgen] at hh
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hh
  have hval : h.val = Filter.Germ.ofFun (fun z ↦ ∑ j, anb_rep (c j) z * f j z) := by
    rw [← hc]
    exact anb_val_sum_mul c g f hrep
  have := Filter.Germ.coe_eq.1 (hH.trans hval)
  filter_upwards [this] with z hz h0
  rw [hz]
  simp [h0]

section RepPoly

open Polynomial

/-- A polynomial over the analytic germs, with its coefficients replaced by chosen representatives:
a polynomial over the functions on `ℂᵈ`. -/
def anb_repPoly {d : ℕ} (T : Polynomial (AnalyticGerm d)) : Polynomial ((Fin d → ℂ) → ℂ) :=
  ∑ i ∈ Finset.range (T.natDegree + 1), monomial i (anb_rep (T.coeff i))

/-- The representative polynomial evaluated at a point `w` of `ℂᵈ`: a polynomial over `ℂ`. -/
def anb_evPoly {d : ℕ} (T : Polynomial (AnalyticGerm d)) (w : Fin d → ℂ) : Polynomial ℂ :=
  (anb_repPoly T).map (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w)

theorem anb_evPoly_eval {d : ℕ} (T : Polynomial (AnalyticGerm d)) (w : Fin d → ℂ) (t : ℂ) :
    (anb_evPoly T w).eval t =
      ∑ i ∈ Finset.range (T.natDegree + 1), anb_rep (T.coeff i) w * t ^ i := by
  simp [anb_evPoly, anb_repPoly, Polynomial.map_sum, eval_finsetSum, eval_monomial]

theorem anb_repPoly_map {d : ℕ} (T : Polynomial (AnalyticGerm d)) :
    (anb_repPoly T).map (Filter.Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
      T.map (AnalyticGerm d).subtype := by
  ext i
  rw [coeff_map, coeff_map, anb_repPoly, finsetSum_coeff]
  simp only [coeff_monomial, Finset.sum_ite_eq', Finset.mem_range]
  split_ifs with hi
  · exact anb_rep_germ _
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    rfl

/-- The representative of a `θ`-evaluation: an element of `𝒪ₙ` mapping to `T(θ)(v)` whose
representative is `z ↦ T(π z)(ℓ z)`. -/
theorem anb_eval₂_rep {n d : ℕ} {P : Ideal (AnalyticGerm n)} (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hcomp : ∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Filter.Germ.ofFun h = a.val → ∀ b : AnalyticGerm n,
      Filter.Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (T : Polynomial (AnalyticGerm d)) (v : AnalyticGerm n) {L : (Fin n → ℂ) → ℂ}
    (hv : v.val = Filter.Germ.ofFun L) :
    ∃ H : AnalyticGerm n, Ideal.Quotient.mk P H = T.eval₂ θ (Ideal.Quotient.mk P v) ∧
      H.val = Filter.Germ.ofFun (fun z ↦ (anb_evPoly T (π z)).eval (L z)) := by
  let b : ℕ → AnalyticGerm n := fun i ↦
    ⟨Filter.Germ.ofFun (fun z ↦ anb_rep (T.coeff i) (π z)), _,
      (anb_rep_analyticAt _).comp_of_eq (π.analyticAt 0) (map_zero π), rfl⟩
  refine ⟨∑ i ∈ Finset.range (T.natDegree + 1), b i * v ^ i, ?_, ?_⟩
  · rw [eval₂_eq_sum_range, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, map_pow, hcomp (T.coeff i) (anb_rep _) (anb_rep_analyticAt _) (anb_rep_germ _)
      (b i) rfl]
  · have : (fun z ↦ (anb_evPoly T (π z)).eval (L z)) =
        ∑ i ∈ Finset.range (T.natDegree + 1), (fun z ↦ anb_rep (T.coeff i) (π z)) * L ^ i := by
      funext z
      rw [anb_evPoly_eval, Finset.sum_apply]
      rfl
    rw [this, AddSubmonoidClass.coe_finsetSum]
    change _ = Filter.Germ.coeRingHom _ _
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, map_pow]
    change (b i).val * v.val ^ i = _
    rw [hv]
    rfl

/-- **The Bezout identity at points.** If `B Q + C Q' = δ` over the analytic germs, then near the
origin, for every `t`, the representative polynomials satisfy it at `w`. -/
theorem anb_bezout_rep {d : ℕ} (Q B C : Polynomial (AnalyticGerm d)) (δ : AnalyticGerm d)
    (h : B * Q + C * Q.derivative = Polynomial.C δ) :
    ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ t,
      (anb_evPoly B w).eval t * (anb_evPoly Q w).eval t +
        (anb_evPoly C w).eval t * (anb_evPoly Q w).derivative.eval t = anb_rep δ w := by
  let E := anb_repPoly B * anb_repPoly Q + anb_repPoly C * derivative (anb_repPoly Q) -
    Polynomial.C (anb_rep δ)
  have hE : E.map (Filter.Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) = 0 := by
    have h1 : E.map (Filter.Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
        (B * Q + C * Q.derivative - Polynomial.C δ).map (AnalyticGerm d).subtype := by
      simp only [E, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
        ← Polynomial.derivative_map, anb_repPoly_map]
      congr 2
      exact anb_rep_germ δ
    rw [h1, h, sub_self, Polynomial.map_zero]
  have hcoef : ∀ k, E.coeff k =ᶠ[𝓝 0] 0 := fun k ↦ by
    have := congrArg (fun F ↦ F.coeff k) hE
    simp only [coeff_map, coeff_zero] at this
    exact Filter.Germ.coe_eq.1 this
  have hall : ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ k ∈ Finset.range (E.natDegree + 1), E.coeff k w = 0 :=
    (Filter.eventually_all_finset _).2 fun k _ ↦ hcoef k
  filter_upwards [hall] with w hw t
  have hEw : E.map (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w) = 0 := by
    ext k
    rw [coeff_map, coeff_zero]
    by_cases hk : k ≤ E.natDegree
    · exact hw k (Finset.mem_range.2 (by omega))
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; rfl
  have := congrArg (fun F ↦ F.eval t) hEw
  simp only [E, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_C, eval_sub, eval_add, eval_mul, eval_C, eval_zero] at this
  rw [← sub_eq_zero]
  simp only [anb_evPoly, Polynomial.derivative_map]
  exact this

end RepPoly

section Branch

open Polynomial

/-- The open set where the representatives of the coefficients of `T` are analytic. -/
def anb_polyDom {d : ℕ} (T : Polynomial (AnalyticGerm d)) : Set (Fin d → ℂ) :=
  ⋂ i ∈ Finset.range (T.natDegree + 1), {w | AnalyticAt ℂ (anb_rep (T.coeff i)) w}

theorem anb_isOpen_polyDom {d : ℕ} (T : Polynomial (AnalyticGerm d)) : IsOpen (anb_polyDom T) :=
  isOpen_biInter_finset fun _ _ ↦ isOpen_analyticAt ℂ _

theorem anb_zero_mem_polyDom {d : ℕ} (T : Polynomial (AnalyticGerm d)) :
    (0 : Fin d → ℂ) ∈ anb_polyDom T :=
  mem_iInter₂.2 fun _ _ ↦ anb_rep_analyticAt _

/-- On its domain, the representative polynomial is jointly analytic in `(w, t)`. -/
theorem anb_evPoly_analyticAt {d : ℕ} (T : Polynomial (AnalyticGerm d)) {w : Fin d → ℂ}
    (hw : w ∈ anb_polyDom T) (t : ℂ) :
    AnalyticAt ℂ (fun u : (Fin d → ℂ) × ℂ ↦ (anb_evPoly T u.1).eval u.2) (w, t) := by
  have : (fun u : (Fin d → ℂ) × ℂ ↦ (anb_evPoly T u.1).eval u.2) =
      fun u ↦ ∑ i ∈ Finset.range (T.natDegree + 1), anb_rep (T.coeff i) u.1 * u.2 ^ i := by
    funext u; rw [anb_evPoly_eval]
  rw [this]
  refine Finset.analyticAt_fun_sum _ fun i hi ↦ ?_
  have hai : AnalyticAt ℂ (anb_rep (T.coeff i)) w := mem_iInter₂.1 hw i hi
  exact (hai.comp analyticAt_fst).mul (analyticAt_snd.pow i)

/-- **Analytic root branch.** At a simple root `t₀` of the representative polynomial at `w₀`,
there is an analytic branch `τ` of roots through `(w₀, t₀)`, and near `(w₀, t₀)` the roots are
exactly the branch. -/
theorem anb_root_branch {d : ℕ} (T : Polynomial (AnalyticGerm d)) {w₀ : Fin d → ℂ}
    (hw₀ : w₀ ∈ anb_polyDom T) {t₀ : ℂ} (hroot : (anb_evPoly T w₀).eval t₀ = 0)
    (hsimple : (anb_evPoly T w₀).derivative.eval t₀ ≠ 0) :
    ∃ τ : (Fin d → ℂ) → ℂ, AnalyticAt ℂ τ w₀ ∧ τ w₀ = t₀ ∧
      ∃ U : Set ((Fin d → ℂ) × ℂ), IsOpen U ∧ (w₀, t₀) ∈ U ∧
        ∀ u ∈ U, ((anb_evPoly T u.1).eval u.2 = 0 ↔ τ u.1 = u.2) := by
  set F : (Fin d → ℂ) × ℂ → ℂ := fun u ↦ (anb_evPoly T u.1).eval u.2
  have hFa := anb_evPoly_analyticAt T hw₀ t₀
  have cdf : ContDiffAt ℂ ω F (w₀, t₀) := hFa.contDiffAt
  have pn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  set c := (anb_evPoly T w₀).derivative.eval t₀
  have hder : fderiv ℂ F (w₀, t₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ =
      (1 : ℂ →L[ℂ] ℂ).smulRight c := by
    have h1 : HasFDerivAt (fun t ↦ F (w₀, t))
        (fderiv ℂ F (w₀, t₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ) t₀ :=
      hFa.differentiableAt.hasFDerivAt.comp t₀ (hasFDerivAt_prodMk_right w₀ t₀)
    have h2 : HasFDerivAt (fun t ↦ F (w₀, t)) ((1 : ℂ →L[ℂ] ℂ).smulRight c) t₀ :=
      (Polynomial.hasDerivAt (anb_evPoly T w₀) t₀).hasFDerivAt
    exact h1.unique h2
  have hc : c ≠ 0 := hsimple
  have if₂ : (fderiv ℂ F (w₀, t₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ).IsInvertible := by
    rw [hder]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 c hc), ?_⟩
    ext
    simp [ContinuousLinearEquiv.unitsEquivAut_apply]
  refine ⟨cdf.implicitFunction pn if₂, (cdf.contDiffAt_implicitFunction pn if₂).analyticAt,
    cdf.implicitFunction_apply_self pn if₂, ?_⟩
  obtain ⟨U, hU, hUo, hU0⟩ :=
    eventually_nhds_iff.1 (cdf.eventually_apply_eq_iff_implicitFunction pn if₂)
  refine ⟨U, hUo, hU0, fun u hu ↦ ?_⟩
  have := hU u hu
  simp only [F, hroot] at this
  exact this

end Branch

/-- For a proper map, the preimages of small neighbourhoods of `y` lie in any open set containing
the fibre over `y`. -/
theorem anb_proper_nhds {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : IsProperMap f) {y : Y} {N : Set X} (hN : IsOpen N) (hfib : f ⁻¹' {y} ⊆ N) :
    ∃ M : Set Y, IsOpen M ∧ y ∈ M ∧ f ⁻¹' M ⊆ N := by
  refine ⟨(f '' Nᶜ)ᶜ, (hf.isClosedMap _ hN.isClosed_compl).isOpen_compl, ?_, fun x hx ↦ ?_⟩
  · rintro ⟨x, hx, rfl⟩
    exact hx (hfib rfl)
  · by_contra hxN
    exact hx ⟨x, hxN, rfl⟩

/-- Generators of an ideal of analytic germs with representatives analytic on a common open
neighbourhood of the origin; their common zeros represent the zero germ of the ideal. -/
theorem anb_generators {n : ℕ} (P : Ideal (AnalyticGerm n)) :
    ∃ (m : ℕ) (g : Fin m → AnalyticGerm n) (f : Fin m → (Fin n → ℂ) → ℂ) (U : Set (Fin n → ℂ)),
      Ideal.span (Set.range g) = P ∧ (∀ j, Filter.Germ.ofFun (f j) = (g j).val) ∧ IsOpen U ∧
      (0 : Fin n → ℂ) ∈ U ∧ (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
      adim2_zeroSet n P = Filter.Germ.ofFun (fun z ↦ ∀ j, f j z = 0) := by
  set gs := adim2_generators n P
  have hgs : Ideal.span (gs : Set (AnalyticGerm n)) = P :=
    ((isNoetherianRing_iff_ideal_fg _).mp (adim_noetherian n) P).choose_spec
  let e := gs.equivFin
  let g : Fin gs.card → AnalyticGerm n := fun j ↦ (e.symm j).1
  have hrange : Set.range g = (gs : Set (AnalyticGerm n)) := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩; exact (e.symm j).2
    · intro hx; exact ⟨e ⟨x, hx⟩, by simp [g]⟩
  let f : Fin gs.card → (Fin n → ℂ) → ℂ := fun j ↦ anb_rep (g j)
  refine ⟨gs.card, g, f, ⋂ j, {z | AnalyticAt ℂ (f j) z}, by rw [hrange, hgs],
    fun j ↦ anb_rep_germ (g j), isOpen_iInter_of_finite fun j ↦ isOpen_analyticAt ℂ (f j),
    mem_iInter.2 fun j ↦ anb_rep_analyticAt (g j), fun j z hz ↦ mem_iInter.1 hz j, ?_⟩
  rw [adim2_zeroSet, Finset.inf_congr rfl fun g _ ↦ anb_zero_eq g, anb_germ_finset_inf]
  refine Filter.Germ.coe_eq.2 (Eventually.of_forall fun z ↦
    propext ⟨fun h j ↦ ?_, fun h x hx ↦ ?_⟩)
  · exact h _ (e.symm j).2
  · have := h (e ⟨x, hx⟩)
    simpa [f, g] using this

end HodgeLean.Foundations.Analytic
