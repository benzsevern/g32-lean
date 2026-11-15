import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceRemmertDim
import HodgeLean.Foundations.AnalyticGermLyingOver
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.MeanValue

/-! # Parametrization helpers for the fibre dimension loci

Helpers prefixed `ancrs_` (copies, under this prefix, of the `ancrs_` helpers of the lane `an-base`,
which lives on another branch): representatives of analytic germs and of polynomials over them,
the Bezout identity at points, analytic root branches at simple roots, the drop of Krull
dimension when an element outside a prime is added, and generators with a common domain. Also:
an analytic map from an open subset of `ℂᵈ` all of whose fibres in it are finite has an injective
derivative somewhere (the rank argument of `an-base`).
HC no distance; AV milestone no distance.
-/

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped ContDiff

namespace HodgeLean.Foundations.Analytic

open HodgeLean.Foundations HodgeLean.Foundations.AnalyticDivisorAlgebraic6

/-- A finite infimum of germs of propositions is the germ of the conjunction. -/
theorem ancrs_germ_finset_inf {α ι : Type*} {l : Filter α} (t : Finset ι) (P : ι → α → Prop) :
    t.inf (fun j ↦ (Filter.Germ.ofFun (P j) : Filter.Germ l Prop)) =
      Filter.Germ.ofFun (fun z ↦ ∀ j ∈ t, P j z) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    rw [Finset.inf_empty]
    exact (Filter.Germ.coe_eq.2 (Eventually.of_forall fun z ↦ by simp)).symm
  | insert a t ha ih =>
    rw [Finset.inf_insert, ih]
    exact Filter.Germ.coe_eq.2 (Eventually.of_forall fun z ↦ by simp)

/-- A finite supremum of germs of propositions is the germ of the disjunction. -/
theorem ancrs_germ_finset_sup {α ι : Type*} {l : Filter α} (t : Finset ι) (P : ι → α → Prop) :
    t.sup (fun j ↦ (Filter.Germ.ofFun (P j) : Filter.Germ l Prop)) =
      Filter.Germ.ofFun (fun z ↦ ∃ j ∈ t, P j z) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    rw [Finset.sup_empty]
    exact (Filter.Germ.coe_eq.2 (Eventually.of_forall fun z ↦ by simp)).symm
  | insert a t ha ih =>
    rw [Finset.sup_insert, ih]
    exact Filter.Germ.coe_eq.2 (Eventually.of_forall fun z ↦ by simp)

/-- A chosen representative of an analytic germ. -/
def ancrs_rep {n : ℕ} (g : AnalyticGerm n) : (Fin n → ℂ) → ℂ := g.property.choose

theorem ancrs_rep_analyticAt {n : ℕ} (g : AnalyticGerm n) : AnalyticAt ℂ (ancrs_rep g) 0 :=
  g.property.choose_spec.1

theorem ancrs_rep_germ {n : ℕ} (g : AnalyticGerm n) : Filter.Germ.ofFun (ancrs_rep g) = g.val :=
  g.property.choose_spec.2

theorem ancrs_zero_eq {n : ℕ} (g : AnalyticGerm n) :
    adim2_zero n g = Filter.Germ.ofFun (fun z ↦ ancrs_rep g z = 0) := by
  rw [adim2_zero, ← ancrs_rep_germ g]
  rfl

section Ring

variable {R : Type*} [CommRing R]

/-- A minimal prime of `I` realizing the (finite) Krull dimension of `R ⧸ I`. -/
theorem ancrs_exists_minimalPrime_dim (I : Ideal R) {D : ℕ}
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
theorem ancrs_dim_sup_lt {P J : Ideal R} [hP : P.IsPrime] {h : R} (hhJ : h ∈ J) (hhP : h ∉ P) :
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
theorem ancrs_val_sum_mul {n m : ℕ} (c g : Fin m → AnalyticGerm n) (f : Fin m → (Fin n → ℂ) → ℂ)
    (hrep : ∀ j, Filter.Germ.ofFun (f j) = (g j).val) :
    (∑ j, c j * g j).val = Filter.Germ.ofFun (fun z ↦ ∑ j, ancrs_rep (c j) z * f j z) := by
  have h1 : (∑ j, c j * g j).val = ∑ j, (c j).val * (g j).val := by
    rw [AddSubmonoidClass.coe_finsetSum]; rfl
  rw [h1]
  have h2 : (fun z ↦ ∑ j, ancrs_rep (c j) z * f j z) = ∑ j, ancrs_rep (c j) * f j := by
    funext z; simp
  rw [h2]
  change _ = Filter.Germ.coeRingHom _ (∑ j, ancrs_rep (c j) * f j)
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_mul]
  change _ = Filter.Germ.ofFun (ancrs_rep (c j)) * Filter.Germ.ofFun (f j)
  rw [ancrs_rep_germ, hrep]

/-- Elements of an ideal vanish near the origin on the common zeros of representatives of its
generators. -/
theorem ancrs_vanish_of_mem {n m : ℕ} {P : Ideal (AnalyticGerm n)} {g : Fin m → AnalyticGerm n}
    (hgen : Ideal.span (Set.range g) = P) {f : Fin m → (Fin n → ℂ) → ℂ}
    (hrep : ∀ j, Filter.Germ.ofFun (f j) = (g j).val) {h : AnalyticGerm n} (hh : h ∈ P)
    {H : (Fin n → ℂ) → ℂ} (hH : Filter.Germ.ofFun H = h.val) :
    ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), (∀ j, f j z = 0) → H z = 0 := by
  rw [← hgen] at hh
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hh
  have hval : h.val = Filter.Germ.ofFun (fun z ↦ ∑ j, ancrs_rep (c j) z * f j z) := by
    rw [← hc]
    exact ancrs_val_sum_mul c g f hrep
  have := Filter.Germ.coe_eq.1 (hH.trans hval)
  filter_upwards [this] with z hz h0
  rw [hz]
  simp [h0]

section RepPoly

open Polynomial

/-- A polynomial over the analytic germs, with its coefficients replaced by chosen representatives:
a polynomial over the functions on `ℂᵈ`. -/
def ancrs_repPoly {d : ℕ} (T : Polynomial (AnalyticGerm d)) : Polynomial ((Fin d → ℂ) → ℂ) :=
  ∑ i ∈ Finset.range (T.natDegree + 1), monomial i (ancrs_rep (T.coeff i))

/-- The representative polynomial evaluated at a point `w` of `ℂᵈ`: a polynomial over `ℂ`. -/
def ancrs_evPoly {d : ℕ} (T : Polynomial (AnalyticGerm d)) (w : Fin d → ℂ) : Polynomial ℂ :=
  (ancrs_repPoly T).map (Pi.evalRingHom (fun _ : Fin d → ℂ ↦ ℂ) w)

theorem ancrs_evPoly_eval {d : ℕ} (T : Polynomial (AnalyticGerm d)) (w : Fin d → ℂ) (t : ℂ) :
    (ancrs_evPoly T w).eval t =
      ∑ i ∈ Finset.range (T.natDegree + 1), ancrs_rep (T.coeff i) w * t ^ i := by
  simp [ancrs_evPoly, ancrs_repPoly, Polynomial.map_sum, eval_finsetSum, eval_monomial]

theorem ancrs_repPoly_map {d : ℕ} (T : Polynomial (AnalyticGerm d)) :
    (ancrs_repPoly T).map (Filter.Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
      T.map (AnalyticGerm d).subtype := by
  ext i
  rw [coeff_map, coeff_map, ancrs_repPoly, finsetSum_coeff]
  simp only [coeff_monomial, Finset.sum_ite_eq', Finset.mem_range]
  split_ifs with hi
  · exact ancrs_rep_germ _
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    rfl

/-- The representative of a `θ`-evaluation: an element of `𝒪ₙ` mapping to `T(θ)(v)` whose
representative is `z ↦ T(π z)(ℓ z)`. -/
theorem ancrs_eval₂_rep {n d : ℕ} {P : Ideal (AnalyticGerm n)} (π : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ))
    (θ : AnalyticGerm d →+* (AnalyticGerm n ⧸ P))
    (hcomp : ∀ (a : AnalyticGerm d) (h : (Fin d → ℂ) → ℂ),
      AnalyticAt ℂ h 0 → Filter.Germ.ofFun h = a.val → ∀ b : AnalyticGerm n,
      Filter.Germ.ofFun (fun z ↦ h (π z)) = b.val → θ a = Ideal.Quotient.mk P b)
    (T : Polynomial (AnalyticGerm d)) (v : AnalyticGerm n) {L : (Fin n → ℂ) → ℂ}
    (hv : v.val = Filter.Germ.ofFun L) :
    ∃ H : AnalyticGerm n, Ideal.Quotient.mk P H = T.eval₂ θ (Ideal.Quotient.mk P v) ∧
      H.val = Filter.Germ.ofFun (fun z ↦ (ancrs_evPoly T (π z)).eval (L z)) := by
  let b : ℕ → AnalyticGerm n := fun i ↦
    ⟨Filter.Germ.ofFun (fun z ↦ ancrs_rep (T.coeff i) (π z)), _,
      (ancrs_rep_analyticAt _).comp_of_eq (π.analyticAt 0) (map_zero π), rfl⟩
  refine ⟨∑ i ∈ Finset.range (T.natDegree + 1), b i * v ^ i, ?_, ?_⟩
  · rw [eval₂_eq_sum_range, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, map_pow,
      hcomp (T.coeff i) (ancrs_rep _) (ancrs_rep_analyticAt _) (ancrs_rep_germ _)
      (b i) rfl]
  · have : (fun z ↦ (ancrs_evPoly T (π z)).eval (L z)) =
        ∑ i ∈ Finset.range (T.natDegree + 1), (fun z ↦ ancrs_rep (T.coeff i) (π z)) * L ^ i := by
      funext z
      rw [ancrs_evPoly_eval, Finset.sum_apply]
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
theorem ancrs_bezout_rep {d : ℕ} (Q B C : Polynomial (AnalyticGerm d)) (δ : AnalyticGerm d)
    (h : B * Q + C * Q.derivative = Polynomial.C δ) :
    ∀ᶠ w in 𝓝 (0 : Fin d → ℂ), ∀ t,
      (ancrs_evPoly B w).eval t * (ancrs_evPoly Q w).eval t +
        (ancrs_evPoly C w).eval t * (ancrs_evPoly Q w).derivative.eval t = ancrs_rep δ w := by
  let E := ancrs_repPoly B * ancrs_repPoly Q + ancrs_repPoly C * derivative (ancrs_repPoly Q) -
    Polynomial.C (ancrs_rep δ)
  have hE : E.map (Filter.Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) = 0 := by
    have h1 : E.map (Filter.Germ.coeRingHom (𝓝 (0 : Fin d → ℂ))) =
        (B * Q + C * Q.derivative - Polynomial.C δ).map (AnalyticGerm d).subtype := by
      simp only [E, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
        ← Polynomial.derivative_map, ancrs_repPoly_map]
      congr 2
      exact ancrs_rep_germ δ
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
  simp only [ancrs_evPoly, Polynomial.derivative_map]
  exact this

end RepPoly

section Branch

open Polynomial

/-- The open set where the representatives of the coefficients of `T` are analytic. -/
def ancrs_polyDom {d : ℕ} (T : Polynomial (AnalyticGerm d)) : Set (Fin d → ℂ) :=
  ⋂ i ∈ Finset.range (T.natDegree + 1), {w | AnalyticAt ℂ (ancrs_rep (T.coeff i)) w}

theorem ancrs_isOpen_polyDom {d : ℕ} (T : Polynomial (AnalyticGerm d)) : IsOpen (ancrs_polyDom T) :=
  isOpen_biInter_finset fun _ _ ↦ isOpen_analyticAt ℂ _

theorem ancrs_zero_mem_polyDom {d : ℕ} (T : Polynomial (AnalyticGerm d)) :
    (0 : Fin d → ℂ) ∈ ancrs_polyDom T :=
  mem_iInter₂.2 fun _ _ ↦ ancrs_rep_analyticAt _

/-- On its domain, the representative polynomial is jointly analytic in `(w, t)`. -/
theorem ancrs_evPoly_analyticAt {d : ℕ} (T : Polynomial (AnalyticGerm d)) {w : Fin d → ℂ}
    (hw : w ∈ ancrs_polyDom T) (t : ℂ) :
    AnalyticAt ℂ (fun u : (Fin d → ℂ) × ℂ ↦ (ancrs_evPoly T u.1).eval u.2) (w, t) := by
  have : (fun u : (Fin d → ℂ) × ℂ ↦ (ancrs_evPoly T u.1).eval u.2) =
      fun u ↦ ∑ i ∈ Finset.range (T.natDegree + 1), ancrs_rep (T.coeff i) u.1 * u.2 ^ i := by
    funext u; rw [ancrs_evPoly_eval]
  rw [this]
  refine Finset.analyticAt_fun_sum _ fun i hi ↦ ?_
  have hai : AnalyticAt ℂ (ancrs_rep (T.coeff i)) w := mem_iInter₂.1 hw i hi
  exact (hai.comp analyticAt_fst).mul (analyticAt_snd.pow i)

/-- **Analytic root branch.** At a simple root `t₀` of the representative polynomial at `w₀`,
there is an analytic branch `τ` of roots through `(w₀, t₀)`, and near `(w₀, t₀)` the roots are
exactly the branch. -/
theorem ancrs_root_branch {d : ℕ} (T : Polynomial (AnalyticGerm d)) {w₀ : Fin d → ℂ}
    (hw₀ : w₀ ∈ ancrs_polyDom T) {t₀ : ℂ} (hroot : (ancrs_evPoly T w₀).eval t₀ = 0)
    (hsimple : (ancrs_evPoly T w₀).derivative.eval t₀ ≠ 0) :
    ∃ τ : (Fin d → ℂ) → ℂ, AnalyticAt ℂ τ w₀ ∧ τ w₀ = t₀ ∧
      ∃ U : Set ((Fin d → ℂ) × ℂ), IsOpen U ∧ (w₀, t₀) ∈ U ∧
        ∀ u ∈ U, ((ancrs_evPoly T u.1).eval u.2 = 0 ↔ τ u.1 = u.2) := by
  set F : (Fin d → ℂ) × ℂ → ℂ := fun u ↦ (ancrs_evPoly T u.1).eval u.2
  have hFa := ancrs_evPoly_analyticAt T hw₀ t₀
  have cdf : ContDiffAt ℂ ω F (w₀, t₀) := hFa.contDiffAt
  have pn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  set c := (ancrs_evPoly T w₀).derivative.eval t₀
  have hder : fderiv ℂ F (w₀, t₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ =
      (1 : ℂ →L[ℂ] ℂ).smulRight c := by
    have h1 : HasFDerivAt (fun t ↦ F (w₀, t))
        (fderiv ℂ F (w₀, t₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ) t₀ :=
      hFa.differentiableAt.hasFDerivAt.comp t₀ (hasFDerivAt_prodMk_right w₀ t₀)
    have h2 : HasFDerivAt (fun t ↦ F (w₀, t)) ((1 : ℂ →L[ℂ] ℂ).smulRight c) t₀ :=
      (Polynomial.hasDerivAt (ancrs_evPoly T w₀) t₀).hasFDerivAt
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
theorem ancrs_proper_nhds {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}
    (hf : IsProperMap f) {y : Y} {N : Set X} (hN : IsOpen N) (hfib : f ⁻¹' {y} ⊆ N) :
    ∃ M : Set Y, IsOpen M ∧ y ∈ M ∧ f ⁻¹' M ⊆ N := by
  refine ⟨(f '' Nᶜ)ᶜ, (hf.isClosedMap _ hN.isClosed_compl).isOpen_compl, ?_, fun x hx ↦ ?_⟩
  · rintro ⟨x, hx, rfl⟩
    exact hx (hfib rfl)
  · by_contra hxN
    exact hx ⟨x, hxN, rfl⟩

/-- Generators of an ideal of analytic germs with representatives analytic on a common open
neighbourhood of the origin; their common zeros represent the zero germ of the ideal. -/
theorem ancrs_generators {n : ℕ} (P : Ideal (AnalyticGerm n)) :
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
  let f : Fin gs.card → (Fin n → ℂ) → ℂ := fun j ↦ ancrs_rep (g j)
  refine ⟨gs.card, g, f, ⋂ j, {z | AnalyticAt ℂ (f j) z}, by rw [hrange, hgs],
    fun j ↦ ancrs_rep_germ (g j), isOpen_iInter_of_finite fun j ↦ isOpen_analyticAt ℂ (f j),
    mem_iInter.2 fun j ↦ ancrs_rep_analyticAt (g j), fun j z hz ↦ mem_iInter.1 hz j, ?_⟩
  rw [adim2_zeroSet, Finset.inf_congr rfl fun g _ ↦ ancrs_zero_eq g, ancrs_germ_finset_inf]
  refine Filter.Germ.coe_eq.2 (Eventually.of_forall fun z ↦
    propext ⟨fun h j ↦ ?_, fun h x hx ↦ ?_⟩)
  · exact h _ (e.symm j).2
  · have := h (e ⟨x, hx⟩)
    simpa [f, g] using this


/-- **Finite fibres give an injective derivative.** An analytic map on an open nonempty
`V ⊆ ℂᵈ` all of whose fibres in `V` are finite has an injective derivative at some point of `V`:
at a point of maximal rank `r < d` a level set would contain a ball of a kernel. -/
theorem ancrs_exists_injective_of_finite_fibres {d e : ℕ} {V : Set (Fin d → ℂ)} (hV : IsOpen V)
    (hne : V.Nonempty) {g : (Fin d → ℂ) → (Fin e → ℂ)} (hg : AnalyticOnNhd ℂ g V)
    (hfin : ∀ w, {v | v ∈ V ∧ g v = w}.Finite) :
    ∃ v ∈ V, Function.Injective (fderiv ℂ g v) := by
  by_contra hno
  push Not at hno
  let rk : (Fin d → ℂ) → ℕ := fun v ↦
    Module.finrank ℂ (LinearMap.range (fderiv ℂ g v : (Fin d → ℂ) →ₗ[ℂ] (Fin e → ℂ)))
  have hrk_lt : ∀ v ∈ V, rk v < d := by
    intro v hv
    have h0 := LinearMap.finrank_range_add_finrank_ker
      (fderiv ℂ g v : (Fin d → ℂ) →ₗ[ℂ] (Fin e → ℂ))
    rw [Module.finrank_fin_fun] at h0
    have hker : LinearMap.ker (fderiv ℂ g v : (Fin d → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ ⊥ := by
      intro hbot
      exact hno v hv (LinearMap.ker_eq_bot.1 hbot)
    have hpos : 0 < Module.finrank ℂ
        (LinearMap.ker (fderiv ℂ g v : (Fin d → ℂ) →ₗ[ℂ] (Fin e → ℂ))) :=
      Nat.pos_of_ne_zero fun h ↦ hker (Submodule.finrank_eq_zero.1 h)
    change Module.finrank ℂ _ < d
    omega
  have hbdd : BddAbove (rk '' V) := ⟨d, by rintro _ ⟨v, hv, rfl⟩; exact (hrk_lt v hv).le⟩
  obtain ⟨v0, hv0, hv0r⟩ := Nat.sSup_mem (hne.image rk) hbdd
  set r := sSup (rk '' V)
  have hmax : ∀ v ∈ V, rk v ≤ r := fun v hv ↦ le_csSup hbdd ⟨v, hv, rfl⟩
  have hrd : r < d := hv0r ▸ hrk_lt v0 hv0
  -- a linear map making `L ∘ g` a submersion at `v0`
  set D0 := fderiv ℂ g v0
  let R0 := LinearMap.range (D0 : (Fin d → ℂ) →ₗ[ℂ] (Fin e → ℂ))
  obtain ⟨prj, hprj⟩ := R0.subtype.exists_leftInverse_of_injective (Submodule.ker_subtype R0)
  have hR0 : Module.finrank ℂ R0 = Module.finrank ℂ (Fin r → ℂ) := by
    rw [Module.finrank_fin_fun, ← hv0r]
  let eqv : R0 ≃ₗ[ℂ] (Fin r → ℂ) := LinearEquiv.ofFinrankEq _ _ hR0
  let L : (Fin e → ℂ) →L[ℂ] (Fin r → ℂ) := LinearMap.toContinuousLinearMap (eqv.toLinearMap ∘ₗ prj)
  have hLsurj : Function.Surjective (L ∘L D0) := by
    intro y
    obtain ⟨u, hu⟩ := (eqv.symm y).2
    refine ⟨u, ?_⟩
    have h1 : D0 u = R0.subtype (eqv.symm y) := hu
    rw [ContinuousLinearMap.comp_apply]
    change eqv (prj (D0 u)) = y
    rw [h1, ← LinearMap.comp_apply prj, hprj, LinearMap.id_apply, LinearEquiv.apply_symm_apply]
  -- the kernel and a projection onto it
  let K := LinearMap.ker ((L ∘L D0 : (Fin d → ℂ) →L[ℂ] (Fin r → ℂ)) :
    (Fin d → ℂ) →ₗ[ℂ] (Fin r → ℂ))
  have hrange : LinearMap.range ((L ∘L D0 : (Fin d → ℂ) →L[ℂ] (Fin r → ℂ)) :
      (Fin d → ℂ) →ₗ[ℂ] (Fin r → ℂ)) = ⊤ := LinearMap.range_eq_top.2 hLsurj
  have hK : Module.finrank ℂ K + r = d := by
    have h0 := LinearMap.finrank_range_add_finrank_ker
      ((L ∘L D0 : (Fin d → ℂ) →L[ℂ] (Fin r → ℂ)) : (Fin d → ℂ) →ₗ[ℂ] (Fin r → ℂ))
    have h1 : Module.finrank ℂ (LinearMap.range ((L ∘L D0 : (Fin d → ℂ) →L[ℂ] (Fin r → ℂ)) :
        (Fin d → ℂ) →ₗ[ℂ] (Fin r → ℂ))) = r := by
      rw [hrange, finrank_top, Module.finrank_fin_fun]
    have h2 : Module.finrank ℂ (Fin d → ℂ) = d := Module.finrank_fin_fun ℂ
    have h3 : Module.finrank ℂ (LinearMap.range ((L ∘L D0 : (Fin d → ℂ) →L[ℂ] (Fin r → ℂ)) :
        (Fin d → ℂ) →ₗ[ℂ] (Fin r → ℂ))) + Module.finrank ℂ K = Module.finrank ℂ (Fin d → ℂ) :=
      h0
    omega
  obtain ⟨Pr₀, hPr₀⟩ := K.subtype.exists_leftInverse_of_injective (Submodule.ker_subtype K)
  let Pr : (Fin d → ℂ) →L[ℂ] K := LinearMap.toContinuousLinearMap Pr₀
  have hPrK : ∀ k : K, Pr k = k := fun k ↦ by
    change Pr₀ (K.subtype k) = k
    rw [← LinearMap.comp_apply, hPr₀, LinearMap.id_apply]
  -- the map `Φ = (L ∘ g, Pr)` and its derivative
  let Φ : (Fin d → ℂ) → (Fin r → ℂ) × K := fun v ↦ (L (g v), Pr v)
  have hΦa : AnalyticOnNhd ℂ Φ V := fun v hv ↦
    ((L.analyticAt _).comp (hg v hv)).prod (Pr.analyticAt v)
  have hΦd : ∀ v ∈ V, HasFDerivAt Φ ((L ∘L fderiv ℂ g v).prod Pr) v := fun v hv ↦
    (L.hasFDerivAt.comp v ((hg v hv).differentiableAt.hasFDerivAt)).prodMk Pr.hasFDerivAt
  have hdimΦ : Module.finrank ℂ (Fin d → ℂ) = Module.finrank ℂ ((Fin r → ℂ) × K) := by
    rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun]; omega
  have hinj0 : Function.Injective ((L ∘L D0).prod Pr) := by
    refine (injective_iff_map_eq_zero _).2 fun u hu ↦ ?_
    have h1 : (L ∘L D0) u = 0 := congrArg Prod.fst hu
    have h2 : Pr u = 0 := congrArg Prod.snd hu
    have huK : u ∈ K := h1
    have := hPrK ⟨u, huK⟩
    rw [h2] at this
    exact congrArg Subtype.val this.symm
  let e0 : (Fin d → ℂ) ≃L[ℂ] (Fin r → ℂ) × K :=
    (LinearMap.linearEquivOfInjective _ hinj0 hdimΦ).toContinuousLinearEquiv
  have he0 : ((e0 : (Fin d → ℂ) →L[ℂ] (Fin r → ℂ) × K)) = (L ∘L D0).prod Pr := by
    exact ContinuousLinearMap.ext fun u ↦ rfl
  -- the local inverse of `Φ` at `v0`
  have hΦc : ContDiffAt ℂ ω Φ v0 := (hΦa v0 hv0).contDiffAt
  have hΦd0 : HasFDerivAt Φ (e0 : (Fin d → ℂ) →L[ℂ] (Fin r → ℂ) × K) v0 := by
    rw [he0]; exact hΦd v0 hv0
  let T := hΦc.toOpenPartialHomeomorph Φ hΦd0 (by simp)
  have hTcoe : (T : (Fin d → ℂ) → (Fin r → ℂ) × K) = Φ := rfl
  have hv0T : v0 ∈ T.source := hΦc.mem_toOpenPartialHomeomorph_source hΦd0 (by simp)
  let Inv := range ((↑) : ((Fin d → ℂ) ≃L[ℂ] (Fin r → ℂ) × K) →
    ((Fin d → ℂ) →L[ℂ] (Fin r → ℂ) × K))
  have hInv : IsOpen Inv := ContinuousLinearEquiv.isOpen
  let U1 := (V ∩ fderiv ℂ Φ ⁻¹' Inv) ∩ T.source
  have hU1 : IsOpen U1 :=
    (hΦa.fderiv.continuousOn.isOpen_inter_preimage hV hInv).inter T.open_source
  have hv0U1 : v0 ∈ U1 := ⟨⟨hv0, ⟨e0, hΦd0.fderiv.symm⟩⟩, hv0T⟩
  let sl : K → (Fin r → ℂ) × K := fun k ↦ (L (g v0), k)
  have hsl : Continuous sl := continuous_const.prodMk continuous_id
  have hslv0 : sl (Pr v0) = Φ v0 := rfl
  have hQ : {k | sl k ∈ T.target ∧ T.symm (sl k) ∈ U1} ∈ 𝓝 (Pr v0) := by
    have h1 : T.target ∈ 𝓝 (Φ v0) := T.open_target.mem_nhds (T.map_source hv0T)
    have h2 : T.symm ⁻¹' U1 ∈ 𝓝 (Φ v0) := by
      refine (T.continuousAt_symm (T.map_source hv0T)).preimage_mem_nhds ?_
      rw [T.left_inv hv0T]
      exact hU1.mem_nhds hv0U1
    exact hsl.continuousAt.preimage_mem_nhds (hslv0 ▸ Filter.inter_mem h1 h2)
  obtain ⟨ε, hε, hεQ⟩ := Metric.mem_nhds_iff.1 hQ
  let Γ : K → (Fin d → ℂ) := fun k ↦ T.symm (sl k)
  -- along the level set, `g` has zero derivative
  have hzero : ∀ k ∈ Metric.ball (Pr v0) ε,
      HasFDerivAt (g ∘ Γ) (0 : K →L[ℂ] (Fin e → ℂ)) k := by
    intro k hk
    obtain ⟨hkT, hkU⟩ := hεQ hk
    set x := Γ k
    obtain ⟨⟨hxV, ex, hex⟩, -⟩ := hkU
    have hfdx : fderiv ℂ Φ x = (L ∘L fderiv ℂ g x).prod Pr := (hΦd x hxV).fderiv
    have hΦx : HasFDerivAt Φ (ex : (Fin d → ℂ) →L[ℂ] (Fin r → ℂ) × K) x := by
      rw [hex]; exact (hΦd x hxV).differentiableAt.hasFDerivAt
    have hexu : ∀ u, ex u = ((L ∘L fderiv ℂ g x) u, Pr u) := fun u ↦ by
      have := congrArg (fun F : (Fin d → ℂ) →L[ℂ] (Fin r → ℂ) × K ↦ F u) (hex.trans hfdx)
      exact this
    -- the kernels of `Dg x` and `L ∘ Dg x` agree
    let A : (Fin d → ℂ) →ₗ[ℂ] (Fin e → ℂ) := fderiv ℂ g x
    let B : (Fin d → ℂ) →ₗ[ℂ] (Fin r → ℂ) := (L ∘L fderiv ℂ g x : (Fin d → ℂ) →L[ℂ] _)
    have hBsurj : LinearMap.range B = ⊤ := by
      refine LinearMap.range_eq_top.2 fun y ↦ ⟨ex.symm (y, 0), ?_⟩
      have := hexu (ex.symm (y, 0))
      rw [ContinuousLinearEquiv.apply_symm_apply] at this
      exact (congrArg Prod.fst this).symm
    have hBA : B = (L : (Fin e → ℂ) →ₗ[ℂ] (Fin r → ℂ)) ∘ₗ A := rfl
    have hrB : Module.finrank ℂ (LinearMap.range B) = r := by
      rw [hBsurj, finrank_top, Module.finrank_fin_fun]
    have hrA : Module.finrank ℂ (LinearMap.range A) = r := by
      refine le_antisymm (hmax x hxV) ?_
      rw [← hrB, hBA, LinearMap.range_comp]
      exact Submodule.finrank_map_le _ _
    have hker : LinearMap.ker A = LinearMap.ker B := by
      refine Submodule.eq_of_le_of_finrank_eq (hBA ▸ LinearMap.ker_le_ker_comp A _) ?_
      have h1 := LinearMap.finrank_range_add_finrank_ker A
      have h2 := LinearMap.finrank_range_add_finrank_ker B
      omega
    -- the derivative of `Γ` and of `g ∘ Γ`
    have hsld : HasFDerivAt sl ((0 : K →L[ℂ] (Fin r → ℂ)).prod (ContinuousLinearMap.id ℂ K)) k :=
      (hasFDerivAt_const _ _).prodMk (hasFDerivAt_id _)
    have hΓd : HasFDerivAt Γ ((ex.symm : (Fin r → ℂ) × K →L[ℂ] (Fin d → ℂ)) ∘L
        ((0 : K →L[ℂ] (Fin r → ℂ)).prod (ContinuousLinearMap.id ℂ K))) k :=
      (T.hasFDerivAt_symm hkT hΦx).comp k hsld
    have hgΓ := ((hg x hxV).differentiableAt.hasFDerivAt).comp k hΓd
    convert hgΓ using 1
    ext1 κ
    simp only [zero_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply]
    set u := ex.symm (0, κ)
    have hu := hexu u
    rw [ContinuousLinearEquiv.apply_symm_apply] at hu
    have huB : u ∈ LinearMap.ker B := (congrArg Prod.fst hu).symm
    rw [← hker] at huB
    exact huB.symm
  -- hence `g` is constant along the level set
  have hΓ0 : Γ (Pr v0) = v0 := T.left_inv hv0T
  have hconst : ∀ k ∈ Metric.ball (Pr v0) ε, g (Γ k) = g v0 := by
    intro k hk
    rw [← hΓ0]
    refine (convex_ball (Pr v0) ε).is_const_of_fderivWithin_eq_zero
      (fun k' hk' ↦ (hzero k' hk').differentiableAt.differentiableWithinAt) (fun k' hk' ↦ ?_)
      hk (Metric.mem_ball_self hε)
    rw [fderivWithin_of_isOpen Metric.isOpen_ball hk']
    exact (hzero k' hk').fderiv
  -- the ball is infinite and `Γ` is injective on it
  have hKpos : 0 < Module.finrank ℂ K := by omega
  obtain ⟨k1, hk1⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hKpos
  have hk1n : 0 < ‖k1‖ := norm_pos_iff.2 hk1
  let c : ℕ → ℝ := fun m ↦ ε / (2 * ‖k1‖ * (m + 1))
  let f : ℕ → K := fun m ↦ Pr v0 + ((c m : ℝ) : ℂ) • k1
  have hfball : ∀ m, f m ∈ Metric.ball (Pr v0) ε := by
    intro m
    rw [Metric.mem_ball, dist_eq_norm]
    simp only [f, add_sub_cancel_left, norm_smul, Complex.norm_real, Real.norm_eq_abs]
    have hc : 0 < c m := by positivity
    rw [abs_of_pos hc]
    calc c m * ‖k1‖ = ε / (2 * (m + 1)) := by
          simp only [c]; field_simp
      _ < ε := by
          rw [div_lt_iff₀ (by positivity)]
          nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hfinj : Function.Injective (Γ ∘ f) := by
    intro m m' hmm'
    have h1 : sl (f m) = sl (f m') :=
      T.symm.injOn (hεQ (hfball m)).1 (hεQ (hfball m')).1 hmm'
    have h2 : ((c m : ℝ) : ℂ) • k1 = ((c m' : ℝ) : ℂ) • k1 := by
      have := congrArg Prod.snd h1
      simpa [sl, f] using this
    have h3 : ((c m : ℝ) : ℂ) = ((c m' : ℝ) : ℂ) := smul_left_injective ℂ hk1 h2
    have h4 : c m = c m' := Complex.ofReal_injective h3
    simp only [c] at h4
    have : (2 * ‖k1‖ * (m + 1) : ℝ) = 2 * ‖k1‖ * (m' + 1) := by
      field_simp at h4
      nlinarith [h4]
    have : (m : ℝ) = m' := by nlinarith [this]
    exact_mod_cast this
  refine (Set.infinite_of_injective_forall_mem hfinj fun m ↦ ?_) (hfin (g v0))
  exact ⟨(hεQ (hfball m)).2.1.1, hconst _ (hfball m)⟩


end HodgeLean.Foundations.Analytic
