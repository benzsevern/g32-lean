import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceDefs

/-! # The finite mapping theorem: local elimination of fibre variables

Helpers for `an_finite_projection` and `an_finite_mapping`, prefixed `anf_`.

* `anf_IsAnalyticNear S y₀`: near `y₀`, the set `S` is the common zero set of finitely many
  functions analytic on a neighbourhood of `y₀`. It is local (`anf_IsAnalyticNear.congr`), stable
  under finite unions (`anf_isAnalyticNear_iUnion`) and transported by continuous linear
  equivalences.
* Common roots: for a monic `P(y, w) = w ^ d + ∑ a_j(y) w ^ j` and remainders
  `R_i(y, w) = ∑ b_{ij}(y) w ^ j`, the set of `y` where `P(y, ·)` and all `R_i(y, ·)` have a common
  root is cut out by the coefficients in `Λ` of the resultant of `P` and `∑ Λ ^ i R_i`
  (`anf_commonRoot_equations`).
* One variable: if `(y₀, a)` is isolated in its fibre of a locally analytic set `A ⊆ ℂⁿ × ℂ`, then
  for small `ε` the set of `y` with a point `(y, t) ∈ A`, `|t - a| < ε`, is analytic near `y₀`:
  Weierstrass preparation of an equation not vanishing on the fibre, division of the others, and
  common roots (`anf_eliminate_one`).
* Several variables, by induction (`anf_eliminate`), and the shrinking lemma
  (`anf_eventually_near`) which makes the radius of the fibre ball irrelevant.

HC no distance; AV milestone no distance.
-/

noncomputable section

open Set Filter Topology Metric Polynomial

namespace HodgeLean.Foundations.Analytic

open HodgeLean.Foundations
open HodgeLean.Foundations.AnalyticDivisorAlgebraic4
open HodgeLean.Foundations.AnalyticDivisorAlgebraic5

/-! ### Sets analytic near a point -/

section Near

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- `S` is *analytic near* `y₀`: on an open neighbourhood `V` of `y₀` it is the common zero set of
finitely many functions analytic on `V`. (Nothing is asked of `S` outside `V`.)
Source: Gunning–Rossi, *Analytic Functions of Several Complex Variables*, Ch. III, §A,
Definition 1 (analytic sets, locally the common zeros of finitely many holomorphic functions). -/
def anf_IsAnalyticNear (S : Set E) (y₀ : E) : Prop :=
  ∃ V : Set E, IsOpen V ∧ y₀ ∈ V ∧ ∃ (κ : Type) (_ : Finite κ) (g : κ → E → ℂ),
    (∀ l, AnalyticOnNhd ℂ (g l) V) ∧ ∀ y ∈ V, (y ∈ S ↔ ∀ l, g l y = 0)

example (y₀ : E) : anf_IsAnalyticNear (univ : Set E) y₀ :=
  ⟨univ, isOpen_univ, mem_univ _, Empty, inferInstance, Empty.elim, fun l ↦ l.elim,
    fun _ _ ↦ by simp⟩

/-- Being analytic near a point depends only on the set near that point. -/
theorem anf_IsAnalyticNear.congr {S S' : Set E} {y₀ : E} (h : anf_IsAnalyticNear S y₀)
    (hSS' : ∀ᶠ y in 𝓝 y₀, (y ∈ S ↔ y ∈ S')) : anf_IsAnalyticNear S' y₀ := by
  obtain ⟨V, hV, hy₀, κ, hκ, g, hg, hS⟩ := h
  obtain ⟨W, hWS, hW, hy₀W⟩ := _root_.eventually_nhds_iff.1 hSS'
  exact ⟨V ∩ W, hV.inter hW, ⟨hy₀, hy₀W⟩, κ, hκ, g, fun l ↦ (hg l).mono inter_subset_left,
    fun y hy ↦ (hWS y hy.2).symm.trans (hS y hy.1)⟩

/-- A finite union of sets analytic near `y₀` is analytic near `y₀`: take all products of one
equation from each set. -/
theorem anf_isAnalyticNear_iUnion {ι : Type*} [Finite ι] {S : ι → Set E} {y₀ : E}
    (h : ∀ i, anf_IsAnalyticNear (S i) y₀) : anf_IsAnalyticNear (⋃ i, S i) y₀ := by
  classical
  choose V hV hy₀ κ hκ g hg hS using h
  have : ∀ i, Finite (κ i) := hκ
  have := Fintype.ofFinite ι
  obtain ⟨N, ⟨e⟩⟩ := Finite.exists_equiv_fin (∀ i, κ i)
  refine ⟨⋂ i, V i, isOpen_iInter_of_finite hV, mem_iInter.2 hy₀, Fin N, inferInstance,
    fun l y ↦ ∏ i, g i (e.symm l i) y, fun l ↦ ?_, fun y hy ↦ ?_⟩
  · exact Finset.analyticOnNhd_fun_prod _ fun i _ ↦ (hg i _).mono (iInter_subset _ i)
  · have hyV : ∀ i, y ∈ V i := mem_iInter.1 hy
    simp only [mem_iUnion, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi⟩ l
      exact ⟨i, (hS i y (hyV i)).1 hi _⟩
    · intro hφ
      by_contra hne
      push Not at hne
      have : ∀ i, ∃ l, g i l y ≠ 0 := fun i ↦ by
        by_contra hall
        push Not at hall
        exact hne i ((hS i y (hyV i)).2 hall)
      choose φ hφ' using this
      obtain ⟨i, hi⟩ := hφ (e φ)
      rw [Equiv.symm_apply_apply] at hi
      exact hφ' i hi

/-- Analytic near a point, pulled back along an analytic map. -/
theorem anf_IsAnalyticNear.preimage {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {φ : E → F} (hφ : ∀ y, AnalyticAt ℂ φ y) {S : Set F} {y₀ : E}
    (h : anf_IsAnalyticNear S (φ y₀)) : anf_IsAnalyticNear (φ ⁻¹' S) y₀ := by
  obtain ⟨V, hV, hy₀, κ, hκ, g, hg, hS⟩ := h
  have hc : Continuous φ := continuous_iff_continuousAt.2 fun y ↦ (hφ y).continuousAt
  exact ⟨φ ⁻¹' V, hV.preimage hc, hy₀, κ, hκ, fun l y ↦ g l (φ y),
    fun l y hy ↦ (hg l (φ y) hy).comp (hφ y), fun y hy ↦ hS (φ y) hy⟩

end Near

/-! ### Shrinking the fibre ball -/

section Shrink

variable {E F : Type*} [NormedAddCommGroup E] [ProperSpace E] [NormedAddCommGroup F]
  [ProperSpace F]

/-- **Points near an isolated point of the fibre stay near it.** Let `A ∩ (B̄(y₀, r) × B̄(a, r))` be
closed and `a` the only point of `B̄(a, r)` over `y₀`. Then for every `δ > 0` and `y` near `y₀`, the
points of `A` over `y` in `B̄(a, r)` lie in `B(a, δ)`: otherwise the compact set of points of
`A ∩ (B̄(y₀, r) × B̄(a, r))` at distance `≥ δ` from `a` projects onto a closed set containing
`y₀`. -/
theorem anf_eventually_near {A : Set (E × F)} {y₀ : E} {a : F} {r : ℝ} (hr : 0 < r)
    (hclosed : IsClosed (A ∩ closedBall y₀ r ×ˢ closedBall a r))
    (hiso : ∀ w ∈ closedBall a r, (y₀, w) ∈ A → w = a) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ y in 𝓝 y₀, ∀ w ∈ closedBall a r, (y, w) ∈ A → dist w a < δ := by
  set K : Set (E × F) := (A ∩ closedBall y₀ r ×ˢ closedBall a r) ∩ {p | δ ≤ dist p.2 a}
  have hKc : IsCompact K := by
    refine ((isCompact_closedBall y₀ r).prod (isCompact_closedBall a r)).of_isClosed_subset
      (hclosed.inter (isClosed_le continuous_const (continuous_snd.dist continuous_const))) ?_
    exact fun p hp ↦ hp.1.2
  have hy₀ : y₀ ∉ Prod.fst '' K := by
    rintro ⟨⟨y, w⟩, ⟨⟨hA, -, hw⟩, hδw⟩, rfl⟩
    have := hiso w hw hA
    subst this
    simp only [mem_ofPred_eq, dist_self] at hδw
    linarith
  filter_upwards [ball_mem_nhds y₀ hr,
    (hKc.image continuous_fst).isClosed.isOpen_compl.mem_nhds hy₀] with y hy hyK w hw hA
  by_contra hlt
  push Not at hlt
  exact hyK ⟨(y, w), ⟨⟨hA, ball_subset_closedBall hy, hw⟩, hlt⟩, rfl⟩

end Shrink

/-! ### Common roots and resultants -/

section CommonRoot

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The ring of functions `E → ℂ` analytic on a neighbourhood of every point of `V`.
Source: Gunning–Rossi, *Analytic Functions of Several Complex Variables*, Ch. I, §A (sums and
products of holomorphic functions are holomorphic); Mathlib's `AnalyticOnNhd.add` and
`AnalyticOnNhd.mul`. -/
def anf_analyticSubring (V : Set E) : Subring (E → ℂ) where
  carrier := {g | AnalyticOnNhd ℂ g V}
  zero_mem' := analyticOnNhd_const
  one_mem' := analyticOnNhd_const
  add_mem' := fun ha hb ↦ ha.add hb
  neg_mem' := fun ha ↦ ha.neg
  mul_mem' := fun ha hb ↦ ha.mul hb

example (V : Set E) : (1 : E → ℂ) ∈ anf_analyticSubring V := (anf_analyticSubring V).one_mem

/-- A polynomial `∑_{i < s} c_i Λ ^ i` vanishes exactly when all its coefficients do. -/
theorem anf_sum_C_mul_X_pow_eq_zero {s : ℕ} (c : Fin s → ℂ) :
    ∑ i : Fin s, C (c i) * (X : ℂ[X]) ^ (i : ℕ) = 0 ↔ ∀ i, c i = 0 := by
  constructor
  · intro h i
    have := congrArg (fun q : ℂ[X] ↦ q.coeff i) h
    simp only [finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at this
    rwa [Finset.sum_eq_single i (fun j _ hj ↦ ite_eq_right fun h ↦ hj (Fin.ext h).symm)
      (fun h ↦ (h (Finset.mem_univ _)).elim), ite_eq_left rfl] at this
  · intro h
    simp [h]

/-- **Common roots are cut out by resultants.** For coefficient functions `a j`, `b i j` analytic
on `V ⊆ ℂⁿ`, the set of `y` at which `w ↦ w ^ d + ∑ a_j(y) w ^ j` and all the
`w ↦ ∑ b_{ij}(y) w ^ j` have a common root is the common zero set of finitely many functions
analytic on `V`: the coefficients in `Λ` of the resultant of `P` and `∑ Λ ^ i R_i`, which over `ℂ`
is `∏_{P(α) = 0} ∑_i R_i(α) Λ ^ i`. -/
theorem anf_commonRoot_equations {n d s : ℕ} {V : Set (Fin n → ℂ)}
    {a : Fin d → (Fin n → ℂ) → ℂ} {b : Fin s → Fin d → (Fin n → ℂ) → ℂ}
    (ha : ∀ j, AnalyticOnNhd ℂ (a j) V) (hb : ∀ i j, AnalyticOnNhd ℂ (b i j) V) :
    ∃ (L : ℕ) (h : Fin L → (Fin n → ℂ) → ℂ), (∀ l, AnalyticOnNhd ℂ (h l) V) ∧
      ∀ y, ((∃ w, monicInLast a (y, w) = 0 ∧ ∀ i, ∑ j, b i j y * w ^ (j : ℕ) = 0) ↔
        ∀ l, h l y = 0) := by
  classical
  set R := anf_analyticSubring V
  let aR : Fin d → R := fun j ↦ ⟨a j, ha j⟩
  let bR : Fin s → Fin d → R := fun i j ↦ ⟨b i j, hb i j⟩
  let P : R[X] := X ^ d + ∑ j, C (aR j) * X ^ (j : ℕ)
  let Q : R[X][X] := ∑ i, ∑ j, C (C (bR i j) * X ^ (i : ℕ)) * X ^ (j : ℕ)
  let ρ : R[X] := resultant (P.map C) Q d d
  refine ⟨ρ.natDegree + 1, fun l ↦ ((ρ.coeff l : R) : (Fin n → ℂ) → ℂ), fun l ↦ (ρ.coeff l).2,
    fun y ↦ ?_⟩
  let ev : R →+* ℂ := (Pi.evalRingHom (fun _ ↦ ℂ) y).comp R.subtype
  set p := monicPoly a y
  obtain ⟨hpm, hpd, hpe⟩ := spec_monicPoly a y
  have hP : P.map ev = p := by
    simp [P, p, monicPoly, Polynomial.map_sum, ev, aR]
  let Qy : ℂ[X][X] := ∑ i, ∑ j, C (C (b i j y) * X ^ (i : ℕ)) * X ^ (j : ℕ)
  have hQ : Q.map (mapRingHom ev) = Qy := by
    simp [Q, Qy, Polynomial.map_sum, ev, bR]
  have hρ : ρ.map ev = resultant (p.map C) Qy d d := by
    change mapRingHom ev ρ = _
    rw [← resultant_map_map, hQ, Polynomial.map_map, mapRingHom_comp_C, ← Polynomial.map_map,
      hP]
  set f : ℂ[X][X] := p.map C
  have hfs : f.Splits := (IsAlgClosed.splits p).map C
  have hfd : f.natDegree = d := by
    rw [natDegree_map_eq_of_injective C_injective, hpd]
  have hfl : f.leadingCoeff = 1 := (hpm.map C).leadingCoeff
  have hQd : Qy.natDegree ≤ d := by
    refine natDegree_sum_le_of_forall_le _ _ fun i _ ↦ natDegree_sum_le_of_forall_le _ _
      fun j _ ↦ (natDegree_C_mul_X_pow_le _ _).trans j.2.le
  have hroots : f.roots = p.roots.map C :=
    (roots_map_of_injective_of_card_eq_natDegree C_injective
      (IsAlgClosed.splits p).natDegree_eq_card_roots.symm).symm
  have heval : ∀ α : ℂ, Qy.eval (C α) =
      ∑ i : Fin s, C (∑ j, b i j y * α ^ (j : ℕ)) * X ^ (i : ℕ) := by
    intro α
    simp only [Qy, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, map_sum, map_mul,
      map_pow, Finset.sum_mul]
    have hc : ∀ (i : Fin s) (j : Fin d), C (b i j y) * (X : ℂ[X]) ^ (i : ℕ) * C α ^ (j : ℕ) =
        C (b i j y) * C α ^ (j : ℕ) * X ^ (i : ℕ) := fun i j ↦ by ring
    simp only [hc]
  have key : ρ.map ev = (p.roots.map fun α ↦ Qy.eval (C α)).prod := by
    have h := resultant_eq_prod_eval f Qy d hQd hfs
    rw [hfd] at h
    rw [hρ, h, hfl, one_pow, one_mul, hroots, Multiset.map_map]
    rfl
  have hzero : ρ.map ev = 0 ↔ ∀ l : Fin (ρ.natDegree + 1),
      ((ρ.coeff l : R) : (Fin n → ℂ) → ℂ) y = 0 := by
    constructor
    · intro h l
      have := congrArg (fun q : ℂ[X] ↦ q.coeff l) h
      simpa [coeff_map, ev] using this
    · intro h
      ext l
      rw [coeff_map, coeff_zero]
      by_cases hl : l ≤ ρ.natDegree
      · exact h ⟨l, Nat.lt_succ_of_le hl⟩
      · rw [coeff_eq_zero_of_natDegree_lt (not_le.1 hl), map_zero]
  rw [← hzero, key, Multiset.prod_eq_zero_iff, Multiset.mem_map]
  constructor
  · rintro ⟨w, hw, hR⟩
    refine ⟨w, (mem_roots hpm.ne_zero).2 ?_, ?_⟩
    · rw [IsRoot, hpe]; exact hw
    · rw [heval]; exact ((anf_sum_C_mul_X_pow_eq_zero _).2 hR)
  · rintro ⟨w, hw, hR⟩
    refine ⟨w, ?_, ?_⟩
    · rw [← hpe]; exact (mem_roots hpm.ne_zero).1 hw
    · rw [heval] at hR; exact (anf_sum_C_mul_X_pow_eq_zero _).1 hR

end CommonRoot

/-! ### Eliminating one variable -/

section One

/-- **Eliminating one variable at the origin.** Let `A ⊆ ℂⁿ × ℂ` contain `0`, be near `0` the common
zero set of finitely many analytic functions, and have `0` isolated in its fibre over `0`. Then for
some `ε > 0` the set of `y` over which `A` has a point `(y, t)` with `‖t‖ < ε` is analytic near
`0`. One equation `f` does not vanish identically on the fibre; Weierstrass preparation writes it
`u · P` with `P` monic in `t`; division writes every equation `q · P + R`; near `0` the points of `A`
over `y` are the common roots of `P(y, ·)` and the `R(y, ·)`, all small. -/
theorem anf_eliminate_one_zero {n : ℕ} {A : Set ((Fin n → ℂ) × ℂ)}
    (hloc : ∃ O : Set ((Fin n → ℂ) × ℂ), IsOpen O ∧ (0 : (Fin n → ℂ) × ℂ) ∈ O ∧
      ∃ (κ : Type) (_ : Finite κ) (f : κ → (Fin n → ℂ) × ℂ → ℂ), (∀ i, AnalyticOnNhd ℂ (f i) O) ∧
        ∀ p ∈ O, (p ∈ A ↔ ∀ i, f i p = 0))
    (hiso : ∃ r > 0, ∀ t : ℂ, ‖t‖ < r → ((0 : Fin n → ℂ), t) ∈ A → t = 0) {ε₀ : ℝ}
    (hε₀ : 0 < ε₀) :
    ∃ ε > 0, ε ≤ ε₀ ∧ anf_IsAnalyticNear {y | ∃ t : ℂ, ‖t‖ < ε ∧ (y, t) ∈ A} 0 := by
  classical
  obtain ⟨O, hO, h0O, κ, hκ, f, hf, hAf⟩ := hloc
  obtain ⟨r, hr, hiso⟩ := hiso
  obtain ⟨s, ⟨e⟩⟩ := Finite.exists_equiv_fin κ
  have hf0 : ∀ i, AnalyticAt ℂ (f i) 0 := fun i ↦ hf i 0 h0O
  -- some equation does not vanish identically on the fibre
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, analyticOrderAt (fun w : ℂ ↦ f i₀ (0, w)) 0 ≠ ⊤ := by
    by_contra h
    push Not at h
    have hall : ∀ᶠ w : ℂ in 𝓝 0, ∀ i, f i (0, w) = 0 :=
      eventually_all.2 fun i ↦ analyticOrderAt_eq_top.1 (h i)
    have hcont : Tendsto (fun w : ℂ ↦ ((0 : Fin n → ℂ), w)) (𝓝 0) (𝓝 0) := by
      exact (continuous_const.prodMk continuous_id).tendsto' 0 0 (by simp)
    have hz : ∀ᶠ w : ℂ in 𝓝 0, w = 0 := by
      filter_upwards [hall, hcont.eventually (hO.mem_nhds h0O), ball_mem_nhds (0 : ℂ) hr]
        with w hw hwO hwr
      exact hiso w (by simpa using hwr) ((hAf _ hwO).2 hw)
    obtain ⟨w, hw0, hw⟩ := ((hz.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : {w : ℂ | w ≠ 0} ∈ 𝓝[≠] 0)).exists
    exact hw hw0
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.1 hi₀
  obtain ⟨u, hu, hu0, a, ha, hfu⟩ := spec_weierstrass_preparation (hf0 i₀) hd.symm
  have hdiv : ∀ i : Fin s, ∃ q : (Fin n → ℂ) × ℂ → ℂ, AnalyticAt ℂ q 0 ∧
      ∃ b : Fin d → (Fin n → ℂ) → ℂ, (∀ j, AnalyticAt ℂ (b j) 0) ∧
        f (e.symm i) =ᶠ[𝓝 0] fun p ↦ q p * monicInLast a p + ∑ j, b j p.1 * p.2 ^ (j : ℕ) :=
    fun i ↦ spec_weierstrass_division (hf0 (e.symm i)) (fun j ↦ (ha j).1) (fun j ↦ (ha j).2)
  choose q hq b hb hqb using hdiv
  -- a polydisc of radius `η` on which all the identities hold
  have hev : ∀ᶠ p in 𝓝 (0 : (Fin n → ℂ) × ℂ), p ∈ O ∧ u p ≠ 0 ∧
      f i₀ p = u p * monicInLast a p ∧
      ∀ i, f (e.symm i) p = q i p * monicInLast a p + ∑ j, b i j p.1 * p.2 ^ (j : ℕ) :=
    (show ∀ᶠ p in 𝓝 (0 : (Fin n → ℂ) × ℂ), p ∈ O from hO.mem_nhds h0O).and ((hu.continuousAt.eventually_ne hu0).and
      (hfu.and (eventually_all.2 hqb)))
  obtain ⟨η₁, hη₁, hηp₁⟩ := Metric.eventually_nhds_iff.1 hev
  set η := min η₁ ε₀
  have hη : 0 < η := lt_min hη₁ hε₀
  have hηp : ∀ ⦃p : (Fin n → ℂ) × ℂ⦄, dist p 0 < η → _ := fun p hp ↦
    hηp₁ (hp.trans_le (min_le_left _ _))
  have hball : ∀ (z : Fin n → ℂ) (w : ℂ), ‖z‖ < η → ‖w‖ < η → dist (z, w) 0 < η :=
    fun z w hz hw ↦ by rw [dist_zero_right, Prod.norm_def]; exact max_lt hz hw
  have hev' : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), (∀ w, monicInLast a (z, w) = 0 → ‖w‖ < η) ∧
      (∀ j, AnalyticAt ℂ (a j) z) ∧ ∀ i j, AnalyticAt ℂ (b i j) z :=
    (spec_monicInLast_roots_small (fun j ↦ (ha j).1.continuousAt) (fun j ↦ (ha j).2) hη).and
      ((eventually_all.2 fun j ↦ (ha j).1.eventually_analyticAt).and
        (eventually_all.2 fun i ↦ eventually_all.2 fun j ↦ (hb i j).eventually_analyticAt))
  obtain ⟨δ, hδ, hδp⟩ := Metric.eventually_nhds_iff.1 hev'
  set δ' := min δ η
  have hδ' : 0 < δ' := lt_min hδ hη
  have hV : ∀ z ∈ ball (0 : Fin n → ℂ) δ', dist z 0 < δ ∧ ‖z‖ < η := fun z hz ↦ by
    rw [mem_ball] at hz
    exact ⟨hz.trans_le (min_le_left _ _), by
      rw [← dist_zero_right]; exact hz.trans_le (min_le_right _ _)⟩
  obtain ⟨L, h, hh, hiff⟩ := anf_commonRoot_equations (V := ball (0 : Fin n → ℂ) δ') (a := a)
    (b := b) (fun j z hz ↦ (hδp (hV z hz).1).2.1 j) (fun i j z hz ↦ (hδp (hV z hz).1).2.2 i j)
  refine ⟨η, hη, min_le_right _ _, ball 0 δ', isOpen_ball, mem_ball_self hδ', Fin L, inferInstance, h,
    fun l ↦ hh l, fun y hy ↦ ?_⟩
  obtain ⟨hyδ, hyη⟩ := hV y hy
  rw [mem_ofPred_eq, ← hiff y]
  constructor
  · rintro ⟨t, ht, htA⟩
    obtain ⟨hpO, hu', hfi₀, hfi⟩ := hηp (hball y t hyη ht)
    have hzero := (hAf _ hpO).1 htA
    have hP : monicInLast a (y, t) = 0 := by
      have := hzero i₀
      rw [hfi₀] at this
      exact (mul_eq_zero.1 this).resolve_left hu'
    refine ⟨t, hP, fun i ↦ ?_⟩
    have := hzero (e.symm i)
    rw [hfi i, hP, mul_zero, zero_add] at this
    exact this
  · rintro ⟨w, hw, hR⟩
    have hwη := (hδp hyδ).1 w hw
    obtain ⟨hpO, -, -, hfi⟩ := hηp (hball y w hyη hwη)
    refine ⟨w, hwη, (hAf _ hpO).2 fun i ↦ ?_⟩
    rw [← e.symm_apply_apply i, hfi (e i), hw, mul_zero, zero_add]
    exact hR (e i)

/-- **Eliminating one variable at a point.** The version of `anf_eliminate_one_zero` over any
finite-dimensional base, at any point: translate to the origin and choose linear coordinates. -/
theorem anf_eliminate_one_exists {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {A : Set (E × ℂ)} {y₀ : E} {a : ℂ}
    (hloc : anf_IsAnalyticNear A (y₀, a))
    (hiso : ∃ r > 0, ∀ t, dist t a < r → (y₀, t) ∈ A → t = a) {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ ε > 0, ε ≤ ε₀ ∧ anf_IsAnalyticNear {y | ∃ t, dist t a < ε ∧ (y, t) ∈ A} y₀ := by
  set n := Module.finrank ℂ E
  let e : E ≃L[ℂ] (Fin n → ℂ) := ContinuousLinearEquiv.ofFinrankEq (by simp [n])
  let σ : (Fin n → ℂ) × ℂ → E × ℂ := fun p ↦ (y₀ + e.symm p.1, a + p.2)
  have hσ : ∀ p, AnalyticAt ℂ σ p := fun p ↦ by
    have h1 : AnalyticAt ℂ (fun p : (Fin n → ℂ) × ℂ ↦ y₀ + e.symm p.1) p :=
      analyticAt_const.add (((e.symm : (Fin n → ℂ) →L[ℂ] E).comp
        (ContinuousLinearMap.fst ℂ _ ℂ)).analyticAt p)
    have h2 : AnalyticAt ℂ (fun p : (Fin n → ℂ) × ℂ ↦ a + p.2) p :=
      analyticAt_const.add ((ContinuousLinearMap.snd ℂ (Fin n → ℂ) ℂ).analyticAt p)
    exact h1.prod h2
  have hσ0 : σ 0 = (y₀, a) := by simp [σ]
  have hloc' : anf_IsAnalyticNear (σ ⁻¹' A) 0 := by
    apply anf_IsAnalyticNear.preimage hσ
    rw [hσ0]
    exact hloc
  obtain ⟨r, hr, hiso⟩ := hiso
  have hiso' : ∀ t : ℂ, ‖t‖ < r → ((0 : Fin n → ℂ), t) ∈ σ ⁻¹' A → t = 0 := by
    intro t ht htA
    have hA : (y₀, a + t) ∈ A := by simpa [σ] using htA
    have h := hiso (a + t) (by simpa [dist_eq_norm] using ht) hA
    simpa using h
  obtain ⟨ε, hε, hεε₀, hS⟩ := anf_eliminate_one_zero hloc' ⟨r, hr, hiso'⟩ hε₀
  refine ⟨ε, hε, hεε₀, ?_⟩
  let φ : E → (Fin n → ℂ) := fun y ↦ e (y - y₀)
  have hφ : ∀ y, AnalyticAt ℂ φ y := fun y ↦
    ((e : E →L[ℂ] (Fin n → ℂ)).analyticAt _).comp (analyticAt_id.sub analyticAt_const)
  have hφ0 : φ y₀ = 0 := by simp [φ]
  have h := anf_IsAnalyticNear.preimage hφ (S := {y | ∃ t : ℂ, ‖t‖ < ε ∧ (y, t) ∈ σ ⁻¹' A})
    (y₀ := y₀) (by rw [hφ0]; exact hS)
  refine h.congr (Eventually.of_forall fun y ↦ ?_)
  simp only [mem_preimage, mem_ofPred_eq, φ, σ, ContinuousLinearEquiv.symm_apply_apply,
    add_sub_cancel]
  constructor
  · rintro ⟨t, ht, htA⟩
    exact ⟨a + t, by simpa [dist_eq_norm] using ht, htA⟩
  · rintro ⟨t, ht, htA⟩
    exact ⟨t - a, by simpa [dist_eq_norm] using ht, by simpa using htA⟩

end One

/-! ### Every small radius -/

section Small

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [ProperSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [ProperSpace F]

/-- From local equations and an isolated point of the fibre, the shrinking lemma
(`anf_eventually_near`) on a small closed polydisc inside the domain of the equations. -/
theorem anf_eventually_near_of_loc {A : Set (E × F)} {y₀ : E} {a : F}
    (hloc : anf_IsAnalyticNear A (y₀, a)) {r : ℝ} (hr : 0 < r)
    (hiso : ∀ w, dist w a < r → (y₀, w) ∈ A → w = a) :
    ∃ r' > 0, r' < r ∧ ∀ δ > 0, ∀ᶠ y in 𝓝 y₀, ∀ w ∈ closedBall a r', (y, w) ∈ A →
      dist w a < δ := by
  obtain ⟨O, hO, hpO, κ, -, f, hf, hAf⟩ := hloc
  obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.1 hO _ hpO
  set r' := min (ε / 2) (r / 2)
  have hr' : 0 < r' := lt_min (half_pos hε) (half_pos hr)
  set K : Set (E × F) := closedBall y₀ r' ×ˢ closedBall a r'
  have hKO : K ⊆ O := by
    intro p hp
    apply hεO
    have hp' : p ∈ closedBall (y₀, a) r' := (closedBall_prod_same y₀ a r') ▸ hp
    exact mem_ball.2 ((mem_closedBall.1 hp').trans_lt
      ((min_le_left _ _).trans_lt (half_lt_self hε)))
  have hKc : IsClosed K := isClosed_closedBall.prod isClosed_closedBall
  have hAK : A ∩ K = K ∩ ⋂ i, (K ∩ f i ⁻¹' {0}) := by
    ext p
    simp only [mem_inter_iff, mem_iInter, mem_preimage, mem_singleton_iff]
    constructor
    · rintro ⟨hpA, hpK⟩
      exact ⟨hpK, fun i ↦ ⟨hpK, (hAf p (hKO hpK)).1 hpA i⟩⟩
    · rintro ⟨hpK, h⟩
      exact ⟨(hAf p (hKO hpK)).2 fun i ↦ (h i).2, hpK⟩
  have hcl : IsClosed (A ∩ K) := by
    rw [hAK]
    exact hKc.inter (isClosed_iInter fun i ↦
      ((hf i).continuousOn.mono hKO).preimage_isClosed_of_isClosed hKc isClosed_singleton)
  refine ⟨r', hr', (min_le_right _ _).trans_lt (half_lt_self hr), fun δ hδ ↦ ?_⟩
  refine anf_eventually_near hr' hcl (fun w hw hwA ↦ hiso w ?_ hwA) hδ
  exact (mem_closedBall.1 hw).trans_lt ((min_le_right _ _).trans_lt (half_lt_self hr))

/-- If arbitrarily small fibre balls give sets analytic near `y₀`, then every small enough fibre
ball does. -/
theorem anf_isAnalyticNear_small {A : Set (E × F)} {y₀ : E} {a : F}
    (hloc : anf_IsAnalyticNear A (y₀, a)) (hiso : ∃ r > 0, ∀ w, dist w a < r → (y₀, w) ∈ A → w = a)
    (hex : ∀ ε₀ > 0, ∃ ε > 0, ε ≤ ε₀ ∧
      anf_IsAnalyticNear {y | ∃ w, dist w a < ε ∧ (y, w) ∈ A} y₀) :
    ∃ ρ > 0, ∀ ε, 0 < ε → ε ≤ ρ →
      anf_IsAnalyticNear {y | ∃ w, dist w a < ε ∧ (y, w) ∈ A} y₀ := by
  obtain ⟨r, hr, hiso⟩ := hiso
  obtain ⟨r', hr', -, hnear⟩ := anf_eventually_near_of_loc hloc hr hiso
  obtain ⟨ε₁, hε₁, hε₁r, hS⟩ := hex r' hr'
  refine ⟨ε₁, hε₁, fun ε hε hεε₁ ↦ hS.congr ?_⟩
  filter_upwards [hnear ε hε] with y hy
  constructor
  · rintro ⟨w, hw, hwA⟩
    exact ⟨w, hy w (mem_closedBall.2 (hw.le.trans hε₁r)) hwA, hwA⟩
  · rintro ⟨w, hw, hwA⟩
    exact ⟨w, hw.trans_le hεε₁, hwA⟩

end Small

/-! ### Eliminating all the fibre variables -/

section Several

universe u

theorem anf_dist_lt_iff {k : ℕ} {w a : Fin (k + 1) → ℂ} {r : ℝ} (hr : 0 < r) :
    dist w a < r ↔ dist (w 0) (a 0) < r ∧ dist (Fin.tail w) (Fin.tail a) < r := by
  rw [dist_pi_lt_iff hr, dist_pi_lt_iff hr, Fin.forall_fin_succ]
  rfl

theorem anf_dist_le_iff {k : ℕ} {w a : Fin (k + 1) → ℂ} {r : ℝ} (hr : 0 ≤ r) :
    dist w a ≤ r ↔ dist (w 0) (a 0) ≤ r ∧ dist (Fin.tail w) (Fin.tail a) ≤ r := by
  rw [dist_pi_le_iff hr, dist_pi_le_iff hr, Fin.forall_fin_succ]
  rfl

/-- **Elimination of the fibre variables.** Let `A ⊆ E × ℂᵏ` be near `(y₀, a)` the common zero set
of finitely many analytic functions, with `a` isolated in the fibre over `y₀`. Then for every small
`ε > 0` the set of `y` over which `A` has a point `(y, w)` with `‖w - a‖ < ε` is analytic near
`y₀`. Induction on `k`: eliminate the first fibre coordinate over the base `E × ℂᵏ⁻¹`
(`anf_eliminate_one_exists`), then the others; the shrinking lemma reconciles the radii. -/
theorem anf_eliminate (k : ℕ) : ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] {A : Set (E × (Fin k → ℂ))} {y₀ : E} {a : Fin k → ℂ},
    anf_IsAnalyticNear A (y₀, a) → (∃ r > 0, ∀ w, dist w a < r → (y₀, w) ∈ A → w = a) →
    ∃ ρ > 0, ∀ ε, 0 < ε → ε ≤ ρ →
      anf_IsAnalyticNear {y | ∃ w, dist w a < ε ∧ (y, w) ∈ A} y₀ := by
  induction k with
  | zero =>
    intro E _ _ _ A y₀ a hloc _
    refine ⟨1, one_pos, fun ε hε _ ↦ ?_⟩
    have h := anf_IsAnalyticNear.preimage (φ := fun y : E ↦ (y, a))
      (fun y ↦ analyticAt_id.prod analyticAt_const) hloc
    refine h.congr (Eventually.of_forall fun y ↦ ⟨fun hy ↦ ⟨a, by simpa using hε, hy⟩, ?_⟩)
    rintro ⟨w, -, hw⟩
    rwa [Subsingleton.elim w a] at hw
  | succ k ih =>
    intro E _ _ _ A y₀ a hloc hiso
    have := FiniteDimensional.proper_rclike ℂ E
    let σ : (E × (Fin k → ℂ)) × ℂ → E × (Fin (k + 1) → ℂ) := fun q ↦ (q.1.1, Fin.cons q.2 q.1.2)
    have hσ : ∀ q, AnalyticAt ℂ σ q := by
      intro q
      refine AnalyticAt.prod (((ContinuousLinearMap.fst ℂ E (Fin k → ℂ)).comp
        (ContinuousLinearMap.fst ℂ _ ℂ)).analyticAt q) (analyticAt_pi_iff.2 fun i ↦ ?_)
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · show AnalyticAt ℂ (fun q : (E × (Fin k → ℂ)) × ℂ ↦ q.2) q
        exact (ContinuousLinearMap.snd ℂ (E × (Fin k → ℂ)) ℂ).analyticAt q
      · show AnalyticAt ℂ (fun q : (E × (Fin k → ℂ)) × ℂ ↦ q.1.2 j) q
        exact (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k ↦ ℂ) j).comp
          ((ContinuousLinearMap.snd ℂ E (Fin k → ℂ)).comp
            (ContinuousLinearMap.fst ℂ _ ℂ))).analyticAt q)
    have hσp : σ ((y₀, Fin.tail a), a 0) = (y₀, a) := by simp [σ, Fin.cons_self_tail]
    obtain ⟨r, hr, hiso⟩ := hiso
    -- the first fibre coordinate
    have hloc₁ : anf_IsAnalyticNear (σ ⁻¹' A) ((y₀, Fin.tail a), a 0) := by
      apply anf_IsAnalyticNear.preimage hσ
      rw [hσp]
      exact hloc
    have hiso₁ : ∃ r > 0, ∀ t, dist t (a 0) < r → ((y₀, Fin.tail a), t) ∈ σ ⁻¹' A →
        t = a 0 := by
      refine ⟨r, hr, fun t ht htA ↦ ?_⟩
      have h := hiso (Fin.cons t (Fin.tail a)) ((anf_dist_lt_iff hr).2
        ⟨by simpa using ht, by simpa using hr⟩) htA
      simpa using congrFun h 0
    obtain ⟨ρ₁, hρ₁, h₁⟩ := anf_isAnalyticNear_small hloc₁ hiso₁
      fun ε₀ hε₀ ↦ anf_eliminate_one_exists hloc₁ hiso₁ hε₀
    obtain ⟨r', hr', hr'r, hnear⟩ := anf_eventually_near_of_loc hloc hr hiso
    set ε₁ := min ρ₁ r'
    have hε₁ : 0 < ε₁ := lt_min hρ₁ hr'
    have hS₁ := h₁ ε₁ hε₁ (min_le_left _ _)
    -- the remaining coordinates
    have hiso₂ : ∃ r > 0, ∀ w', dist w' (Fin.tail a) < r →
        (y₀, w') ∈ {u | ∃ t, dist t (a 0) < ε₁ ∧ (u, t) ∈ σ ⁻¹' A} → w' = Fin.tail a := by
      refine ⟨r, hr, fun w' hw' ⟨t, ht, htA⟩ ↦ ?_⟩
      have h := hiso (Fin.cons t w') ((anf_dist_lt_iff hr).2
        ⟨by simpa using ht.trans_le ((min_le_right _ _).trans hr'r.le), by simpa using hw'⟩) htA
      simpa using congrArg Fin.tail h
    obtain ⟨ρ₂, hρ₂, h₂⟩ := ih hS₁ hiso₂
    refine ⟨min ρ₂ ε₁, lt_min hρ₂ hε₁, fun ε hε hερ ↦ (h₂ ε hε
      (hερ.trans (min_le_left _ _))).congr ?_⟩
    have hεε₁ : ε ≤ ε₁ := hερ.trans (min_le_right _ _)
    have hε₁r' : ε₁ ≤ r' := min_le_right _ _
    filter_upwards [hnear ε hε] with y hy
    constructor
    · rintro ⟨w', hw', t, ht, htA⟩
      refine ⟨Fin.cons t w', hy _ ?_ htA, htA⟩
      rw [mem_closedBall, anf_dist_le_iff hr'.le]
      exact ⟨by simpa using ht.le.trans hε₁r', by simpa using (hw'.le.trans hεε₁).trans hε₁r'⟩
    · rintro ⟨w, hw, hwA⟩
      obtain ⟨hw0, hwt⟩ := (anf_dist_lt_iff hε).1 hw
      refine ⟨Fin.tail w, hwt, w 0, hw0.trans_le hεε₁, ?_⟩
      show σ ((y, Fin.tail w), w 0) ∈ A
      simpa [σ, Fin.cons_self_tail] using hwA

end Several

/-! ### Proper projections with finite fibres -/

section Projection

/-- In a normed space charted by itself, a closed analytic set is a closed set analytic near each
of its points. -/
theorem anf_isClosedAnalytic_self_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (Z : Set E) : IsClosedAnalytic E Z ↔ IsClosed Z ∧ ∀ x ∈ Z, anf_IsAnalyticNear Z x := by
  rw [isClosedAnalytic_iff_finite]
  simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_apply, id_eq,
    OpenPartialHomeomorph.refl_target, subset_univ, true_and, OpenPartialHomeomorph.refl_symm]
  rfl

/-- A point of a finite set has a ball meeting the set only in that point. -/
theorem anf_finite_isolated {F : Type*} [MetricSpace F] {s : Set F} (hs : s.Finite) (x : F) :
    ∃ r > 0, ∀ y ∈ s, dist y x < r → y = x := by
  have hx : x ∈ (s \ {x})ᶜ := fun h ↦ h.2 rfl
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (hs.sdiff.isClosed.isOpen_compl) x hx
  refine ⟨r, hr, fun y hy hyx ↦ ?_⟩
  by_contra hne
  exact hball (mem_ball.2 hyx) ⟨hy, hne⟩

/-- **Proper projections with finite fibres.** The image in `ℂᵐ` of a closed analytic set
`T ⊆ ℂᵐ × ℂᵏ` whose projection is proper with finite fibres is closed analytic: closed because a
proper map is closed; near a point `y₀` of the image, properness confines the points of `T` over
nearby `y` to small balls around the finitely many points of the fibre over `y₀`, and over each
ball the image is analytic near `y₀` (`anf_eliminate`). -/
theorem anf_finite_projection (m k : ℕ) (T : Set ((Fin m → ℂ) × (Fin k → ℂ)))
    (hT : IsClosedAnalytic ((Fin m → ℂ) × (Fin k → ℂ)) T)
    (hproper : IsProperMap (fun a : T ↦ (a : (Fin m → ℂ) × (Fin k → ℂ)).1))
    (hfin : ∀ y, {a | a ∈ T ∧ a.1 = y}.Finite) :
    IsClosedAnalytic (Fin m → ℂ) (Prod.fst '' T) := by
  classical
  rw [anf_isClosedAnalytic_self_iff] at hT ⊢
  have hrange : Prod.fst '' T = range (fun a : T ↦ (a : (Fin m → ℂ) × (Fin k → ℂ)).1) := by
    ext y
    simp
  refine ⟨hrange ▸ hproper.isClosedMap.isClosed_range, ?_⟩
  rintro y₀ ⟨⟨y, w₀⟩, -, rfl⟩
  set y₀ := y
  set W := {w | (y₀, w) ∈ T}
  have hW : W.Finite := ((hfin y₀).image Prod.snd).subset fun w hw ↦ ⟨(y₀, w), ⟨hw, rfl⟩, rfl⟩
  have : Finite W := hW.to_subtype
  have hρ : ∀ w : W, ∃ ρ > 0, ∀ ε, 0 < ε → ε ≤ ρ →
      anf_IsAnalyticNear {y | ∃ w', dist w' (w : Fin k → ℂ) < ε ∧ (y, w') ∈ T} y₀ := by
    intro w
    obtain ⟨r, hr, hiso⟩ := anf_finite_isolated hW (w : Fin k → ℂ)
    exact anf_eliminate k (hT.2 _ w.2) ⟨r, hr, fun w' hw' hT' ↦ hiso w' hT' hw'⟩
  choose ρ hρpos hρ using hρ
  have hU := anf_isAnalyticNear_iUnion fun w : W ↦ hρ w (ρ w) (hρpos w) le_rfl
  refine hU.congr ?_
  -- the points of `T` away from the balls project to a closed set missing `y₀`
  set C : Set T := {a | ∀ w : W, ρ w ≤ dist (a : (Fin m → ℂ) × (Fin k → ℂ)).2 w}
  have hC : IsClosed C := by
    simp only [C, ofPred_forall]
    exact isClosed_iInter fun w ↦ isClosed_le continuous_const
      ((continuous_snd.comp continuous_subtype_val).dist continuous_const)
  have hD := hproper.isClosedMap C hC
  have hy₀ : y₀ ∉ (fun a : T ↦ (a : (Fin m → ℂ) × (Fin k → ℂ)).1) '' C := by
    rintro ⟨⟨⟨y', w'⟩, hT'⟩, hC', rfl⟩
    have := hC' ⟨w', hT'⟩
    simp only [dist_self] at this
    exact (hρpos _).not_ge this
  filter_upwards [hD.isOpen_compl.mem_nhds hy₀] with y hy
  simp only [mem_iUnion, mem_ofPred_eq, mem_image]
  constructor
  · rintro ⟨w, w', -, hT'⟩
    exact ⟨(y, w'), hT', rfl⟩
  · rintro ⟨⟨y', w'⟩, hT', rfl⟩
    by_contra hno
    push Not at hno
    exact hy ⟨⟨(y', w'), hT'⟩, fun w ↦ not_lt.1 fun h ↦ hno w w' h hT', rfl⟩

end Projection

/-! ### Charts of reduced spaces -/

section Charts

universe u v

variable {X : Type u} [TopologicalSpace X]

/-- A chart map is continuous on its domain. -/
theorem anf_chart_continuousOn (c : an_Chart X) : ContinuousOn c.toFun c.dom :=
  continuousOn_iff_continuous_domRestrict.2 c.isEmbedding.continuous

/-- A chart map is injective on its domain. -/
theorem anf_chart_injOn (c : an_Chart X) : InjOn c.toFun c.dom := fun x hx y hy h ↦
  congrArg Subtype.val (c.isEmbedding.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) h)

/-- An open subset of the chart domain is the trace of an open subset of `ℂⁿ`. -/
theorem anf_chart_open_eq (c : an_Chart X) {N : Set X} (hN : IsOpen N) :
    ∃ Ω : Set (Fin c.n → ℂ), IsOpen Ω ∧ N ∩ c.dom = c.dom ∩ c.toFun ⁻¹' Ω := by
  have hN' : IsOpen ((Subtype.val : c.dom → X) ⁻¹' N) := hN.preimage continuous_subtype_val
  rw [c.isEmbedding.isInducing.isOpen_iff] at hN'
  obtain ⟨Ω, hΩ, hΩN⟩ := hN'
  refine ⟨Ω, hΩ, ?_⟩
  ext x
  constructor
  · rintro ⟨hxN, hx⟩
    refine ⟨hx, ?_⟩
    have : (⟨x, hx⟩ : c.dom) ∈ c.dom.domRestrict c.toFun ⁻¹' Ω := by rw [hΩN]; exact hxN
    exact this
  · rintro ⟨hx, hxΩ⟩
    have : (⟨x, hx⟩ : c.dom) ∈ c.dom.domRestrict c.toFun ⁻¹' Ω := hxΩ
    rw [hΩN] at this
    exact ⟨this, hx⟩

/-- A function analytic on an open `V ⊆ ℂⁿ`, read through a chart, is holomorphic on any subset of
the chart domain mapped into `V`: in another chart the first chart map is holomorphic, by
analyticity of the atlas. -/
theorem anf_isHolFun_comp_chart (S : an_ReducedSpace X) (j : S.atlas.ι)
    {V : Set (Fin (S.atlas.chart j).n → ℂ)} {G : (Fin (S.atlas.chart j).n → ℂ) → ℂ}
    (hG : AnalyticOnNhd ℂ G V) {W : Set X} (hW : W ⊆ (S.atlas.chart j).dom)
    (hWV : ∀ y ∈ W, (S.atlas.chart j).toFun y ∈ V) :
    S.IsHolFun (fun y : W ↦ G ((S.atlas.chart j).toFun y)) := by
  intro y i hyi
  obtain ⟨W', hW', hyW', H, hH, hHeq⟩ := S.isAnalytic i j (y : X) ⟨hW y.2, hyi⟩
  refine ⟨(S.atlas.chart i).dom ∩ (S.atlas.chart i).toFun ⁻¹' W',
    (anf_chart_continuousOn _).isOpen_inter_preimage (S.atlas.chart i).isOpen_dom hW',
    ⟨hyi, hyW'⟩, G ∘ H, ?_, fun y' hy' ↦ ?_⟩
  · have hHy := hHeq (y : X) ⟨hW y.2, hyi⟩ hyW'
    refine AnalyticAt.comp (g := G) ?_ (hH _ hyW')
    rw [← hHy]
    exact hG _ (hWV y y.2)
  · simp only [Function.comp_apply]
    rw [← hHeq (y' : X) ⟨hW y'.2, hy'.2⟩ hy'.1.2]

end Charts

/-! ### The finite mapping theorem -/

section Mapping

universe u v

variable {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]

/-- **The image near one point of a fibre.** Let `f` be holomorphic, `Z` closed analytic with finite
fibre over `y₀`, `x ∈ Z` over `y₀`, and `c` a chart of the target at `y₀`. Then some open `N ∋ x`
has image `f (Z ∩ N)` which, read in `c`, is analytic near `c y₀`. In a chart `d` at `x`, the set
`A` of pairs `(c (f x'), d x')` for `x' ∈ Z` near `x` is the zero set of the equations of the local
model, the local equations of `Z`, and `v = H w` with `H` the chart form of `f`; the point
`(c y₀, d x)` is isolated in its fibre, so `anf_eliminate` applies. -/
theorem anf_finite_mapping_local (S : an_ReducedSpace X) (T : an_ReducedSpace Y) {f : X → Y}
    (hf : an_IsHom S T f) {Z : Set X} (hZ : an_IsClosedAnalytic S Z) {y₀ : Y}
    (hfin : (Z ∩ f ⁻¹' {y₀}).Finite) (j : T.atlas.ι) (hy₀ : y₀ ∈ (T.atlas.chart j).dom)
    {x : X} (hxZ : x ∈ Z) (hfx : f x = y₀) :
    ∃ N : Set X, IsOpen N ∧ x ∈ N ∧ ∃ Sx : Set (Fin (T.atlas.chart j).n → ℂ),
      anf_IsAnalyticNear Sx ((T.atlas.chart j).toFun y₀) ∧
      ∀ y ∈ (T.atlas.chart j).dom,
        ((T.atlas.chart j).toFun y ∈ Sx ↔ ∃ x' ∈ Z ∩ N, f x' = y) := by
  classical
  set c := T.atlas.chart j with hc
  set i := S.atlas.chartAt x
  set d := S.atlas.chart i with hd
  have hx : x ∈ d.dom := S.atlas.mem_chartAt x
  set p := d.toFun x
  have hfxc : f x ∈ c.dom := by rw [hfx]; exact hy₀
  -- the local equations of `Z` in the chart `d`
  obtain ⟨WZ, hWZ, hxWZ, kZ, g, hg, hZg⟩ := hZ.2 x hxZ
  have hGl : ∀ l, ∃ N : Set X, IsOpen N ∧ x ∈ N ∧ ∃ G : (Fin d.n → ℂ) → ℂ, AnalyticAt ℂ G p ∧
      ∀ y : WZ, (y : X) ∈ N ∩ d.dom → g l y = G (d.toFun y) := fun l ↦ hg l ⟨x, hxWZ⟩ i hx
  choose NZ hNZ hxNZ G hG hGeq using hGl
  -- the chart form of `f`
  have hcoord : ∀ κ : Fin c.n, T.IsHolFun (fun y : c.dom ↦ c.toFun y κ) := fun κ ↦
    anf_isHolFun_comp_chart T j (V := univ) (G := fun w ↦ w κ)
      (fun w _ ↦ (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin c.n ↦ ℂ) κ).analyticAt w)
      subset_rfl (fun _ _ ↦ mem_univ _)
  have hHκ : ∀ κ : Fin c.n, ∃ N : Set X, IsOpen N ∧ x ∈ N ∧
      ∃ H : (Fin d.n → ℂ) → ℂ, AnalyticAt ℂ H p ∧
        ∀ x' : f ⁻¹' c.dom, (x' : X) ∈ N ∩ d.dom → c.toFun (f x') κ = H (d.toFun x') :=
    fun κ ↦ hf.2 c.dom c.isOpen_dom _ (hcoord κ) ⟨x, hfxc⟩ i hx
  choose NH hNH hxNH H hH hHeq using hHκ
  let Hv : (Fin d.n → ℂ) → (Fin c.n → ℂ) := fun w κ ↦ H κ w
  have hHv : AnalyticAt ℂ Hv p := analyticAt_pi_iff.2 fun κ ↦ hH κ
  set M := WZ ∩ (⋂ l, NZ l) ∩ (⋂ κ, NH κ) ∩ d.dom ∩ f ⁻¹' c.dom
  have hM : IsOpen M := (((hWZ.inter (isOpen_iInter_of_finite hNZ)).inter
    (isOpen_iInter_of_finite hNH)).inter d.isOpen_dom).inter (c.isOpen_dom.preimage hf.1)
  have hxM : x ∈ M := ⟨⟨⟨⟨hxWZ, mem_iInter.2 hxNZ⟩, mem_iInter.2 hxNH⟩, hx⟩, hfxc⟩
  have hMd : M ⊆ d.dom := fun x' h ↦ h.1.2
  have hMc : ∀ x' ∈ M, f x' ∈ c.dom := fun x' h ↦ h.2
  have hMZ : ∀ x' ∈ M, (x' ∈ Z ↔ ∀ l, G l (d.toFun x') = 0) := by
    intro x' h
    have hW : x' ∈ WZ := h.1.1.1.1
    rw [show x' ∈ Z ↔ ((⟨x', hW⟩ : WZ) : X) ∈ Z from Iff.rfl, hZg ⟨x', hW⟩]
    refine forall_congr' fun l ↦ ?_
    rw [hGeq l ⟨x', hW⟩ ⟨mem_iInter.1 h.1.1.1.2 l, h.1.2⟩]
  have hMH : ∀ x' ∈ M, c.toFun (f x') = Hv (d.toFun x') := by
    intro x' h
    funext κ
    exact hHeq κ ⟨x', h.2⟩ ⟨mem_iInter.1 h.1.1.2 κ, h.1.2⟩
  obtain ⟨Ω, hΩ, hMΩ⟩ := anf_chart_open_eq d hM
  have hMΩ' : ∀ x' ∈ d.dom, (x' ∈ M ↔ d.toFun x' ∈ Ω) := by
    intro x' hx'
    constructor
    · intro h
      have : x' ∈ d.dom ∩ d.toFun ⁻¹' Ω := hMΩ ▸ ⟨h, hx'⟩
      exact this.2
    · intro h
      have : x' ∈ M ∩ d.dom := hMΩ ▸ ⟨hx', h⟩
      exact this.1
  have hpU : p ∈ d.U := by
    have : p ∈ d.toFun '' d.dom := ⟨x, hx, rfl⟩
    rw [d.image_eq] at this
    exact this.1
  have hev : ∀ᶠ w in 𝓝 p, w ∈ d.U ∧ w ∈ Ω ∧ (∀ l, AnalyticAt ℂ (G l) w) ∧
      AnalyticAt ℂ Hv w :=
    (show ∀ᶠ w in 𝓝 p, w ∈ d.U from d.isOpen_U.mem_nhds hpU).and
      ((show ∀ᶠ w in 𝓝 p, w ∈ Ω from hΩ.mem_nhds ((hMΩ' x hx).1 hxM)).and
        ((eventually_all.2 fun l ↦ (hG l).eventually_analyticAt).and hHv.eventually_analyticAt))
  obtain ⟨β, hβ, hβp⟩ := Metric.eventually_nhds_iff.1 hev
  -- the set of pairs `(c (f x'), d x')`
  set A : Set ((Fin c.n → ℂ) × (Fin d.n → ℂ)) :=
    {q | ∃ x' ∈ Z ∩ M, d.toFun x' = q.2 ∧ c.toFun (f x') = q.1}
  have hloc : anf_IsAnalyticNear A (c.toFun y₀, p) := by
    refine ⟨univ ×ˢ ball p β, isOpen_univ.prod isOpen_ball, ⟨mem_univ _, mem_ball_self hβ⟩,
      Fin d.k ⊕ Fin kZ ⊕ Fin c.n, inferInstance,
      Sum.elim (fun q w ↦ d.eqns w.2 q)
        (Sum.elim (fun l w ↦ G l w.2) (fun κ w ↦ w.1 κ - Hv w.2 κ)), ?_, ?_⟩
    · rintro (q | l | κ) ⟨v, w⟩ ⟨-, hw⟩
      · exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin d.k ↦ ℂ) q).analyticAt _).comp
          ((d.analyticOnNhd_eqns _ (hβp hw).1).comp
            ((ContinuousLinearMap.snd ℂ (Fin c.n → ℂ) (Fin d.n → ℂ)).analyticAt _))
      · exact ((hβp hw).2.2.1 l).comp
          ((ContinuousLinearMap.snd ℂ (Fin c.n → ℂ) (Fin d.n → ℂ)).analyticAt _)
      · exact (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin c.n ↦ ℂ) κ).comp
          (ContinuousLinearMap.fst ℂ (Fin c.n → ℂ) (Fin d.n → ℂ))).analyticAt _).sub
          (((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin c.n ↦ ℂ) κ).analyticAt _).comp
            ((hβp hw).2.2.2.comp
              ((ContinuousLinearMap.snd ℂ (Fin c.n → ℂ) (Fin d.n → ℂ)).analyticAt _)))
    · rintro ⟨v, w⟩ ⟨-, hw⟩
      obtain ⟨hwU, hwΩ, -, -⟩ := hβp hw
      simp only [Sum.forall, Sum.elim_inl, Sum.elim_inr]
      constructor
      · rintro ⟨x', ⟨hx'Z, hx'M⟩, rfl, rfl⟩
        have hz : d.toFun x' ∈ an_zeroLocus d.U d.eqns := d.image_eq ▸ ⟨x', hMd hx'M, rfl⟩
        refine ⟨fun q ↦ congrFun hz.2 q, fun l ↦ (hMZ x' hx'M).1 hx'Z l, fun κ ↦ ?_⟩
        rw [hMH x' hx'M, sub_self]
      · rintro ⟨heq, hGz, hHz⟩
        have hz : w ∈ an_zeroLocus d.U d.eqns := ⟨hwU, funext heq⟩
        rw [← d.image_eq] at hz
        obtain ⟨x', hx'd, rfl⟩ := hz
        have hx'M : x' ∈ M := (hMΩ' x' hx'd).2 hwΩ
        refine ⟨x', ⟨(hMZ x' hx'M).2 hGz, hx'M⟩, rfl, ?_⟩
        rw [hMH x' hx'M]
        funext κ
        exact (sub_eq_zero.1 (hHz κ)).symm
  have hiso : ∃ r > 0, ∀ w, dist w p < r → (c.toFun y₀, w) ∈ A → w = p := by
    obtain ⟨r, hr, h⟩ := anf_finite_isolated (hfin.image d.toFun) p
    refine ⟨r, hr, fun w hw hwA ↦ h w ?_ hw⟩
    obtain ⟨x', ⟨hx'Z, hx'M⟩, hw', hv⟩ := hwA
    have : f x' = y₀ := anf_chart_injOn c (hMc x' hx'M) hy₀ hv
    exact ⟨x', ⟨hx'Z, this⟩, hw'⟩
  obtain ⟨ρ, hρ, hρS⟩ := anf_eliminate d.n hloc hiso
  refine ⟨M ∩ d.toFun ⁻¹' ball p ρ,
    ((anf_chart_continuousOn d).mono hMd).isOpen_inter_preimage hM isOpen_ball,
    ⟨hxM, mem_ball_self hρ⟩, _, hρS ρ hρ le_rfl, fun y hy ↦ ?_⟩
  simp only [mem_ofPred_eq]
  constructor
  · rintro ⟨w, hw, x', ⟨hx'Z, hx'M⟩, rfl, hv⟩
    exact ⟨x', ⟨hx'Z, hx'M, hw⟩, anf_chart_injOn c (hMc x' hx'M) hy hv⟩
  · rintro ⟨x', ⟨hx'Z, hx'M, hx'b⟩, rfl⟩
    exact ⟨d.toFun x', hx'b, x', ⟨hx'Z, hx'M⟩, rfl, rfl⟩

/-- **The finite mapping theorem.** The image of a closed analytic subset under a proper
holomorphic map with finite fibres on it is closed analytic: closed because proper maps are closed;
near `y₀`, properness confines the points of `Z` over nearby points to the neighbourhoods given by
`anf_finite_mapping_local` around the finitely many points of the fibre, and the union of their
images, read in a chart at `y₀`, is analytic near `y₀` (`anf_isAnalyticNear_iUnion`); its
equations, composed with the chart, are holomorphic (`anf_isHolFun_comp_chart`). -/
theorem anf_finite_mapping (S : an_ReducedSpace X) (T : an_ReducedSpace Y) (f : X → Y)
    (hf : an_IsProperHom S T f) {Z : Set X} (hZ : an_IsClosedAnalytic S Z)
    (hfin : ∀ y, (Z ∩ f ⁻¹' {y}).Finite) :
    an_IsClosedAnalytic T (f '' Z) := by
  classical
  refine ⟨hf.1.isClosedMap Z hZ.1, ?_⟩
  rintro y₀ -
  set j := T.atlas.chartAt y₀
  set c := T.atlas.chart j
  have hy₀ : y₀ ∈ c.dom := T.atlas.mem_chartAt y₀
  set F := Z ∩ f ⁻¹' {y₀}
  have : Finite F := (hfin y₀).to_subtype
  have hloc : ∀ x : F, ∃ N : Set X, IsOpen N ∧ (x : X) ∈ N ∧ ∃ Sx : Set (Fin c.n → ℂ),
      anf_IsAnalyticNear Sx (c.toFun y₀) ∧
      ∀ y ∈ c.dom, (c.toFun y ∈ Sx ↔ ∃ x' ∈ Z ∩ N, f x' = y) := fun x ↦
    anf_finite_mapping_local S T hf.2 hZ (hfin y₀) j hy₀ x.2.1 x.2.2
  choose N hN hxN Sx hSx hiff using hloc
  obtain ⟨V, hV, hv₀, κ, hκ, g, hg, hVS⟩ := anf_isAnalyticNear_iUnion hSx
  obtain ⟨L, ⟨e⟩⟩ := Finite.exists_equiv_fin κ
  -- points of `Z` outside the neighbourhoods map to a closed set missing `y₀`
  set C := Z \ ⋃ x : F, N x
  have hC : IsClosed C := hZ.1.sdiff (isOpen_iUnion hN)
  have hD : IsClosed (f '' C) := hf.1.isClosedMap C hC
  have hy₀D : y₀ ∉ f '' C := by
    rintro ⟨x', ⟨hx'Z, hx'N⟩, hfx'⟩
    exact hx'N (mem_iUnion.2 ⟨⟨x', hx'Z, hfx'⟩, hxN _⟩)
  set W := (c.dom ∩ c.toFun ⁻¹' V) ∩ (f '' C)ᶜ
  have hW : IsOpen W :=
    ((anf_chart_continuousOn c).isOpen_inter_preimage c.isOpen_dom hV).inter hD.isOpen_compl
  refine ⟨W, hW, ⟨⟨hy₀, hv₀⟩, hy₀D⟩, L, fun l y ↦ g (e.symm l) (c.toFun y), fun l ↦
    anf_isHolFun_comp_chart T j (hg (e.symm l)) (fun y hy ↦ hy.1.1) (fun y hy ↦ hy.1.2),
    fun y ↦ ?_⟩
  obtain ⟨⟨hyc, hyV⟩, hyD⟩ := y.2
  have heq : (∀ l, g (e.symm l) (c.toFun y) = 0) ↔ ∀ l, g l (c.toFun y) = 0 :=
    ⟨fun h l ↦ by simpa using h (e l), fun h l ↦ h _⟩
  rw [heq, ← hVS _ hyV, mem_iUnion]
  constructor
  · rintro ⟨x', hx'Z, hfx'⟩
    have hx' : x' ∈ ⋃ x : F, N x := by
      by_contra h
      exact hyD ⟨x', ⟨hx'Z, h⟩, hfx'⟩
    obtain ⟨x, hx⟩ := mem_iUnion.1 hx'
    exact ⟨x, (hiff x y hyc).2 ⟨x', ⟨hx'Z, hx⟩, hfx'⟩⟩
  · rintro ⟨x, hx⟩
    obtain ⟨x', ⟨hx'Z, -⟩, hfx'⟩ := (hiff x y hyc).1 hx
    exact ⟨x', hx'Z, hfx'⟩

end Mapping

end HodgeLean.Foundations.Analytic
