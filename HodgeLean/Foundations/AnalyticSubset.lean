import Mathlib

/-!
# Closed analytic subsets and the identity principle

Let `M` be a topological space with charts in a complex normed space `E` (for instance an analytic
complex manifold, `IsManifold 𝓘(ℂ, E) ω M`).  A subset `Z ⊆ M` is *closed analytic*
(`IsClosedAnalytic E Z`) if it is closed and, near each of its points `x`, in the preferred chart
`chartAt E x` it is the common zero set of finitely many holomorphic functions.

## Main results

* `HodgeLean.Foundations.IsClosedAnalytic.eq_univ_of_nonempty_interior`: the identity principle.
  On a connected `M`, a closed analytic subset with nonempty interior is all of `M`.
* Closure properties: `∅`, `univ`, finite unions and finite intersections.
* Examples on `ℂ`: a point is closed analytic with empty interior, and the imaginary axis is not
  closed analytic (`not_isClosedAnalytic_re_eq_zero`).

## Chart dependence

The definition uses the preferred chart `chartAt E x` at each point `x ∈ Z`.  On an analytic
manifold every chart transition is analytic, so being locally a common zero set of finitely many
holomorphic functions does not depend on the chart; that independence is not proved here.  On a
charted space whose transitions are not analytic, the predicate may depend on the preferred chart,
and it is the usual notion only on an analytic complex manifold.  The identity principle itself
needs neither the analytic atlas nor finite dimensionality of `E`.

HC: no distance.  AV milestone: no distance.  The Blocks identity-principle hypotheses get
instances for the true predicate.
-/

open Set Filter Topology

noncomputable section

namespace HodgeLean.Foundations

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- A subset `Z` of a space charted on the complex normed space `E` is *closed analytic* if it is
closed and every `x ∈ Z` has an open neighbourhood `U` of `chartAt E x x` inside the chart's
target, together with finitely many functions `f : Fin n → E → ℂ` analytic on `U`, such that for
`z ∈ U`, the point `(chartAt E x).symm z` lies in `Z` exactly when all `f i z` vanish.  Equivalently,
`Z ∩ (chartAt E x).symm '' U` is the common zero set of the `f i ∘ chartAt E x` on the open
neighbourhood `(chartAt E x).symm '' U` of `x`.

The chart used at `x` is the preferred chart `chartAt E x`; on an analytic manifold
(`IsManifold 𝓘(ℂ, E) ω M`) this choice does not matter, but that is not proved here.

Source: Christian Schnell, *Complex Manifolds* (lecture notes), Definition 3.2 and its manifold
version (analytic subsets are closed, and locally the common zero set of finitely many
holomorphic functions). -/
def IsClosedAnalytic (Z : Set M) : Prop :=
  IsClosed Z ∧ ∀ x ∈ Z, ∃ U : Set E, IsOpen U ∧ chartAt E x x ∈ U ∧
    U ⊆ (chartAt E x).target ∧ ∃ (n : ℕ) (f : Fin n → E → ℂ), (∀ i, AnalyticOnNhd ℂ (f i) U) ∧
      ∀ z ∈ U, ((chartAt E x).symm z ∈ Z ↔ ∀ i, f i z = 0)

example : IsClosedAnalytic ℂ (∅ : Set ℂ) := ⟨isClosed_empty, by simp⟩

variable {E}

/-- A closed analytic set is closed. -/
theorem IsClosedAnalytic.isClosed {Z : Set M} (hZ : IsClosedAnalytic E Z) : IsClosed Z := hZ.1

/-- The defining local description may use any finite index type instead of `Fin n`. -/
theorem isClosedAnalytic_iff_finite {Z : Set M} :
    IsClosedAnalytic E Z ↔ IsClosed Z ∧ ∀ x ∈ Z, ∃ U : Set E, IsOpen U ∧ chartAt E x x ∈ U ∧
      U ⊆ (chartAt E x).target ∧ ∃ (ι : Type) (_ : Finite ι) (f : ι → E → ℂ),
        (∀ i, AnalyticOnNhd ℂ (f i) U) ∧ ∀ z ∈ U, ((chartAt E x).symm z ∈ Z ↔ ∀ i, f i z = 0) := by
  refine and_congr_right fun _ => forall₂_congr fun x _ => ?_
  refine exists_congr fun U => and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨n, f, hf, hZf⟩
    exact ⟨Fin n, inferInstance, f, hf, hZf⟩
  · rintro ⟨ι, _, f, hf, hZf⟩
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
    refine ⟨n, fun k => f (e.symm k), fun k => hf _, fun z hz => (hZf z hz).trans ⟨?_, ?_⟩⟩
    · exact fun h k => h _
    · intro h i
      simpa using h (e i)

/-- **Identity principle.**  On a connected space charted on a complex normed space, a closed
analytic subset with nonempty interior is the whole space.

Source: Christian Schnell, *Complex Manifolds* (lecture notes), Theorem 1.8 (identity theorem),
applied chart by chart; the interior is open, and closed because a point of its closure has a
ball-shaped chart neighbourhood on which each local equation vanishes on an open set. -/
theorem IsClosedAnalytic.eq_univ_of_nonempty_interior [ConnectedSpace M] {Z : Set M}
    (hZ : IsClosedAnalytic E Z) (h : (interior Z).Nonempty) : Z = univ := by
  have hcl : closure (interior Z) ⊆ interior Z := by
    intro x hx
    have hxZ : x ∈ Z := hZ.isClosed.closure_subset (closure_mono interior_subset hx)
    obtain ⟨U, hUo, hxU, hUt, n, f, hf, hZf⟩ := hZ.2 x hxZ
    set e := chartAt E x
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hUo _ hxU
    set B := Metric.ball (e x) r
    have hNo : IsOpen (e.source ∩ e ⁻¹' B) :=
      e.continuousOn.isOpen_inter_preimage e.open_source Metric.isOpen_ball
    have hxN : x ∈ e.source ∩ e ⁻¹' B := ⟨mem_chart_source E x, Metric.mem_ball_self hr⟩
    -- points of `e.source ∩ e ⁻¹' B` lie in `Z` exactly when the `f i` vanish at their image
    have key : ∀ y ∈ e.source ∩ e ⁻¹' B, (y ∈ Z ↔ ∀ i, f i (e y) = 0) := fun y hy => by
      simpa [e.left_inv hy.1] using hZf (e y) (hrU hy.2)
    obtain ⟨y, hyN, hyI⟩ := mem_closure_iff.1 hx _ hNo hxN
    have hvan : ∀ i, EqOn (f i) 0 B := fun i => by
      refine ((hf i).mono hrU).eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (convex_ball _ _).isPreconnected hyN.2 ?_
      have hmem : e '' (e.source ∩ e ⁻¹' B ∩ interior Z) ∈ 𝓝 (e y) :=
        e.image_mem_nhds hyN.1 ((hNo.inter isOpen_interior).mem_nhds ⟨hyN, hyI⟩)
      filter_upwards [hmem]
      rintro _ ⟨v, ⟨hvN, hvI⟩, rfl⟩
      exact (key v hvN).1 (interior_subset hvI) i
    refine mem_interior_iff_mem_nhds.2 (mem_of_superset (hNo.mem_nhds hxN) fun y hy => ?_)
    exact (key y hy).2 fun i => hvan i hy.2
  have hclopen : IsClopen (interior Z) :=
    ⟨closure_subset_iff_isClosed.1 hcl, isOpen_interior⟩
  exact eq_univ_of_univ_subset ((hclopen.eq_univ h).symm ▸ interior_subset)

/-- The empty set is closed analytic. -/
theorem isClosedAnalytic_empty : IsClosedAnalytic E (∅ : Set M) :=
  ⟨isClosed_empty, by simp⟩

/-- The whole space is closed analytic: no equations, on the chart's target. -/
theorem isClosedAnalytic_univ : IsClosedAnalytic E (univ : Set M) := by
  refine ⟨isClosed_univ, fun x _ => ⟨_, (chartAt E x).open_target, mem_chart_target E x,
    subset_rfl, 0, Fin.elim0, fun i => i.elim0, fun z _ => ?_⟩⟩
  simp

/-- The intersection of two closed analytic sets is closed analytic: concatenate the equations. -/
theorem IsClosedAnalytic.inter {Z₁ Z₂ : Set M} (h₁ : IsClosedAnalytic E Z₁)
    (h₂ : IsClosedAnalytic E Z₂) : IsClosedAnalytic E (Z₁ ∩ Z₂) := by
  rw [isClosedAnalytic_iff_finite] at h₁ h₂ ⊢
  refine ⟨h₁.1.inter h₂.1, fun x hx => ?_⟩
  obtain ⟨U₁, hU₁o, hxU₁, hU₁t, ι₁, _, f₁, hf₁, hZf₁⟩ := h₁.2 x hx.1
  obtain ⟨U₂, hU₂o, hxU₂, -, ι₂, _, f₂, hf₂, hZf₂⟩ := h₂.2 x hx.2
  refine ⟨U₁ ∩ U₂, hU₁o.inter hU₂o, ⟨hxU₁, hxU₂⟩, inter_subset_left.trans hU₁t, ι₁ ⊕ ι₂,
    inferInstance, Sum.elim f₁ f₂, ?_, fun z hz => ?_⟩
  · rintro (i | i)
    · exact (hf₁ i).mono inter_subset_left
    · exact (hf₂ i).mono inter_subset_right
  · rw [mem_inter_iff, hZf₁ z hz.1, hZf₂ z hz.2, Sum.forall]
    rfl

/-- The union of two closed analytic sets is closed analytic: near a point of both, take all
pairwise products of the equations; near a point of only one, the other is absent. -/
theorem IsClosedAnalytic.union {Z₁ Z₂ : Set M} (h₁ : IsClosedAnalytic E Z₁)
    (h₂ : IsClosedAnalytic E Z₂) : IsClosedAnalytic E (Z₁ ∪ Z₂) := by
  -- near a point outside `W`, a local description of `Z` also describes `Z ∪ W`
  have away : ∀ {Z W : Set M}, IsClosedAnalytic E Z → IsClosed W → ∀ x ∈ Z, x ∉ W →
      ∃ U : Set E, IsOpen U ∧ chartAt E x x ∈ U ∧ U ⊆ (chartAt E x).target ∧
        ∃ (n : ℕ) (f : Fin n → E → ℂ), (∀ i, AnalyticOnNhd ℂ (f i) U) ∧
          ∀ z ∈ U, ((chartAt E x).symm z ∈ Z ∪ W ↔ ∀ i, f i z = 0) := by
    intro Z W hZ hW x hxZ hxW
    obtain ⟨U, hUo, hxU, hUt, n, f, hf, hZf⟩ := hZ.2 x hxZ
    refine ⟨U ∩ ((chartAt E x).target ∩ (chartAt E x).symm ⁻¹' Wᶜ),
      hUo.inter ((chartAt E x).isOpen_inter_preimage_symm hW.isOpen_compl),
      ⟨hxU, mem_chart_target E x, ?_⟩, inter_subset_left.trans hUt, n, f,
      fun i => (hf i).mono inter_subset_left, fun z hz => ?_⟩
    · simpa [(chartAt E x).left_inv (mem_chart_source E x)] using hxW
    · have : (chartAt E x).symm z ∉ W := hz.2.2
      rw [← hZf z hz.1]
      simp [this]
  refine ⟨h₁.isClosed.union h₂.isClosed, fun x hx => ?_⟩
  by_cases hx₁ : x ∈ Z₁ <;> by_cases hx₂ : x ∈ Z₂
  · have h₁' := (isClosedAnalytic_iff_finite.1 h₁).2 x hx₁
    have h₂' := (isClosedAnalytic_iff_finite.1 h₂).2 x hx₂
    obtain ⟨U₁, hU₁o, hxU₁, hU₁t, ι₁, _, f₁, hf₁, hZf₁⟩ := h₁'
    obtain ⟨U₂, hU₂o, hxU₂, -, ι₂, _, f₂, hf₂, hZf₂⟩ := h₂'
    -- index the pairwise products by `Fin m`
    obtain ⟨m, ⟨eq⟩⟩ := Finite.exists_equiv_fin (ι₁ × ι₂)
    refine ⟨U₁ ∩ U₂, hU₁o.inter hU₂o, ⟨hxU₁, hxU₂⟩, inter_subset_left.trans hU₁t, m,
      fun k z => f₁ (eq.symm k).1 z * f₂ (eq.symm k).2 z,
      fun k => ((hf₁ _).mono inter_subset_left).mul ((hf₂ _).mono inter_subset_right),
      fun z hz => ?_⟩
    rw [mem_union, hZf₁ z hz.1, hZf₂ z hz.2]
    constructor
    · rintro (h | h) k <;> simp [h]
    · intro h
      by_contra hne
      push Not at hne
      obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hne
      exact mul_ne_zero hi hj (by simpa using h (eq (i, j)))
  · exact away h₁ h₂.isClosed x hx₁ hx₂
  · simpa only [union_comm] using away h₂ h₁.isClosed x hx₂ hx₁
  · exact absurd hx (by simp [hx₁, hx₂])

/-- A finite union of closed analytic sets is closed analytic. -/
theorem IsClosedAnalytic.biUnion_finset {ι : Type*} (s : Finset ι) {Z : ι → Set M}
    (h : ∀ i ∈ s, IsClosedAnalytic E (Z i)) : IsClosedAnalytic E (⋃ i ∈ s, Z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isClosedAnalytic_empty
  | insert a t _ ih =>
    rw [Finset.set_biUnion_insert]
    exact (h a (by simp)).union (ih fun i hi => h i (by simp [hi]))

/-- A finite intersection of closed analytic sets is closed analytic. -/
theorem IsClosedAnalytic.biInter_finset {ι : Type*} (s : Finset ι) {Z : ι → Set M}
    (h : ∀ i ∈ s, IsClosedAnalytic E (Z i)) : IsClosedAnalytic E (⋂ i ∈ s, Z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isClosedAnalytic_univ
  | insert a t _ ih =>
    rw [Finset.set_biInter_insert]
    exact (h a (by simp)).inter (ih fun i hi => h i (by simp [hi]))

/-! ### Examples on `ℂ` -/

/-- A point of `ℂ` is closed analytic, cut out by `z - a`. -/
theorem isClosedAnalytic_singleton (a : ℂ) : IsClosedAnalytic ℂ ({a} : Set ℂ) := by
  refine ⟨isClosed_singleton, fun x _ => ⟨univ, isOpen_univ, mem_univ _, by simp, 1,
    fun _ z => z - a, fun _ => analyticOnNhd_id.sub analyticOnNhd_const, fun z _ => ?_⟩⟩
  simp [sub_eq_zero]

example (a : ℂ) : interior ({a} : Set ℂ) = ∅ := interior_singleton a

/-- **Falsification.**  The imaginary axis is closed but not closed analytic: a holomorphic
function of one variable vanishing on it near `0` vanishes on a neighbourhood of `0`, which would
put a disc into the axis. -/
theorem not_isClosedAnalytic_re_eq_zero : ¬ IsClosedAnalytic ℂ {z : ℂ | z.re = 0} := by
  rintro ⟨-, h⟩
  obtain ⟨U, hUo, h0U, -, n, f, hf, hZf⟩ := h 0 (by simp)
  simp only [chartAt_self_eq, OpenPartialHomeomorph.refl_apply, OpenPartialHomeomorph.refl_symm,
    id_eq, mem_ofPred_eq] at h0U hZf
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hUo 0 h0U
  -- each `f i` vanishes near `0`: otherwise it would be nonzero at small points of the axis
  have hloc : ∀ i, ∀ᶠ z in 𝓝 (0 : ℂ), f i z = 0 := fun i => by
    refine ((hf i 0 h0U).eventually_eq_zero_or_eventually_ne_zero).resolve_right fun hne => ?_
    obtain ⟨ε, hε, hεne⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hne)
    obtain ⟨t, ht, htm⟩ := exists_between (lt_min hε hr)
    obtain ⟨htε, htr⟩ := lt_min_iff.1 htm
    have hnorm : dist ((t : ℂ) * Complex.I) 0 = t := by
      simp [Complex.norm_real, abs_of_pos ht]
    refine hεne (by rwa [hnorm]) (by simp [ht.ne']) ?_
    exact (hZf _ (hrU (by rwa [Metric.mem_ball, hnorm]))).1 (by simp) i
  obtain ⟨δ, hδ, hδ0⟩ := Metric.eventually_nhds_iff.1 (eventually_all.2 hloc)
  obtain ⟨s, hs, hsm⟩ := exists_between (lt_min hδ hr)
  obtain ⟨hsδ, hsr⟩ := lt_min_iff.1 hsm
  have hnorm : dist (s : ℂ) 0 = s := by simp [abs_of_pos hs]
  have := (hZf _ (hrU (by rwa [Metric.mem_ball, hnorm]))).2 (hδ0 (by rwa [hnorm]))
  simp [hs.ne'] at this

example : IsClosed {z : ℂ | z.re = 0} := isClosed_eq Complex.continuous_re continuous_const

/-- On `ℂ`, a closed analytic set with nonempty interior is everything. -/
example (Z : Set ℂ) (hZ : IsClosedAnalytic ℂ Z) (h : (interior Z).Nonempty) : Z = univ :=
  hZ.eq_univ_of_nonempty_interior h

example : IsClosedAnalytic ℂ ({0, 1} : Set ℂ) :=
  (isClosedAnalytic_singleton 0).union (isClosedAnalytic_singleton 1)

/-- On `ℂ²`, the line `{z₁ = 0}` is closed analytic, cut out by the first coordinate. -/
example : IsClosedAnalytic (ℂ × ℂ) {p : ℂ × ℂ | p.1 = 0} := by
  refine ⟨isClosed_eq continuous_fst continuous_const, fun x _ => ⟨univ, isOpen_univ, mem_univ _,
    by simp, 1, fun _ p => p.1, fun _ => (ContinuousLinearMap.fst ℂ ℂ ℂ).analyticOnNhd _,
    fun z _ => ?_⟩⟩
  simp

end HodgeLean.Foundations
