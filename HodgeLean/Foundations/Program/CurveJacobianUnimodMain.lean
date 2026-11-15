import HodgeLean.Foundations.Program.CurveJacobianUnimodCount
import HodgeLean.Foundations.Program.CurveJacobianUnimodAlg

/-! # Track B3, lane Unimod: dual level loops exist

`b3Unimod_level`: on a compact connected Riemann surface, a holomorphic form `θ ≠ 0` with integral
real periods and finitely many loops `δ` give loops `Γ₁, …, Γ_k` transverse to every `δ` with
`Σᵢ Γᵢ · δ = Re ∫_δ θ`. Let `f` be the real primitive of `θ` mod `1`. Choose a level `c` that
avoids `f` of the finitely many zeros of `θ` and is regular for the lifts
`F_δ(t) = f(δ 0) + Re ∫₀ᵗ θ(δ, δ')` (critical values have measure zero). The level set
`L = {f ∈ c + ℤ}` is compact and is the disjoint union of finitely many orbits of periodic vertical
curves; their loops meet each `δ` transversally, and the signed count of the crossings is the
degree of `F_δ - c` mod `1`, which is `Re ∫_δ θ` (`CurveJacobianUnimodDegree.lean`).
With `CurveJacobianUnimodAlg.lean` this makes the intersection form unimodular
(`b3Unimod_intersectionForm_bijective`).
HC no distance; AV milestone no distance.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold
open scoped Topology ContDiff

namespace HodgeLean.Foundations.Program

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

attribute [local instance] b3Forms_isManifold_real

section Lift

variable (θ : b3_HolForm E C) (δ : b3_SmoothLoop E C)

/-- The integrand `θ(δ, δ')` along a loop. -/
def b3Unimod_X (t : ℝ) : ℂ := θ.1 ⟨δ.1 t, b3_velocity E C δ.1 t⟩

theorem b3Unimod_X_continuous : Continuous (b3Unimod_X θ δ) :=
  b3Forms_continuous_holIntegrand θ δ.2.2

theorem b3Unimod_X_periodic : Function.Periodic (b3Unimod_X θ δ) 1 := by
  intro t
  have h := b3Rest2_velocity_add_int δ.2.2 δ.2.1 t 1
  simp only [Int.cast_one] at h
  simp only [b3Unimod_X]
  rw [b3Forms_velocity_eq_b3, b3Forms_velocity_eq_b3, h]
  have key : ∀ (x y : C) (_ : x = y) (v : E), θ.1 ⟨x, v⟩ = θ.1 ⟨y, v⟩ := by
    rintro x _ rfl v; rfl
  exact key _ _ (δ.2.1 t) _

theorem b3Unimod_hasDerivAt_lift (t : ℝ) :
    HasDerivAt (fun t ↦ (∫ s in (0 : ℝ)..t, b3Unimod_X θ δ s).re) (b3Unimod_X θ δ t).re t :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
    ((b3Unimod_X_continuous θ δ).integral_hasStrictDerivAt 0 t).hasDerivAt

theorem b3Unimod_lift_add_one (t : ℝ) :
    (∫ s in (0 : ℝ)..t + 1, b3Unimod_X θ δ s).re =
      (∫ s in (0 : ℝ)..t, b3Unimod_X θ δ s).re + (b3_period E C δ θ).re := by
  have hi : ∀ a b : ℝ, IntervalIntegrable (b3Unimod_X θ δ) MeasureTheory.volume a b :=
    fun a b ↦ (b3Unimod_X_continuous θ δ).intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 t) (hi t (t + 1)),
    (b3Unimod_X_periodic θ δ).intervalIntegral_add_eq t 0, zero_add, Complex.add_re]
  rfl

theorem b3Unimod_X_fract (t : ℝ) :
    b3Unimod_X θ δ (Int.fract t) = b3Unimod_X θ δ t ∧ δ.1 (Int.fract t) = δ.1 t := by
  have e : Int.fract t + (⌊t⌋ : ℝ) * 1 = t := by rw [mul_one]; exact Int.fract_add_floor t
  constructor
  · conv_rhs => rw [← e]
    exact ((b3Unimod_X_periodic θ δ).int_mul ⌊t⌋ (Int.fract t)).symm
  · conv_rhs => rw [← e]
    exact (δ.2.1.int_mul ⌊t⌋ (Int.fract t)).symm

variable [ConnectedSpace C]

/-- **Membership in the level set along a loop**, through the lift. -/
theorem b3Unimod_level_iff (hint : ∀ γ : b3_SmoothLoop E C, ∃ m : ℤ, (b3_period E C γ θ).re = m)
    (p₀ : C) (c t : ℝ) :
    δ.1 t ∈ b3Unimod_L θ p₀ c ↔ ∃ m : ℤ,
      b3Unimod_f θ p₀ (δ.1 0) + (∫ s in (0 : ℝ)..t, b3Unimod_X θ δ s).re = c + m := by
  obtain ⟨m', hm'⟩ := b3Unimod_f_path hint p₀ δ.2.2 0 t
  change _ = (∫ s in (0 : ℝ)..t, b3Unimod_X θ δ s).re + m' at hm'
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m - m', by push_cast; linarith⟩
  · rintro ⟨m, hm⟩
    exact ⟨m + m', by push_cast; linarith⟩

end Lift

/-- **Dual level loops exist** on a compact connected Riemann surface. -/
theorem b3Unimod_level [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) : b3Unimod_Level E C := by
  classical
  intro θ hint D
  by_cases hθ : θ = 0
  · refine ⟨0, Fin.elim0, fun δ _ ↦ ⟨fun i ↦ i.elim0, ?_⟩⟩
    rw [hθ, b3Forms_linearDual_apply_zero (b3Forms_period_mem_linearDual δ)]
    simp
  obtain ⟨p₀⟩ : Nonempty C := inferInstance
  -- the lifts along the loops of `D`
  set e : Fin D.card ≃ D := D.equivFin.symm
  set F : Fin D.card → ℝ → ℝ := fun j t ↦
    b3Unimod_f θ p₀ ((e j).1.1 0) + (∫ s in (0 : ℝ)..t, b3Unimod_X θ (e j).1 s).re
  set F' : Fin D.card → ℝ → ℝ := fun j t ↦ (b3Unimod_X θ (e j).1 t).re
  have hF : ∀ j t, HasDerivAt (F j) (F' j t) t := fun j t ↦
    (b3Unimod_hasDerivAt_lift θ (e j).1 t).const_add _
  -- a regular level avoiding the zeros of `θ`
  have hZ : (b3Unimod_Z θ).Finite := b3Unimod_Z_finite hE hθ
  set A : Set ℝ := ⋃ z ∈ b3Unimod_Z θ, range fun m : ℤ ↦ b3Unimod_f θ p₀ z - m
  have hA : A.Countable := hZ.countable.biUnion fun z _ ↦ countable_range _
  obtain ⟨c, hcA, hreg⟩ := b3Unimod_exists_regular F F' hF hA
  set L := b3Unimod_L θ p₀ c
  have hLZ : ∀ y ∈ L, y ∉ b3Unimod_Z θ := by
    rintro y ⟨m, hm⟩ hyZ
    exact hcA (mem_biUnion hyZ ⟨m, by simp only; linarith⟩)
  have hLc : IsCompact L := (b3Unimod_isClosed_level hint hE p₀ c).isCompact
  obtain ⟨ρ₀, hρ₀, hch₀⟩ := b3Unimod_uniform_charts hE θ hLc hLZ
  set ρ := min ρ₀ (1 / 4)
  have hρ : 0 < ρ := lt_min hρ₀ (by norm_num)
  have hρ4 : ρ ≤ 1 / 4 := min_le_right _ _
  have hch : ∀ y ∈ L, ∃ Fl : b3Unimod_Flat hE θ, y ∈ Fl.F.source ∧
      Metric.ball (Fl.F y) ρ ⊆ Fl.F.target := fun y hy ↦ by
    obtain ⟨Fl, h1, h2⟩ := hch₀ y hy
    exact ⟨Fl, h1, (Metric.ball_subset_ball (min_le_left _ _)).trans h2⟩
  -- periodic vertical curves through the points of `L`
  have hcl := fun y : L ↦ b3Unimod_exists_closed hint p₀ c hE hρ hρ4 hch y.2
  choose τ hτ hτ0 hτL T hT hper hinj using hcl
  have hnhds : ∀ y : L, ∃ N ∈ 𝓝 (y : C), N ∩ L ⊆ range (τ y) := fun y ↦ by
    have := b3Unimod_orbit_nhds hint p₀ c hρ hρ4 hch (hτ y) (hτL y) 0
    rwa [hτ0] at this
  choose N hN hNsub using hnhds
  obtain ⟨t, ht⟩ := hLc.elim_nhds_subcover' (fun y hy ↦ N ⟨y, hy⟩) fun y hy ↦ hN ⟨y, hy⟩
  -- orbits are equal or disjoint
  have horb : ∀ y y' : L, (range (τ y) ∩ range (τ y')).Nonempty →
      range (τ y) = range (τ y') := by
    rintro y y' ⟨z, ⟨s, hs⟩, ⟨s', hs'⟩⟩
    have h := (hτ y).shift_eq (hτ y') (hs.trans hs'.symm)
    ext w
    constructor
    · rintro ⟨r, rfl⟩
      refine ⟨s' + (r - s), ?_⟩
      rw [← h]
      congr 1
      ring
    · rintro ⟨r, rfl⟩
      refine ⟨s + (r - s'), ?_⟩
      rw [h]
      congr 1
      ring
  set S : Finset (Set C) := t.image fun y ↦ range (τ y)
  have hrep : ∀ Ω : S, ∃ y : L, range (τ y) = Ω := fun Ω ↦ by
    obtain ⟨y, -, hy⟩ := Finset.mem_image.1 Ω.2
    exact ⟨y, hy⟩
  choose rep hrep using hrep
  set τ' : S → ℝ → C := fun Ω ↦ τ (rep Ω)
  have hτ' : ∀ Ω, b3Unimod_Vertical hE θ (τ' Ω) := fun Ω ↦ hτ _
  have hper' : ∀ Ω, Function.Periodic (τ' Ω) (T (rep Ω)) := fun Ω ↦ hper _
  have hdisj : Pairwise fun Ω Ω' : S ↦ Disjoint (range (τ' Ω)) (range (τ' Ω')) := by
    intro Ω Ω' hne
    rw [Set.disjoint_iff_inter_eq_empty]
    by_contra hne'
    have := horb _ _ (nonempty_iff_ne_empty.2 hne')
    exact hne (Subtype.ext ((hrep Ω).symm.trans (this.trans (hrep Ω'))))
  have hcover : ⋃ Ω, range (τ' Ω) = L := by
    ext z
    rw [mem_iUnion]
    constructor
    · rintro ⟨Ω, s, rfl⟩
      exact hτL _ s
    · intro hz
      obtain ⟨y, hyt, hzy⟩ := mem_iUnion₂.1 (ht hz)
      have hzr := hNsub y ⟨hzy, hz⟩
      refine ⟨⟨range (τ y), Finset.mem_image_of_mem _ hyt⟩, ?_⟩
      show z ∈ range (τ (rep _))
      rw [hrep]
      exact hzr
  -- conclusion, loop by loop
  set eS : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  refine ⟨Fintype.card S, fun i ↦ b3Unimod_loop (hτ' (eS i)) (hper' (eS i)), fun δ hδ ↦ ?_⟩
  set j := e.symm ⟨δ, hδ⟩
  have hej : (e j).1 = δ := by simp [j]
  have htr : ∀ t, δ.1 t ∈ L → (θ.1 ⟨δ.1 t, b3_velocity E C δ.1 t⟩).re ≠ 0 := by
    intro t htL
    obtain ⟨hXf, hδf⟩ := b3Unimod_X_fract θ δ t
    change (b3Unimod_X θ δ t).re ≠ 0
    rw [← hXf]
    rw [← hδf] at htL
    obtain ⟨m, hm⟩ := (b3Unimod_level_iff θ δ hint p₀ c _).1 htL
    have := hreg j (Int.fract t) ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩ m
      (by simp only [F, hej]; exact hm)
    simpa only [F', hej] using this
  obtain ⟨htrans, hfin, hsum⟩ := b3Unimod_sum_intersection hτ' (fun Ω ↦ hT _) hper'
    (fun Ω ↦ hinj _) hdisj hcover δ htr
  refine ⟨fun i ↦ htrans (eS i), ?_⟩
  have hreidx : (∑ i : Fin (Fintype.card S),
      b3_intersection E (b3Unimod_loop (hτ' (eS i)) (hper' (eS i))) δ) =
      ∑ Ω : S, b3_intersection E (b3Unimod_loop (hτ' Ω) (hper' Ω)) δ :=
    Equiv.sum_comp eS fun Ω ↦ b3_intersection E (b3Unimod_loop (hτ' Ω) (hper' Ω)) δ
  rw [hreidx, hsum]
  -- the degree of the lift
  obtain ⟨n₀, hn₀⟩ := hint δ
  set g : ℝ → ℝ := fun t ↦
    b3Unimod_f θ p₀ (δ.1 0) + (∫ s in (0 : ℝ)..t, b3Unimod_X θ δ s).re - c
  have hg : ∀ t, HasDerivAt g (b3Unimod_X θ δ t).re t := fun t ↦
    ((b3Unimod_hasDerivAt_lift θ δ t).const_add _).sub_const c
  have hg' : Continuous fun t ↦ (b3Unimod_X θ δ t).re :=
    Complex.continuous_re.comp (b3Unimod_X_continuous θ δ)
  have hgper : ∀ t, g (t + 1) = g t + n₀ := by
    intro t
    simp only [g]
    rw [b3Unimod_lift_add_one, hn₀]
    ring
  have hset : {t | t ∈ Ico (0 : ℝ) 1 ∧ δ.1 t ∈ L} =
      {t | t ∈ Ico (0 : ℝ) 1 ∧ ∃ m : ℤ, g t = m} := by
    ext t
    simp only [mem_ofPred_eq]
    rw [b3Unimod_level_iff θ δ hint p₀ c t]
    constructor
    · rintro ⟨h1, m, hm⟩; exact ⟨h1, m, by simp only [g]; linarith⟩
    · rintro ⟨h1, m, hm⟩; exact ⟨h1, m, by simp only [g] at hm; linarith⟩
  have hregd : ∀ t ∈ Icc (0 : ℝ) 1, (∃ m : ℤ, g t = m) → (b3Unimod_X θ δ t).re ≠ 0 := by
    rintro t ht ⟨m, hm⟩
    have := hreg j t ht m (by simp only [F, hej]; simp only [g] at hm; linarith)
    simpa only [F', hej] using this
  rw [hset] at hfin ⊢
  have hdeg : (∑ᶠ t ∈ {t | t ∈ Ico (0 : ℝ) 1 ∧ ∃ m : ℤ, g t = m},
      ((SignType.sign (θ.1 ⟨δ.1 t, b3_velocity E C δ.1 t⟩).re : SignType) : ℤ)) = n₀ :=
    b3Unimod_degree hg hg' hgper hregd hfin
  rw [hdeg, hn₀]

/-- **The intersection form is unimodular.** -/
theorem b3Unimod_intersectionForm_bijective [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (Q : LinearMap.BilinForm ℤ (b3_periodLattice E C))
    (hQ : b3_IsIntersectionForm E Q) : Function.Bijective Q := by
  let : MeasurableSpace E := borel E
  have : BorelSpace E := ⟨rfl⟩
  exact b3Unimod_bijective_of_level hE (b3Unimod_level hE) Q hQ

end HodgeLean.Foundations.Program
