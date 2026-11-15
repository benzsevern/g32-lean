import HodgeLean.Foundations.Program.CoverDictionaryExtend

/-! # B6-5 stage 5d, stage four: descent of invariant vectors of forms

For holomorphic forms `ω₀, …, ω₃` on a fibre and a matrix function `N` analytic in charts at the
regular points and meromorphic in charts everywhere, if the vector `g = N · (ωᵢ/ds)` is invariant
under the deck group on the regular locus, then `g = r(s)` there for a rational vector `r` whose
denominators vanish only at the poles (`b65g_descend_generic`): `g` descends to a function of `s`
that is analytic off the poles (local sections of the covering of stage three), meromorphic at
the poles and at `∞` (`caf_meromorphicAt_of_comp_pow`), hence rational
(`caf_ratFunc_of_meromorphic`).
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Filter Matrix Manifold
open scoped Topology ContDiff
open HodgeLean.Papers
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

local notation "𝔼" => (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)

section General

variable {M : Type} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ, ℂ) ω M]

/-- The chart coefficient of a holomorphic form is analytic on the chart target. -/
theorem caf_holForm_chart_analytic (ω' : TangentBundle 𝓘(ℂ, ℂ) M → ℂ)
    (hω : ω' ∈ b3_HolForm ℂ M) (x : M) (z : ℂ) (hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) x).target) :
    AnalyticAt ℂ (fun z ↦ ω' ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z,
      mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ)⟩) z := by
  have h1 : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun z : ℂ ↦ ω' ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z,
      mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ)⟩) z :=
    (hω.1 _).comp _ (caf_contMDiffAt_chart_field x z hz)
  exact (contMDiffAt_iff_contDiffAt.mp h1).analyticAt

/-- The chart vector `∂/∂z` is nonzero. -/
theorem caf_chart_vector_ne (x : M) (z : ℂ) (hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) x).target) :
    (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z) (1 : ℂ) ≠ 0 := by
  set L : ℂ →L[ℂ] ℂ := mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z
  set L' : ℂ →L[ℂ] ℂ := mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x)
    ((extChartAt 𝓘(ℂ, ℂ) x).symm z)
  have h2 : L (L' 1) = 1 := caf_mfderiv_chart_symm x z hz (1 : ℂ)
  intro h0
  have hL : L = 0 := ContinuousLinearMap.ext_ring (by rw [ContinuousLinearMap.zero_apply]; exact h0)
  rw [hL, ContinuousLinearMap.zero_apply] at h2
  exact zero_ne_one h2

/-- A holomorphic form on a tangent line is a multiple of its value at `1`. -/
theorem caf_holForm_apply_smul (ω' : TangentBundle 𝓘(ℂ, ℂ) M → ℂ) (hω : ω' ∈ b3_HolForm ℂ M)
    (y : M) (ξ : ℂ) : ω' ⟨y, ξ⟩ = ξ * ω' ⟨y, (1 : ℂ)⟩ := by
  have h0 : ω' ⟨y, 0⟩ = 0 := by
    have := hω.2 y 1 0 0
    simp only [one_smul, add_zero, one_mul] at this
    linear_combination -this
  have := hω.2 y ξ (1 : ℂ) 0
  rw [add_zero, h0, add_zero] at this
  rw [← this]
  congr 2
  change ξ = ξ * 1
  rw [mul_one]

end General

section Fibre

variable {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
  (t : b6t_polydisc c) {a b : ℂ}

/-- `ds` on a tangent line is a multiple of its value at `1`. -/
theorem b65g_ds_smul (y : b65z_fibre c D.C t) (ξ : ℂ) :
    b65g_ds D t a b ⟨y, ξ⟩ = ξ * b65g_ds D t a b ⟨y, (1 : ℂ)⟩ := by
  simp only [b65g_ds]
  set L : ℂ →L[ℂ] ℂ := mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b65g_sFun D t a b) y
  change L ξ = ξ * L 1
  rw [← smul_eq_mul, ← L.map_smul, smul_eq_mul, mul_one]

/-- A point over a finite `s` that is not a pole is regular. -/
theorem b65g_good_of_not_pole (hba : b - a ≠ 0) (poles : Fin 4 ⊕ Fin 12 → ℂ)
    (h0 : poles (Sum.inl 0) = 0) (x : b65z_fibre c D.C t)
    (hfin : b63d_projection c D.C D.atlas.f (b6t_polydisc c) (Subset.refl _) t x ≠
      ((b / (b - a) : ℂ) : OnePoint ℂ))
    (hs : b65g_sFun D t a b x ∉ Set.range poles) : x ∈ b65g_good D t a b poles := by
  by_contra hx
  obtain ⟨q, hq⟩ := b65g_nongood_pole D t hba poles h0 x hx hfin
  exact hs ⟨q, hq⟩

/-- Regular points with the same `s` lie in one orbit. -/
theorem b65g_good_orbit (hab : a * b ≠ 0) (hba : b - a ≠ 0) (poles : Fin 4 ⊕ Fin 12 → ℂ)
    {x y : b65z_fibre c D.C t} (hx : x ∈ b65g_good D t a b poles)
    (hy : y ∈ b65g_good D t a b poles) (hxy : b65g_sFun D t a b x = b65g_sFun D t a b y) :
    ∃ h : b4b_Group, h • x = y := by
  obtain ⟨z, hz, -, -⟩ := hx
  obtain ⟨z', hz', -, -⟩ := hy
  have : z = z' := by
    apply b65g_sCoord_injective hab hba
    simpa [b65g_sFun, hz, hz'] using hxy
  exact (D.hgal t).2 x y (by rw [hz, hz', this])

end Fibre


variable {p : Fin 12 → ℂ} (O : b65p_Outputs p) {g : Fin 13 → b4b_Group}
  (D : b65z_SharedFamily (b65z_centre p) g)

/-- **At a regular point the chart derivative of `s` does not vanish** (the regular locus is a
covering of the base, stage three). -/
theorem b65g_chart_deriv_ne_good (θ : ℂ) (hθO : θ ∈ ball (0 : ℂ) O.radius)
    (t : b6t_polydisc (b65z_centre p)) (ht : t.val = b65p_curve p θ)
    (x : b65z_fibre (b65z_centre p) D.C t)
    (hx : x ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ)) :
    deriv (fun z ↦ b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11)
      ((extChartAt 𝓘(ℂ, ℂ) x).symm z)) (extChartAt 𝓘(ℂ, ℂ) x x) ≠ 0 := by
  obtain ⟨ha, hb, hab⟩ := b65g_moving_ne p O θ hθO
  have hab' : b65p_moving p θ 10 * b65p_moving p θ 11 ≠ 0 := mul_ne_zero ha hb
  have hba : b65p_moving p θ 11 - b65p_moving p θ 10 ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hπ := b65g_quotientCovering p O g D θ hθO t ht
  obtain ⟨U, hUo, hxU, hinj⟩ := hπ.isLocalHomeomorph.isLocallyInjective ⟨x, hx⟩
  have hgo := b65g_good_isOpen D t hab' hba (b65p_poles p θ)
  refine b65g_chart_deriv_ne D t hab' hba x (b65g_good_finite D t hba hx)
    ⟨Subtype.val '' U, (hgo.isOpenMap_subtype_val U hUo).mem_nhds ⟨_, hxU, rfl⟩, ?_⟩
  rintro y₁ ⟨a₁, ha₁, rfl⟩ y₂ ⟨a₂, ha₂, rfl⟩ h
  have : b65g_sProj D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) a₁ =
      b65g_sProj D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) a₂ :=
    Subtype.ext h
  exact congrArg Subtype.val (hinj ha₁ ha₂ this)

/-- **`ds` does not vanish at regular points.** -/
theorem b65g_ds_ne_good (θ : ℂ) (hθO : θ ∈ ball (0 : ℂ) O.radius)
    (t : b6t_polydisc (b65z_centre p)) (ht : t.val = b65p_curve p θ)
    (x : b65z_fibre (b65z_centre p) D.C t)
    (hx : x ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ)) :
    b65g_ds D t (b65p_moving p θ 10) (b65p_moving p θ 11) ⟨x, (1 : ℂ)⟩ ≠ 0 := by
  obtain ⟨ha, hb, hab⟩ := b65g_moving_ne p O θ hθO
  have hab' : b65p_moving p θ 10 * b65p_moving p θ 11 ≠ 0 := mul_ne_zero ha hb
  have hba : b65p_moving p θ 11 - b65p_moving p θ 10 ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hd := b65g_chart_deriv_ne_good O D θ hθO t ht x hx
  set y := (extChartAt 𝓘(ℂ, ℂ) x).symm (extChartAt 𝓘(ℂ, ℂ) x x)
  have hyx : y = x := extChartAt_to_inv x
  have hy : y ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ) := by
    rw [hyx]; exact hx
  have hs : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      (b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11)) y := by
    obtain ⟨w, hw, hw', -⟩ := hy
    exact (b65g_sFun_hasMFDerivAt D t hab' hba y w hw hw').mdifferentiableAt
  have h1 := (b65g_ds_chart D t _ _ x _ (mem_extChartAt_target x) hs).deriv
  have hy1 : b65g_ds D t (b65p_moving p θ 10) (b65p_moving p θ 11) ⟨y, (1 : ℂ)⟩ ≠ 0 := by
    intro h0
    have hL : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b65g_sFun D t (b65p_moving p θ 10)
        (b65p_moving p θ 11)) y = 0 := ContinuousLinearMap.ext_ring h0
    apply hd
    rw [h1]
    change (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b65g_sFun D t (b65p_moving p θ 10)
        (b65p_moving p θ 11)) y) _ = 0
    rw [hL]
    rfl
  have key : ∀ y' : b65z_fibre (b65z_centre p) D.C t, y' = x →
      b65g_ds D t (b65p_moving p θ 10) (b65p_moving p θ 11) ⟨y', (1 : ℂ)⟩ ≠ 0 →
      b65g_ds D t (b65p_moving p θ 10) (b65p_moving p θ 11) ⟨x, (1 : ℂ)⟩ ≠ 0 := by
    rintro y' rfl h; exact h
  exact key y hyx hy1


/-- **The descended vector in a chart.** At regular points of a chart, the invariant vector
`N · (ωᵢ/ds)` is `N · (cᵢ/s')`, with `cᵢ` the chart coefficients of the forms. -/
theorem b65g_vector_chart (θ : ℂ) (hθO : θ ∈ ball (0 : ℂ) O.radius)
    (t : b6t_polydisc (b65z_centre p))
    (N : b65z_fibre (b65z_centre p) D.C t → Matrix (Fin 4) (Fin 4) ℂ)
    (ω' : Fin 4 → TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ)
    (hω : ∀ i, ω' i ∈ b3_HolForm ℂ (b65z_fibre (b65z_centre p) D.C t))
    (x : b65z_fibre (b65z_centre p) D.C t) (z : ℂ) (hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) x).target)
    (hg : (extChartAt 𝓘(ℂ, ℂ) x).symm z ∈
      b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ)) :
    N ((extChartAt 𝓘(ℂ, ℂ) x).symm z) *ᵥ (fun i ↦ ω' i ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z, (1 : ℂ)⟩ /
        b65g_ds D t (b65p_moving p θ 10) (b65p_moving p θ 11)
          ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z, (1 : ℂ)⟩) =
      N ((extChartAt 𝓘(ℂ, ℂ) x).symm z) *ᵥ (fun i ↦ ω' i ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z,
          mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ)⟩ /
        deriv (fun w ↦ b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11)
          ((extChartAt 𝓘(ℂ, ℂ) x).symm w)) z) := by
  obtain ⟨ha, hb, hab⟩ := b65g_moving_ne p O θ hθO
  have hab' : b65p_moving p θ 10 * b65p_moving p θ 11 ≠ 0 := mul_ne_zero ha hb
  have hba : b65p_moving p θ 11 - b65p_moving p θ 10 ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  set y := (extChartAt 𝓘(ℂ, ℂ) x).symm z
  have hs : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      (b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11)) y := by
    obtain ⟨w, hw, hw', -⟩ := hg
    exact (b65g_sFun_hasMFDerivAt D t hab' hba y w hw hw').mdifferentiableAt
  have h1 := (b65g_ds_chart D t _ _ x z hz hs).deriv
  set ξ : ℂ := mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ)
  have hξ : ξ ≠ 0 := caf_chart_vector_ne x z hz
  congr 1
  funext i
  rw [h1, caf_holForm_apply_smul _ (hω i) y ξ,
    b65g_ds_smul D t ((extChartAt 𝓘(ℂ, ℂ) x).symm z) ξ]
  exact (mul_div_mul_left (ω' i ⟨y, (1 : ℂ)⟩)
    (b65g_ds D t (b65p_moving p θ 10) (b65p_moving p θ 11) ⟨y, (1 : ℂ)⟩) hξ).symm

/-- **Descent of invariant vectors of forms** to rational vectors of `s`. -/
theorem b65g_descend_generic (θ : ℂ) (hθO : θ ∈ ball (0 : ℂ) O.radius)
    (t : b6t_polydisc (b65z_centre p)) (ht : t.val = b65p_curve p θ)
    (N : b65z_fibre (b65z_centre p) D.C t → Matrix (Fin 4) (Fin 4) ℂ)
    (ω' : Fin 4 → TangentBundle 𝓘(ℂ, ℂ) (b65z_fibre (b65z_centre p) D.C t) → ℂ)
    (hω : ∀ i, ω' i ∈ b3_HolForm ℂ (b65z_fibre (b65z_centre p) D.C t))
    (hNa : ∀ x ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ),
      ∀ i j, AnalyticAt ℂ (fun z ↦ N ((extChartAt 𝓘(ℂ, ℂ) x).symm z) i j)
        (extChartAt 𝓘(ℂ, ℂ) x x))
    (hNm : ∀ x, ∀ i j, MeromorphicAt (fun z ↦ N ((extChartAt 𝓘(ℂ, ℂ) x).symm z) i j)
        (extChartAt 𝓘(ℂ, ℂ) x x))
    (hinv : ∀ x ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ),
      ∀ h : b4b_Group, N (h • x) *ᵥ (fun i ↦ ω' i ⟨h • x, (1 : ℂ)⟩ /
          b65g_ds D t (b65p_moving p θ 10) (b65p_moving p θ 11) ⟨h • x, (1 : ℂ)⟩) =
        N x *ᵥ (fun i ↦ ω' i ⟨x, (1 : ℂ)⟩ /
          b65g_ds D t (b65p_moving p θ 10) (b65p_moving p θ 11) ⟨x, (1 : ℂ)⟩)) :
    ∃ r : Fin 4 → RatFunc ℂ, (∀ i s, (r i).denom.eval s = 0 → s ∈ Set.range (b65p_poles p θ)) ∧
      ∀ x ∈ b65g_good D t (b65p_moving p θ 10) (b65p_moving p θ 11) (b65p_poles p θ),
        N x *ᵥ (fun i ↦ ω' i ⟨x, (1 : ℂ)⟩ /
          b65g_ds D t (b65p_moving p θ 10) (b65p_moving p θ 11) ⟨x, (1 : ℂ)⟩) =
        fun j ↦ b65q_eval (r j) (b65g_sFun D t (b65p_moving p θ 10) (b65p_moving p θ 11) x) := by
  classical
  obtain ⟨ha, hb, hab⟩ := b65g_moving_ne p O θ hθO
  have hab' : b65p_moving p θ 10 * b65p_moving p θ 11 ≠ 0 := mul_ne_zero ha hb
  have hba : b65p_moving p θ 11 - b65p_moving p θ 10 ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  set a := b65p_moving p θ 10
  set b := b65p_moving p θ 11
  set poles := b65p_poles p θ
  set good := b65g_good D t a b poles
  set gf : b65z_fibre (b65z_centre p) D.C t → Fin 4 → ℂ := fun x ↦
    N x *ᵥ (fun i ↦ ω' i ⟨x, (1 : ℂ)⟩ / b65g_ds D t a b ⟨x, (1 : ℂ)⟩)
  set F : ℂ → Fin 4 → ℂ := fun s ↦
    if h : ∃ y, y ∈ good ∧ b65g_sFun D t a b y = s then gf h.choose else 0
  have hF : ∀ y ∈ good, F (b65g_sFun D t a b y) = gf y := by
    intro y hy
    have h : ∃ y', y' ∈ good ∧ b65g_sFun D t a b y' = b65g_sFun D t a b y := ⟨y, hy, rfl⟩
    simp only [F, dite_eq_left h]
    obtain ⟨hy', hys⟩ := h.choose_spec
    obtain ⟨k, hk⟩ := b65g_good_orbit D t hab' hba poles hy hy' hys.symm
    rw [← hk]
    exact hinv y hy k
  -- the chart expression at regular points of a chart
  have hchart : ∀ (x : b65z_fibre (b65z_centre p) D.C t) (z : ℂ)
      (hz : z ∈ (extChartAt 𝓘(ℂ, ℂ) x).target) (hg : (extChartAt 𝓘(ℂ, ℂ) x).symm z ∈ good),
      F (b65g_sFun D t a b ((extChartAt 𝓘(ℂ, ℂ) x).symm z)) =
        N ((extChartAt 𝓘(ℂ, ℂ) x).symm z) *ᵥ (fun i ↦ ω' i ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z,
            mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ)⟩ /
          deriv (fun w ↦ b65g_sFun D t a b ((extChartAt 𝓘(ℂ, ℂ) x).symm w)) z) := by
    intro x z hz hg
    rw [hF _ hg]
    exact b65g_vector_chart O D θ hθO t N ω' hω x z hz hg
  -- the chart expression is meromorphic everywhere
  have hEm : ∀ (x : b65z_fibre (b65z_centre p) D.C t),
      MeromorphicAt (deriv fun w ↦ b65g_sFun D t a b ((extChartAt 𝓘(ℂ, ℂ) x).symm w))
        (extChartAt 𝓘(ℂ, ℂ) x x) → ∀ j,
      MeromorphicAt (fun z ↦ (N ((extChartAt 𝓘(ℂ, ℂ) x).symm z) *ᵥ
        (fun i ↦ ω' i ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z,
            mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ)⟩ /
          deriv (fun w ↦ b65g_sFun D t a b ((extChartAt 𝓘(ℂ, ℂ) x).symm w)) z)) j)
        (extChartAt 𝓘(ℂ, ℂ) x x) := by
    intro x hd j
    refine caf_meromorphic_mulVec _ _ _ (hNm x) (fun i ↦ ?_) j
    exact ((caf_holForm_chart_analytic _ (hω i) x _ (mem_extChartAt_target x)).meromorphicAt).div hd
  -- the chart expression equals `F ∘ s` on a punctured chart disc
  have hpunct : ∀ (x : b65z_fibre (b65z_centre p) D.C t) (j : Fin 4),
      (fun z ↦ (N ((extChartAt 𝓘(ℂ, ℂ) x).symm z) *ᵥ
        (fun i ↦ ω' i ⟨(extChartAt 𝓘(ℂ, ℂ) x).symm z,
            mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x).symm z (1 : ℂ)⟩ /
          deriv (fun w ↦ b65g_sFun D t a b ((extChartAt 𝓘(ℂ, ℂ) x).symm w)) z)) j) =ᶠ[𝓝[≠]
        (extChartAt 𝓘(ℂ, ℂ) x x)]
      fun z ↦ F (b65g_sFun D t a b ((extChartAt 𝓘(ℂ, ℂ) x).symm z)) j := by
    intro x j
    filter_upwards [b65g_chart_punctured_good D t hab' hba poles x] with z ⟨hz, hg⟩
    rw [hchart x z hz hg]
  -- analyticity off the poles
  have hAn : ∀ s₀ ∉ Set.range poles, ∀ j, AnalyticAt ℂ (fun s ↦ F s j) s₀ := by
    intro s₀ hs₀ j
    obtain ⟨x₀, hfin, hxs⟩ := b65g_exists_over D t hab' hba s₀
    have hx₀ : x₀ ∈ good :=
      b65g_good_of_not_pole D t hba poles rfl x₀ hfin (by rw [hxs]; exact hs₀)
    have hsc := b65g_sFun_chart_analytic D t hba x₀ hfin
    have hd0 := b65g_chart_deriv_ne_good O D θ hθO t ht x₀ hx₀
    have hgo : IsOpen good := b65g_good_isOpen D t hab' hba poles
    have hnb : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) x₀ x₀), z ∈ (extChartAt 𝓘(ℂ, ℂ) x₀).target ∧
        (extChartAt 𝓘(ℂ, ℂ) x₀).symm z ∈ good := by
      have h1 : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) x₀ x₀), z ∈ (extChartAt 𝓘(ℂ, ℂ) x₀).target :=
        (isOpen_extChartAt_target x₀).mem_nhds (mem_extChartAt_target x₀)
      have h2 : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) x₀ x₀), (extChartAt 𝓘(ℂ, ℂ) x₀).symm z ∈ good :=
        (continuousAt_extChartAt_symm (I := 𝓘(ℂ, ℂ)) x₀).preimage_mem_nhds
          (by rw [extChartAt_to_inv]; exact hgo.mem_nhds hx₀)
      exact h1.and h2
    have hE : AnalyticAt ℂ (fun z ↦ (N ((extChartAt 𝓘(ℂ, ℂ) x₀).symm z) *ᵥ
        (fun i ↦ ω' i ⟨(extChartAt 𝓘(ℂ, ℂ) x₀).symm z,
            mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (extChartAt 𝓘(ℂ, ℂ) x₀).symm z (1 : ℂ)⟩ /
          deriv (fun w ↦ b65g_sFun D t a b ((extChartAt 𝓘(ℂ, ℂ) x₀).symm w)) z)) j)
        (extChartAt 𝓘(ℂ, ℂ) x₀ x₀) := by
      simp only [Matrix.mulVec, dotProduct]
      exact Finset.analyticAt_fun_sum _ fun k _ ↦ (hNa x₀ hx₀ j k).mul
        ((caf_holForm_chart_analytic _ (hω k) x₀ _ (mem_extChartAt_target x₀)).div hsc.deriv hd0)
    have hcomp : AnalyticAt ℂ ((fun s ↦ F s j) ∘
        fun z ↦ b65g_sFun D t a b ((extChartAt 𝓘(ℂ, ℂ) x₀).symm z))
        (extChartAt 𝓘(ℂ, ℂ) x₀ x₀) := by
      refine hE.congr ?_
      filter_upwards [hnb] with z ⟨hz, hg⟩
      rw [Function.comp_apply, hchart x₀ z hz hg]
    have := (analyticAt_comp_iff_of_deriv_ne_zero hsc hd0).mp hcomp
    have hsc0 : b65g_sFun D t a b ((extChartAt 𝓘(ℂ, ℂ) x₀).symm (extChartAt 𝓘(ℂ, ℂ) x₀ x₀)) =
        s₀ := by rw [extChartAt_to_inv, hxs]
    rwa [hsc0] at this
  -- punctured neighbourhoods of a point contain no pole
  have hpole_punct : ∀ s : ℂ, ∀ᶠ σ in 𝓝[≠] s, σ ∉ Set.range poles := by
    intro s
    have hfin : (Set.range poles \ {s}).Finite := (Set.finite_range poles).subset sdiff_subset
    filter_upwards [nhdsWithin_le_nhds (hfin.isClosed.isOpen_compl.mem_nhds
      (by simp : s ∈ (Set.range poles \ {s})ᶜ)), self_mem_nhdsWithin] with σ h1 h2 h3
    exact h1 ⟨h3, h2⟩
  -- meromorphy at the poles
  have hMer : ∀ q j, MeromorphicAt (fun s ↦ F s j) (poles q) := by
    intro q j
    obtain ⟨x, hfin, hxs⟩ := b65g_exists_over D t hab' hba (poles q)
    obtain ⟨e, he, l, hl, hl0, hs⟩ := b65g_sFun_root D t hab' hba x hfin
    have hsc := b65g_sFun_chart_analytic D t hba x hfin
    have hcomp := (hEm x hsc.deriv.meromorphicAt j).congr (hpunct x j)
    set z₀ := extChartAt 𝓘(ℂ, ℂ) x x
    have hcomp2 : MeromorphicAt (fun z ↦ F (poles q + ((z - z₀) * l z) ^ e) j) z₀ := by
      refine hcomp.congr (nhdsWithin_le_nhds ?_)
      filter_upwards [hs] with z hz
      rw [hz, hxs]
    set κ : ℂ → ℂ := fun z ↦ (z - z₀) * l z
    have hκ : AnalyticAt ℂ κ z₀ := (analyticAt_id.sub analyticAt_const).mul hl
    have hκ' : deriv κ z₀ ≠ 0 := by
      have h := ((hasDerivAt_id z₀).sub_const z₀).mul hl.differentiableAt.hasDerivAt
      rw [show (1 : ℂ) * l z₀ + (id z₀ - z₀) * deriv l z₀ = l z₀ by simp] at h
      rw [show deriv κ z₀ = l z₀ from h.deriv]; exact hl0
    have h3 := (meromorphicAt_comp_iff_of_deriv_ne_zero (f := fun y ↦ F (poles q + y ^ e) j)
      hκ hκ').mp hcomp2
    rw [show κ z₀ = 0 by simp [κ]] at h3
    refine caf_meromorphicAt_of_comp_pow (fun s ↦ F s j) (poles q) e he ?_ h3
    filter_upwards [hpole_punct (poles q)] with σ hσ using hAn σ hσ j
  -- meromorphy at infinity
  have hInf : ∀ j, MeromorphicAt (fun w ↦ F w⁻¹ j) 0 := by
    intro j
    obtain ⟨x, hx⟩ := D.hsurj t ((b / (b - a) : ℂ) : OnePoint ℂ)
    obtain ⟨e, he, l, hl, hl0, hs⟩ := b65g_sFun_root_infty D t hab' hba x hx
    set z₀ := extChartAt 𝓘(ℂ, ℂ) x x
    set κ : ℂ → ℂ := fun z ↦ (z - z₀) * l z
    have hκ : AnalyticAt ℂ κ z₀ := (analyticAt_id.sub analyticAt_const).mul hl
    have hκ' : deriv κ z₀ ≠ 0 := by
      have h := ((hasDerivAt_id z₀).sub_const z₀).mul hl.differentiableAt.hasDerivAt
      rw [show (1 : ℂ) * l z₀ + (id z₀ - z₀) * deriv l z₀ = l z₀ by simp] at h
      rw [show deriv κ z₀ = l z₀ from h.deriv]; exact hl0
    have hdi := caf_deriv_infty _ l z₀ e hl hl0 hs
    have hd : MeromorphicAt (deriv fun w ↦ b65g_sFun D t a b ((extChartAt 𝓘(ℂ, ℂ) x).symm w))
        z₀ := by
      have hm : MeromorphicAt (fun z ↦ κ z ^ (-(2 * e : ℤ)) *
          -deriv (fun y ↦ κ y ^ e) z) z₀ :=
        (hκ.meromorphicAt.zpow _).mul (hκ.pow e).deriv.neg.meromorphicAt
      exact hm.congr (hdi.mono fun z hz ↦ hz.2.2.symm)
    have hcomp := (hEm x hd j).congr (hpunct x j)
    have hcomp2 : MeromorphicAt (fun z ↦ (fun w ↦ F w⁻¹ j) (0 + κ z ^ e)) z₀ := by
      refine hcomp.congr ?_
      filter_upwards [hdi] with z hz
      simp only [zero_add]
      rw [hz.2.1]
    have h3 := (meromorphicAt_comp_iff_of_deriv_ne_zero
      (f := fun y ↦ (fun w ↦ F w⁻¹ j) (0 + y ^ e)) hκ hκ').mp hcomp2
    rw [show κ z₀ = 0 by simp [κ]] at h3
    refine caf_meromorphicAt_of_comp_pow (fun w ↦ F w⁻¹ j) 0 e he ?_ h3
    have hfin : (((fun s : ℂ ↦ s⁻¹) '' Set.range poles) \ {0}).Finite :=
      ((Set.finite_range poles).image _).subset sdiff_subset
    filter_upwards [nhdsWithin_le_nhds (hfin.isClosed.isOpen_compl.mem_nhds
      (by simp : (0 : ℂ) ∈ (((fun s : ℂ ↦ s⁻¹) '' Set.range poles) \ {0})ᶜ)),
      self_mem_nhdsWithin] with w h1 h2
    have hw' : w⁻¹ ∉ Set.range poles := by
      rintro ⟨q, hq⟩
      exact h1 ⟨⟨poles q, ⟨q, rfl⟩, show (poles q)⁻¹ = w by rw [hq, inv_inv]⟩, h2⟩
    exact (hAn _ hw' j).comp (analyticAt_id.inv h2)
  -- rationality
  set S : Finset ℂ := Finset.univ.image poles
  have hS : ∀ z, z ∈ S ↔ z ∈ Set.range poles := by simp [S]
  have hrat : ∀ j, ∃ r : RatFunc ℂ, ∀ z ∉ S, F z j = r.eval (RingHom.id ℂ) z := fun j ↦
    caf_ratFunc_of_meromorphic (fun s ↦ F s j) S
      (fun z hz ↦ hAn z (by rwa [← hS]) j)
      (fun z hz ↦ by obtain ⟨q, rfl⟩ := (hS z).mp hz; exact hMer q j) (hInf j)
  choose r hr using hrat
  refine ⟨r, ?_, ?_⟩
  · intro i s hs
    by_contra hns
    have han := hAn s hns i
    have hev : b65q_eval (r i) =ᶠ[𝓝[≠] s] fun σ ↦ F σ i := by
      filter_upwards [hpole_punct s] with σ hσ
      exact (hr i σ (by rwa [hS])).symm
    have hord : 0 ≤ meromorphicOrderAt (b65q_eval (r i)) s := by
      rw [meromorphicOrderAt_congr hev]
      exact han.meromorphicOrderAt_nonneg
    exact (caf_order_ratFunc_nonneg_iff (r i) s).mp hord hs
  · intro x hx
    funext j
    exact (congrFun (hF x hx) j).symm.trans (hr j _ (by rw [hS]; exact b65g_good_sFun hx))

end HodgeLean.Foundations.Program
