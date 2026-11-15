import HodgeLean.Foundations.Program.RelativeFrameOperatorDefs
import HodgeLean.Foundations.Program.RelativeFrameOperatorDescent

set_option maxHeartbeats 400000

noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff BoundedContinuousFunction
namespace HodgeLean.Foundations.Program

theorem rf4_sector_pullback (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : 0 < r) (c ε : ℂ)
    (hε : ‖ε‖ < r) (u : ℂ) (hu : u ∈ b63r_annulus n r) (g : Fin n → ℂ → ℂ) :
    rf4_rootMap n ε u ^ n = u ^ n - ε ∧
      HasDerivAt (rf4_rootMap n ε) ((1 - ε * u ^ (-(n : ℤ))) ^ ((n : ℂ)⁻¹ - 1)) u ∧
      rf4_sectorCoeff n g (c + ε) (rf4_rootMap n ε u) *
          (1 - ε * u ^ (-(n : ℤ))) ^ ((n : ℂ)⁻¹ - 1) =
        (n : ℂ) * ∑ j : Fin n, rf4_multiplierFun n ε j u * g j (c + u ^ n) := by
  have hn0 : n ≠ 0 := by omega
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have hun : 0 < ‖u‖ ^ n := hr.trans hu.1
  have hu0 : u ≠ 0 := by
    intro h
    simpa [h, hn0] using hun
  have hsmall : ‖-ε * u ^ (-(n : ℤ))‖ < 1 := by
    rw [norm_mul, norm_neg, norm_zpow, zpow_neg, zpow_natCast,
      ← div_eq_mul_inv, div_lt_one hun]
    exact hε.trans hu.1
  have hslit : 1 - ε * u ^ (-(n : ℤ)) ∈ Complex.slitPlane := by
    convert Complex.mem_slitPlane_of_norm_lt_one hsmall using 1 <;> ring
  have hA := Complex.slitPlane_ne_zero hslit
  have hp : rf4_rootMap n ε u ^ n = u ^ n - ε := by
    rw [rf4_rootMap, mul_pow, Complex.cpow_nat_inv_pow _ hn0,
      zpow_neg, zpow_natCast]
    field_simp
  have hpow : (1 - ε * u ^ (-(n : ℤ))) ^ ((n : ℂ)⁻¹) =
      (1 - ε * u ^ (-(n : ℤ))) ^ ((n : ℂ)⁻¹ - 1) *
        (1 - ε * u ^ (-(n : ℤ))) := by
    calc
      _ = (1 - ε * u ^ (-(n : ℤ))) ^ (((n : ℂ)⁻¹ - 1) + 1) := by congr 1; ring
      _ = _ := by rw [Complex.cpow_add _ _ hA, Complex.cpow_one]
  have hz : u * u ^ (-(n : ℤ) - 1) = u ^ (-(n : ℤ)) := by
    calc
      _ = u ^ (1 : ℤ) * u ^ (-(n : ℤ) - 1) := by rw [zpow_one]
      _ = _ := by rw [← zpow_add₀ hu0]; congr 1; ring
  have hd := (hasDerivAt_id u).mul
    ((((hasDerivAt_zpow (-(n : ℤ)) u (Or.inl hu0)).const_mul ε).const_sub 1).cpow_const
      (c := (n : ℂ)⁻¹) hslit)
  have hder : HasDerivAt (rf4_rootMap n ε)
      ((1 - ε * u ^ (-(n : ℤ))) ^ ((n : ℂ)⁻¹ - 1)) u := by
    convert! hd using 1
    symm
    simp only [id_eq, one_mul, Int.cast_neg, Int.cast_natCast]
    rw [hpow]
    have hninv : (n : ℂ)⁻¹ * n = 1 := inv_mul_cancel₀ hnC
    calc
      _ = (1 - ε * u ^ (-(n : ℤ))) ^ ((n : ℂ)⁻¹ - 1) *
          (1 - ε * u ^ (-(n : ℤ)) + ε * ((n : ℂ)⁻¹ * n) *
            (u * u ^ (-(n : ℤ) - 1))) := by ring
      _ = _ := by rw [hninv, hz]; ring
  refine ⟨hp, hder, ?_⟩
  simp only [rf4_sectorCoeff, rf4_multiplierFun, hp,
    show c + ε + (u ^ n - ε) = c + u ^ n by ring]
  rw [mul_assoc, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [rf4_rootMap, mul_pow]
  have hexp : (j : ℂ) * (n : ℂ)⁻¹ + ((n : ℂ)⁻¹ - 1) = rf4_sectorExp n j := by
    simp only [rf4_sectorExp, div_eq_mul_inv]
    ring
  rw [← Complex.cpow_nat_mul]
  rw [show u ^ (j : ℕ) * (1 - ε * u ^ (-(n : ℤ))) ^ ((j : ℕ) * (n : ℂ)⁻¹) *
      g j (c + u ^ n) * (1 - ε * u ^ (-(n : ℤ))) ^ ((n : ℂ)⁻¹ - 1) =
      u ^ (j : ℕ) * ((1 - ε * u ^ (-(n : ℤ))) ^ ((j : ℕ) * (n : ℂ)⁻¹) *
        (1 - ε * u ^ (-(n : ℤ))) ^ ((n : ℂ)⁻¹ - 1)) * g j (c + u ^ n) by ring]
  rw [← Complex.cpow_add _ _ hA, hexp]

theorem rf4_sectorOp_pullback (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : 0 < r) (c ε : ℂ)
    (hε : ‖ε‖ < r) (g : Fin n → b63r_bddHol (Metric.ball c (2 * r)))
    (u : b63r_annulus n r) :
    rf4_sectorCoeff n (fun j ↦ rf4_extendBdd (g j)) (c + ε) (rf4_rootMap n ε u) *
        deriv (rf4_rootMap n ε) u =
      ((rf4_sectorOp n hn r hr c ε g : b63r_bddHol (b63r_annulus n r)) :
        b63r_annulus n r →ᵇ ℂ) u := by
  have h := rf4_sector_pullback n hn r hr c ε hε u u.property
    (fun j ↦ rf4_extendBdd (g j))
  rw [h.2.1.deriv]
  exact h.2.2.trans (rf4_sectorOp_apply n hn r hr c ε hε g u).symm

def rf4_chartCoeff {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    (θ : TangentBundle 𝓘(ℂ, ℂ) C → ℂ) (e : OpenPartialHomeomorph C ℂ) (z : ℂ) : ℂ :=
  θ ⟨e.symm z, mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e.symm z (1 : ℂ)⟩

theorem rf4_chartCoeff_contMDiffOn {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (θ : b3_HolForm ℂ C) (e : OpenPartialHomeomorph C ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω C) :
    ContMDiffOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω
      (rf4_chartCoeff (θ : TangentBundle 𝓘(ℂ, ℂ) C → ℂ) e) e.target := by
  let σ : ℂ → TangentBundle 𝓘(ℂ, ℂ) ℂ := fun z ↦ ⟨z, (1 : ℂ)⟩
  have hσ : ContMDiff 𝓘(ℂ, ℂ) (𝓘(ℂ, ℂ)).tangent ω σ :=
    contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
  have he' := contMDiffOn_symm_of_mem_maximalAtlas he
  have ht := he'.contMDiffOn_tangentMapWithin (m := ω) (by simp)
    e.open_target.uniqueMDiffOn
  have hh := θ.property.1.comp_contMDiffOn (ht.comp hσ.contMDiffOn (fun z hz ↦ hz))
  apply hh.congr
  intro z hz
  change (θ : TangentBundle 𝓘(ℂ, ℂ) C → ℂ)
    ⟨e.symm z, mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e.symm z (1 : ℂ)⟩ =
    (θ : TangentBundle 𝓘(ℂ, ℂ) C → ℂ)
    ⟨e.symm z, mfderivWithin 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e.symm e.target z (1 : ℂ)⟩
  rw [mfderivWithin_eq_mfderiv (e.open_target.uniqueMDiffOn z hz)
    ((contMDiffAt_symm_of_mem_maximalAtlas he hz).mdifferentiableAt (by simp))]

theorem rf4_holForm_coeff_bdd {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (θ : b3_HolForm ℂ C) (e : OpenPartialHomeomorph C ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω C) (V : Set ℂ)
    (hVc : IsCompact (closure V)) (hVe : closure V ⊆ e.target) :
    ∃ g : b63r_bddHol V, ∀ z : V,
      (g : V →ᵇ ℂ) z = rf4_chartCoeff (θ : TangentBundle 𝓘(ℂ, ℂ) C → ℂ) e z := by
  have hc := rf4_chartCoeff_contMDiffOn θ e he
  have hd := hc.contDiffOn.differentiableOn (by simp)
  exact ⟨rf4_bddOn hVc subset_closure _ (hc.continuousOn.mono hVe)
    (hd.mono (subset_closure.trans hVe)), fun _ ↦ rfl⟩

theorem rf4_chart_inverse_mfderiv {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (e : OpenPartialHomeomorph C ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω C) (p : C) (hp : p ∈ e.source)
    (v : TangentSpace 𝓘(ℂ, ℂ) p) :
    mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e.symm (e p)
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e p v) = v := by
  have hd := (contMDiffAt_of_mem_maximalAtlas he hp).mdifferentiableAt (by simp)
  have hi := (contMDiffAt_symm_of_mem_maximalAtlas he (e.map_source hp)).mdifferentiableAt
    (by simp)
  have hcomp := mfderiv_comp p hi hd
  have hev : e.symm ∘ e =ᶠ[𝓝 p] id := by
    filter_upwards [e.open_source.mem_nhds hp] with q hq
    exact e.left_inv hq
  rw [hev.mfderiv_eq, mfderiv_id] at hcomp
  have hv := congrArg (fun L : ℂ →L[ℂ] ℂ ↦ L v) hcomp
  change v = mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e.symm (e p)
    (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e p v) at hv
  exact hv.symm

theorem rf4_chartCoeff_reconstruct {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (θ : b3_HolForm ℂ C) (e : OpenPartialHomeomorph C ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω C) (p : C) (hp : p ∈ e.source)
    (v : TangentSpace 𝓘(ℂ, ℂ) p) :
    rf4_chartCoeff (θ : TangentBundle 𝓘(ℂ, ℂ) C → ℂ) e (e p) *
        (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e p v) = θ.val ⟨p, v⟩ := by
  let L : ℂ →L[ℂ] ℂ := b3Forms_holCLM θ p
  let A : ℂ →L[ℂ] ℂ := mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e.symm (e p)
  let a : ℂ := mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e p v
  have hscale := (L.comp A).map_smul a (1 : ℂ)
  simp only [ContinuousLinearMap.comp_apply, smul_eq_mul, mul_one] at hscale
  rw [rf4_chartCoeff, e.left_inv hp]
  change L (A 1) * a = L v
  calc
    _ = a * L (A 1) := mul_comm _ _
    _ = L (A a) := hscale.symm
    _ = L v := congrArg L (rf4_chart_inverse_mfderiv e he p hp v)

theorem rf4_chartCoeff_transition {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] (θ : b3_HolForm ℂ C)
    (e d : OpenPartialHomeomorph C ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω C)
    (hd : d ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω C)
    (z w : ℂ) (hz : z ∈ e.target) (hw : w ∈ d.target)
    (hzw : e.symm z = d.symm w) :
    rf4_chartCoeff θ.val e z = rf4_chartCoeff θ.val d w * deriv (d ∘ e.symm) z := by
  have hp : e.symm z ∈ d.source := by
    rw [hzw]
    exact d.map_target hw
  have heD := (contMDiffAt_symm_of_mem_maximalAtlas he hz).mdifferentiableAt (by simp)
  have hdD := (contMDiffAt_of_mem_maximalAtlas hd hp).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp z hdD heD
  have hx := congrArg (fun L : ℂ →L[ℂ] ℂ ↦ L 1) hcomp
  rw [mfderiv_eq_fderiv] at hx
  change fderiv ℂ (d ∘ e.symm) z 1 =
    mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) d (e.symm z)
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e.symm z (1 : ℂ)) at hx
  rw [fderiv_eq_deriv_mul, mul_one] at hx
  have hrec := rf4_chartCoeff_reconstruct θ d hd (e.symm z) hp
    (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e.symm z (1 : ℂ))
  have heval : d (e.symm z) = w := by rw [hzw, d.right_inv hw]
  rw [heval] at hrec
  exact hrec.symm.trans (congrArg (fun a : ℂ ↦ rf4_chartCoeff θ.val d w * a) hx.symm)

theorem rf4_innerDisc_closure_compact (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (ε : ℂ) :
    IsCompact (closure (rf4_innerDisc n r ε)) := by
  have hs : rf4_innerDisc n r ε ⊆ Metric.closedBall (0 : ℂ) (max 1 (2 * r + ‖ε‖)) := by
    intro w hw
    rw [Metric.mem_closedBall, dist_zero_right]
    by_cases h : ‖w‖ ≤ 1
    · exact h.trans (le_max_left _ _)
    · have hp : ‖w‖ ≤ ‖w‖ ^ n := by
        simpa only [pow_one] using pow_le_pow_right₀ (le_of_not_ge h) hn
      have hnorm : ‖w‖ ^ n ≤ ‖w ^ n + ε‖ + ‖ε‖ := by
        rw [← norm_pow]
        simpa only [add_sub_cancel_right] using norm_sub_le (w ^ n + ε) ε
      have hwi : ‖w ^ n + ε‖ < 2 * r := hw
      have hb : ‖w ^ n + ε‖ + ‖ε‖ ≤ 2 * r + ‖ε‖ := by linarith
      exact (hp.trans (hnorm.trans hb)).trans (le_max_right _ _)
  exact (isCompact_closedBall (0 : ℂ) (max 1 (2 * r + ‖ε‖))).of_isClosed_subset
    isClosed_closure (closure_minimal hs Metric.isClosed_closedBall)

theorem rf4_holForm_inner_sectors {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    (S : rf4_Plumbing D ε X) (θ : b3_HolForm ℂ X) (x : Fin D.m) :
    ∃ g : Fin (D.deg x) → b63r_bddHol (Metric.ball (D.c x) (2 * D.r)),
      ∀ z ∈ rf4_innerDisc (D.deg x) D.r (ε x),
        rf4_chartCoeff θ.val (S.w x) z =
          rf4_sectorCoeff (D.deg x) (fun j ↦ rf4_extendBdd (g j)) (D.c x + ε x) z := by
  have hc := rf4_chartCoeff_contMDiffOn θ (S.w x) (S.w_mem x)
  have hd := hc.contDiffOn.differentiableOn (by simp)
  have ht : rf4_innerDisc (D.deg x) D.r (ε x) ⊆ (S.w x).target :=
    subset_closure.trans (S.w_target x)
  obtain ⟨M, hM⟩ := (rf4_innerDisc_closure_compact (D.deg x) (D.hdeg x) D.r (ε x)).exists_bound_of_continuousOn
    (hc.continuousOn.mono (S.w_target x))
  have hb : BddAbove ((fun z ↦ ‖rf4_chartCoeff θ.val (S.w x) z‖) ''
      rf4_innerDisc (D.deg x) D.r (ε x)) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact hM z (subset_closure hz)
  exact rf4_sector_surjective_core (D.deg x) (D.hdeg x) D.r D.hr (D.c x) (ε x)
    (S.small x) (rf4_chartCoeff θ.val (S.w x)) (hd.mono ht) hb

theorem rf4_stationaryChart_target {C X : Type} [TopologicalSpace C] [TopologicalSpace X]
    (h : C ≃ₜ X) (e : OpenPartialHomeomorph C ℂ) :
    (h.symm.toOpenPartialHomeomorph ≫ₕ e).target = e.target := by
  rw [OpenPartialHomeomorph.trans_target]
  change e.target ∩ e.symm ⁻¹' Set.univ = e.target
  rw [Set.preimage_univ, Set.inter_univ]

theorem rf4_holForm_outer_tuple {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    (S : rf4_Plumbing D ε X) (θ : b3_HolForm ℂ X) :
    ∃ α : rf2_bddForm D.P, ∀ (i : Fin D.P.n) (z : D.P.piece i),
      (α.val i : D.P.piece i →ᵇ ℂ) z =
        rf4_chartCoeff θ.val (S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart i) z := by
  classical
  let e : Fin D.P.n → OpenPartialHomeomorph X ℂ :=
    fun i ↦ S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart i
  have hcontain : ∀ i, closure (D.P.piece i) ⊆ (e i).target := by
    intro i
    dsimp only [e]
    rw [rf4_stationaryChart_target]
    exact D.P.contained i
  choose g hg using (fun i ↦ rf4_holForm_coeff_bdd θ (e i) (S.stationary i)
    (D.P.piece i) (D.P.compact i) (hcontain i))
  refine ⟨⟨g, ?_⟩, hg⟩
  intro i j z w hzw
  have hz : (z : ℂ) ∈ (e i).target := hcontain i (subset_closure z.property)
  have hw : (w : ℂ) ∈ (e j).target := hcontain j (subset_closure w.property)
  have hsame : (e i).symm z = (e j).symm w := by
    change S.h ((D.P.chart i).symm z) = S.h ((D.P.chart j).symm w)
    exact congrArg S.h hzw
  have htrans := rf4_chartCoeff_transition θ (e i) (e j) (S.stationary i) (S.stationary j)
    z w hz hw hsame
  have hfun : (e j) ∘ (e i).symm = (D.P.chart j) ∘ (D.P.chart i).symm := by
    funext u
    change D.P.chart j (S.h.symm (S.h ((D.P.chart i).symm u))) =
      D.P.chart j ((D.P.chart i).symm u)
    rw [S.h.symm_apply_apply]
  rw [hg i z, hg j w, ← hfun]
  exact htrans

theorem rf4_holForm_annulus_pullback {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    (S : rf4_Plumbing D ε X) (θ : b3_HolForm ℂ X) (x : Fin D.m)
    (u : b63r_annulus (D.deg x) D.r) :
    rf4_chartCoeff θ.val (S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart (D.ann x)) u =
      rf4_chartCoeff θ.val (S.w x) (rf4_rootMap (D.deg x) (ε x) u) *
        deriv (rf4_rootMap (D.deg x) (ε x)) u := by
  let e := S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart (D.ann x)
  have hu : (u : ℂ) ∈ e.target := by
    dsimp only [e]
    rw [rf4_stationaryChart_target]
    apply D.P.contained (D.ann x)
    apply subset_closure
    rw [D.hann x]
    exact u.property
  have hglue := S.glue x u u.property
  have hw : rf4_rootMap (D.deg x) (ε x) u ∈ (S.w x).target := by
    rw [← hglue.2]
    exact (S.w x).map_source hglue.1
  have hsame : e.symm u = (S.w x).symm (rf4_rootMap (D.deg x) (ε x) u) := by
    rw [← hglue.2, (S.w x).left_inv hglue.1]
    rfl
  have htrans := rf4_chartCoeff_transition θ e (S.w x) (S.stationary (D.ann x))
    (S.w_mem x) u (rf4_rootMap (D.deg x) (ε x) u) hu hw hsame
  have hev : (S.w x) ∘ e.symm =ᶠ[𝓝 (u : ℂ)] rf4_rootMap (D.deg x) (ε x) := by
    filter_upwards [(rf4_annulus_isOpen (D.deg x) D.r).mem_nhds u.property] with z hz
    exact (S.glue x z hz).2
  rw [hev.deriv_eq] at htrans
  exact htrans

theorem rf4_holForm_kernel_data {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    (S : rf4_Plumbing D ε X) (θ : b3_HolForm ℂ X) :
    ∃ k : (rf4_delta D ε).ker,
      (∀ (i : Fin D.P.n) (z : D.P.piece i),
        (k.val.1.val i : D.P.piece i →ᵇ ℂ) z =
          rf4_chartCoeff θ.val (S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart i) z) ∧
      ∀ (x : Fin D.m) z, z ∈ rf4_innerDisc (D.deg x) D.r (ε x) →
        rf4_chartCoeff θ.val (S.w x) z =
          rf4_sectorCoeff (D.deg x) (fun j ↦ rf4_extendBdd (k.val.2 x j)) (D.c x + ε x) z := by
  classical
  obtain ⟨α, hα⟩ := rf4_holForm_outer_tuple S θ
  choose g hg using (fun x ↦ rf4_holForm_inner_sectors S θ x)
  have hk : rf4_delta D ε (α, g) = 0 := by
    funext x
    apply Subtype.ext
    apply BoundedContinuousFunction.ext
    intro u
    change (α.val (D.ann x) : D.P.piece (D.ann x) →ᵇ ℂ)
      ⟨u, (D.hann x).ge u.property⟩ -
      ((rf4_sectorOp (D.deg x) (D.hdeg x) D.r D.hr (D.c x) (ε x) (g x) :
        b63r_bddHol (b63r_annulus (D.deg x) D.r)) :
          b63r_annulus (D.deg x) D.r →ᵇ ℂ) u = 0
    have hp := (rf4_sector_pullback (D.deg x) (D.hdeg x) D.r D.hr (D.c x) (ε x)
      (S.small x) u u.property (fun j ↦ rf4_extendBdd (g x j))).1
    have hroot : rf4_rootMap (D.deg x) (ε x) u ∈ rf4_innerDisc (D.deg x) D.r (ε x) := by
      change ‖rf4_rootMap (D.deg x) (ε x) u ^ D.deg x + ε x‖ < 2 * D.r
      rw [hp, sub_add_cancel, norm_pow]
      exact u.property.2
    rw [hα (D.ann x) ⟨u, (D.hann x).ge u.property⟩,
      rf4_holForm_annulus_pullback S θ x u, hg x _ hroot,
      rf4_sectorOp_pullback (D.deg x) (D.hdeg x) D.r D.hr (D.c x) (ε x) (S.small x) (g x) u,
      sub_self]
  exact ⟨⟨(α, g), hk⟩, hα, hg⟩

theorem rf4_holForm_glue_preimage {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    (S : rf4_Plumbing D ε X) (θ : b3_HolForm ℂ X) :
    ∃ k : (rf4_delta D ε).ker, rf4_glue S k.val = θ.val := by
  classical
  obtain ⟨k, hα, hg⟩ := rf4_holForm_kernel_data S θ
  refine ⟨k, ?_⟩
  funext q
  unfold rf4_glue
  split_ifs with hO hD
  · let i := Classical.choose hO
    have hi := Classical.choose_spec hO
    have hep : q.1 ∈ (S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart i).source := by
      change q.1 ∈ Set.univ ∩ _
      exact ⟨Set.mem_univ _, hi.1⟩
    rw [rf4_extendBdd, dite_eq_left hi.2, hα i ⟨D.P.chart i (S.h.symm q.1), hi.2⟩]
    exact rf4_chartCoeff_reconstruct θ (S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart i)
      (S.stationary i) q.1 hep q.2
  · let x := Classical.choose hD
    have hx := Classical.choose_spec hD
    rw [← hg x _ hx.2]
    exact rf4_chartCoeff_reconstruct θ (S.w x) (S.w_mem x) q.1 hx.1 q.2
  · rcases S.cover q.1 with ho | ⟨x, hx⟩
    · exfalso
      apply hO
      have ho' := (Set.ext_iff.mp D.P.covers (S.h.symm q.1)).mp ho
      obtain ⟨i, z, hz, heq⟩ := Set.mem_iUnion.mp ho'
      have ht := D.P.contained i (subset_closure hz)
      refine ⟨i, ?_, ?_⟩
      · rw [← heq]
        exact (D.P.chart i).map_target ht
      · rw [← heq, (D.P.chart i).right_inv ht]
        exact hz
    · exfalso
      apply hD
      obtain ⟨z, hz, heq⟩ := hx
      have ht := S.w_target x (subset_closure hz)
      refine ⟨x, ?_, ?_⟩
      · rw [← heq]
        exact (S.w x).map_target ht
      · rw [← heq, (S.w x).right_inv ht]
        exact hz

theorem rf4_chartForm_contMDiffAt {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ, ℂ) ω X] (e : OpenPartialHomeomorph X ℂ)
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℂ, ℂ) ω X) (U : Set ℂ) (hU : IsOpen U)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f U) (q : TangentBundle 𝓘(ℂ, ℂ) X)
    (hq : q.1 ∈ e.source) (harg : e q.1 ∈ U) :
    ContMDiffAt (𝓘(ℂ, ℂ)).tangent 𝓘(ℂ, ℂ) ω
      (fun p : TangentBundle 𝓘(ℂ, ℂ) X ↦ f (e p.1) *
        (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e p.1 p.2)) q := by
  have hproj : ContMDiff (𝓘(ℂ, ℂ)).tangent 𝓘(ℂ, ℂ) ω
      (fun p : TangentBundle 𝓘(ℂ, ℂ) X ↦ p.1) := Bundle.contMDiff_proj (TangentSpace 𝓘(ℂ, ℂ))
  have hV := e.open_source.preimage hproj.continuous
  have ht := (contMDiffOn_of_mem_maximalAtlas he).contMDiffOn_tangentMapWithin
    (m := ω) (by simp) e.open_source.uniqueMDiffOn
  have htAt := (ht q hq).contMDiffAt (hV.mem_nhds hq)
  have hs := (contMDiff_snd_tangentBundle_modelSpace ℂ 𝓘(ℂ, ℂ) (n := ω)).contMDiffAt.comp q htAt
  have hderiv : ContMDiffAt (𝓘(ℂ, ℂ)).tangent 𝓘(ℂ, ℂ) ω
      (fun p : TangentBundle 𝓘(ℂ, ℂ) X ↦
        (show ℂ from mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e p.1 p.2)) q := by
    apply hs.congr_of_eventuallyEq
    filter_upwards [hV.mem_nhds hq] with p hp
    change mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e p.1 p.2 =
      mfderivWithin 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) e e.source p.1 p.2
    rw [mfderivWithin_eq_mfderiv (e.open_source.uniqueMDiffOn p.1 hp)
      ((contMDiffAt_of_mem_maximalAtlas he hp).mdifferentiableAt (by simp))]
  have hfAt : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f (e q.1) :=
    ((hf.analyticOnNhd hU (e q.1) harg).contDiffAt).contMDiffAt
  have hb := (contMDiffAt_of_mem_maximalAtlas he hq).comp q hproj.contMDiffAt
  exact (hfAt.comp q hb).mul hderiv

end HodgeLean.Foundations.Program
