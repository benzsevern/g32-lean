import HodgeLean.Foundations.Analytic.ComplexAnalyticSpaceDefs
import HodgeLean.Foundations.AnalyticGermRSAssembly

/-! # The holomorphic rank theorem

A holomorphic map `g` of constant rank `r` on an open `U ⊆ ℂⁿ` is, near each point `x ∈ U`, of the
form `(u, v) ↦ h (u, 0)` in coordinates `(u, v)` of the source given by the inverse function
theorem. The image of a small neighbourhood `W` of `x` is then the graph `{y | y = h (P y, 0)}`
over an open set, where `P` projects onto the range of `dg(x)`: it is cut out by holomorphic
equations, and it is an analytic retract of `ℂʳ`, so its germ has dimension `r`.
HC no distance; AV milestone no distance.
-/

noncomputable section

open Set Filter Topology Module

namespace HodgeLean.Foundations.Analytic

open HodgeLean.Foundations
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6

/-- A linear map `A` from `K × N` whose composite with `P` is the first projection, and whose rank
is at most `dim K`, vanishes on `0 × N`.
Source: linear algebra; the step of Gunning–Rossi, *Analytic Functions of Several Complex
Variables*, I.B, Theorem 10 (rank theorem) where constant rank kills the transverse derivative. -/
theorem ancr_apply_inr_eq_zero {K N F : Type*} [AddCommGroup K] [Module ℂ K] [AddCommGroup N]
    [Module ℂ N] [AddCommGroup F] [Module ℂ F] [FiniteDimensional ℂ F]
    (A : K × N →ₗ[ℂ] F) (P : F →ₗ[ℂ] K) (hPA : ∀ w, P (A w) = w.1)
    (hrank : finrank ℂ (LinearMap.range A) ≤ finrank ℂ K) (b : N) : A (0, b) = 0 := by
  have hinj : Function.Injective (A.comp (LinearMap.inl ℂ K N)) := by
    intro a a' h
    have := congrArg P h
    simpa [hPA] using this
  have hS : finrank ℂ (LinearMap.range (A.comp (LinearMap.inl ℂ K N))) = finrank ℂ K :=
    LinearMap.finrank_range_of_inj hinj
  have hle : LinearMap.range (A.comp (LinearMap.inl ℂ K N)) ≤ LinearMap.range A :=
    LinearMap.range_comp_le_range _ _
  have heq : LinearMap.range (A.comp (LinearMap.inl ℂ K N)) = LinearMap.range A :=
    Submodule.eq_of_le_of_finrank_le hle (by rw [hS]; exact hrank)
  obtain ⟨a, ha⟩ : A (0, b) ∈ LinearMap.range (A.comp (LinearMap.inl ℂ K N)) :=
    heq ▸ LinearMap.mem_range_self A (0, b)
  have ha0 : a = 0 := by
    have := congrArg P ha
    simpa [hPA] using this
  rw [← ha, ha0, map_zero]

/-- A map holomorphic near `w` with derivative of rank at most `dim K` whose composite with `P` is
the first projection has derivative vanishing on `0 × N`.
Source: Gunning–Rossi, *Analytic Functions of Several Complex Variables*, I.B, Theorem 10. -/
theorem ancr_fderiv_inr_eq_zero {K N F : Type*} [NormedAddCommGroup K] [NormedSpace ℂ K]
    [NormedAddCommGroup N] [NormedSpace ℂ N] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [FiniteDimensional ℂ F] (h : K × N → F) (P : F →L[ℂ] K) {w : K × N}
    (hh : DifferentiableAt ℂ h w) (hP : (fun w' ↦ P (h w')) =ᶠ[𝓝 w] Prod.fst)
    (hrank : finrank ℂ (LinearMap.range (fderiv ℂ h w : K × N →ₗ[ℂ] F)) ≤ finrank ℂ K)
    (b : N) : fderiv ℂ h w (0, b) = 0 := by
  have h1 : HasFDerivAt (fun w' ↦ P (h w')) (P.comp (fderiv ℂ h w)) w :=
    P.hasFDerivAt.comp w hh.hasFDerivAt
  have h2 : HasFDerivAt (fun w' ↦ P (h w')) (ContinuousLinearMap.fst ℂ K N) w :=
    (hasFDerivAt_fst).congr_of_eventuallyEq hP
  have heq := h1.unique h2
  refine ancr_apply_inr_eq_zero (fderiv ℂ h w : K × N →ₗ[ℂ] F) (P : F →ₗ[ℂ] K) ?_ hrank b
  intro w'
  exact congrArg (fun A : K × N →L[ℂ] K ↦ A w') heq

/-- **The holomorphic rank theorem.** A map holomorphic of constant rank `r` on an open `U ⊆ ℂⁿ`
sends a small open neighbourhood `W` of `x` onto a set cut out by holomorphic equations on an open
`V`, whose germ at `g x` has dimension `r`.
Source: Gunning–Rossi, *Analytic Functions of Several Complex Variables*, I.B, Theorem 10 (rank
theorem); the dimension of a submanifold germ is that of its parameter ring
(`adim9b_retractGerm_dimension`, `adim6_parameter_dimension`). -/
theorem ancr_constant_rank (n m r : ℕ) (U : Set (Fin n → ℂ)) (hU : IsOpen U)
    (g : (Fin n → ℂ) → (Fin m → ℂ)) (hg : AnalyticOnNhd ℂ g U)
    (hr : ∀ z ∈ U, Module.finrank ℂ
      (LinearMap.range (fderiv ℂ g z : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ))) = r)
    {x : Fin n → ℂ} (hx : x ∈ U) :
    ∃ (W : Set (Fin n → ℂ)) (V : Set (Fin m → ℂ)), IsOpen W ∧ x ∈ W ∧ W ⊆ U ∧ IsOpen V ∧
      g '' W ⊆ V ∧
      (∃ (k : ℕ) (F : (Fin m → ℂ) → (Fin k → ℂ)), AnalyticOnNhd ℂ F V ∧
        ∀ y ∈ V, (y ∈ g '' W ↔ F y = 0)) ∧
      adim2_dimension m (adim2_germ m (g '' W) (g x)) = ((r : ℕ∞) : WithBot ℕ∞) := by
  classical
  set L : (Fin n → ℂ) →L[ℂ] (Fin m → ℂ) := fderiv ℂ g x with hLdef
  set K : Submodule ℂ (Fin m → ℂ) := LinearMap.range (L : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ))
  set N : Submodule ℂ (Fin n → ℂ) := LinearMap.ker (L : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ))
  obtain ⟨C, hC⟩ := K.exists_isCompl
  obtain ⟨N', hN'⟩ := N.exists_isCompl
  let PK : (Fin m → ℂ) →L[ℂ] K := LinearMap.toContinuousLinearMap (K.projectionOnto C hC)
  let PN : (Fin n → ℂ) →L[ℂ] N := LinearMap.toContinuousLinearMap (N.projectionOnto N' hN')
  have hPK : ∀ y : K, PK y = y := Submodule.projectionOnto_apply_left hC
  have hPN : ∀ y : N, PN y = y := Submodule.projectionOnto_apply_left hN'
  have hKr : finrank ℂ K = r := hr x hx
  let φ : (Fin n → ℂ) → K × N := fun z ↦ (PK (g z), PN (z - x))
  have hgx : AnalyticAt ℂ g x := hg x hx
  have hφa : AnalyticAt ℂ φ x :=
    ((PK.analyticAt _).comp hgx).prod ((PN.analyticAt _).comp
      (analyticAt_id.sub analyticAt_const))
  let D : (Fin n → ℂ) →L[ℂ] K × N := (PK.comp L).prod PN
  have hφd : HasFDerivAt φ D x := by
    have h1 : HasFDerivAt (fun z ↦ PK (g z)) (PK.comp L) x :=
      PK.hasFDerivAt.comp x hgx.differentiableAt.hasFDerivAt
    have h2 : HasFDerivAt (fun z ↦ PN (z - x)) PN x :=
      (PN.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const x)).congr_fderiv (by ext1 a; rfl)
    exact h1.prodMk h2
  have hDinj : Function.Injective (D : (Fin n → ℂ) →ₗ[ℂ] K × N) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    have h1 : PK (L a) = 0 := congrArg Prod.fst ha
    have h2 : PN a = 0 := congrArg Prod.snd ha
    have hLa : L a = 0 := by
      have := hPK ⟨L a, LinearMap.mem_range_self _ a⟩
      rw [h1] at this
      exact (congrArg Subtype.val this).symm
    have := hPN ⟨a, hLa⟩
    rw [h2] at this
    exact (congrArg Subtype.val this).symm
  have hdim : finrank ℂ (Fin n → ℂ) = finrank ℂ (K × N) := by
    rw [Module.finrank_prod]
    exact (LinearMap.finrank_range_add_finrank_ker _).symm
  let De : (Fin n → ℂ) ≃L[ℂ] K × N :=
    (LinearMap.linearEquivOfInjective _ hDinj hdim).toContinuousLinearEquiv
  have hDe : (De : (Fin n → ℂ) →L[ℂ] K × N) = D := by
    ext1 a; rfl
  have hφs : HasStrictFDerivAt φ (De : (Fin n → ℂ) →L[ℂ] K × N) x := by
    rw [hDe, ← hφd.fderiv]; exact hφa.hasStrictFDerivAt
  let Φ := hφs.toOpenPartialHomeomorph φ
  have hΦ : (Φ : (Fin n → ℂ) → K × N) = φ := rfl
  have hxs : x ∈ Φ.source := hφs.mem_toOpenPartialHomeomorph_source
  have hxt : φ x ∈ Φ.target := hφs.image_mem_toOpenPartialHomeomorph_target
  have hΦx : Φ.symm (φ x) = x := Φ.left_inv hxs
  have hsymm : AnalyticAt ℂ Φ.symm (φ x) :=
    Φ.analyticAt_symm' hxs hφa (by rw [hΦ, hφd.fderiv, ← hDe])
  have hev : ∀ᶠ w in 𝓝 (φ x), w ∈ Φ.target ∧ AnalyticAt ℂ Φ.symm w ∧ Φ.symm w ∈ U := by
    have h1 : ∀ᶠ w in 𝓝 (φ x), w ∈ Φ.target := Φ.open_target.mem_nhds hxt
    have h3 : ∀ᶠ w in 𝓝 (φ x), Φ.symm w ∈ U :=
      Φ.continuousAt_symm hxt (hU.mem_nhds (by rw [hΦx]; exact hx))
    exact h1.and (hsymm.eventually_analyticAt.and h3)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  set u0 : K := PK (g x)
  have hφx : φ x = (u0, 0) := by simp [φ, u0]
  rw [hφx] at hball hΦx
  have hmemB : ∀ u : K, ∀ v : N, (u, v) ∈ Metric.ball (u0, (0 : N)) ε ↔
      u ∈ Metric.ball u0 ε ∧ v ∈ Metric.ball (0 : N) ε := by
    intro u v
    rw [← ball_prod_same]; rfl
  let h : K × N → (Fin m → ℂ) := fun w ↦ g (Φ.symm w)
  have hh : ∀ w ∈ Metric.ball (u0, (0 : N)) ε, AnalyticAt ℂ h w := fun w hw ↦
    (hg _ (hball w hw).2.2).comp (hball w hw).2.1
  have hPh : ∀ w ∈ Metric.ball (u0, (0 : N)) ε, PK (h w) = w.1 := fun w hw ↦
    congrArg Prod.fst (Φ.right_inv (hball w hw).1)
  have hDh : ∀ w ∈ Metric.ball (u0, (0 : N)) ε, ∀ b : N, fderiv ℂ h w (0, b) = 0 := by
    intro w hw b
    refine ancr_fderiv_inr_eq_zero h PK (hh w hw).differentiableAt ?_ ?_ b
    · filter_upwards [Metric.isOpen_ball.mem_nhds hw] with w' hw'
      exact hPh w' hw'
    · have hcomp : fderiv ℂ h w = (fderiv ℂ g (Φ.symm w)).comp (fderiv ℂ Φ.symm w) :=
        fderiv_comp w (hg _ (hball w hw).2.2).differentiableAt
          (hball w hw).2.1.differentiableAt
      rw [hcomp, hKr, ← hr _ (hball w hw).2.2]
      apply Submodule.finrank_mono
      exact LinearMap.range_comp_le_range (fderiv ℂ Φ.symm w : K × N →ₗ[ℂ] (Fin n → ℂ))
        (fderiv ℂ g (Φ.symm w) : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ))
  have hconst : ∀ u : K, ∀ v : N, (u, v) ∈ Metric.ball (u0, (0 : N)) ε → h (u, v) = h (u, 0) := by
    intro u v huv
    have hu := ((hmemB u v).mp huv).1
    have hv := ((hmemB u v).mp huv).2
    have hin : ∀ t ∈ Metric.ball (0 : N) ε, (u, t) ∈ Metric.ball (u0, (0 : N)) ε :=
      fun t ht ↦ (hmemB u t).mpr ⟨hu, ht⟩
    have hdiff : ∀ t ∈ Metric.ball (0 : N) ε,
        HasFDerivAt (fun t' : N ↦ h (u, t')) ((fderiv ℂ h (u, t)).comp
          (ContinuousLinearMap.inr ℂ K N)) t := fun t ht ↦
      (hh _ (hin t ht)).differentiableAt.hasFDerivAt.comp t (hasFDerivAt_prodMk_right u t)
    refine (convex_ball (0 : N) ε).is_const_of_fderivWithin_eq_zero (𝕜 := ℂ)
      (fun t ht ↦ (hdiff t ht).differentiableAt.differentiableWithinAt) (fun t ht ↦ ?_) hv
      (Metric.mem_ball_self hε)
    rw [fderivWithin_of_isOpen Metric.isOpen_ball ht, (hdiff t ht).fderiv]
    ext1 b
    exact hDh _ (hin t ht) b
  set W : Set (Fin n → ℂ) := Φ.source ∩ Φ ⁻¹' Metric.ball (u0, (0 : N)) ε with hWdef
  set V : Set (Fin m → ℂ) := PK ⁻¹' Metric.ball u0 ε with hVdef
  have hWU : W ⊆ U := by
    rintro z ⟨hzs, hzb⟩
    have := (hball _ hzb).2.2
    rwa [Φ.left_inv hzs] at this
  have himage : ∀ y ∈ V, y ∈ g '' W ↔ y = h (PK y, 0) := by
    intro y hy
    constructor
    · rintro ⟨z, ⟨hzs, hzb⟩, rfl⟩
      have hz : Φ.symm (Φ z) = z := Φ.left_inv hzs
      have h1 : PK (g z) = (Φ z).1 := rfl
      have h2 : g z = h (Φ z) := by simp only [h, hz]
      calc g z = h ((Φ z).1, (Φ z).2) := h2
        _ = h ((Φ z).1, 0) := hconst _ _ hzb
        _ = h (PK (g z), 0) := by rw [h1]
    · intro hy'
      have hw : (PK y, (0 : N)) ∈ Metric.ball (u0, (0 : N)) ε :=
        (hmemB _ _).mpr ⟨hy, Metric.mem_ball_self hε⟩
      refine ⟨Φ.symm (PK y, 0), ⟨Φ.map_target (hball _ hw).1, ?_⟩, hy'.symm⟩
      rw [Set.mem_preimage, Φ.right_inv (hball _ hw).1]
      exact hw
  have hsub : g '' W ⊆ V := by
    rintro _ ⟨z, ⟨_, hzb⟩, rfl⟩
    exact ((hmemB _ _).mp hzb).1
  have hPKa : ∀ y ∈ V, AnalyticAt ℂ (fun y' ↦ h (PK y', 0)) y := fun y hy ↦
    (hh _ ((hmemB _ _).mpr ⟨hy, Metric.mem_ball_self hε⟩)).comp
      (f := fun y' ↦ (PK y', (0 : N))) ((PK.analyticAt y).prod analyticAt_const)
  refine ⟨W, V, Φ.isOpen_inter_preimage Metric.isOpen_ball, ⟨hxs, ?_⟩, hWU,
    Metric.isOpen_ball.preimage PK.continuous, hsub,
    ⟨m, fun y ↦ y - h (PK y, 0), fun y hy ↦ analyticAt_id.sub (hPKa y hy), fun y hy ↦ ?_⟩, ?_⟩
  · rw [Set.mem_preimage, show (Φ x) = φ x from rfl, hφx]
    exact Metric.mem_ball_self hε
  · rw [himage y hy, sub_eq_zero]
  -- the germ of the image is an analytic retract of `ℂʳ`
  have hfin : finrank ℂ (Fin r → ℂ) = finrank ℂ K := by rw [Module.finrank_fin_fun, hKr]
  let j : (Fin r → ℂ) ≃L[ℂ] K := ContinuousLinearEquiv.ofFinrankEq hfin
  let σ : (Fin r → ℂ) → (Fin m → ℂ) := fun u ↦ h (u0 + j u, 0) - g x
  let π : (Fin m → ℂ) → (Fin r → ℂ) := fun z ↦ j.symm (PK (g x + z) - u0)
  have hc0 : (u0 + j 0, (0 : N)) = (u0, 0) := by simp
  have hcont : Continuous (fun u : Fin r → ℂ ↦ (u0 + j u, (0 : N))) :=
    (continuous_const.add j.continuous).prodMk continuous_const
  have hσa : AnalyticAt ℂ σ 0 :=
    ((hh _ (Metric.mem_ball_self hε)).comp_of_eq
      ((analyticAt_const.add (j.analyticAt 0)).prod analyticAt_const) hc0).sub analyticAt_const
  have hhx : h (u0, 0) = g x := by simp only [h, hΦx]
  have hσ0 : σ 0 = 0 := by simp only [σ, map_zero, add_zero, hhx, sub_self]
  have hπa : AnalyticAt ℂ π 0 :=
    (j.symm.analyticAt _).comp (((PK.analyticAt _).comp
      (analyticAt_const.add analyticAt_id)).sub analyticAt_const)
  have hπ0 : π 0 = 0 := by simp [π, u0]
  have hnear : ∀ᶠ u in 𝓝 (0 : Fin r → ℂ), (u0 + j u, (0 : N)) ∈ Metric.ball (u0, (0 : N)) ε :=
    hcont.continuousAt.preimage_mem_nhds
      (by rw [map_zero, add_zero]; exact Metric.ball_mem_nhds _ hε)
  have hgerm : adim2_germ m (g '' W) (g x) = adim2_germ m {z | g x + z ∈ g '' W} 0 := by
    unfold adim2_germ; congr 1; funext z; simp only [zero_add, Set.mem_ofPred_eq]
  have key := adim9b_retractGerm_dimension σ hσa hσ0 π hπa hπ0 {z | g x + z ∈ g '' W}
    (by
      filter_upwards [hnear] with u hu
      simp only [π, σ, add_sub_cancel, hPh _ hu, add_sub_cancel_left, j.symm_apply_apply])
    (by
      filter_upwards [hnear] with u hu
      simp only [σ, add_sub_cancel]
      refine ⟨Φ.symm (u0 + j u, 0), ⟨Φ.map_target (hball _ hu).1, ?_⟩, rfl⟩
      rw [Set.mem_preimage, Φ.right_inv (hball _ hu).1]
      exact hu)
    (Eventually.of_forall fun z hz ↦ by
      have hzV : g x + z ∈ V := hsub hz
      have := (himage _ hzV).mp hz
      simp only [σ, π, j.apply_symm_apply, add_sub_cancel]
      rw [← this, add_sub_cancel_left])
  rw [adim2_dimension, hgerm, key]
  rfl

end HodgeLean.Foundations.Analytic
