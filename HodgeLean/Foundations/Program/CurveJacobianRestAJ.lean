import HodgeLean.Foundations.Program.CurveJacobianAExact
import HodgeLean.Foundations.Program.CurveJacobianAPeriods

/-! # Track B3, lane Rest: the Abel–Jacobi map is holomorphic

Near a point `q`, an Abel–Jacobi map is `y ↦ aj q + [v_y]`, where `v_y` has as periods the integrals
along the chart segment from `q` to `y`. These integrals are differences of primitives of the disc
coefficients, hence holomorphic in the chart coordinate. Reading `[v_y]` through its periods on a
basis of `Ω¹(C)` (an injective linear map of `(ℂ ⊗ Λ) ⧸ F`, inverted on the left), the map is the
covering map of the torus composed with a holomorphic map into linear coordinates.
HC no distance; AV milestone no distance.
-/

set_option maxHeartbeats 400000

noncomputable section

open Manifold Filter Topology Set Metric
open scoped TensorProduct ContDiff

namespace HodgeLean.Foundations.Program

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- The periods of a class of `(ℂ ⊗ Λ) ⧸ F` on a family of holomorphic forms. -/
def b3Rest_evalQ {ι : Type} (θs : ι → b3_HolForm E C) :
    ((ℂ ⊗[ℤ] b3_periodLattice E C) ⧸ b3_periodF E C) →ₗ[ℂ] (ι → ℂ) :=
  (b3_periodF E C).liftQ
    (LinearMap.pi fun j ↦ (LinearMap.proj (R := ℂ) (φ := fun _ : b3_HolForm E C ↦ ℂ) (θs j)) ∘ₗ
      b3_cplxPeriod E C)
    (fun v hv ↦ by
      have hv' : b3_cplxPeriod E C v = 0 := hv
      ext j
      simp [hv'])

theorem b3Rest_evalQ_mk {ι : Type} (θs : ι → b3_HolForm E C) (v : ℂ ⊗[ℤ] b3_periodLattice E C)
    (j : ι) : b3Rest_evalQ θs (Submodule.Quotient.mk v) j = b3_cplxPeriod E C v (θs j) := rfl

/-- On a basis of `Ω¹(C)`, the periods determine the class. -/
theorem b3Rest_evalQ_injective {ι : Type} (bθ : Module.Basis ι ℂ (b3_HolForm E C)) :
    Function.Injective (b3Rest_evalQ (E := E) (C := C) bθ) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro w hw
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rw [LinearMap.mem_ker] at hw
  have hd : b3A_toDual ⟨b3_cplxPeriod E C v, b3A_cplxPeriod_mem_linearDual v⟩ = 0 := by
    refine bθ.ext fun j ↦ ?_
    have := congr_fun hw j
    rw [b3Rest_evalQ_mk] at this
    exact this
  have h0 : b3_cplxPeriod E C v = 0 := by
    have := b3A_toDual_injective (hd.trans (map_zero _).symm)
    exact congrArg Subtype.val this
  exact (Submodule.Quotient.mk_eq_zero _).2 h0

theorem b3Rest_coordH_apply [Module.Finite ℤ (b3_periodLattice E C)]
    (w : (ℂ ⊗[ℤ] b3_periodLattice E C) ⧸ b3_periodF E C) :
    b2_coordHomeomorph (b3_periodLattice E C) (b3_periodF E C) w = b2_coord _ w := rfl

theorem b3Rest_torusCover_coord [Module.Finite ℤ (b3_periodLattice E C)]
    (w : (ℂ ⊗[ℤ] b3_periodLattice E C) ⧸ b3_periodF E C) :
    b2_torusCover (b3_periodLattice E C) (b3_periodF E C)
      (b2_coordHomeomorph (b3_periodLattice E C) (b3_periodF E C) w) = QuotientAddGroup.mk w := by
  unfold b2_torusCover
  rw [Homeomorph.symm_apply_apply]

/-- An `E`-valued description of a torus-valued map near `q`: if `aj = aj q + [W]` near `q`, with
`W` holomorphic in linear coordinates, then `aj` is holomorphic at `q`. -/
theorem b3Rest_contMDiffAt_of_local [Module.Finite ℤ (b3_periodLattice E C)]
    [DiscreteTopology (b2_latticeMap (b3_periodLattice E C) (b3_periodF E C)).range]
    (aj : C → b3_Jacobian E C) (q : C)
    (W : C → (ℂ ⊗[ℤ] b3_periodLattice E C) ⧸ b3_periodF E C)
    (hW : ∀ᶠ y in 𝓝 q, aj y = aj q + QuotientAddGroup.mk (W y))
    (hWd : ContMDiffAt 𝓘(ℂ, E)
      𝓘(ℂ, Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] b3_periodLattice E C) ⧸ b3_periodF E C)) → ℂ) ω
      (fun y ↦ b2_coord _ (W y)) q) :
    ContMDiffAt 𝓘(ℂ, E)
      𝓘(ℂ, Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] b3_periodLattice E C) ⧸ b3_periodF E C)) → ℂ) ω
      aj q := by
  obtain ⟨c₀, hc₀⟩ := QuotientAddGroup.mk_surjective (aj q)
  have hM : ContMDiffAt 𝓘(ℂ, E)
      𝓘(ℂ, Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] b3_periodLattice E C) ⧸ b3_periodF E C)) → ℂ) ω
      (fun y ↦ b2_coord _ c₀ + b2_coord _ (W y)) q :=
    contMDiffAt_const.add hWd
  refine ((b2_torusCover_contMDiff (b3_periodF E C) _).comp q hM).congr_of_eventuallyEq ?_
  filter_upwards [hW] with y hy
  have e1 : b2_coord _ c₀ + b2_coord _ (W y) =
      b2_coordHomeomorph (b3_periodLattice E C) (b3_periodF E C) (c₀ + W y) := by
    rw [b3Rest_coordH_apply]
    exact (map_add (b2_coord _) c₀ (W y)).symm
  have e2 := b3Rest_torusCover_coord (c₀ + W y)
  rw [Function.comp_apply, e1, e2, hy, ← hc₀]
  rfl

/-- Linear coordinates of a linear image of a holomorphic map are holomorphic. -/
theorem b3Rest_contDiffAt_coord_comp {ι : Type} [Fintype ι] [Module.Finite ℤ (b3_periodLattice E C)]
    (L : (ι → ℂ) →ₗ[ℂ] ((ℂ ⊗[ℤ] b3_periodLattice E C) ⧸ b3_periodF E C))
    (Gv : ℂ → (ι → ℂ)) {z₀ : ℂ} (hGv : ContDiffAt ℂ ω Gv z₀) :
    ContDiffAt ℂ ω (fun z ↦ b2_coord ((ℂ ⊗[ℤ] b3_periodLattice E C) ⧸ b3_periodF E C) (L (Gv z)))
      z₀ := by
  let A : (ι → ℂ) →L[ℂ]
      (Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] b3_periodLattice E C) ⧸ b3_periodF E C)) → ℂ) :=
    LinearMap.toContinuousLinearMap
      ((b2_coord ((ℂ ⊗[ℤ] b3_periodLattice E C) ⧸ b3_periodF E C)).toLinearMap ∘ₗ L)
  exact A.contDiff.contDiffAt.comp z₀ hGv

/-- Along the chart segment from `q` to the disc point `z`, an Abel–Jacobi map moves by the class
with periods `G_j z - G_j 0` on a basis. -/
theorem b3Rest_abelJacobi_disc {ι : Type} (bθ : Module.Basis ι ℂ (b3_HolForm E C))
    (L : (ι → ℂ) →ₗ[ℂ] ((ℂ ⊗[ℤ] b3_periodLattice E C) ⧸ b3_periodF E C))
    (hL : L ∘ₗ b3Rest_evalQ bθ = LinearMap.id)
    (p₀ : C) (aj : C → b3_Jacobian E C) (h : b3_IsAbelJacobi E C p₀ aj)
    (κ : E →L[ℂ] ℂ) (u : E) (hκ : ∀ w : E, w = κ w • u) (hκu : κ u = 1) (q : C) {R : ℝ}
    (hR : ∀ z : ℂ, ‖z‖ < R → chartAt E q q + z • u ∈ (chartAt E q).target)
    (G : ι → ℂ → ℂ)
    (hG : ∀ j, ∀ z ∈ ball (0 : ℂ) R,
      HasDerivAt (G j) (b3A_discCoef ((bθ j : b3_HolForm E C) : TangentBundle 𝓘(ℂ, E) C → ℂ) q u z)
        z)
    (z : ℂ) (hz : ‖z‖ < R) :
    aj (b3A_disc q u z) = aj q + QuotientAddGroup.mk (L (fun j ↦ G j z - G j 0)) := by
  let γ : ℝ → C := fun t ↦ (chartAt E q).symm (chartAt E q q +
    Real.smoothTransition (3 * t - 1) • (chartAt E q q + z • u - chartAt E q q))
  have hs : b3A_IsGoodPath (E := E) γ ((chartAt E q).symm (chartAt E q q))
      ((chartAt E q).symm (chartAt E q q + z • u)) :=
    b3A_isGoodPath_segment q (chartAt E q q) (chartAt E q q + z • u)
      (b3A_segment_subset u q hR z hz)
  have hs1 : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ := hs.1
  obtain ⟨v, hv, hvaj⟩ := h.2 γ hs1
  have h0 : γ 0 = q := hs.apply_zero.trans ((chartAt E q).left_inv (mem_chart_source E q))
  have h1 : γ 1 = b3A_disc q u z := hs.apply_one
  rw [h0, h1] at hvaj
  have hT : b3Rest_evalQ bθ (Submodule.Quotient.mk v) = fun j ↦ G j z - G j 0 := by
    funext j
    rw [b3Rest_evalQ_mk, hv]
    exact b3A_segment_integral (bθ j).2 κ u hκ hκu q hR (hG j) z hz
  have : L (fun j ↦ G j z - G j 0) = Submodule.Quotient.mk v := by
    rw [← hT]
    exact LinearMap.congr_fun hL _
  rw [this, ← hvaj]
  exact (add_sub_cancel _ _).symm

/-- **Abel–Jacobi maps are holomorphic at each point.** -/
theorem b3Rest_abelJacobi_contMDiffAt [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) [Module.Finite ℤ (b3_periodLattice E C)]
    [DiscreteTopology (b2_latticeMap (b3_periodLattice E C) (b3_periodF E C)).range]
    (p₀ : C) (aj : C → b3_Jacobian E C) (h : b3_IsAbelJacobi E C p₀ aj) (q : C) :
    ContMDiffAt 𝓘(ℂ, E)
      𝓘(ℂ, Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] b3_periodLattice E C) ⧸ b3_periodF E C)) → ℂ) ω
      aj q := by
  have : FiniteDimensional ℂ E := Module.finite_of_finrank_eq_succ hE
  have : FiniteDimensional ℂ (b3_HolForm E C) := b3A_holForm_finiteDimensional hE
  let bθ := Module.finBasis ℂ (b3_HolForm E C)
  obtain ⟨L, hL⟩ := (b3Rest_evalQ (E := E) (C := C) bθ).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 (b3Rest_evalQ_injective bθ))
  let b := Module.finBasisOfFinrankEq ℂ E hE
  let u := b 0
  let κ : E →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (b.coord 0)
  have hκ : ∀ w : E, w = κ w • u := by
    intro w
    conv_lhs => rw [← b.sum_repr w]
    simp [κ, u]
  have hκu : κ u = 1 := by simp [κ, u]
  have hu : u ≠ 0 := b.ne_zero 0
  obtain ⟨R, hR0, hR⟩ := b3A_chart_radius u hu q
  have hG : ∀ j, ∃ G : ℂ → ℂ, ∀ z ∈ ball (0 : ℂ) R,
      HasDerivAt G (b3A_discCoef ((bθ j : b3_HolForm E C) : TangentBundle 𝓘(ℂ, E) C → ℂ) q u z)
        z := by
    intro j
    exact DifferentiableOn.isExactOn_ball fun z hz ↦ (b3A_discCoef_differentiableAt (bθ j).2 q u
      (hR z (mem_ball_zero_iff.1 hz))).differentiableWithinAt
  choose G hG using hG
  let Gv : ℂ → (Fin (Module.finrank ℂ (b3_HolForm E C)) → ℂ) := fun z j ↦ G j z - G j 0
  have hseg : ∀ z : ℂ, ‖z‖ < R → aj (b3A_disc q u z) =
      aj q + QuotientAddGroup.mk (L (Gv z)) :=
    fun z hz ↦ b3Rest_abelJacobi_disc bθ L hL p₀ aj h κ u hκ hκu q hR G hG z hz
  let ζ : C → ℂ := fun y ↦ κ (chartAt E q y - chartAt E q q)
  have hζ : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω ζ q := by
    have h1 := contMDiffAt_extChartAt (I := 𝓘(ℂ, E)) (n := ω) (x := q)
    have h2 : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω (fun w : E ↦ κ (w - chartAt E q q)) :=
      (κ.contDiff.comp (contDiff_id.sub contDiff_const)).contMDiff
    exact (h2 _).comp q h1
  have hζ0 : ζ q = 0 := by simp [ζ]
  refine b3Rest_contMDiffAt_of_local aj q (fun y ↦ L (Gv (ζ y))) ?_ ?_
  · have hU : (chartAt E q).source ∩ {y | ‖ζ y‖ < R} ∈ 𝓝 q := by
      refine inter_mem ((chartAt E q).open_source.mem_nhds (mem_chart_source E q)) ?_
      exact hζ.continuousAt.preimage_mem_nhds (isOpen_lt continuous_norm continuous_const
        |>.mem_nhds (by simp [hζ0, hR0]))
    filter_upwards [hU] with y ⟨hy, hyR⟩
    have hdisc : b3A_disc q u (ζ y) = y := by
      rw [b3A_disc, ← hκ, add_sub_cancel]
      exact (chartAt E q).left_inv hy
    have := hseg _ hyR
    rwa [hdisc] at this
  · have hGv : ContDiffAt ℂ ω Gv 0 := by
      have hd : DifferentiableOn ℂ Gv (ball (0 : ℂ) R) := by
        rw [differentiableOn_pi]
        intro j z hz
        exact ((hG j z hz).differentiableAt.sub_const _).differentiableWithinAt
      exact (hd.analyticAt (ball_mem_nhds 0 hR0)).contDiffAt
    have hGv' : ContDiffAt ℂ ω Gv (ζ q) := by rw [hζ0]; exact hGv
    exact (b3Rest_contDiffAt_coord_comp L Gv hGv').contMDiffAt.comp q hζ

/-- **Abel–Jacobi maps are holomorphic.** -/
theorem b3Rest_abelJacobi_holomorphic [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) [Module.Finite ℤ (b3_periodLattice E C)]
    [DiscreteTopology (b2_latticeMap (b3_periodLattice E C) (b3_periodF E C)).range]
    (p₀ : C) (aj : C → b3_Jacobian E C) (h : b3_IsAbelJacobi E C p₀ aj) :
    ContMDiff 𝓘(ℂ, E)
      𝓘(ℂ, Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] b3_periodLattice E C) ⧸ b3_periodF E C)) → ℂ) ω
      aj :=
  fun q ↦ b3Rest_abelJacobi_contMDiffAt hE p₀ aj h q

end HodgeLean.Foundations.Program
