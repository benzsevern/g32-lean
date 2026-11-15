import HodgeLean.Foundations.Program.RelativeFrameEllipticPeriodic

/-! # A genus-one witness: the cokernel of `δ₀` on `rfw_E` is a line
A lattice-periodic function `H`, holomorphic and bounded over the outer region, and a bounded
holomorphic `G` on `D(0, 2/5)` give the source datum `(H on every piece, G)` of `δ₀`, whose image
is `H − G` on the annulus (`rfw_mem_range_of`). With the periodization `rfw_periodize`, every
target element is a multiple of `du/u` modulo the range; with the residue obstruction
`rfw_invT_not_mem_range`, `du/u` is not in the range. So the quotient has dimension one.
-/

noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff BoundedContinuousFunction
namespace HodgeLean.Foundations.Program

theorem rfw_extendBdd_ext {U : Set ℂ} {f₁ f₂ : b63r_bddHol U}
    (h : ∀ u ∈ U, rf4_extendBdd f₁ u = rf4_extendBdd f₂ u) : f₁ = f₂ := by
  apply Subtype.ext
  ext u
  have := h u u.2
  simpa [rf4_extendBdd, u.2] using this

theorem rfw_extendBdd_sub {U : Set ℂ} (f₁ f₂ : b63r_bddHol U) (u : ℂ) :
    rf4_extendBdd (f₁ - f₂) u = rf4_extendBdd f₁ u - rf4_extendBdd f₂ u := by
  unfold rf4_extendBdd
  split_ifs <;> simp

theorem rfw_extendBdd_smul {U : Set ℂ} (c : ℂ) (f : b63r_bddHol U) (u : ℂ) :
    rf4_extendBdd (c • f) u = c * rf4_extendBdd f u := by
  unfold rf4_extendBdd
  split_ifs <;> simp

theorem rfw_piece_mem_O (i : Fin (rfw_centres.card + 1)) {z : ℂ} (hz : z ∈ rfw_piece i) :
    rfw_proj z ∈ rfw_O := by
  induction i using Fin.cases with
  | zero => exact rfw_annulus_mem_O hz
  | succ k => exact hz.2

/-- The bounded chart form of a lattice-periodic function, holomorphic and bounded by `B` over
the outer region: the function itself on every piece (transitions are translations). -/
def rfw_periodicForm (H : ℂ → ℂ) (hHp : ∀ z z', rfw_proj z = rfw_proj z' → H z = H z')
    (hHd : ∀ z, rfw_proj z ∈ rfw_O → DifferentiableAt ℂ H z) (B : ℝ)
    (hB : ∀ z, rfw_proj z ∈ rfw_O → ‖H z‖ ≤ B) : rf2_bddForm rfw_cover :=
  ⟨fun i ↦ ⟨BoundedContinuousFunction.ofNormedAddCommGroup (fun z : rfw_piece i ↦ H z)
      (DifferentiableOn.continuousOn (f := H) (s := rfw_piece i)
        (fun z hz ↦ (hHd z (rfw_piece_mem_O i hz)).differentiableWithinAt)).domRestrict B
      (fun z ↦ hB z (rfw_piece_mem_O i z.2)),
    ⟨H, fun z hz ↦ (hHd z (rfw_piece_mem_O i hz)).differentiableWithinAt, fun _ ↦ rfl⟩⟩, by
    intro i j z w h
    change H z = H w * deriv (rfw_chart (rfw_cen j) ∘ (rfw_chart (rfw_cen i)).symm) z
    have hw : rfw_proj (w : ℂ) ∈ (rfw_chart (rfw_cen j)).source :=
      rfw_proj_mem_source (rfw_piece_subset j w.2)
    have h' : rfw_proj (z : ℂ) = rfw_proj (w : ℂ) := h
    rw [rfw_deriv_transition (h' ▸ hw), mul_one, hHp _ _ h']⟩

/-- **The range criterion**: `H − G` on the annulus is in the range of `δ₀`. -/
theorem rfw_mem_range_of (t : rf4_Tgt rfw_outer) (H G : ℂ → ℂ)
    (hHp : ∀ z z', rfw_proj z = rfw_proj z' → H z = H z')
    (hHd : ∀ z, rfw_proj z ∈ rfw_O → DifferentiableAt ℂ H z)
    (hHb : ∃ B, ∀ z, rfw_proj z ∈ rfw_O → ‖H z‖ ≤ B)
    (hGd : DifferentiableOn ℂ G (Metric.ball 0 (2 * (1 / 5))))
    (hGb : ∃ B, ∀ z ∈ Metric.ball (0 : ℂ) (2 * (1 / 5)), ‖G z‖ ≤ B)
    (ht : ∀ x, ∀ u ∈ b63r_annulus 1 (1 / 5), rf4_extendBdd (t x) u = H u - G u) :
    t ∈ (rf4_delta rfw_outer (fun _ ↦ 0)).range := by
  obtain ⟨BH, hBH⟩ := hHb
  obtain ⟨BG, hBG⟩ := hGb
  let α := rfw_periodicForm H hHp hHd BH hBH
  let gv : b63r_bddHol (Metric.ball (0 : ℂ) (2 * (1 / 5))) :=
    ⟨BoundedContinuousFunction.ofNormedAddCommGroup
      (fun z : Metric.ball (0 : ℂ) (2 * (1 / 5)) ↦ G z)
      hGd.continuousOn.domRestrict BG (fun z ↦ hBG z z.2), ⟨G, hGd, fun _ ↦ rfl⟩⟩
  let g : rf4_Disc rfw_outer := fun _ _ ↦ gv
  refine ⟨(α, g), ?_⟩
  change rf4_delta rfw_outer (fun _ ↦ 0) (α, g) = t
  funext x
  refine rfw_extendBdd_ext fun u hu ↦ ?_
  have hu' : u ∈ b63r_annulus 1 (1 / 5) := hu
  rw [rfw_delta_apply _ x hu', ht x u hu']
  have hu2 : u ∈ rfw_outer.P.piece (rfw_outer.ann x) := hu
  have hub : u ∈ Metric.ball (0 : ℂ) (2 * (1 / 5)) := by
    rw [mem_ball_zero_iff]; have := (rfw_annulus_norm hu').2; linarith
  have hub' : u ∈ Metric.ball (rfw_outer.c x) (2 * rfw_outer.r) := hub
  simp only [rf4_extendBdd, hu2, hub', ↓reduceDIte]
  rfl

theorem rfw_fin_eq (x : Fin rfw_outer.m) : x = rfw_x0 := by
  have := x.2
  change x.val < 1 at this
  exact Fin.ext (by change x.val = 0; omega)

/-- **The cokernel of `δ₀` is a line.** -/
theorem rfw_coker_finrank :
    Module.finrank ℂ (rf4_Tgt rfw_outer ⧸ (rf4_delta rfw_outer (fun _ ↦ 0)).range) = 1 := by
  set R := (rf4_delta rfw_outer (fun _ ↦ 0)).range
  have hq : Submodule.Quotient.mk (p := R) rfw_invT ≠ 0 := by
    rw [Ne, Submodule.Quotient.mk_eq_zero]
    exact rfw_invT_not_mem_range
  refine (finrank_eq_one_iff_of_nonzero' _ hq).mpr fun y ↦ ?_
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective R y
  obtain ⟨fx, hfx, hft⟩ := (t rfw_x0).2
  have hfx' : DifferentiableOn ℂ fx (b63r_annulus 1 (1 / 5)) := hfx
  have hM : ∀ u ∈ b63r_annulus 1 (1 / 5), ‖fx u‖ ≤ ‖((t rfw_x0 : b63r_bddHol _) :
      b63r_annulus (rfw_outer.deg rfw_x0) rfw_outer.r →ᵇ ℂ)‖ := by
    intro u hu
    rw [← hft ⟨u, hu⟩]
    exact BoundedContinuousFunction.norm_coe_le_norm _ _
  obtain ⟨c, H, G, h1, h2, h3, h4, h5, h6⟩ := rfw_periodize hfx' hM
  refine ⟨c, ?_⟩
  have hmem : t - c • rfw_invT ∈ R := by
    refine rfw_mem_range_of _ H G h1 h2 h3 h4 h5 fun x u hu ↦ ?_
    rw [← h6 u hu, rfw_fin_eq x]
    change rf4_extendBdd (t rfw_x0 - c • rfw_invT rfw_x0) u = _
    rw [rfw_extendBdd_sub, rfw_extendBdd_smul, rfw_invT_apply _ hu]
    have hu1 : u ∈ b63r_annulus (rfw_outer.deg rfw_x0) rfw_outer.r := hu
    simp only [rf4_extendBdd, hu1, ↓reduceDIte]
    rw [hft ⟨u, hu1⟩]
  rw [← Submodule.Quotient.mk_smul]
  exact ((Submodule.Quotient.eq R).mpr hmem).symm

end HodgeLean.Foundations.Program
