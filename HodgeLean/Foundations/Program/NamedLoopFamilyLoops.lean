import HodgeLean.Foundations.Program.BraidBridgesThree
import HodgeLean.Foundations.Program.PathCoverFamilyExists
import HodgeLean.Foundations.Program.PathCoverFamily
import HodgeLean.Foundations.Program.SchlesingerPathMobius

/-! # Specified named-loop family: the slot lassos as positive peripheral loops

In the certificate coordinate the normalization of the target sphere is affine, so every slot
lasso is carried to a stem followed by a round circle about a single mark. Shrinking that circle
onto its mark identifies the rotation generator detected by a lift of the lasso.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- An affine image of a point distinct from the finite marks avoids the thirteen marks. -/
theorem b65w_affine_mem (c : Fin 10 → ℂ) (α β : ℂ) (hα : α ≠ 0) (wk : Fin 12 → ℂ)
    (hmark : ∀ k, b6_branch c k.castSucc = ((α * wk k + β : ℂ) : OnePoint ℂ))
    (z : ℂ) (hz : ∀ k, z ≠ wk k) :
    ((α * z + β : ℂ) : OnePoint ℂ) ∈ b6t_punctured c := by
  rintro ⟨i, hi⟩
  induction i using Fin.lastCases with
  | last => rw [mr_branch_last] at hi; exact OnePoint.infty_ne_coe _ hi
  | cast k =>
    rw [hmark] at hi
    apply hz k
    have h := OnePoint.coe_injective hi
    exact (mul_left_cancel₀ hα (add_right_cancel h)).symm

/-- A round circle about a point of a disc, inside that disc and around its only mark. -/
theorem b65w_ring_ne (wk : Fin 12 → ℂ) (j : Fin 12) (c₀ : ℂ) (r : ℝ)
    (hsep : ∀ k, k ≠ j → r < ‖wk k - c₀‖) (m : ℂ) (R : ℝ) (u : ℂ) (hu : ‖u‖ = 1)
    (h1 : ‖m - wk j‖ < R) (h2 : ‖m - c₀‖ + R ≤ r) :
    ∀ k, m + (R : ℂ) * Complex.I * u ≠ wk k := by
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg _) h1
  have hn : ‖(R : ℂ) * Complex.I * u‖ = R := by
    rw [norm_mul, norm_mul, Complex.norm_I, hu, Complex.norm_real, Real.norm_of_nonneg hR.le]
    ring
  intro k hk
  by_cases hkj : k = j
  · subst hkj
    have : m - wk k = -((R : ℂ) * Complex.I * u) := by rw [← hk]; ring
    rw [this, norm_neg, hn] at h1
    exact lt_irrefl _ h1
  · have h3 := hsep k hkj
    rw [← hk] at h3
    have h4 : ‖m + (R : ℂ) * Complex.I * u - c₀‖ ≤ ‖m - c₀‖ + R := by
      calc ‖m + (R : ℂ) * Complex.I * u - c₀‖ = ‖(m - c₀) + (R : ℂ) * Complex.I * u‖ := by
            ring_nf
        _ ≤ ‖m - c₀‖ + ‖(R : ℂ) * Complex.I * u‖ := norm_add_le _ _
        _ = ‖m - c₀‖ + R := by rw [hn]
    linarith

/-- The norm of a complex number exceeds `r` when its squared parts do. -/
theorem b65w_lt_norm (z : ℂ) (r : ℝ) (h : r ^ 2 < z.re ^ 2 + z.im ^ 2) :
    r < ‖z‖ := by
  by_contra hle
  push Not at hle
  have h1 : ‖z‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
  rw [Complex.sq_norm, Complex.normSq_apply] at h1
  nlinarith

/-- The norm of a complex number is below `r` when its squared parts are. -/
theorem b65w_norm_lt (z : ℂ) (r : ℝ) (hr : 0 ≤ r) (h : z.re ^ 2 + z.im ^ 2 < r ^ 2) :
    ‖z‖ < r := by
  by_contra hle
  push Not at hle
  have h1 : r ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ hr hle 2
  rw [Complex.sq_norm, Complex.normSq_apply] at h1
  nlinarith

/-- **The outer loop.** If all finite marks lie in an affine image of the disc of radius `9`
about `mr_centre`, a lift of the affine image of `mr_outer` detects the rotation generator at
`∞`. -/
theorem b65w_outer_rotGen (c : Fin 10 → ℂ) (α β : ℂ) (hα : α ≠ 0) (wk : Fin 12 → ℂ)
    (hmark : ∀ k, b6_branch c k.castSucc = ((α * wk k + β : ℂ) : OnePoint ℂ))
    (hbd : ∀ k, ‖wk k - mr_centre‖ < 9)
    {y₀ : b6t_punctured c} (L : Path y₀ y₀)
    (hL : ∀ s : unitInterval, (L s : OnePoint ℂ) = ((α * mr_outer s + β : ℂ) : OnePoint ℂ))
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    {G : Type} [Group G] [Finite G] [MulAction G C] [FaithfulSMul G C]
    (hG : ∀ k : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ k • x))
    (f : C → OnePoint ℂ) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hgal : b4_IsGaloisCover G f)
    (hfree : ∀ x, f x ∉ Set.range (b6_branch c) → MulAction.stabilizer G x = ⊥)
    (Γ : C(unitInterval, C)) (l : G) (hΓ : ∀ t, f (Γ t) = (L t : OnePoint ℂ))
    (hend : Γ 1 = l • Γ 0) :
    ∃ q, f q = b6_branch c (Fin.last 12) ∧ b4_IsRotGen ℂ q l := by
  rw [mr_branch_last]
  have hE : Module.finrank ℂ ℂ = 1 := Module.finrank_self ℂ
  have hB : (Set.range (b6_branch c)).Finite := Set.finite_range _
  have hαn : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have hd : ∀ s : unitInterval, (L.symm s : OnePoint ℂ) =
      (((α * mr_centre + β) + Complex.exp ((((s : ℝ) * (2 * Real.pi) : ℝ) : ℂ) *
        Complex.I) * (α * (10 * Complex.I)) : ℂ) : OnePoint ℂ) := by
    intro s
    change (L (unitInterval.symm s) : OnePoint ℂ) = _
    rw [hL, unitInterval.coe_symm_eq, mr_outer_symm]
    congr 1
    ring
  have hbound : ∀ b : ℂ, (b : OnePoint ℂ) ∈ Set.range (b6_branch c) →
      ‖b - (α * mr_centre + β)‖ < 9 * ‖α‖ := by
    rintro b ⟨i, hi⟩
    induction i using Fin.lastCases with
    | last => rw [mr_branch_last] at hi; exact absurd hi (OnePoint.infty_ne_coe b)
    | cast k =>
      rw [hmark] at hi
      rw [← OnePoint.coe_injective hi]
      have : α * wk k + β - (α * mr_centre + β) = α * (wk k - mr_centre) := by ring
      rw [this, norm_mul]
      have := hbd k
      nlinarith
  have havoid := RiemannRochTop_infinity_disk_avoids _ (α * mr_centre + β) (9 * ‖α‖)
    (by positivity) hbound
  have hc2 : FundamentalGroup.fromPath ⟦L⟧ = FundamentalGroup.fromPath
      ⟦((Path.refl y₀).trans L.symm.symm).trans (Path.refl y₀).symm⟧ := by
    rw [Path.symm_symm, Path.refl_symm]
    apply congrArg FundamentalGroup.fromPath
    apply Quotient.sound
    exact (((Path.Homotopic.refl_trans _).hcomp (Path.Homotopic.refl _)).trans
      (Path.Homotopic.trans_refl _)).symm
  refine RiemannRochTop_rotGen_infinity_circle hE hG f hf hgal _ hB hfree (α * mr_centre + β)
    (9 * ‖α‖)⁻¹ havoid (α * (10 * Complex.I)) ?_ ?_ (Path.refl y₀) L.symm hd L hc2 Γ l hΓ hend
  · rw [norm_inv, norm_mul, norm_mul, Complex.norm_I]
    norm_num
    have hi := inv_pos.mpr hαn
    nlinarith
  · exact mul_ne_zero hα (by simp)

/-- **A slot lasso.** In an affine coordinate, a stem from `o` to the top of the circle of radius
`r` about `c₀`, that circle, and the stem back, where the disc about `c₀` contains exactly the
mark `j`: a lift of the loop detects the rotation generator at the mark `j`. The circle is shrunk
onto the mark inside the disc, and the based class is the stem conjugate of a round circle.
Source: `RiemannRochTop_rotGen_affine_circle`, `mr_loop_conj_of_homotopy`;
Mathlib `Path.Homotopic.subpath_trans_subpath`. -/
theorem b65w_lasso_rotGen (c : Fin 10 → ℂ) (α β : ℂ) (hα : α ≠ 0) (wk : Fin 12 → ℂ)
    (hmark : ∀ k, b6_branch c k.castSucc = ((α * wk k + β : ℂ) : OnePoint ℂ))
    (j : Fin 12) (c₀ o : ℂ) (r : ℝ) (hin : ‖wk j - c₀‖ < r)
    (hsep : ∀ k, k ≠ j → r < ‖wk k - c₀‖)
    {y₀ : b6t_punctured c} (L : Path y₀ y₀)
    (hL1 : ∀ s : unitInterval, (s : ℝ) ≤ 1 / 3 → (L s : OnePoint ℂ) =
      ((α * (o + ((3 * (s : ℝ) : ℝ) : ℂ) * (c₀ + Complex.I * (r : ℂ) - o)) + β : ℂ) :
        OnePoint ℂ))
    (hL2 : ∀ s : unitInterval, 1 / 3 ≤ (s : ℝ) → (s : ℝ) ≤ 2 / 3 → (L s : OnePoint ℂ) =
      ((α * (c₀ + Complex.I * (r : ℂ) *
        Complex.exp ((((3 * (s : ℝ) - 1) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I)) + β : ℂ) :
          OnePoint ℂ))
    (hL3 : ∀ s : unitInterval, 2 / 3 ≤ (s : ℝ) → (L s : OnePoint ℂ) =
      ((α * (o + ((3 - 3 * (s : ℝ) : ℝ) : ℂ) * (c₀ + Complex.I * (r : ℂ) - o)) + β : ℂ) :
        OnePoint ℂ))
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    {G : Type} [Group G] [Finite G] [MulAction G C] [FaithfulSMul G C]
    (hG : ∀ k : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ k • x))
    (f : C → OnePoint ℂ) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hgal : b4_IsGaloisCover G f)
    (hfree : ∀ x, f x ∉ Set.range (b6_branch c) → MulAction.stabilizer G x = ⊥)
    (Γ : C(unitInterval, C)) (l : G) (hΓ : ∀ t, f (Γ t) = (L t : OnePoint ℂ))
    (hend : Γ 1 = l • Γ 0) :
    ∃ q, f q = b6_branch c j.castSucc ∧ b4_IsRotGen ℂ q l := by
  have hE : Module.finrank ℂ ℂ = 1 := Module.finrank_self ℂ
  have hB : (Set.range (b6_branch c)).Finite := Set.finite_range _
  have hαn : 0 < ‖α‖ := norm_pos_iff.mpr hα
  set d := ‖wk j - c₀‖ with hd_def
  have hd0 : 0 ≤ d := norm_nonneg _
  have hrd : 0 < r - d := by linarith
  set ε : ℝ := (r - d) / 2 with hε_def
  have hε : 0 < ε := by rw [hε_def]; linarith
  have hmem := b65w_affine_mem c α β hα wk hmark
  let pt : unitInterval → {u : ℂ // ‖u‖ = 1} → ℂ := fun τ u ↦
    (((1 - (τ : ℝ)) : ℝ) : ℂ) * c₀ + ((τ : ℝ) : ℂ) * wk j +
      (((1 - (τ : ℝ)) * r + (τ : ℝ) * ε : ℝ) : ℂ) * Complex.I * (u : ℂ)
  have hpt : ∀ τ u k, pt τ u ≠ wk k := by
    intro τ u k
    have hτ0 := τ.2.1
    have hτ1 := τ.2.2
    have h1 : ‖(((1 - (τ : ℝ)) : ℝ) : ℂ) * c₀ + ((τ : ℝ) : ℂ) * wk j - wk j‖ <
        (1 - (τ : ℝ)) * r + (τ : ℝ) * ε := by
      have : (((1 - (τ : ℝ)) : ℝ) : ℂ) * c₀ + ((τ : ℝ) : ℂ) * wk j - wk j =
          (((1 - (τ : ℝ)) : ℝ) : ℂ) * (c₀ - wk j) := by push_cast; ring
      rw [this, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith), norm_sub_rev,
        ← hd_def]
      nlinarith [mul_nonneg (sub_nonneg.2 hτ1) hrd.le]
    have h2 : ‖(((1 - (τ : ℝ)) : ℝ) : ℂ) * c₀ + ((τ : ℝ) : ℂ) * wk j - c₀‖ +
        ((1 - (τ : ℝ)) * r + (τ : ℝ) * ε) ≤ r := by
      have : (((1 - (τ : ℝ)) : ℝ) : ℂ) * c₀ + ((τ : ℝ) : ℂ) * wk j - c₀ =
          ((τ : ℝ) : ℂ) * (wk j - c₀) := by push_cast; ring
      rw [this, norm_mul, Complex.norm_real, Real.norm_of_nonneg hτ0, ← hd_def]
      nlinarith [mul_nonneg hτ0 hrd.le]
    exact b65w_ring_ne wk j c₀ r hsep _ _ (u : ℂ) u.2 h1 h2 k
  have hptc : Continuous (fun x : unitInterval × {u : ℂ // ‖u‖ = 1} ↦ pt x.1 x.2) := by
    show Continuous (fun x : unitInterval × {u : ℂ // ‖u‖ = 1} ↦
      (((1 - (x.1 : ℝ)) : ℝ) : ℂ) * c₀ + ((x.1 : ℝ) : ℂ) * wk j +
        (((1 - (x.1 : ℝ)) * r + (x.1 : ℝ) * ε : ℝ) : ℂ) * Complex.I * (x.2 : ℂ))
    fun_prop
  let F₀ : C(unitInterval × {u : ℂ // ‖u‖ = 1}, b6t_punctured c) :=
    ⟨fun x ↦ ⟨((α * pt x.1 x.2 + β : ℂ) : OnePoint ℂ), hmem _ (hpt x.1 x.2)⟩,
      (OnePoint.continuous_coe.comp
        ((continuous_const.mul hptc).add continuous_const)).subtype_mk _⟩
  let fC : C({u : ℂ // ‖u‖ = 1}, b6t_punctured c) :=
    ⟨fun u ↦ F₀ (0, u), F₀.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let gC : C({u : ℂ // ‖u‖ = 1}, b6t_punctured c) :=
    ⟨fun u ↦ F₀ (1, u), F₀.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let H : fC.Homotopy gC :=
    { toContinuousMap := F₀, map_zero_left := fun _ ↦ rfl, map_one_left := fun _ ↦ rfl }
  let u₁ : unitInterval := ⟨1 / 3, by norm_num, by norm_num⟩
  let u₂ : unitInterval := ⟨2 / 3, by norm_num, by norm_num⟩
  have hu₁ : (u₁ : ℝ) = 1 / 3 := rfl
  have hu₂ : (u₂ : ℝ) = 2 / 3 := rfl
  let α' := (L.subpath 0 u₁).cast L.source.symm rfl
  let δ' := L.subpath u₁ u₂
  let β' := (L.subpath u₂ 1).cast rfl L.target.symm
  have hsplit : ((α'.trans δ').trans β').Homotopic L := by
    have H1 : (α'.trans δ').Homotopic ((L.subpath 0 u₂).cast L.source.symm rfl) :=
      (Path.Homotopic.subpath_trans_subpath L 0 u₁ u₂).pathCast L.source.symm rfl
    have H2 : (((L.subpath 0 u₂).cast L.source.symm rfl).trans β').Homotopic
        ((L.subpath 0 1).cast L.source.symm L.target.symm) :=
      (Path.Homotopic.subpath_trans_subpath L 0 u₂ 1).pathCast L.source.symm L.target.symm
    have H3 : (L.subpath 0 1).cast L.source.symm L.target.symm = L := by
      ext s; simp
    rw [H3] at H2
    exact (H1.hcomp (Path.Homotopic.refl β')).trans H2
  have hval1 : (L u₁ : OnePoint ℂ) = ((α * (c₀ + Complex.I * r) + β : ℂ) : OnePoint ℂ) := by
    rw [hL1 u₁ (by rw [hu₁]), hu₁]
    congr 2
    push_cast
    ring
  have hval2 : (L u₂ : OnePoint ℂ) = ((α * (c₀ + Complex.I * r) + β : ℂ) : OnePoint ℂ) := by
    rw [hL2 u₂ (by rw [hu₂]; norm_num) (by rw [hu₂]), hu₂]
    have : ((((3 * (2 / 3 : ℝ) - 1) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) =
        2 * Real.pi * Complex.I := by push_cast; ring
    rw [this, Complex.exp_two_pi_mul_I, mul_one]
  have h12 : L u₁ = L u₂ := Subtype.ext (hval1.trans hval2.symm)
  let z₁ : {u : ℂ // ‖u‖ = 1} := ⟨1, by simp⟩
  have hx : fC z₁ = L u₁ := by
    apply Subtype.ext
    change ((α * pt 0 z₁ + β : ℂ) : OnePoint ℂ) = _
    rw [hval1]
    congr 2
    simp only [pt, z₁, Set.Icc.coe_zero]
    push_cast
    ring
  let δ'' : Path (L u₁) (L u₁) := δ'.cast rfl h12
  have hP : ∀ s, δ'' s = fC (mr_unitLoop s) := by
    intro s
    apply Subtype.ext
    change (L (Set.Icc.convexComb u₁ u₂ s) : OnePoint ℂ) =
      ((α * pt 0 (mr_unitLoop s) + β : ℂ) : OnePoint ℂ)
    have hcs : ((Set.Icc.convexComb u₁ u₂ s : unitInterval) : ℝ) = 1 / 3 + (s : ℝ) / 3 := by
      rw [Set.Icc.coe_convexComb, hu₁, hu₂]; ring
    rw [hL2 _ (by rw [hcs]; linarith [s.2.1]) (by rw [hcs]; linarith [s.2.2]), hcs]
    congr 2
    simp only [pt, mr_unitLoop_apply, Set.Icc.coe_zero]
    have : (3 * (1 / 3 + (s : ℝ) / 3) - 1) = (s : ℝ) := by ring
    rw [this]
    push_cast
    ring
  let c' := mr_unitLoop.map gC.continuous
  let K := (H.evalAt z₁).cast hx.symm rfl
  have hhom : δ''.Homotopic ((K.trans c').trans K.symm) :=
    mr_loop_conj_of_homotopy H z₁ mr_unitLoop δ'' c' hx rfl hP (fun _ ↦ rfl) K
      (Path.Homotopic.refl _)
  let β'' : Path (L u₁) y₀ := β'.cast h12 rfl
  have hβ : β'' = α'.symm := by
    apply Path.ext
    funext s
    apply Subtype.ext
    change (L (Set.Icc.convexComb u₂ 1 s) : OnePoint ℂ) =
      (L (Set.Icc.convexComb 0 u₁ (unitInterval.symm s)) : OnePoint ℂ)
    have h1 : ((Set.Icc.convexComb u₂ 1 s : unitInterval) : ℝ) = 2 / 3 + (s : ℝ) / 3 := by
      rw [Set.Icc.coe_convexComb, hu₂]; simp; ring
    have h2 : ((Set.Icc.convexComb 0 u₁ (unitInterval.symm s) : unitInterval) : ℝ) =
        (1 - (s : ℝ)) / 3 := by
      rw [Set.Icc.coe_convexComb, hu₁, unitInterval.coe_symm_eq]; simp; ring
    rw [hL3 _ (by rw [h1]; linarith [s.2.1]), hL1 _ (by rw [h2]; linarith [s.2.1]), h1, h2]
    congr 2
    push_cast
    ring
  have hmain : L.Homotopic (((α'.trans K).trans c').trans (α'.trans K).symm) := by
    have e1 : L.Homotopic ((α'.trans δ'').trans α'.symm) := by
      rw [← hβ]
      exact hsplit.symm
    have e2 : ((α'.trans δ'').trans α'.symm).Homotopic
        ((α'.trans ((K.trans c').trans K.symm)).trans α'.symm) :=
      ((Path.Homotopic.refl α').hcomp hhom).hcomp (Path.Homotopic.refl _)
    have e3 : ((α'.trans ((K.trans c').trans K.symm)).trans α'.symm).Homotopic
        (((α'.trans K).trans c').trans (α'.trans K).symm) := by
      rw [Path.trans_symm]
      have a1 : (α'.trans ((K.trans c').trans K.symm)).Homotopic
          (((α'.trans K).trans c').trans K.symm) :=
        (Path.Homotopic.trans_assoc α' (K.trans c') K.symm).symm.trans
          ((Path.Homotopic.trans_assoc α' K c').symm.hcomp (Path.Homotopic.refl _))
      exact (a1.hcomp (Path.Homotopic.refl _)).trans (Path.Homotopic.trans_assoc _ _ _)
    exact (e1.trans e2).trans e3
  have hcL : FundamentalGroup.fromPath ⟦L⟧ =
      FundamentalGroup.fromPath ⟦((α'.trans K).trans c').trans (α'.trans K).symm⟧ :=
    congrArg FundamentalGroup.fromPath (Quotient.sound hmain)
  have hd' : ∀ t : unitInterval, (c' t : OnePoint ℂ) = (((α * wk j + β) +
      Complex.exp ((((t : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) *
        (α * ((ε : ℂ) * Complex.I)) : ℂ) : OnePoint ℂ) := by
    intro t
    change ((α * pt 1 (mr_unitLoop t) + β : ℂ) : OnePoint ℂ) = _
    congr 1
    simp only [pt, mr_unitLoop_apply, Set.Icc.coe_one]
    push_cast
    ring
  have havoid : ∀ z : ℂ, ‖z‖ < ‖α‖ * (r - d) → z ≠ 0 →
      (((α * wk j + β) + z : ℂ) : OnePoint ℂ) ∉ Set.range (b6_branch c) := by
    intro z hz hz0
    have heq : (α * wk j + β) + z = α * (wk j + z / α) + β := by field_simp; ring
    rw [heq]
    apply hmem
    intro k hk
    have hzα : ‖z / α‖ < r - d := by
      rw [norm_div, div_lt_iff₀ hαn]; linarith
    by_cases hkj : k = j
    · rw [hkj] at hk
      apply hz0
      have : z / α = 0 := by linear_combination hk
      exact (div_eq_zero_iff.mp this).resolve_right hα
    · have h3 := hsep k hkj
      rw [← hk] at h3
      have : ‖wk j + z / α - c₀‖ ≤ d + ‖z / α‖ := by
        calc ‖wk j + z / α - c₀‖ = ‖(wk j - c₀) + z / α‖ := by ring_nf
          _ ≤ ‖wk j - c₀‖ + ‖z / α‖ := norm_add_le _ _
      linarith
  have hw : ‖α * ((ε : ℂ) * Complex.I)‖ < ‖α‖ * (r - d) := by
    rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg hε.le,
      mul_one]
    exact mul_lt_mul_of_pos_left (by rw [hε_def]; linarith) hαn
  have hw0 : α * ((ε : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero hα (mul_ne_zero (by exact_mod_cast hε.ne') Complex.I_ne_zero)
  obtain ⟨q, hq, hrot⟩ := RiemannRochTop_rotGen_affine_circle hE hG f hf hgal _ hB hfree
    (α * wk j + β) (‖α‖ * (r - d)) havoid (α * ((ε : ℂ) * Complex.I)) hw hw0
    (α'.trans K) c' hd' L hcL Γ l hΓ hend
  exact ⟨q, by rw [hq, hmark], hrot⟩

/-- Linear coefficient of the normalization of the target sphere in the certificate coordinate.
Source: `b65b_inverseNormalization`, `b65s_normalize`. -/
def b65w_scale (A B : ℂ) : ℂ :=
  B * A * (((b65b_boxCentre 6).1 : ℂ) - ((b65b_boxCentre 0).1 : ℂ)) /
    ((B - A) * ((b65b_boxCentre 0).1 : ℂ) * ((b65b_boxCentre 6).1 : ℂ))

/-- Constant coefficient of the normalization of the target sphere in the certificate
coordinate. Source: `b65b_inverseNormalization`, `b65s_normalize`. -/
def b65w_shift (A B : ℂ) : ℂ :=
  B / (B - A) * (1 - A / ((b65b_boxCentre 0).1 : ℂ))

theorem b65w_boxCentre_ne :
    ((b65b_boxCentre 0).1 : ℂ) ≠ 0 ∧ ((b65b_boxCentre 6).1 : ℂ) ≠ 0 ∧
      ((b65b_boxCentre 6).1 : ℂ) - ((b65b_boxCentre 0).1 : ℂ) ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [b65b_boxCentre]

/-- In the certificate coordinate the normalization sending `A ↦ 0`, `B ↦ 1`, `0 ↦ ∞` is
affine. -/
theorem b65w_affine_identity (A B w : ℂ) (hAB : B - A ≠ 0)
    (hw : b65b_inverseNormalization w ≠ 0) :
    b65s_normalize A B (b65b_inverseNormalization w) = b65w_scale A B * w + b65w_shift A B := by
  obtain ⟨ha, hb, hba⟩ := b65w_boxCentre_ne
  simp only [b65b_inverseNormalization] at hw ⊢
  have hD : ((b65b_boxCentre 6).1 : ℂ) - w * (((b65b_boxCentre 6).1 : ℂ) -
      ((b65b_boxCentre 0).1 : ℂ)) ≠ 0 := by
    intro h
    apply hw
    rw [h, div_zero]
  unfold b65s_normalize b65w_scale b65w_shift
  field_simp
  ring

/-- The certificate inverse normalization undoes the certificate normalization. -/
theorem b65w_inverse_normalize (z : ℂ) (hz : z ≠ 0) :
    b65b_inverseNormalization
      (b65s_normalize ((b65b_boxCentre 0).1 : ℂ) ((b65b_boxCentre 6).1 : ℂ) z) = z := by
  obtain ⟨ha, hb, hba⟩ := b65w_boxCentre_ne
  simp only [b65b_inverseNormalization, b65s_normalize]
  field_simp
  ring_nf
  exact mul_inv_cancel₀ ha

theorem b65w_scale_ne (A B : ℂ) (hA : A ≠ 0) (hB : B ≠ 0) (hAB : B - A ≠ 0) :
    b65w_scale A B ≠ 0 := by
  obtain ⟨ha, hb, hba⟩ := b65w_boxCentre_ne
  unfold b65w_scale
  exact div_ne_zero (mul_ne_zero (mul_ne_zero hB hA) hba)
    (mul_ne_zero (mul_ne_zero hAB ha) hb)

/-- The twelve labelled roots are nonzero and the two normalizing roots are distinct. -/
theorem b65w_roots_ne (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0) :
    (∀ k, p k ≠ 0) ∧ p 11 - p 10 ≠ 0 := by
  have hinj := (b65p_base_system p hp).1
  refine ⟨fun k h ↦ ?_, fun h ↦ ?_⟩
  · have h1 : b65p_poles p 0 (Sum.inr k) = b65p_poles p 0 (Sum.inl 0) := by
      simp [b65p_poles, b65p_fixedPole, h]
    exact Sum.inr_ne_inl (hinj h1)
  · have h1 : b65p_poles p 0 (Sum.inr 11) = b65p_poles p 0 (Sum.inr 10) := by
      simp [b65p_poles]
      linear_combination h
    exact absurd (Sum.inr.inj (hinj h1)) (by decide)

/-- The finite marks of the normalized centre are the normalized roots. -/
theorem b65w_branch_mark (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0) (k : Fin 12) :
    b6_branch (b65z_centre p) k.castSucc =
      ((b65s_normalize (p 10) (p 11) (p k) : ℂ) : OnePoint ℂ) := by
  obtain ⟨M, hM, hlab⟩ := ((b65p_normalized_path p hp).1.self_of_nhds).2
  have hmov : b65p_moving p 0 = p := by
    funext j
    simp [b65p_moving, b65p_poles]
  have hsrc : b65p_source p 0 k.castSucc = ((p k : ℂ) : OnePoint ℂ) := by
    rw [b65p_source, hmov]
    fin_cases k <;> simp [Fin.append, Fin.addCases]
  have h := hlab k.castSucc
  rw [hM, hmov, hsrc] at h
  change b6_branch (b65p_curve p 0) k.castSucc = _
  rw [← h]
  simp [b65p_mobius, (b65w_roots_ne p hp).1 k]

/-- Each normalized root lies in its certified lasso disc. -/
theorem b65w_mark_enclosure (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0) (k : Fin 12) :
    ‖b65s_normalize ((b65b_boxCentre 0).1 : ℂ) ((b65b_boxCentre 6).1 : ℂ) (p k) -
      b65b_track 0 k‖ < ((b65b_radius k : ℚ) : ℝ) := by
  have key : ∀ m, ‖b65s_normalize ((b65b_boxCentre 0).1 : ℂ) ((b65b_boxCentre 6).1 : ℂ)
      (p (b65b_boxIndex m)) - b65b_track 0 (b65b_boxIndex m)‖ <
        ((b65b_radius (b65b_boxIndex m) : ℚ) : ℝ) := by
    intro m
    have h := (b65b_normalization_enclosure m (p (b65b_boxIndex m))
      ((b65b_boxCentre 0).1 : ℝ) ((b65b_boxCentre 6).1 : ℝ) (hp m).1.le (hp m).2.1.le
      (by simp) (by simp)).2.2.2
    rwa [Complex.ofReal_ratCast, Complex.ofReal_ratCast] at h
  have hs : Function.Surjective b65b_boxIndex := by decide
  obtain ⟨m, rfl⟩ := hs k
  exact key m

/-- The certified lasso discs are pairwise separated. -/
theorem b65w_track_sep (j k : Fin 12) (h : j ≠ k) :
    ((b65b_radius j : ℚ) : ℝ) + ((b65b_radius k : ℚ) : ℝ) <
      ‖b65b_track 0 j - b65b_track 0 k‖ := by
  apply b65w_lt_norm
  simp only [b65b_track, Complex.ofReal_zero, sub_zero, one_mul, zero_mul, add_zero,
    Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im]
  fin_cases j <;> fin_cases k <;> first
    | exact absurd rfl h
    | norm_num [b65b_vertex0, b65b_radius]

/-- The certified lasso discs lie well inside the outer circle. -/
theorem b65w_track_bound (k : Fin 12) :
    ‖b65b_track 0 k - mr_centre‖ + ((b65b_radius k : ℚ) : ℝ) < 9 := by
  have h1 : ‖b65b_track 0 k - mr_centre‖ < 8 := by
    apply b65w_norm_lt _ _ (by norm_num)
    simp only [b65b_track, mr_centre, Complex.ofReal_zero, sub_zero, one_mul, zero_mul,
      add_zero, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re,
      Complex.I_im, Complex.div_re, Complex.div_im, Complex.neg_re, Complex.neg_im]
    fin_cases k <;> norm_num [b65b_vertex0]
  have h2 : ((b65b_radius k : ℚ) : ℝ) ≤ 1 / 4 := by
    have h3 : ((b65b_radius k : ℚ) : ℝ) ≤ ((1 / 4 : ℚ) : ℝ) :=
      Rat.cast_le.mpr (b65b_rational_enclosures.1 k).2
    rwa [show ((1 / 4 : ℚ) : ℝ) = 1 / 4 by norm_num] at h3
  linarith

/-- **The slot lassos are positive peripheral loops.** Carried to the punctured sphere at the
normalized centre, the `i`-th slot lasso is detected as positive at the mark `(b65x_slot i).rev`:
the outer loop at `∞` for slot `0`, and the lasso about the normalized root `12 - b65x_slot i`
otherwise.
Source: `b65w_outer_rotGen`, `b65w_lasso_rotGen`; `b65b_normalization_enclosure`,
`b65b_rational_enclosures`, `b65b_path_geometry` (certificate data). -/
theorem b65w_slot_rotGen (p : Fin 12 → ℂ)
    (hp : ∀ k : Fin 12,
      |(p (b65b_boxIndex k)).re - ((b65b_boxCentre k).1 : ℝ)| < (1/10000 : ℝ) ∧
      |(p (b65b_boxIndex k)).im - ((b65b_boxCentre k).2 : ℝ)| < (1/10000 : ℝ) ∧
      b65r_P (b65b_boxFibre k) (p (b65b_boxIndex k)) = 0)
    (e : b65s_sphere ≃ₜ b6t_punctured (b65z_centre p))
    (he : ∀ z, (e z : OnePoint ℂ) = b65p_mobius (p 10) (p 11) z)
    (x : b65s_regular) (δ : Fin 13 → Path x x)
    (hδ : ∀ i s, (δ i s).val = b65b_inverseNormalization (b65b_lasso (b65x_slot i) s))
    (i : Fin 13)
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    {G : Type} [Group G] [Finite G] [MulAction G C] [FaithfulSMul G C]
    (hG : ∀ k : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ k • x))
    (f : C → OnePoint ℂ) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hgal : b4_IsGaloisCover G f)
    (hfree : ∀ x, f x ∉ Set.range (b6_branch (b65z_centre p)) →
      MulAction.stabilizer G x = ⊥)
    (Γ : C(unitInterval, C)) (l : G)
    (hΓ : ∀ t, f (Γ t) =
      ((e (b65s_inclusion (δ i t)) : b6t_punctured (b65z_centre p)) : OnePoint ℂ))
    (hend : Γ 1 = l • Γ 0) :
    ∃ q, f q = b6_branch (b65z_centre p) (b65x_slot i).rev ∧ b4_IsRotGen ℂ q l := by
  obtain ⟨hne, hAB⟩ := b65w_roots_ne p hp
  let α := b65w_scale (p 10) (p 11)
  let β := b65w_shift (p 10) (p 11)
  have hα : α ≠ 0 := b65w_scale_ne _ _ (hne 10) (hne 11) hAB
  let wk : Fin 12 → ℂ := fun k ↦
    b65s_normalize ((b65b_boxCentre 0).1 : ℂ) ((b65b_boxCentre 6).1 : ℂ) (p k)
  have hmark : ∀ k, b6_branch (b65z_centre p) k.castSucc =
      ((α * wk k + β : ℂ) : OnePoint ℂ) := by
    intro k
    rw [b65w_branch_mark p hp k]
    congr 1
    have hw : b65b_inverseNormalization (wk k) ≠ 0 := by
      simp only [wk]
      rw [b65w_inverse_normalize _ (hne k)]
      exact hne k
    rw [← b65w_affine_identity _ _ _ hAB hw]
    simp only [wk]
    rw [b65w_inverse_normalize _ (hne k)]
  have hval : ∀ s : unitInterval,
      ((e (b65s_inclusion (δ i s)) : b6t_punctured (b65z_centre p)) : OnePoint ℂ) =
        ((α * b65b_lasso (b65x_slot i) s + β : ℂ) : OnePoint ℂ) := by
    intro s
    rw [he]
    have h0 : (δ i s).val ≠ 0 := (δ i s).property.1
    have hm : b65p_mobius (p 10) (p 11) (((δ i s).val : ℂ) : OnePoint ℂ) =
        ((b65s_normalize (p 10) (p 11) (δ i s).val : ℂ) : OnePoint ℂ) := by
      simp [b65p_mobius, h0]
    change b65p_mobius (p 10) (p 11) (((δ i s).val : ℂ) : OnePoint ℂ) = _
    rw [hm, hδ i s, b65w_affine_identity _ _ _ hAB (by rw [← hδ i s]; exact h0)]
  let L : Path (e (b65s_inclusion x)) (e (b65s_inclusion x)) :=
    ((δ i).map b65s_inclusion.continuous).map e.continuous
  have hLv : ∀ s, (L s : OnePoint ℂ) =
      ((α * b65b_lasso (b65x_slot i) s + β : ℂ) : OnePoint ℂ) := fun s ↦ hval s
  have hΓ' : ∀ t, f (Γ t) = (L t : OnePoint ℂ) := hΓ
  by_cases hk : (b65x_slot i).val = 0
  · have hrev : (b65x_slot i).rev = Fin.last 12 := by
      ext
      simp only [Fin.val_rev, Fin.val_last]
      omega
    rw [hrev]
    refine b65w_outer_rotGen _ α β hα wk hmark ?_ L ?_ hG f hf hgal hfree Γ l hΓ' hend
    · intro k
      have h1 := b65w_mark_enclosure p hp k
      have h2 := b65w_track_bound k
      have h3 : ‖wk k - mr_centre‖ ≤ ‖wk k - b65b_track 0 k‖ + ‖b65b_track 0 k - mr_centre‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      linarith
    · intro s
      rw [hLv, b65b_lasso, dite_eq_left hk]
  · let j : Fin 12 := ⟨13 - (b65x_slot i).val - 1, by omega⟩
    have hrev : (b65x_slot i).rev = j.castSucc := by
      ext
      simp only [Fin.val_rev, Fin.val_castSucc, j]
      omega
    rw [hrev]
    have hlasso : ∀ s : ℝ, b65b_lasso (b65x_slot i) s =
        if s ≤ 1/3 then mr_basePoint + (3 * s : ℂ) *
          (b65b_track 0 j + Complex.I * ((b65b_radius j : ℚ) : ℂ) - mr_basePoint)
        else if s ≤ 2/3 then b65b_track 0 j + Complex.I * ((b65b_radius j : ℚ) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * (3 * s - 1 : ℂ))
        else mr_basePoint + (3 - 3 * s : ℂ) *
          (b65b_track 0 j + Complex.I * ((b65b_radius j : ℚ) : ℂ) - mr_basePoint) := by
      intro s
      rw [b65b_lasso, dite_eq_right hk]
    have hin := b65w_mark_enclosure p hp j
    have hsep : ∀ k', k' ≠ j → ((b65b_radius j : ℚ) : ℝ) < ‖wk k' - b65b_track 0 j‖ := by
      intro k' hk'
      have h1 := b65w_mark_enclosure p hp k'
      have h2 := b65w_track_sep k' j hk'
      have h3 : ‖b65b_track 0 k' - b65b_track 0 j‖ ≤
          ‖wk k' - b65b_track 0 k'‖ + ‖wk k' - b65b_track 0 j‖ := by
        calc ‖b65b_track 0 k' - b65b_track 0 j‖ =
            ‖(wk k' - b65b_track 0 j) - (wk k' - b65b_track 0 k')‖ := by ring_nf
          _ ≤ ‖wk k' - b65b_track 0 j‖ + ‖wk k' - b65b_track 0 k'‖ := norm_sub_le _ _
          _ = _ := add_comm _ _
      linarith
    have hexp : ∀ s : ℝ, 2 * (Real.pi : ℂ) * Complex.I * (3 * s - 1 : ℂ) =
        ((((3 * s - 1) * (2 * Real.pi)) : ℝ) : ℂ) * Complex.I := by
      intro s; push_cast; ring
    refine b65w_lasso_rotGen _ α β hα wk hmark j (b65b_track 0 j) mr_basePoint
      ((b65b_radius j : ℚ) : ℝ) hin hsep L ?_ ?_ ?_ hG f hf hgal hfree Γ l hΓ' hend
    · intro s hs
      rw [hLv, hlasso, ite_eq_left hs]
      congr 1
      push_cast
      ring
    · intro s hs1 hs2
      rw [hLv, hlasso]
      rcases eq_or_lt_of_le hs1 with h | h
      · rw [ite_eq_left (le_of_eq h.symm), ← h]
        have : ((((3 * (1 / 3 : ℝ) - 1) * (2 * Real.pi)) : ℝ) : ℂ) * Complex.I = 0 := by
          push_cast; ring
        rw [this, Complex.exp_zero]
        congr 1
        push_cast
        ring
      · rw [ite_eq_right (not_le.mpr h), ite_eq_left hs2, hexp]
        congr 1
    · intro s hs
      rw [hLv, hlasso]
      rcases eq_or_lt_of_le hs with h | h
      · rw [ite_eq_right (by rw [← h]; norm_num), ite_eq_left (le_of_eq h.symm), ← h, hexp]
        have : ((((3 * (2 / 3 : ℝ) - 1) * (2 * Real.pi)) : ℝ) : ℂ) * Complex.I =
            2 * Real.pi * Complex.I := by
          push_cast; ring
        rw [this, Complex.exp_two_pi_mul_I]
        congr 1
        push_cast
        ring
      · rw [ite_eq_right (by linarith), ite_eq_right (not_le.mpr h)]
        congr 1
        push_cast
        ring

end HodgeLean.Foundations.Program
