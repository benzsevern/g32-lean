import HodgeLean.Adapters.AbelianHomPullback
import HodgeLean.Foundations.Program.TorusAlgebraizationB56Assembly

/-! # The theta map is the exponential of its derivative

A continuous homomorphism `ℂᵉ → W(ℂ)` into the complex points of a commutative group object is
determined by its derivative `D` at `0` in the identity chart: it is `exp ∘ D`. The argument is
that of S12 for the analytic representation of a homomorphism (`spec_abelianHom_analyticRepresentation`):
near `0` the homomorphism is `exp ∘ h` for a locally additive `h` with derivative `D`, so
`h = D` near `0`, and subdivision extends the identity to all of `ℂᵉ`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Topology Filter
open scoped TensorProduct Manifold ContDiff CategoryTheory.MonObj
open HodgeLean.Foundations HodgeLean.Adapters

namespace HodgeLean.Foundations.Program

/-- Every vector is a multiple of an arbitrarily small vector. -/
theorem b56_exists_nsmul_eq_small {e : ℕ} (v : Fin e → ℂ) {t : ℝ} (ht : 0 < t) :
    ∃ (n : ℕ) (w : Fin e → ℂ), 0 < n ∧ ‖w‖ < t ∧ (n : ℝ) * ‖w‖ = ‖v‖ ∧ n • w = v := by
  obtain ⟨n, hn⟩ := exists_nat_gt (‖v‖ / t)
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (div_nonneg (norm_nonneg _) ht.le) hn
  refine ⟨n, (n : ℝ)⁻¹ • v, by exact_mod_cast hn0, ?_, ?_, ?_⟩
  · rw [norm_smul, norm_inv, Real.norm_natCast, inv_mul_eq_div, div_lt_iff₀ hn0]
    rwa [div_lt_iff₀ ht, mul_comm] at hn
  · rw [norm_smul, norm_inv, Real.norm_natCast, ← mul_assoc, mul_inv_cancel₀ hn0.ne', one_mul]
  · rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hn0.ne', one_smul]

/-- Near `0`, a map continuous at `0` with value `1` lands in the identity chart. -/
theorem b56_eventually_mem_identityChart_source {W : Over (Spec ↧ℂ)} {d e : ℕ}
    [GrpObj W] [SmoothOfRelativeDimension d W.hom] {k : (Fin e → ℂ) → ComplexPoint W}
    (hk : ContinuousAt k 0) (hk0 : k 0 = 1) :
    ∀ᶠ v in 𝓝 0, k v ∈ (identityChart W d).source := by
  apply hk.tendsto.eventually
  rw [hk0]
  exact (identityChart W d).open_source.mem_nhds (mem_localChart_source W d 1)

/-- A continuous homomorphism `ℂ^e → W(ℂ)` whose expression in the identity chart of `W` has real
derivative `D` at `0` is `exp_W ∘ D`. -/
theorem b56_eq_complexExponential_of_hasFDerivAt {W : Over (Spec ↧ℂ)} {d e : ℕ}
    [GrpObj W] [IsCommMonObj W] [SmoothOfRelativeDimension d W.hom]
    (g : (Fin e → ℂ) →+ Additive (ComplexPoint W)) (hg : ContinuousAt g 0)
    (D : (Fin e → ℂ) →L[ℝ] (Fin d → ℂ))
    (hD : HasFDerivAt (fun v ↦ identityChart W d (g v).toMul) D 0) (v : Fin e → ℂ) :
    g v = complexExponential W d (D v) := by
  set E : (Fin d → ℂ) → (Fin d → ℂ) :=
    fun v ↦ identityChart W d (complexExponential W d v).toMul with hEdef
  set F : (Fin e → ℂ) → (Fin d → ℂ) := fun v ↦ identityChart W d (g v).toMul with hFdef
  have hE0 : E 0 = 0 := by
    simp only [hEdef, complexExponential_zero, toMul_zero, identityChart_one]
  have hF0 : F 0 = 0 := by
    simp only [hFdef, map_zero, toMul_zero, identityChart_one]
  have hEd : HasFDerivAt E
      ((ContinuousLinearEquiv.refl ℝ (Fin d → ℂ)) : (Fin d → ℂ) →L[ℝ] (Fin d → ℂ)) 0 :=
    hasFDerivAt_complexExponential_chart W d
  have hs : HasStrictFDerivAt E
      ((ContinuousLinearEquiv.refl ℝ (Fin d → ℂ)) : (Fin d → ℂ) →L[ℝ] (Fin d → ℂ)) 0 :=
    (contDiffAt_complexExponential_chart W d).hasStrictFDerivAt' hEd one_ne_zero
  set L := hs.localInverse E _ 0 with hLdef
  have hL : HasStrictFDerivAt L
      ((ContinuousLinearEquiv.refl ℝ (Fin d → ℂ)).symm : (Fin d → ℂ) →L[ℝ] (Fin d → ℂ)) (E 0) :=
    hs.to_localInverse
  have hLE : ∀ᶠ x in 𝓝 0, L (E x) = x := hs.eventually_left_inverse
  have hEL : ∀ᶠ y in 𝓝 (E 0), E (L y) = y := hs.eventually_right_inverse
  have hL0 : L 0 = 0 := by
    have := hLE.self_of_nhds
    rwa [hE0] at this
  set h : (Fin e → ℂ) → (Fin d → ℂ) := fun v ↦ L (F v) with hhdef
  have hh0 : h 0 = 0 := by simp only [hhdef, hF0, hL0]
  have hhd : HasFDerivAt h D 0 := by
    have hL' : HasFDerivAt L
        ((ContinuousLinearEquiv.refl ℝ (Fin d → ℂ)).symm : (Fin d → ℂ) →L[ℝ] (Fin d → ℂ))
        (F 0) := by
      rw [hF0, ← hE0]
      exact hL.hasFDerivAt
    have := hL'.comp 0 hD
    simpa using this
  -- `exp ∘ h = g` near `0`
  have hgv : ∀ᶠ v in 𝓝 0, complexExponential W d (h v) = g v := by
    have hexp : ContinuousAt (fun v ↦ (complexExponential W d (h v)).toMul) 0 :=
      (continuous_toMul.comp (continuous_complexExponential W d)).continuousAt.comp
        hhd.continuousAt
    have h1 := b56_eventually_mem_identityChart_source (d := d) hexp
      (by simp only [hh0, complexExponential_zero, toMul_zero])
    have h2 := b56_eventually_mem_identityChart_source (d := d)
      (k := fun v ↦ (g v).toMul) (continuous_toMul.continuousAt.comp hg) (by simp)
    have h3 : ∀ᶠ v in 𝓝 0, E (L (F v)) = F v := by
      refine hD.continuousAt.tendsto.eventually (p := fun y ↦ E (L y) = y) ?_
      rw [hF0, ← hE0]
      exact hEL
    filter_upwards [h1, h2, h3] with v h1 h2 h3
    exact Additive.toMul.injective ((identityChart W d).injOn h1 h2 h3)
  -- local injectivity of `exp`
  obtain ⟨r, hr, hrN⟩ := Metric.eventually_nhds_iff_ball.mp hLE
  have hexpinj : ∀ x ∈ Metric.ball (0 : Fin d → ℂ) r, ∀ y ∈ Metric.ball (0 : Fin d → ℂ) r,
      complexExponential W d x = complexExponential W d y → x = y := by
    intro x hx y hy hxy
    rw [← hrN x hx, ← hrN y hy]
    simp only [hEdef, hxy]
  have hsmall : ∀ᶠ v in 𝓝 0, h v ∈ Metric.ball (0 : Fin d → ℂ) (r / 2) := by
    refine hhd.continuousAt.tendsto.eventually (p := fun y ↦ y ∈ Metric.ball 0 (r / 2)) ?_
    rw [hh0]
    exact Metric.ball_mem_nhds _ (half_pos hr)
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff_ball.mp (hgv.and hsmall)
  have hδ : 0 < ε / 2 := half_pos hε
  -- local additivity of `h`
  have hadd : ∀ u : Fin e → ℂ, ‖u‖ < ε / 2 → ∀ w : Fin e → ℂ, ‖w‖ < ε / 2 →
      h (u + w) = h u + h w := by
    intro u hu w hw
    have huw : u + w ∈ Metric.ball (0 : Fin e → ℂ) ε := by
      rw [mem_ball_zero_iff]
      calc ‖u + w‖ ≤ ‖u‖ + ‖w‖ := norm_add_le _ _
        _ < ε / 2 + ε / 2 := add_lt_add hu hw
        _ = ε := add_halves ε
    have hu' : u ∈ Metric.ball (0 : Fin e → ℂ) ε := by
      rw [mem_ball_zero_iff]; linarith
    have hw' : w ∈ Metric.ball (0 : Fin e → ℂ) ε := by
      rw [mem_ball_zero_iff]; linarith
    have h1 := (hεP _ huw).2
    have h2 := (hεP _ hu').2
    have h3 := (hεP _ hw').2
    rw [mem_ball_zero_iff] at h1 h2 h3
    apply hexpinj
    · rw [mem_ball_zero_iff]; linarith
    · rw [mem_ball_zero_iff]
      calc ‖h u + h w‖ ≤ ‖h u‖ + ‖h w‖ := norm_add_le _ _
        _ < r / 2 + r / 2 := add_lt_add h2 h3
        _ = r := add_halves r
    · have hm : complexExponential W d (h u + h w) =
          complexExponential W d (h u) + complexExponential W d (h w) :=
        (complexExponentialHom W d).map_add _ _
      rw [(hεP _ huw).1, hm, (hεP _ hu').1, (hεP _ hw').1, map_add]
  have hmul : ∀ u : Fin e → ℂ, ‖u‖ < ε / 2 → ∀ k : ℕ, (k : ℝ) * ‖u‖ < ε / 2 →
      h (k • u) = k • h u := by
    intro u hu k
    induction k with
    | zero => intro _; simp [hh0]
    | succ k ih =>
      intro hk
      have hk' : (k : ℝ) * ‖u‖ < ε / 2 := by
        refine lt_of_le_of_lt ?_ hk
        gcongr
        simp
      rw [succ_nsmul, succ_nsmul, hadd _ (by rw [RCLike.norm_nsmul ℝ, nsmul_eq_mul]; exact hk') u hu,
        ih hk']
  -- `h` agrees with `D` near `0`
  have hlo : (fun u ↦ h u - D u) =o[𝓝 0] fun u ↦ u := by
    have := hasFDerivAt_iff_isLittleO_nhds_zero.mp hhd
    simpa [hh0] using this
  have hlin : ∀ u : Fin e → ℂ, ‖u‖ < ε / 2 → h u = D u := by
    intro u hu
    have key : ∀ c : ℝ, 0 < c → ‖h u - D u‖ ≤ c * ‖u‖ := by
      intro c hc
      obtain ⟨ρ, hρ, hρP⟩ := Metric.eventually_nhds_iff_ball.mp (hlo.def hc)
      obtain ⟨n, w, hn, hw, hnw, hwu⟩ := b56_exists_nsmul_eq_small u (lt_min hρ hδ)
      have hwρ : w ∈ Metric.ball (0 : Fin e → ℂ) ρ :=
        mem_ball_zero_iff.mpr (lt_of_lt_of_le hw (min_le_left _ _))
      have hwδ : ‖w‖ < ε / 2 := lt_of_lt_of_le hw (min_le_right _ _)
      have he : h u - D u = n • (h w - D w) := by
        rw [← hwu, hmul w hwδ n (by rw [hnw]; exact hu), map_nsmul, nsmul_sub]
      rw [he, RCLike.norm_nsmul ℝ, nsmul_eq_mul, ← hnw]
      have := hρP _ hwρ
      calc (n : ℝ) * ‖h w - D w‖ ≤ n * (c * ‖w‖) := by gcongr
        _ = c * (n * ‖w‖) := by ring
    rw [← sub_eq_zero, ← norm_le_zero_iff]
    by_contra hne
    replace hne := not_le.mp hne
    have h1 := key (‖h u - D u‖ / (‖u‖ + 1)) (div_pos hne (by positivity))
    have h2 : ‖h u - D u‖ / (‖u‖ + 1) * ‖u‖ < ‖h u - D u‖ := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg u]
    linarith
  -- globalize by subdivision
  obtain ⟨n, w, hn, hw, hnw, hwv⟩ := b56_exists_nsmul_eq_small v hδ
  have hwε : w ∈ Metric.ball (0 : Fin e → ℂ) ε := by
    rw [mem_ball_zero_iff]; linarith
  have hexp : complexExponential W d (D w) = g w := by
    rw [← hlin w hw]
    exact (hεP _ hwε).1
  rw [← hwv, map_nsmul, map_nsmul, ← hexp]
  exact ((complexExponentialHom W d).map_nsmul _ _).symm


variable {Λ : Type} [AddCommGroup Λ] [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
  {F : Submodule ℂ (ℂ ⊗[ℤ] Λ)} {hF : b2_IsWeightOne Λ F} {Q : LinearMap.BilinForm ℤ Λ}
  (hirr : ∀ z, (HomogeneousIdeal.irrelevant (b5_grade Λ F hF Q)).toIdeal.map
      (b5_evalGlobal Λ F hF Q z) = ⊤)
  (P : b5_V Λ F → ComplexPoint (b5_model Λ F hF Q))
  (hP : ∀ z, (P z).left =
    Proj.fromOfGlobalSections (b5_grade Λ F hF Q) (b5_evalGlobal Λ F hF Q z) (hirr z))
  (hbpf : ∀ z, ∃ t ∈ b5_grade Λ F hF Q 1, b5_eval Λ F hF Q z t ≠ 0)
  (θ : b2_torus Λ F → ComplexPoint (b5_model Λ F hF Q))
  (hθP : ∀ z, θ (b2_torusCover Λ F z) = P z)
include hP hbpf hθP

/-- For a group structure making `θ` a homomorphism, the theta map on the cover is the
exponential of its derivative at `0` in the identity chart.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, §1.1 and §1.2; S12
`spec_abelianHom_analyticRepresentation`. -/
theorem b56_thetaCover_eq_exp [GrpObj (b5_model Λ F hF Q)] [IsCommMonObj (b5_model Λ F hF Q)]
    (d : ℕ) [SmoothOfRelativeDimension d (b5_model Λ F hF Q).hom]
    (hθ0 : θ 0 = 1) (hθadd : ∀ t u, θ (t + u) = θ t * θ u) (v : b5_V Λ F) :
    P v = (complexExponential (b5_model Λ F hF Q) d
      (fderiv ℂ (fun z ↦ identityChart (b5_model Λ F hF Q) d (P z)) 0 v)).toMul := by
  have hP0 : P 0 = 1 := by
    rw [← hθP, ← hθ0]
    congr 1
    simp [b2_torusCover, b2_coordHomeomorph]
  let g : b5_V Λ F →+ Additive (ComplexPoint (b5_model Λ F hF Q)) :=
    { toFun := fun v ↦ Additive.ofMul (P v)
      map_zero' := by rw [hP0]; rfl
      map_add' := fun v w ↦ by
        rw [← hθP, ← hθP, ← hθP, b55_torusCover_add, hθadd]
        rfl }
  have hcont := b56_continuous hirr P hP hbpf
  have hg : ContinuousAt g 0 := (continuous_ofMul.comp hcont).continuousAt
  let G : b5_V Λ F → (Fin d → ℂ) := fun v ↦ identityChart (b5_model Λ F hF Q) d (g v).toMul
  have hG : AnalyticAt ℂ G 0 := by
    have hsrc : P 0 ∈ (localChart (b5_model Λ F hF Q) d 1).source := by
      rw [hP0]
      exact mem_localChart_source _ d 1
    exact (b56_theta_analyticAt_chart hirr P hP hbpf d 1 0 hsrc).sub analyticAt_const
  have hD : HasFDerivAt G ((fderiv ℂ G 0).restrictScalars ℝ) 0 :=
    hG.differentiableAt.hasFDerivAt.restrictScalars ℝ
  have h := b56_eq_complexExponential_of_hasFDerivAt g hg _ hD v
  rw [ContinuousLinearMap.coe_restrictScalars'] at h
  exact congrArg Additive.toMul h

omit hP hbpf in
/-- The theta map on the cover is an open map. -/
theorem b56_isOpenMap [DiscreteTopology (b2_latticeMap Λ F).range] (hθ : IsHomeomorph θ) :
    IsOpenMap P := by
  have h : P = θ ∘ b2_torusCover Λ F := funext fun z ↦ (hθP z).symm
  rw [h]
  exact hθ.isOpenMap.comp (b2t_torusCover_isCoveringMap (Λ := Λ) (F := F)).isOpenMap

omit hP hbpf in
/-- The theta map on the cover is invariant under lattice translations. -/
theorem b56_periodic (z : b5_V Λ F) (l : Λ) : P (z + b5_lattice Λ F l) = P z := by
  rw [← hθP, ← hθP, b56_torusCover_add_lattice]

/-- The derivative of the theta map at `0` in the identity chart is bijective.
Source: Birkenhake–Lange, Theorem 4.5.1; `b56_fderiv_injective`, `b56_dim_le`. -/
theorem b56_identityChart_fderiv_bijective [GrpObj (b5_model Λ F hF Q)]
    [DiscreteTopology (b2_latticeMap Λ F).range]
    (d : ℕ) [SmoothOfRelativeDimension d (b5_model Λ F hF Q).hom]
    (htan : ∀ z v, v ≠ 0 → ∃ s ∈ b5_grade Λ F hF Q 1, b5_eval Λ F hF Q z s = 0 ∧
      fderiv ℂ (fun w ↦ b5_eval Λ F hF Q w s) z v ≠ 0)
    (hθ : IsHomeomorph θ) (hP0 : P 0 = 1) :
    Function.Bijective (fderiv ℂ (fun z ↦ identityChart (b5_model Λ F hF Q) d (P z)) 0) := by
  have hPopen := b56_isOpenMap P θ hθP hθ
  have hinj := b56_fderiv_injective hirr P hP hbpf d htan 0
  have hdim := b56_dim_le hirr P hP hbpf d hPopen
  rw [hP0] at hinj
  have heq : fderiv ℂ (fun z ↦ identityChart (b5_model Λ F hF Q) d (P z)) 0 =
      fderiv ℂ (fun z ↦ localChart (b5_model Λ F hF Q) d 1 (P z)) 0 :=
    fderiv_sub_const _
  rw [heq]
  have hfin : Module.finrank ℂ (b5_V Λ F) = Module.finrank ℂ (Fin d → ℂ) := by
    refine le_antisymm (LinearMap.finrank_le_finrank_of_injective hinj) ?_
    simpa using hdim
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hinj⟩

/-- Lattice vectors are mapped into the period lattice by the derivative.
Source: Birkenhake–Lange, §1.1; `b56_thetaCover_eq_exp`. -/
theorem b56_exp_lattice [GrpObj (b5_model Λ F hF Q)] [IsCommMonObj (b5_model Λ F hF Q)]
    (d : ℕ) [SmoothOfRelativeDimension d (b5_model Λ F hF Q).hom]
    (hθ0 : θ 0 = 1) (hθadd : ∀ t u, θ (t + u) = θ t * θ u) (l : Λ) :
    complexExponential (b5_model Λ F hF Q) d
      (fderiv ℂ (fun z ↦ identityChart (b5_model Λ F hF Q) d (P z)) 0 (b5_lattice Λ F l)) = 0 := by
  have h := b56_thetaCover_eq_exp hirr P hP hbpf θ hθP d hθ0 hθadd (b5_lattice Λ F l)
  have hP0 : P 0 = 1 := by
    rw [← hθP, ← hθ0]
    congr 1
    simp [b2_torusCover, b2_coordHomeomorph]
  have hl : P (b5_lattice Λ F l) = 1 := by
    rw [← zero_add (b5_lattice Λ F l), b56_periodic P θ hθP, hP0]
  rw [hl] at h
  apply Additive.toMul.injective
  rw [← h]
  rfl

/-- Every period is the derivative of a lattice vector.
Source: Birkenhake–Lange, §1.1; `b56_thetaCover_eq_exp` and injectivity of `θ`. -/
theorem b56_period_surjective [GrpObj (b5_model Λ F hF Q)] [IsCommMonObj (b5_model Λ F hF Q)]
    (d : ℕ) [SmoothOfRelativeDimension d (b5_model Λ F hF Q).hom]
    (hθ : Function.Injective θ) (hθ0 : θ 0 = 1) (hθadd : ∀ t u, θ (t + u) = θ t * θ u)
    (hD : Function.Surjective
      (fderiv ℂ (fun z ↦ identityChart (b5_model Λ F hF Q) d (P z)) 0))
    (w : Fin d → ℂ) (hw : complexExponential (b5_model Λ F hF Q) d w = 0) :
    ∃ l : Λ, fderiv ℂ (fun z ↦ identityChart (b5_model Λ F hF Q) d (P z)) 0
      (b5_lattice Λ F l) = w := by
  obtain ⟨v, rfl⟩ := hD w
  have h := b56_thetaCover_eq_exp hirr P hP hbpf θ hθP d hθ0 hθadd v
  rw [hw] at h
  have h0 : b2_torusCover Λ F 0 = 0 := by simp [b2_torusCover, b2_coordHomeomorph]
  have hcov : b2_torusCover Λ F v = 0 := by
    apply hθ
    rw [hθP, hθ0, h]
    rfl
  obtain ⟨l, hl⟩ := (QuotientAddGroup.eq_zero_iff _).mp hcov
  refine ⟨l, ?_⟩
  congr 1
  change b2_coord _ (b2_latticeMap Λ F l) = v
  rw [hl]
  exact (b2_coordHomeomorph Λ F).apply_symm_apply v

omit hP hbpf hθP in
/-- If a surjection `φ : Λ → L` onto a lattice of `ℂᵈ` is `D` on lattice vectors, for an injective
linear `D`, then the complexification of `φ` carries `F` onto the kernel of the evaluation
`ℂ ⊗ L → ℂᵈ`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, §1.1 (`V = (ℂ ⊗ Λ) ⧸ F`). -/
theorem b56_filtration_eq {d : ℕ} (L : Submodule ℤ (Fin d → ℂ)) (φ : Λ →+ L)
    (hφ : Function.Surjective φ) (D : b5_V Λ F →ₗ[ℂ] (Fin d → ℂ)) (hD : Function.Injective D)
    (hφD : ∀ l, (φ l : Fin d → ℂ) = D (b5_lattice Λ F l)) :
    F.map (b2_cplxMap φ) = LinearMap.ker (LinearMap.liftBaseChange ℂ L.subtype) := by
  let e := b2_cplxMap φ
  let N : (ℂ ⊗[ℤ] Λ) →ₗ[ℂ] (Fin d → ℂ) :=
    D ∘ₗ (b2_coord ((ℂ ⊗[ℤ] Λ) ⧸ F)).toLinearMap ∘ₗ F.mkQ
  have hMN : LinearMap.liftBaseChange ℂ L.subtype ∘ₗ e = N := by
    refine LinearMap.ext fun x ↦ ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c l =>
      have hcl : c ⊗ₜ[ℤ] l = c • ((1 : ℂ) ⊗ₜ[ℤ] l) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have h1 : N ((1 : ℂ) ⊗ₜ[ℤ] l) = D (b5_lattice Λ F l) := rfl
      rw [hcl, map_smul, map_smul, h1, ← hφD]
      simp [e, b2_cplxMap]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hkerN : LinearMap.ker N = F := by
    have hinj : Function.Injective (D ∘ₗ (b2_coord ((ℂ ⊗[ℤ] Λ) ⧸ F)).toLinearMap) :=
      hD.comp (b2_coord _).injective
    change LinearMap.ker ((D ∘ₗ (b2_coord ((ℂ ⊗[ℤ] Λ) ⧸ F)).toLinearMap) ∘ₗ F.mkQ) = F
    rw [LinearMap.ker_comp, LinearMap.ker_eq_bot.mpr hinj, Submodule.comap_bot,
      Submodule.ker_mkQ]
  have he : Function.Surjective e := by
    rw [← LinearMap.range_eq_top, eq_top_iff]
    rintro y -
    induction y using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul c m =>
      obtain ⟨l, rfl⟩ := hφ m
      exact ⟨c ⊗ₜ[ℤ] l, rfl⟩
    | add x y hx hy => exact Submodule.add_mem _ hx hy
  have hF : F = (LinearMap.ker (LinearMap.liftBaseChange ℂ L.subtype)).comap e := by
    rw [← LinearMap.ker_comp, hMN, hkerN]
  rw [hF, Submodule.map_comap_eq_of_surjective he]

end HodgeLean.Foundations.Program
