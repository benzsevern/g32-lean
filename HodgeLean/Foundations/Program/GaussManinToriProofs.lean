import HodgeLean.Foundations.Program.GaussManinToriDefs
import HodgeLean.Foundations.Program.GaussManinToriHermitian
import HodgeLean.Foundations.Program.GaussManinToriPolarization
import HodgeLean.Foundations.Program.GaussManinToriChart
import HodgeLean.Foundations.Program.GaussManinToriKS

/-! # The weight-one VHS associated to a marked period presentation: proof obligations -/

noncomputable section

open CategoryTheory Manifold
open scoped TensorProduct ContDiff Matrix Topology

namespace HodgeLean.Foundations.Program

open HodgeBlocks HodgeLean.Foundations.AppellHumbert HodgeLean.Papers

section Lattice

variable {g : ℕ} {P : Fin g → Fin (2 * g) → ℂ}

theorem d2_isRiemannForm_iff_hermitian_aux (hP : d2_IsPeriodMatrix P)
    (A : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) :
    d2_IsRiemannForm P A ↔ ∃ H : HermitianForm (V := Fin g → ℂ), H.IsPositiveDefinite ∧
      ∀ s t, H.imaginary (d2_realMap P s) (d2_realMap P t) = d2_riemannReal A s t := by
  set b := d2l_basis hP
  have hL : ∀ s, d2_realMap P s = b.equivFun.symm s := d2l_realMap_eq hP
  constructor
  · intro hA
    let E : (Fin g → ℂ) → (Fin g → ℂ) → ℝ := fun v w ↦
      d2_riemannReal A (b.equivFun v) (b.equivFun w)
    have hrelv : ∀ v, d2_realMap P (b.equivFun (Complex.I • v)) =
        Complex.I • d2_realMap P (b.equivFun v) := fun v ↦ by
      rw [hL, hL, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    obtain ⟨H, hH⟩ := (spec_appellHumbert_riemann_relations E
      (fun x y z ↦ by simp only [E, map_add, d2l_riemannReal_add_left])
      (fun r x y ↦ by simp only [E, map_smul, d2l_riemannReal_smul_left])
      (fun x y z ↦ by simp only [E, map_add, d2l_riemannReal_add_right])
      (fun r x y ↦ by simp only [E, map_smul, d2l_riemannReal_smul_right])
      (fun x ↦ d2l_riemannReal_self hA.alternating _)).2
      (fun v w ↦ hA.typeOneOne _ _ _ _ (hrelv v) (hrelv w))
    refine ⟨H, fun v hv ↦ ?_, fun s t ↦ ?_⟩
    · rw [← d2l_imaginary_I_right, hH]
      refine hA.positive _ _ ?_ (hrelv v)
      intro h0
      exact hv (by simpa using congrArg b.equivFun.symm h0)
    · rw [hH, hL, hL]
      simp only [E, LinearEquiv.apply_symm_apply]
  · rintro ⟨H, hpos, hH⟩
    refine ⟨?_, fun s t s' t' hs ht ↦ ?_, fun s s' hs hrel ↦ ?_⟩
    · ext i j
      have h := hH (Pi.single j 1) (Pi.single i 1)
      rw [d2l_imaginary_swap, hH, d2l_riemannReal_single, d2l_riemannReal_single] at h
      rw [Matrix.transpose_apply, Matrix.neg_apply]
      exact_mod_cast h.symm
    · rw [← hH, ← hH, hs, ht, d2l_imaginary_I_I]
    · rw [← hH, hrel, d2l_imaginary_I_right]
      refine hpos _ fun h0 ↦ hs (d2l_realMap_injective hP ?_)
      rw [h0, map_zero]

end Lattice

section Hodge

variable {g : ℕ} {P : Fin g → Fin (2 * g) → ℂ}

theorem d2_filtration_isHodge_aux (hP : d2_IsPeriodMatrix P) :
    d1_IsHodgeFiltration 1 (d2_filtration P) :=
  d2v_filtration_isHodge hP

theorem d2_filtration_isPolarized_aux {A : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ}
    (hA : d2_IsRiemannForm P A) :
    d1_IsPolarizedFiltration 1 (d2_dualForm A) (d2_filtration P) :=
  d2v_filtration_isPolarized hA

end Hodge

section Family

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {B : Type*} [TopologicalSpace B] [ChartedSpace E B]
variable {g : ℕ}

theorem d2_filtration_holomorphic_aux [IsManifold 𝓘(ℂ, E) ω B] (X : d2_MarkedPeriodFamily E B g)
    (p : ℤ) :
    (d2_localSystem B g).IsHolomorphicSubbundle E (fun b ↦ d2_filtration (X.period b) p) :=
  d2v_filtration_holomorphic X p

theorem d2_filtration_transversal_aux [IsManifold 𝓘(ℂ, E) ω B] (X : d2_MarkedPeriodFamily E B g) :
    (d2_localSystem B g).IsTransversal E (fun p b ↦ d2_filtration (X.period b) p) := by
  intro U hU _ b₀ p s _ hsF b v
  by_cases hp : p ≤ 1
  · show _ ∈ d2_filtration (X.period b) (p - 1)
    rw [d2v_filtration_of_le_zero _ (by omega)]
    exact Submodule.mem_top
  · have hs0 : ∀ b' : U, s b' = 0 := fun b' ↦
      d2v_mem_filtration_le _ p _ (hsF b') (by omega)
    have hc : (d2_localSystem B g).flatCoord U hU b₀ s = fun _ ↦ 0 := by
      funext b'
      by_cases hb : b' ∈ U
      · simp only [d1_LocalSystem.flatCoord, hb, dite_true]
        rw [hs0 ⟨b', hb⟩, map_zero]
      · simp [d1_LocalSystem.flatCoord, hb]
    have hd : d1_flatDeriv E (fun _ : B ↦ (0 : (d2_localSystem B g).cFiber b₀)) b v = 0 := by
      have : (d1_coord _ ∘ fun _ : B ↦ (0 : (d2_localSystem B g).cFiber b₀)) =
          fun _ ↦ 0 := by funext; simp
      rw [d1_flatDeriv, this, mfderiv_const]
      exact map_zero _
    simp only [d1_LocalSystem.connection, hc, hd, map_zero]
    exact Submodule.zero_mem _

theorem d2_mkVHS_periodMap_aux [IsManifold 𝓘(ℂ, E) ω B] (X : d2_MarkedPeriodFamily E B g)
    (A : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ)
    (hhol : ∀ p, (d2_localSystem B g).IsHolomorphicSubbundle E
      (fun b ↦ d2_filtration (X.period b) p))
    (htr : (d2_localSystem B g).IsTransversal E (fun p b ↦ d2_filtration (X.period b) p))
    (hpol : ∀ b, d1_IsPolarizedFiltration 1 (d2_dualForm A) (d2_filtration (X.period b)))
    (U : Set B) (hU : IsSimplyConnected U) (b₀ : U) (b : B) (hb : b ∈ U) (p : ℤ) :
    d1_periodMap (d2_mkVHS X A hhol htr hpol) U hU b₀ b p = d2_filtration (X.period b) p := by
  simp only [d1_periodMap, hb, dite_true]
  ext x
  simp only [Submodule.mem_map, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h := d1_constLocalSystem_flatTransport (Fin (2 * g) → ℚ) U hU ⟨b, hb⟩ b₀ y
    convert hy using 1
    exact Iff.of_eq (congrArg (· ∈ d2_filtration (X.period b) p) h)
  · exact fun hx ↦ ⟨x, hx, d1_constLocalSystem_flatTransport _ U hU ⟨b, hb⟩ b₀ x⟩

theorem d2_mkVHS_chartDomain_aux [IsManifold 𝓘(ℂ, E) ω B] (X : d2_MarkedPeriodFamily E B g)
    (A : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ)
    (hhol : ∀ p, (d2_localSystem B g).IsHolomorphicSubbundle E
      (fun b ↦ d2_filtration (X.period b) p))
    (htr : (d2_localSystem B g).IsTransversal E (fun p b ↦ d2_filtration (X.period b) p))
    (hpol : ∀ b, d1_IsPolarizedFiltration 1 (d2_dualForm A) (d2_filtration (X.period b)))
    (U : Set B) (hU : IsSimplyConnected U) (hUo : IsOpen U) (b₀ : U) :
    d1_chartDomain (d2_mkVHS X A hhol htr hpol) U hU b₀ 1 1 = U ∩ d2_chartDomain X b₀ := by
  have hset : {b | b ∈ U ∧ d1_periodMap (d2_mkVHS X A hhol htr hpol) U hU b₀ b ∈
      d1_chartDomainSet (d2_mkVHS X A hhol htr hpol).weight
        (d1_refFiltration (d2_mkVHS X A hhol htr hpol) b₀) 1 1} =
      U ∩ {b | d2_filtration (X.period b) ∈
        d1_chartDomainSet 1 (d2_filtration (X.period b₀)) 1 1} := by
    ext b
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    refine and_congr_right fun hb ↦ ?_
    have h : d1_periodMap (d2_mkVHS X A hhol htr hpol) U hU b₀ b =
        d2_filtration (X.period b) :=
      funext fun p ↦ d2_mkVHS_periodMap_aux X A hhol htr hpol U hU b₀ b hb p
    rw [h]
    rfl
  rw [d1_chartDomain, hset, interior_inter, hUo.interior_eq]
  rfl

theorem d2_mkVHS_chartPeriod_aux [IsManifold 𝓘(ℂ, E) ω B] (X : d2_MarkedPeriodFamily E B g)
    (A : Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ)
    (hhol : ∀ p, (d2_localSystem B g).IsHolomorphicSubbundle E
      (fun b ↦ d2_filtration (X.period b) p))
    (htr : (d2_localSystem B g).IsTransversal E (fun p b ↦ d2_filtration (X.period b) p))
    (hpol : ∀ b, d1_IsPolarizedFiltration 1 (d2_dualForm A) (d2_filtration (X.period b)))
    (U : Set B) (hU : IsSimplyConnected U) (b₀ : U) (b : B) (hb : b ∈ U) :
    d1_chartPeriod (d2_mkVHS X A hhol htr hpol) U hU b₀ 1 1 b = d2_chartPeriod X b₀ b := by
  have h : d1_periodMap (d2_mkVHS X A hhol htr hpol) U hU b₀ b =
      d2_filtration (X.period b) :=
    funext fun p ↦ d2_mkVHS_periodMap_aux X A hhol htr hpol U hU b₀ b hb p
  rw [d1_chartPeriod, h]
  rfl

end Family

section Differential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {B : Type*} [TopologicalSpace B] [ChartedSpace E B]
variable {g : ℕ}

theorem d2_mem_chartDomain_aux [IsManifold 𝓘(ℂ, E) ω B] (X : d2_MarkedPeriodFamily E B g) (b₀ : B) :
    b₀ ∈ d2_chartDomain X b₀ :=
  d2v_mem_chartDomain X b₀

theorem d2_chartPeriod_holomorphic_aux [IsManifold 𝓘(ℂ, E) ω B] (X : d2_MarkedPeriodFamily E B g)
    (b₀ : B) :
    ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, d2_ChartTarget g) ω (d2_chartPeriod X b₀)
      (d2_chartDomain X b₀) :=
  d2v_chartPeriod_holomorphic X b₀

theorem d2_ker_mfderiv_chartPeriod_aux [IsManifold 𝓘(ℂ, E) ω B] (X : d2_MarkedPeriodFamily E B g)
    (b₀ b : B) (hb : b ∈ d2_chartDomain X b₀) :
    LinearMap.ker (show E →L[ℂ] d2_ChartTarget g from
      mfderiv 𝓘(ℂ, E) 𝓘(ℂ, d2_ChartTarget g) (d2_chartPeriod X b₀) b).toLinearMap =
      LinearMap.ker (d2_kodairaSpencer X b) := by
  exact d2k_ker_mfderiv X b₀ b hb
    (((d2_chartPeriod_holomorphic_aux X b₀).contMDiffAt
      (isOpen_interior.mem_nhds hb)).mdifferentiableAt (by simp))

theorem d2_finrank_range_mfderiv_aux [IsManifold 𝓘(ℂ, E) ω B] [FiniteDimensional ℂ E]
    (X : d2_MarkedPeriodFamily E B g) (b₀ b : B) (hb : b ∈ d2_chartDomain X b₀) :
    Module.finrank ℂ (LinearMap.range (show E →L[ℂ] d2_ChartTarget g from
      mfderiv 𝓘(ℂ, E) 𝓘(ℂ, d2_ChartTarget g) (d2_chartPeriod X b₀) b).toLinearMap) =
      Module.finrank ℂ (LinearMap.range (d2_kodairaSpencer X b)) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (show E →L[ℂ] d2_ChartTarget g from
    mfderiv 𝓘(ℂ, E) 𝓘(ℂ, d2_ChartTarget g) (d2_chartPeriod X b₀) b).toLinearMap
  have h2 := LinearMap.finrank_range_add_finrank_ker (d2_kodairaSpencer X b)
  rw [d2_ker_mfderiv_chartPeriod_aux X b₀ b hb] at h1
  omega

theorem d2_mfderiv_injective_of_rank_aux [IsManifold 𝓘(ℂ, E) ω B] [FiniteDimensional ℂ E]
    (X : d2_MarkedPeriodFamily E B g) (b₀ b : B) (hb : b ∈ d2_chartDomain X b₀)
    (hrank : Module.finrank ℂ (LinearMap.range (d2_kodairaSpencer X b)) =
      Module.finrank ℂ E) :
    Function.Injective (show E →L[ℂ] d2_ChartTarget g from
      mfderiv 𝓘(ℂ, E) 𝓘(ℂ, d2_ChartTarget g) (d2_chartPeriod X b₀) b) := by
  have h2 := LinearMap.finrank_range_add_finrank_ker (d2_kodairaSpencer X b)
  have hker : LinearMap.ker (d2_kodairaSpencer X b) = ⊥ :=
    Submodule.finrank_eq_zero.1 (by omega)
  rw [← d2_ker_mfderiv_chartPeriod_aux X b₀ b hb] at hker
  exact LinearMap.ker_eq_bot.1 hker

theorem d2_hodgeOne_injOn_of_rank_aux [IsManifold 𝓘(ℂ, E) ω B] [FiniteDimensional ℂ E]
    (X : d2_MarkedPeriodFamily E B g) (b : B)
    (hrank : Module.finrank ℂ (LinearMap.range (d2_kodairaSpencer X b)) =
      Module.finrank ℂ E) :
    ∃ W ∈ 𝓝 b, Set.InjOn (fun b' ↦ d2_hodgeOne (X.period b')) W := by
  have hmem := d2_mem_chartDomain_aux X b
  have hΦ : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, d2_ChartTarget g) ω (d2_chartPeriod X b) b :=
    (d2_chartPeriod_holomorphic_aux X b).contMDiffAt (isOpen_interior.mem_nhds hmem)
  have hstrict := (d2k_contDiffAt_chart hΦ).hasStrictFDerivAt (by simp)
  have hinj := d2_mfderiv_injective_of_rank_aux X b b hmem hrank
  have hinj' : Function.Injective (fderiv ℂ (d2_chartPeriod X b ∘ (extChartAt 𝓘(ℂ, E) b).symm)
      (extChartAt 𝓘(ℂ, E) b b)) := by
    rw [← d2k_mfderiv_eq_fderiv (hΦ.mdifferentiableAt (by simp))]
    exact hinj
  obtain ⟨s, hs, hinjOn⟩ := d2k_injOn_of_hasStrictFDerivAt hstrict hinj'
  set e := extChartAt 𝓘(ℂ, E) b
  refine ⟨e.source ∩ e ⁻¹' s, Filter.inter_mem (extChartAt_source_mem_nhds b)
    ((continuousAt_extChartAt b) hs), ?_⟩
  rintro b' ⟨hb'1, hb'2⟩ b'' ⟨hb''1, hb''2⟩ h
  dsimp only at h
  have hF : d2_filtration (X.period b') = d2_filtration (X.period b'') := by
    funext p
    simp only [d2_filtration, h]
  have hΦeq : d2_chartPeriod X b b' = d2_chartPeriod X b b'' := by
    simp only [d2_chartPeriod, hF]
  apply e.injOn hb'1 hb''1
  apply hinjOn hb'2 hb''2
  simp only [Function.comp_apply, e.left_inv hb'1, e.left_inv hb''1, hΦeq]

theorem d2_kodairaSpencer_const_aux [IsManifold 𝓘(ℂ, E) ω B]
    (P : Fin g → Fin (2 * g) → ℂ) (hP : d2_IsPeriodMatrix P) (b : B) :
    d2_kodairaSpencer (d2_constFamily E B P hP) b = 0 := by
  have h : mfderiv 𝓘(ℂ, E) 𝓘(ℂ, Fin g → Fin (2 * g) → ℂ) (d2_constFamily E B P hP).period b = 0 :=
    mfderiv_const
  ext v φ
  have hv : (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, Fin g → Fin (2 * g) → ℂ) (d2_constFamily E B P hP).period b v :
      Fin g → Fin (2 * g) → ℂ) = 0 := by
    rw [h]; rfl
  change (d2_hodgeOne _).mkQ (d2_evalBilin (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, Fin g → Fin (2 * g) → ℂ)
    (d2_constFamily E B P hP).period b v : Fin g → Fin (2 * g) → ℂ) φ) = 0
  rw [hv]
  change (d2_hodgeOne _).mkQ (d2_evalBilin (0 : Fin g → Fin (2 * g) → ℂ) φ) = 0
  rw [map_zero, LinearMap.zero_apply, map_zero]

end Differential

section Witnesses

theorem d2_dualForm_stdRiemann_aux : d2_dualForm d2_stdRiemann = d1_sympForm := by
  have hinv : (d2_stdRiemann.map (Int.cast : ℤ → ℚ))⁻¹ = !![0, -1; 1, 0] := by
    apply Matrix.inv_eq_left_inv
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [d2_stdRiemann, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  refine LinearMap.ext fun x ↦ LinearMap.ext fun y ↦ ?_
  rw [d2_dualForm, hinv, Matrix.toBilin'_apply', d1_sympForm_apply]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

theorem d2_hodgeOne_gauss_aux :
    d2_hodgeOne (d2_ellipticPeriod Complex.I) = ℂ ∙ d1_hodgeVector := by
  have key : ∀ φ : Module.Dual ℂ (Fin 1 → ℂ),
      d2_evalBilin (d2_ellipticPeriod Complex.I) φ = φ (fun _ ↦ 1) • d1_hodgeVector := by
    intro φ
    have hφ : ∀ c : ℂ, φ (fun _ ↦ c) = c * φ (fun _ ↦ 1) := fun c ↦ by
      rw [← smul_eq_mul, ← map_smul]; congr 1; funext; simp
    show d2_vec (2 * 1) _ = _
    have : (fun k : Fin (2 * 1) ↦ φ (fun i ↦ d2_ellipticPeriod Complex.I i k)) =
        ![φ (fun _ ↦ 1), Complex.I * φ (fun _ ↦ 1)] := by
      funext k; fin_cases k
      · simp [d2_ellipticPeriod]
      · simp [d2_ellipticPeriod, ← hφ]
    rw [this, d2l_vec_two, d1_hodgeVector, smul_add, TensorProduct.smul_tmul',
      TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, mul_comm Complex.I]
    congr 2
    exact (mul_one _).symm
  ext x
  rw [d2_hodgeOne, LinearMap.mem_range, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨φ, rfl⟩; exact ⟨_, (key φ).symm⟩
  · rintro ⟨c, rfl⟩
    refine ⟨c • LinearMap.proj 0, ?_⟩
    rw [key]; simp

theorem d2_ellipticPeriod_holomorphic_aux :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin 1 → Fin (2 * 1) → ℂ) ω
      (fun τ : d2_upperHalf ↦ d2_ellipticPeriod τ) := by
  have h : ContDiff ℂ ω (d2_ellipticPeriod) := by
    refine contDiff_pi.2 fun _ ↦ contDiff_pi.2 fun k ↦ ?_
    simp only [d2_ellipticPeriod]
    split_ifs
    · exact contDiff_const
    · exact contDiff_id
  exact h.contMDiff.comp contMDiff_subtype_val

theorem d2_kodairaSpencer_elliptic_injective_aux
    (hol : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin 1 → Fin (2 * 1) → ℂ) ω
      (fun τ : d2_upperHalf ↦ d2_ellipticPeriod τ))
    (hper : ∀ τ : d2_upperHalf, d2_IsPeriodMatrix (d2_ellipticPeriod τ)) (τ : d2_upperHalf) :
    Function.Injective
      (d2_kodairaSpencer (⟨fun τ ↦ d2_ellipticPeriod τ, hol, hper⟩ :
        d2_MarkedPeriodFamily ℂ d2_upperHalf 1) τ) := by
  set e₁ : Fin 1 → Fin (2 * 1) → ℂ := fun _ k ↦ if (k : ℕ) = 0 then 0 else 1
  have hform : d2_ellipticPeriod = fun t ↦ d2_ellipticPeriod 0 + t • e₁ := by
    funext t i k
    fin_cases k <;> simp [d2_ellipticPeriod, e₁]
  have hD : HasFDerivAt d2_ellipticPeriod ((ContinuousLinearMap.id ℂ ℂ).smulRight e₁) (τ : ℂ) := by
    rw [hform]
    exact ((hasFDerivAt_id (τ : ℂ)).smul_const e₁).const_add _
  obtain ⟨-, hm⟩ := d2k_mfderiv_opens d2_upperHalf (hol.mdifferentiableAt (by simp))
    d2_ellipticPeriod (Filter.Eventually.of_forall fun t h ↦ rfl)
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  have h0 := LinearMap.congr_fun hv (LinearMap.proj (R := ℂ) (φ := fun _ : Fin 1 ↦ ℂ) 0)
  change (d2_hodgeOne _).mkQ (d2_evalBilin ((show ℂ →L[ℂ] (Fin 1 → Fin (2 * 1) → ℂ) from
    mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin 1 → Fin (2 * 1) → ℂ) (fun τ : d2_upperHalf ↦ d2_ellipticPeriod τ) τ)
      v) _) = 0 at h0
  rw [hm, hD.fderiv, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
  obtain ⟨ψ, hψ⟩ := h0
  have hψ' := (d2_vec (2 * 1)).injective hψ
  have k0 := congrFun hψ' 0
  have k1 := congrFun hψ' 1
  simp only [d2_ellipticPeriod, e₁, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, Pi.smul_apply, LinearMap.proj_apply] at k0 k1
  norm_num at k0 k1
  have hτ : (fun _ : Fin 1 ↦ (τ : ℂ)) = (τ : ℂ) • fun _ : Fin 1 ↦ (1 : ℂ) := by
    funext; simp
  rw [hτ, map_smul, k0, smul_zero] at k1
  exact k1.symm

end Witnesses

section G32

variable {g : ℕ} {W : TopologicalSpace.Opens (Fin 10 → ℂ)}

theorem d2_g32Chart_isOpen_aux (X : d2_MarkedPeriodFamily (Fin 10 → ℂ) W g) (b₀ : W) :
    IsOpen (d2_g32Chart X b₀) := by
  exact W.isOpen.isOpenMap_subtype_val _ isOpen_interior

theorem d2_g32Period_analytic_aux (X : d2_MarkedPeriodFamily (Fin 10 → ℂ) W g) (b₀ : W)
    (κ : d2_ChartTarget g → Fin 9 → ℂ)
    (hκ : AnalyticOnNhd ℂ κ (d2_chartPeriod X b₀ '' d2_chartDomain X b₀)) :
    AnalyticOnNhd ℂ (d2_g32Period X b₀ κ) (d2_g32Chart X b₀) := by
  classical
  rintro _ ⟨b, hb, rfl⟩
  set Φ' : (Fin 10 → ℂ) → d2_ChartTarget g :=
    fun t ↦ if h : t ∈ W then d2_chartPeriod X b₀ ⟨t, h⟩ else 0
  have hΦ : ContMDiffAt 𝓘(ℂ, Fin 10 → ℂ) 𝓘(ℂ, d2_ChartTarget g) ω (d2_chartPeriod X b₀) b :=
    (d2_chartPeriod_holomorphic_aux X b₀).contMDiffAt (isOpen_interior.mem_nhds hb)
  have h1 := d2k_contDiffAt_opens W hΦ Φ' (Filter.Eventually.of_forall fun t h ↦ by simp [Φ', h])
  have h2 : AnalyticAt ℂ κ (Φ' b) := by
    simpa [Φ'] using hκ _ ⟨b, hb, rfl⟩
  refine (h2.comp h1.analyticAt).congr ?_
  filter_upwards [W.isOpen.mem_nhds b.2] with t ht
  have ht' : t ∈ W := ht
  simp [d2_g32Period, Φ', ht']

theorem d2_g32_finrank_aux (X : d2_MarkedPeriodFamily (Fin 10 → ℂ) W g) (b₀ b : W)
    (hb : b ∈ d2_chartDomain X b₀) (κ : d2_ChartTarget g → Fin 9 → ℂ)
    (hκ : DifferentiableAt ℂ κ (d2_chartPeriod X b₀ b))
    (hinj : Disjoint (LinearMap.ker (fderiv ℂ κ (d2_chartPeriod X b₀ b)).toLinearMap)
      (LinearMap.range (show (Fin 10 → ℂ) →L[ℂ] d2_ChartTarget g from
        mfderiv 𝓘(ℂ, Fin 10 → ℂ) 𝓘(ℂ, d2_ChartTarget g) (d2_chartPeriod X b₀) b).toLinearMap)) :
    Module.finrank ℂ (LinearMap.range
      (fderiv ℂ (d2_g32Period X b₀ κ) b : (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ)) =
      Module.finrank ℂ (LinearMap.range (d2_kodairaSpencer X b)) := by
  classical
  set Φ' : (Fin 10 → ℂ) → d2_ChartTarget g :=
    fun t ↦ if h : t ∈ W then d2_chartPeriod X b₀ ⟨t, h⟩ else 0
  have hΦ : MDifferentiableAt 𝓘(ℂ, Fin 10 → ℂ) 𝓘(ℂ, d2_ChartTarget g) (d2_chartPeriod X b₀) b :=
    ((d2_chartPeriod_holomorphic_aux X b₀).contMDiffAt
      (isOpen_interior.mem_nhds hb)).mdifferentiableAt (by simp)
  obtain ⟨hd, hm⟩ := d2k_mfderiv_opens W hΦ Φ'
    (Filter.Eventually.of_forall fun t h ↦ by simp [Φ', h])
  have hb' : Φ' b = d2_chartPeriod X b₀ b := by simp [Φ']
  have heq : d2_g32Period X b₀ κ =ᶠ[𝓝 (b : Fin 10 → ℂ)] κ ∘ Φ' := by
    filter_upwards [W.isOpen.mem_nhds b.2] with t ht
    have ht' : t ∈ W := ht
    simp [d2_g32Period, Φ', ht']
  have hcomp : fderiv ℂ (d2_g32Period X b₀ κ) b =
      (fderiv ℂ κ (d2_chartPeriod X b₀ b)).comp (fderiv ℂ Φ' b) := by
    rw [heq.fderiv_eq, fderiv_comp _ (hb' ▸ hκ) hd, hb']
  rw [← d2_finrank_range_mfderiv_aux X b₀ b hb, hcomp, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.range_comp, hm]
  exact d2k_finrank_map_of_disjoint _ _ (hm ▸ hinj)

theorem d2_g32_rank_nine_aux (X : d2_MarkedPeriodFamily (Fin 10 → ℂ) W g) (b₀ b : W)
    (hb : b ∈ d2_chartDomain X b₀) (κ : d2_ChartTarget g → Fin 9 → ℂ)
    (hκ : DifferentiableAt ℂ κ (d2_chartPeriod X b₀ b))
    (hinj : Disjoint (LinearMap.ker (fderiv ℂ κ (d2_chartPeriod X b₀ b)).toLinearMap)
      (LinearMap.range (show (Fin 10 → ℂ) →L[ℂ] d2_ChartTarget g from
        mfderiv 𝓘(ℂ, Fin 10 → ℂ) 𝓘(ℂ, d2_ChartTarget g) (d2_chartPeriod X b₀) b).toLinearMap))
    (h9 : Module.finrank ℂ (LinearMap.range (d2_kodairaSpencer X b)) = 9) :
    Module.finrank ℂ (LinearMap.range
      (fderiv ℂ (d2_g32Period X b₀ κ) b : (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ)) = 9 := by
  rw [d2_g32_finrank_aux X b₀ b hb κ hκ hinj, h9]

end G32

end HodgeLean.Foundations.Program
