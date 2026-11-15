import HodgeLean.Foundations.Program.GaussManinToriDefs
import HodgeLean.Foundations.Program.GaussManinToriLatticeProofs

/-!
# The weight-one VHS of marked period data: helper lemmas

Coordinates on `ℂ ⊗ ℚ^{2g}`, complex conjugation of period matrices and of linear forms, the
real map of a period matrix, and the Hodge decomposition `F¹ ⊕ \bar F¹` of a period matrix.
Helper names carry the prefix `d2v_`.
-/

noncomputable section

open scoped TensorProduct ContDiff
open Manifold
namespace HodgeLean.Foundations.Program
open HodgeBlocks

theorem d2v_vec_apply (n : ℕ) (c : Fin n → ℂ) :
    d2_vec n c = ∑ k, c k ⊗ₜ[ℚ] (Pi.single k 1 : Fin n → ℚ) := by
  simp [d2_vec, Module.Basis.equivFun_symm_apply, Module.Basis.baseChange_apply,
    TensorProduct.smul_tmul']

theorem d2v_sigmaQ_vec (n : ℕ) (c : Fin n → ℂ) :
    sigmaQ (Fin n → ℚ) (d2_vec n c) = d2_vec n (fun k ↦ starRingEnd ℂ (c k)) := by
  rw [d2v_vec_apply, d2v_vec_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  exact sigmaQ_tmul _ _ _

variable {g : ℕ}

/-- The complex conjugate of a period matrix, entry by entry; its row space is `\bar F¹`.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §1.2 (the conjugate period
matrix `\bar Π`). -/
def d2v_conj (P : Fin g → Fin (2 * g) → ℂ) : Fin g → Fin (2 * g) → ℂ :=
  fun i k ↦ starRingEnd ℂ (P i k)

/-- The conjugate `v ↦ \overline{φ(\bar v)}` of a `ℂ`-linear form on `ℂ^g`, written with the
conjugated coefficients of `φ`.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §1.2 (`\bar Ω = \overline{Ω}`). -/
def d2v_conjDual (φ : Module.Dual ℂ (Fin g → ℂ)) : Module.Dual ℂ (Fin g → ℂ) :=
  ∑ i, starRingEnd ℂ (φ (Pi.single i 1)) • LinearMap.proj i

example (P : Fin g → Fin (2 * g) → ℂ) (i : Fin g) (k : Fin (2 * g)) :
    d2v_conj P i k = starRingEnd ℂ (P i k) := rfl

example : d2v_conjDual (0 : Module.Dual ℂ (Fin g → ℂ)) = 0 := by
  simp [d2v_conjDual]

theorem d2v_dual_apply (φ : Module.Dual ℂ (Fin g → ℂ)) (v : Fin g → ℂ) :
    φ v = ∑ i, v i * φ (Pi.single i 1) := by
  conv_lhs => rw [pi_eq_sum_univ v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_smul, smul_eq_mul]
  congr 2
  funext j
  simp [Pi.single_apply, eq_comm]

theorem d2v_conjDual_apply (φ : Module.Dual ℂ (Fin g → ℂ)) (v : Fin g → ℂ) :
    d2v_conjDual φ (fun i ↦ starRingEnd ℂ (v i)) = starRingEnd ℂ (φ v) := by
  rw [d2v_dual_apply φ v, map_sum]
  simp [d2v_conjDual, mul_comm]

theorem d2v_sigmaQ_evalBilin (P : Fin g → Fin (2 * g) → ℂ) (φ : Module.Dual ℂ (Fin g → ℂ)) :
    sigmaQ _ (d2_evalBilin P φ) = d2_evalBilin (d2v_conj P) (d2v_conjDual φ) := by
  show sigmaQ _ (d2_vec _ _) = d2_vec _ _
  rw [d2v_sigmaQ_vec]
  congr 1; funext k
  exact (d2v_conjDual_apply φ (fun i ↦ P i k)).symm

theorem d2v_conjDual_conjDual (φ : Module.Dual ℂ (Fin g → ℂ)) :
    d2v_conjDual (d2v_conjDual φ) = φ := by
  refine LinearMap.ext fun v ↦ ?_
  have := d2v_conjDual_apply (d2v_conjDual φ) (fun i ↦ starRingEnd ℂ (v i))
  simp only [Complex.conj_conj] at this
  rw [this, d2v_conjDual_apply, Complex.conj_conj]

theorem d2v_map_sigmaQ_hodgeOne (P : Fin g → Fin (2 * g) → ℂ) :
    (d2_hodgeOne P).map (sigmaQ _) = d2_hodgeOne (d2v_conj P) := by
  ext x
  simp only [Submodule.mem_map, d2_hodgeOne, LinearMap.mem_range]
  constructor
  · rintro ⟨_, ⟨φ, rfl⟩, rfl⟩
    exact ⟨_, (d2v_sigmaQ_evalBilin P φ).symm⟩
  · rintro ⟨ψ, rfl⟩
    refine ⟨_, ⟨d2v_conjDual ψ, rfl⟩, ?_⟩
    rw [d2v_sigmaQ_evalBilin, d2v_conjDual_conjDual]

theorem d2v_finrank_real : Module.finrank ℝ (Fin g → ℂ) = 2 * g := by
  rw [Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, mul_comm]

theorem d2v_realMap_injective {P : Fin g → Fin (2 * g) → ℂ} (hP : d2_IsPeriodMatrix P) :
    Function.Injective (d2_realMap P) :=
  hP.fintypeLinearCombination_injective

theorem d2v_realMap_bijective {P : Fin g → Fin (2 * g) → ℂ} (hP : d2_IsPeriodMatrix P) :
    Function.Bijective (d2_realMap P) := by
  refine ⟨d2v_realMap_injective hP, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rw [Module.finrank_fin_fun, d2v_finrank_real])).mp (d2v_realMap_injective hP)

theorem d2v_isPeriodMatrix_conj {P : Fin g → Fin (2 * g) → ℂ} (hP : d2_IsPeriodMatrix P) :
    d2_IsPeriodMatrix (d2v_conj P) := by
  let c : (Fin g → ℂ) ≃ₗ[ℝ] (Fin g → ℂ) :=
    LinearEquiv.piCongrRight (fun _ ↦ Complex.conjAe.toLinearEquiv)
  exact hP.map' c.toLinearMap c.ker


theorem d2v_evalBilin_injective {P : Fin g → Fin (2 * g) → ℂ} (hP : d2_IsPeriodMatrix P) :
    Function.Injective (d2_evalBilin P) := by
  have h := LinearMap.finrank_range_add_finrank_ker (d2_evalBilin P)
  have h1 : Module.finrank ℂ (LinearMap.range (d2_evalBilin P)) = g := d2_finrank_hodgeOne_aux hP
  rw [h1, Subspace.dual_finrank_eq, Module.finrank_fin_fun] at h
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.finrank_eq_zero.mp (by omega)

theorem d2v_finrank_cFiber : Module.finrank ℂ (ℂ ⊗[ℚ] (Fin (2 * g) → ℚ)) = 2 * g := by
  rw [Module.finrank_baseChange, Module.finrank_fin_fun]

/-- An `ℝ`-linear form evaluated on `realMap`. -/
theorem d2v_apply_realMap (P : Fin g → Fin (2 * g) → ℂ) (f : (Fin g → ℂ) →ₗ[ℝ] ℂ)
    (s : Fin (2 * g) → ℝ) : f (d2_realMap P s) = ∑ k, s k • f (d2_column P k) := by
  rw [d2_realMap, Fintype.linearCombination_apply, map_sum]
  simp only [map_smul]

theorem d2v_disjoint_hodgeOne {P : Fin g → Fin (2 * g) → ℂ} (hP : d2_IsPeriodMatrix P) :
    Disjoint (d2_hodgeOne P) (d2_hodgeOne (d2v_conj P)) := by
  rw [Submodule.disjoint_def]
  rintro x ⟨φ, rfl⟩ ⟨ψ, hψ⟩
  have hk : ∀ k, φ (d2_column P k) = ψ (fun i ↦ starRingEnd ℂ (d2_column P k i)) := by
    intro k
    have := congrArg (fun y ↦ (d2_vec (2 * g)).symm y k) hψ
    show φ (fun i ↦ P i k) = _
    simpa [d2_evalBilin, d2v_conj, d2_column] using this.symm
  let c : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) :=
    (LinearEquiv.piCongrRight (fun _ ↦ Complex.conjAe.toLinearEquiv)).toLinearMap
  have hz : ∀ z, φ z = ψ (fun i ↦ starRingEnd ℂ (z i)) := by
    intro z
    obtain ⟨s, rfl⟩ := (d2v_realMap_bijective hP).2 z
    have h1 := d2v_apply_realMap P (φ.restrictScalars ℝ) s
    have h2 := d2v_apply_realMap P ((ψ.restrictScalars ℝ).comp c) s
    simp only [LinearMap.restrictScalars_apply, LinearMap.comp_apply] at h1 h2
    have hc : ∀ w, c w = fun i ↦ starRingEnd ℂ (w i) := fun _ ↦ rfl
    rw [hc] at h2
    simp only [hc] at h2
    rw [h1, h2]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [hk]
  have h0 : φ = 0 := by
    refine LinearMap.ext fun z ↦ ?_
    have h1 := hz (Complex.I • z)
    rw [map_smul, hz z] at h1
    have h2 : (fun i ↦ starRingEnd ℂ ((Complex.I • z) i)) =
        (-Complex.I) • fun i ↦ starRingEnd ℂ (z i) := by
      funext i; simp
    rw [h2, map_smul] at h1
    have : (2 * Complex.I) * ψ (fun i ↦ starRingEnd ℂ (z i)) = 0 := by
      rw [smul_eq_mul, smul_eq_mul] at h1; linear_combination h1
    rw [hz z]
    simpa [Complex.I_ne_zero] using this
  rw [h0, map_zero]

theorem d2v_isCompl_hodgeOne {P : Fin g → Fin (2 * g) → ℂ} (hP : d2_IsPeriodMatrix P) :
    IsCompl (d2_hodgeOne P) ((d2_hodgeOne P).map (sigmaQ _)) := by
  rw [d2v_map_sigmaQ_hodgeOne]
  have hdisj := d2v_disjoint_hodgeOne hP
  refine ⟨hdisj, codisjoint_iff.mpr (Submodule.eq_top_of_finrank_eq ?_)⟩
  have h := Submodule.finrank_sup_add_finrank_inf_eq (d2_hodgeOne P) (d2_hodgeOne (d2v_conj P))
  rw [disjoint_iff.mp hdisj, finrank_bot, d2_finrank_hodgeOne_aux hP,
    d2_finrank_hodgeOne_aux (d2v_isPeriodMatrix_conj hP)] at h
  rw [d2v_finrank_cFiber]
  omega

theorem d2v_filtration_isHodge {P : Fin g → Fin (2 * g) → ℂ} (hP : d2_IsPeriodMatrix P) :
    d1_IsHodgeFiltration 1 (d2_filtration P) := by
  refine ⟨fun a b hab ↦ ?_, ⟨0, by simp [d2_filtration]⟩,
    ⟨2, by simp [d2_filtration]⟩, fun p ↦ ?_⟩
  · simp only [d2_filtration]
    split_ifs <;> first | exact le_top | exact bot_le | exact le_rfl | omega
  · simp only [d2_filtration]
    split_ifs <;> first
      | omega
      | (rw [Submodule.map_bot]; exact isCompl_top_bot)
      | (rw [d1_map_sigmaQ_top]; exact isCompl_bot_top)
      | (subst_vars; exact d2v_isCompl_hodgeOne hP)


theorem d2v_mem_filtration_le (P : Fin g → Fin (2 * g) → ℂ) (p : ℤ)
    (x : ℂ ⊗[ℚ] (Fin (2 * g) → ℚ)) (hx : x ∈ d2_filtration P p) (hp : 2 ≤ p) : x = 0 := by
  have : ¬ p ≤ 0 := by omega
  have h' : p ≠ 1 := by omega
  simpa [d2_filtration, this, h'] using hx

theorem d2v_filtration_of_le_zero (P : Fin g → Fin (2 * g) → ℂ) {p : ℤ} (hp : p ≤ 0) :
    d2_filtration P p = ⊤ := by
  simp [d2_filtration, hp]


section Chart
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {B : Type*} [TopologicalSpace B] [ChartedSpace E B]

theorem d2v_exists_simplyConnected_nhds (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    {B : Type*} [TopologicalSpace B] [ChartedSpace E B] (b₁ : B) :
    ∃ U : Set B, IsSimplyConnected U ∧ b₁ ∈ U ∧ IsOpen U := by
  let e := chartAt E b₁
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp e.open_target (e b₁) (mem_chart_target E b₁)
  let s := e.source ∩ e ⁻¹' Metric.ball (e b₁) r
  have hs : e '' s = Metric.ball (e b₁) r := by
    ext z
    constructor
    · rintro ⟨x, ⟨_, hx'⟩, rfl⟩
      exact hx'
    · intro hz
      refine ⟨e.symm z, ⟨e.map_target (hball hz), ?_⟩, e.right_inv (hball hz)⟩
      simpa [Set.mem_preimage, e.right_inv (hball hz)] using hz
  refine ⟨s, ?_, ⟨mem_chart_source E b₁, by simpa using hr⟩,
    e.isOpen_inter_preimage Metric.isOpen_ball⟩
  have h := e.homeomorphOfImageSubsetSource Set.inter_subset_left hs
  have : ContractibleSpace (Metric.ball (e b₁) r) :=
    (convex_ball (e b₁) r).contractibleSpace ⟨e b₁, Metric.mem_ball_self hr⟩
  exact (h.toHomotopyEquiv.simplyConnectedSpace_iff).mpr inferInstance

/-- A family of subspaces of the constant fibre spanned at every point by a global holomorphic
frame is a holomorphic subbundle of `d2_localSystem`. -/
theorem d2v_isHolomorphicSubbundle_of_frame
    (G : ∀ b, Submodule ℂ ((d2_localSystem B g).cFiber b)) (r : ℕ)
    (σ : Fin r → B → ℂ ⊗[ℚ] (Fin (2 * g) → ℚ))
    (hσ : ∀ i, ContMDiff 𝓘(ℂ, E)
      𝓘(ℂ, Fin (Module.finrank ℂ (ℂ ⊗[ℚ] (Fin (2 * g) → ℚ))) → ℂ) ω
      (d1_coord (ℂ ⊗[ℚ] (Fin (2 * g) → ℚ)) ∘ σ i))
    (hli : ∀ b, LinearIndependent ℂ (fun i ↦ σ i b))
    (hsp : ∀ b, Submodule.span ℂ (Set.range fun i ↦ σ i b) = G b) :
    (d2_localSystem B g).IsHolomorphicSubbundle E G := by
  intro b₁
  obtain ⟨U, hU, h₁, hUo⟩ := d2v_exists_simplyConnected_nhds E b₁
  refine ⟨U, hU, h₁, hUo, r, σ, fun i ↦ ?_, fun b _ ↦ ⟨hli b, hsp b⟩⟩
  show ContMDiffOn _ _ _ _ U
  refine (hσ i).contMDiffOn.congr fun b hb ↦ ?_
  simp only [Function.comp_apply, d1_LocalSystem.flatCoord, hb, dite_true]
  exact congrArg (d1_coord _) (d1_constLocalSystem_flatTransport _ U hU ⟨b, hb⟩ ⟨b₁, h₁⟩ _)

theorem d2v_linearIndependent_proj :
    LinearIndependent ℂ (fun i : Fin g ↦ (LinearMap.proj i : Module.Dual ℂ (Fin g → ℂ))) := by
  have h : (fun i : Fin g ↦ (LinearMap.proj i : Module.Dual ℂ (Fin g → ℂ))) =
      (Pi.basisFun ℂ (Fin g)).dualBasis := by
    funext i
    refine LinearMap.ext fun v ↦ ?_
    simp
  rw [h]
  exact (Pi.basisFun ℂ (Fin g)).dualBasis.linearIndependent

theorem d2v_span_proj :
    Submodule.span ℂ (Set.range fun i : Fin g ↦
      (LinearMap.proj i : Module.Dual ℂ (Fin g → ℂ))) = ⊤ := by
  have h : (fun i : Fin g ↦ (LinearMap.proj i : Module.Dual ℂ (Fin g → ℂ))) =
      (Pi.basisFun ℂ (Fin g)).dualBasis := by
    funext i
    refine LinearMap.ext fun v ↦ ?_
    simp
  rw [h]
  exact (Pi.basisFun ℂ (Fin g)).dualBasis.span_eq

theorem d2v_filtration_holomorphic [IsManifold 𝓘(ℂ, E) ω B] (X : d2_MarkedPeriodFamily E B g)
    (p : ℤ) :
    (d2_localSystem B g).IsHolomorphicSubbundle E (fun b ↦ d2_filtration (X.period b) p) := by
  by_cases hp0 : p ≤ 0
  · let β := Module.finBasis ℂ (ℂ ⊗[ℚ] (Fin (2 * g) → ℚ))
    refine d2v_isHolomorphicSubbundle_of_frame _ _ (fun i _ ↦ β i) (fun i ↦ contMDiff_const)
      (fun _ ↦ β.linearIndependent) (fun b ↦ ?_)
    rw [d2v_filtration_of_le_zero _ hp0]
    exact β.span_eq
  by_cases hp1 : p = 1
  · subst hp1
    let L : Fin g → (Fin g → Fin (2 * g) → ℂ) →ₗ[ℂ] ℂ ⊗[ℚ] (Fin (2 * g) → ℚ) :=
      fun i ↦ d2_evalBilin.flip (LinearMap.proj i)
    refine d2v_isHolomorphicSubbundle_of_frame _ g
      (fun i b ↦ d2_evalBilin (X.period b) (LinearMap.proj i))
      (fun i ↦ ?_) (fun b ↦ ?_) (fun b ↦ ?_)
    · let c := ((d1_coord (ℂ ⊗[ℚ] (Fin (2 * g) → ℚ))).toLinearMap ∘ₗ L i).toContinuousLinearMap
      have hc : (d1_coord (ℂ ⊗[ℚ] (Fin (2 * g) → ℚ)) ∘
          fun b ↦ d2_evalBilin (X.period b) (LinearMap.proj i)) = c ∘ X.period := by
        funext b
        simp [c, L]
      rw [hc]
      exact c.contDiff.contMDiff.comp X.holomorphic
    · have := d2v_linearIndependent_proj.map' (d2_evalBilin (X.period b))
        (LinearMap.ker_eq_bot.mpr (d2v_evalBilin_injective (X.isPeriod b)))
      exact this
    · show _ = d2_filtration (X.period b) 1
      simp only [d2_filtration, show ¬ (1 : ℤ) ≤ 0 by omega, ite_false, ite_true]
      have : (fun i ↦ d2_evalBilin (X.period b) (LinearMap.proj i)) =
          d2_evalBilin (X.period b) ∘ fun i ↦ LinearMap.proj i := rfl
      rw [this, Set.range_comp, ← Submodule.map_span, d2v_span_proj, Submodule.map_top]
      rfl
  · refine d2v_isHolomorphicSubbundle_of_frame _ 0 (fun i ↦ Fin.elim0 i) (fun i ↦ Fin.elim0 i)
      (fun _ ↦ linearIndependent_empty_type) (fun b ↦ ?_)
    simp [d2_filtration, hp0, hp1]
end Chart

end HodgeLean.Foundations.Program
