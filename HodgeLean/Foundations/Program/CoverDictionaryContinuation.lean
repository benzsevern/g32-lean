import HodgeLean.Foundations.Program.CoverAnalyticThree
import HodgeLean.Foundations.Program.CoverAnalyticTwo

/-! # B6-5 stage 5d, stage five: continuation of a solution over a quotient covering

General statements. For a quotient covering `π : V → U` of an open part `U` of the plane by the
finite group `b4b_Group`, with `V` path-connected and locally path-connected, and an analytic
coefficient `A` on `U` whose transport along every loop at a base point is conjugate, by one
invertible operator, to the column monodromy of the deck group, transport along projected paths
from a fixed point of the fibre gives a single-valued invertible function `Y` on `V`. It satisfies
the deck law `Y (h • v) = Y v · ρ(h⁻¹)` and, near each point `v`, equals the disc solution of the
system at `π v` times `Y v`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Metric Filter
open scoped Topology
namespace HodgeLean.Foundations.Program

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
variable {V : Type*} [TopologicalSpace V] {U : Set ℂ}

/-- Transport of the system with coefficient `A` along the projection of a path of `V`.
Source: `b65f_transport`; Ilyashenko–Yakovenko, §15 (continuation along paths). -/
def caf_pathT (A : ℂ → E →L[ℂ] E) (π : V → U) {v w : V} (γ : Path v w) : E →L[ℂ] E :=
  b65f_transport E A (fun t ↦ (π (γ.extend t)).val)

omit [FiniteDimensional ℂ E] in
theorem caf_pathT_eq_map (A : ℂ → E →L[ℂ] E) {π : V → U} (hπ : Continuous π) {v w : V}
    (γ : Path v w) :
    caf_pathT A π γ = b65f_transport E A (fun t ↦ ((γ.map hπ).extend t).val) := rfl

/-- Transport along a concatenation, with the later factor on the left. -/
theorem caf_pathT_trans (hU : IsOpen U) (A : ℂ → E →L[ℂ] E) (hA : AnalyticOnNhd ℂ A U)
    {π : V → U} (hπ : Continuous π) {v w z : V} (γ : Path v w) (δ : Path w z) :
    caf_pathT A π (γ.trans δ) = caf_pathT A π δ * caf_pathT A π γ := by
  rw [caf_pathT_eq_map A hπ, caf_pathT_eq_map A hπ, caf_pathT_eq_map A hπ, Path.map_trans]
  exact b65f_path_composition E U hU A hA _ _ _ (γ.map hπ) (δ.map hπ)

theorem caf_pathT_isUnit (hU : IsOpen U) (A : ℂ → E →L[ℂ] E) (hA : AnalyticOnNhd ℂ A U)
    {π : V → U} (hπ : Continuous π) {v w : V} (γ : Path v w) :
    IsUnit (caf_pathT A π γ) := by
  rw [caf_pathT_eq_map A hπ]
  exact (b65f_path_convergence E U hU A hA _ _ (γ.map hπ)).2

/-- Transport along a path inside a disc of `U` is the disc solution. -/
theorem caf_pathT_disc (A : ℂ → E →L[ℂ] E) {π : V → U} (hπ : Continuous π) {v w : V}
    (γ : Path v w) (r : ℝ) (hr : 0 < r) (hA : AnalyticOnNhd ℂ A (ball (π v).val r))
    (hγ : ∀ t, (π (γ t)).val ∈ ball (π v).val r) :
    caf_pathT A π γ = b65f_segment E A (π v).val (π w).val := by
  let γb : Path (⟨(π v).val, mem_ball_self hr⟩ : ball (π v).val r)
      ⟨(π w).val, by simpa using hγ 1⟩ :=
    { toFun := fun t ↦ ⟨(π (γ t)).val, hγ t⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp (hπ.comp γ.continuous)
      source' := by simp
      target' := by simp }
  have := b65f_disc_transport E A (π v).val r hr hA ⟨(π w).val, by simpa using hγ 1⟩ γb
  rw [caf_pathT]
  exact this

end General

section Deck

variable {V : Type*} [TopologicalSpace V] [MulAction b4b_Group V] {U : Set ℂ}

/-- The column action of the identity is the identity. -/
theorem caf_operator_one : b65r_operator (b4b_toMatrix (1 : b4b_Group)⁻¹) = 1 := by
  rw [inv_one, map_one]
  ext v i
  simp [b65r_operator]

/-- **Transport along a projected path from `u` to `h • u`** is `C ρ(h⁻¹) C⁻¹`, when transport
along every loop at the base point is conjugate by `C` to the column monodromy at `u`. -/
theorem caf_pathT_deck (A : ℂ → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))
    {π : V → U} (hp : IsQuotientCoveringMap π b4b_Group) (x : U) (u : π ⁻¹' {x})
    (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hL : ∀ η : Path x x, b65f_transport (Fin 4 → ℂ) A (fun v ↦ (η.extend v).val) =
        C.val * (b65s_column (hp.fundamentalGroupToMulOpposite u)
          (FundamentalGroup.fromPath ⟦η⟧)).val * (C⁻¹).val)
    (h : b4b_Group) {w : V} (δ : Path (u : V) w) (hw : w = h • (u : V)) :
    caf_pathT A π δ = C.val * b65r_operator (b4b_toMatrix h⁻¹) * (C⁻¹).val := by
  subst hw
  have hx : π (u : V) = x := u.property
  let η : Path x x :=
    { toFun := fun t ↦ π (δ t)
      continuous_toFun := hp.continuous.comp δ.continuous
      source' := by simp [hx]
      target' := by simp [hp.map_smul, hx] }
  have hk := hp.fundamentalGroupToMulOpposite_apply_mk_eq (e := u) (γ := η) (g := h)
    (Γ := δ.toContinuousMap) (by funext t; rfl) δ.source δ.target
  have h1 : caf_pathT A π δ = b65f_transport (Fin 4 → ℂ) A (fun v ↦ (η.extend v).val) := rfl
  rw [h1, hL η]
  congr 2
  change (b65s_column (hp.fundamentalGroupToMulOpposite u) (.of (.mk η))).val = _
  simp only [b65s_column, MonoidHom.comp_apply]
  rw [hk]
  rfl

/-- **Continuation over a quotient covering.** If `V` is path-connected and locally
path-connected and transport along every loop at `x` is conjugate by `C` to the column monodromy
at `u`, then transport along projected paths from `u`, times `C`, is a well-defined invertible
function `Y` on `V` with the deck law `Y (h • v) = Y v ρ(h⁻¹)` which near each point `v` is the disc
solution at `π v` times `Y v`. -/
theorem caf_continuation [PathConnectedSpace V] [LocallyPathConnectedSpace V] (hU : IsOpen U)
    (A : ℂ → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ)) (hA : AnalyticOnNhd ℂ A U)
    {π : V → U} (hp : IsQuotientCoveringMap π b4b_Group) (x : U) (u : π ⁻¹' {x})
    (C : ((Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ))ˣ)
    (hL : ∀ η : Path x x, b65f_transport (Fin 4 → ℂ) A (fun v ↦ (η.extend v).val) =
        C.val * (b65s_column (hp.fundamentalGroupToMulOpposite u)
          (FundamentalGroup.fromPath ⟦η⟧)).val * (C⁻¹).val) :
    ∃ Y : V → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ), (∀ v, IsUnit (Y v)) ∧
      (∀ (h : b4b_Group) v, Y (h • v) = Y v * b65r_operator (b4b_toMatrix h⁻¹)) ∧
      ∀ v (r : ℝ), 0 < r → ball (π v).val r ⊆ U →
        ∀ᶠ w in 𝓝 v, Y w = b65f_segment (Fin 4 → ℂ) A (π v).val (π w).val * Y v := by
  have hπ : Continuous π := hp.continuous
  have hloop : ∀ {v : V} (γ : Path (u : V) v) (γ' : Path (u : V) v),
      caf_pathT A π γ' = caf_pathT A π γ := by
    intro v γ γ'
    have h1 := caf_pathT_deck A hp x u C hL 1 (γ'.trans γ.symm) (one_smul _ _).symm
    have h2 := caf_pathT_deck A hp x u C hL 1 (γ.trans γ.symm) (one_smul _ _).symm
    rw [caf_pathT_trans hU A hA hπ] at h1 h2
    have hu := caf_pathT_isUnit hU A hA hπ γ.symm
    apply hu.mul_left_cancel
    rw [h1, h2]
  let Y : V → (Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ) := fun v ↦
    caf_pathT A π (PathConnectedSpace.somePath (u : V) v) * C.val
  have hY : ∀ {v : V} (γ : Path (u : V) v), Y v = caf_pathT A π γ * C.val := fun γ ↦ by
    simp only [Y]
    rw [hloop γ (PathConnectedSpace.somePath (u : V) _)]
  refine ⟨Y, fun v ↦ (caf_pathT_isUnit hU A hA hπ _).mul C.isUnit, ?_, ?_⟩
  · intro h v
    let γ := PathConnectedSpace.somePath (u : V) v
    let δ := PathConnectedSpace.somePath (u : V) (h • (u : V))
    have := hp.toContinuousConstSMul
    have hc : Continuous (fun y : V ↦ h • y) := continuous_const_smul h
    have hhγ : caf_pathT A π (γ.map hc) = caf_pathT A π γ := by
      simp only [caf_pathT]
      congr 1
      funext t
      exact congrArg Subtype.val (hp.map_smul h)
    rw [hY (δ.trans (γ.map hc)), caf_pathT_trans hU A hA hπ, hhγ,
      caf_pathT_deck A hp x u C hL h δ rfl, hY γ]
    simp only [mul_assoc, Units.inv_mul, mul_one]
  · intro v r hr hball
    set N : Set V := π ⁻¹' (Subtype.val ⁻¹' ball (π v).val r)
    have hN : N ∈ 𝓝 v := ((isOpen_ball.preimage continuous_subtype_val).preimage hπ).mem_nhds
      (mem_ball_self hr)
    filter_upwards [pathComponentIn_mem_nhds hN] with w hw
    have hj : JoinedIn N v w := hw
    let δ := hj.somePath
    let γ := PathConnectedSpace.somePath (u : V) v
    rw [hY (γ.trans δ), caf_pathT_trans hU A hA hπ, hY γ, mul_assoc]
    congr 1
    exact caf_pathT_disc A hπ δ r hr (hA.mono hball) (fun t ↦ hj.somePath_mem t)

end Deck

end HodgeLean.Foundations.Program
