import HodgeLean.Foundations.Program.CurveJacobianRest2Lattice

/-! # Track B3, lane Rest2: the intersection form and the rank of the period lattice

`b3Rest2_Key`: for transverse loops `γ`, `δ` there is a dual form `η_γ` of `γ` with
`∫_δ η_γ = γ · δ` (the local computation at the crossings is `CurveJacobianRest2Key.lean`).
From it:
* `b3Rest2_Q λ μ ∈ ℤ` on the period lattice: on generators `Q(λ_γ, λ_δ) = γ · δ'` for a loop `δ'`
  transverse to `γ` with the periods of `δ`; so `Q` is an integral form computing intersection
  numbers (`b3Rest2_exists_intersectionForm`);
* the forms `θ_λ` span `Ω¹(C)` over `ℝ` (a form `W`-orthogonal to all of them has vanishing real
  periods, hence is zero), and a basis `θ_{λ₁}, …, θ_{λ_{2g}}` among them embeds the lattice into
  `ℤ^{2g}` by `μ ↦ (Re μ(θ_{λ_j}))_j = (Q(λ_j, μ))_j`; so `rk Λ ≤ 2 dim Ω¹(C)`.
HC no distance; AV milestone no distance.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold ContinuousAlternatingMap MeasureTheory Metric
open scoped Topology ContDiff

namespace HodgeLean.Foundations.Program

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

attribute [local instance] b3Forms_isManifold_real

variable [T2Space C] [CompactSpace C] [MeasurableSpace E] [BorelSpace E]
variable (hE : Module.finrank ℂ E = 1)

/-- **The local intersection computation**: for transverse loops `γ`, `δ`, a dual form `η` of
`γ` with `∫_δ η = γ · δ`. -/
def b3Rest2_Key : Prop :=
  ∀ γ δ : b3_SmoothLoop E C, b3_Transverse E γ δ →
    ∃ η : C → E [⋀^Fin 1]→L[ℝ] ℝ, b3Forms_IsSmooth η ∧
      (∀ α : C → E [⋀^Fin 1]→L[ℝ] ℝ, b3Forms_IsSmooth α → b3Forms_d α = 0 →
        b3Forms_integral (b3Rest_b hE) (b3Forms_wedgeForm α η) =
          b3Forms_lineIntegral α γ.1 0 1) ∧
      b3Forms_lineIntegral η δ.1 0 1 = (b3_intersection E γ δ : ℝ)

variable [ConnectedSpace C]

theorem b3Rest2_latticePeriod_eq {γ δ : b3_SmoothLoop E C}
    (h : b3_period E C γ = b3_period E C δ) :
    b3_latticePeriod E C γ = b3_latticePeriod E C δ := Subtype.ext h

theorem b3Rest2_Q_transverse (hK : b3Rest2_Key (C := C) hE) (γ δ : b3_SmoothLoop E C)
    (h : b3_Transverse E γ δ) :
    b3Rest2_Q hE (b3_latticePeriod E C γ) (b3_latticePeriod E C δ) = b3_intersection E γ δ := by
  obtain ⟨η, hη, hη', hδ⟩ := hK γ δ h
  rw [b3Rest2_Q_eq_lineIntegral hE γ δ hη hη', hδ]

/-- `Q` as a biadditive map. -/
def b3Rest2_QHom : b3_periodLattice E C →+ b3_periodLattice E C →+ ℝ :=
  AddMonoidHom.mk' (fun l ↦ AddMonoidHom.mk' (b3Rest2_Q hE l) (b3Rest2_Q_add_right hE l))
    fun l l' ↦ by ext m; exact b3Rest2_Q_add_left hE l l' m

theorem b3Rest2_QHom_apply (l m : b3_periodLattice E C) :
    b3Rest2_QHom hE l m = b3Rest2_Q hE l m := rfl

/-- **The real intersection pairing is integral on the period lattice.** -/
theorem b3Rest2_Q_int (hK : b3Rest2_Key (C := C) hE) (l m : b3_periodLattice E C) :
    ∃ k : ℤ, b3Rest2_Q hE l m = k := by
  have hgen : ∀ γ δ : b3_SmoothLoop E C,
      ∃ k : ℤ, b3Rest2_Q hE (b3_latticePeriod E C γ) (b3_latticePeriod E C δ) = k := by
    intro γ δ
    obtain ⟨δ', htr, hper⟩ := b3Rest_exists_transverse hE γ δ
    refine ⟨b3_intersection E γ δ', ?_⟩
    rw [← b3Rest2_latticePeriod_eq hper, b3Rest2_Q_transverse hE hK γ δ' htr]
  -- the set of `x` with integral pairing against a fixed `y`, on either side
  have hsub : ∀ (P : b3_periodLattice E C → Prop), P 0 → (∀ x y, P x → P y → P (x + y)) →
      (∀ x, P x → P (-x)) → (∀ γ, P (b3_latticePeriod E C γ)) → ∀ x, P x := by
    intro P h0 hadd hneg hg x
    obtain ⟨x, hx⟩ := x
    induction hx using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨γ, rfl⟩ := hy
      exact hg γ
    | zero => exact h0
    | add y z _ _ hy hz => exact hadd ⟨y, _⟩ ⟨z, _⟩ hy hz
    | neg y _ hy => exact hneg ⟨y, _⟩ hy
  have hright : ∀ γ : b3_SmoothLoop E C, ∀ m,
      ∃ k : ℤ, b3Rest2_Q hE (b3_latticePeriod E C γ) m = k := by
    intro γ
    refine hsub _ ⟨0, ?_⟩ (fun x y ⟨a, ha⟩ ⟨b, hb⟩ ↦ ⟨a + b, ?_⟩)
      (fun x ⟨a, ha⟩ ↦ ⟨-a, ?_⟩) (hgen γ)
    · rw [← b3Rest2_QHom_apply, _root_.map_zero]; simp
    · rw [← b3Rest2_QHom_apply, map_add, b3Rest2_QHom_apply, b3Rest2_QHom_apply, ha, hb]
      push_cast; ring
    · rw [← b3Rest2_QHom_apply, map_neg, b3Rest2_QHom_apply, ha]
      push_cast; ring
  refine hsub (fun x ↦ ∃ k : ℤ, b3Rest2_Q hE x m = k) ⟨0, ?_⟩
    (fun x y ⟨a, ha⟩ ⟨b, hb⟩ ↦ ⟨a + b, ?_⟩) (fun x ⟨a, ha⟩ ↦ ⟨-a, ?_⟩)
    (fun γ ↦ hright γ m) l
  · rw [← b3Rest2_QHom_apply, _root_.map_zero]; simp
  · rw [← b3Rest2_QHom_apply, map_add, AddMonoidHom.add_apply, b3Rest2_QHom_apply,
      b3Rest2_QHom_apply, ha, hb]
    push_cast; ring
  · rw [← b3Rest2_QHom_apply, map_neg, AddMonoidHom.neg_apply, b3Rest2_QHom_apply, ha]
    push_cast; ring

theorem b3Rest2_floor_Q (hK : b3Rest2_Key (C := C) hE) (l m : b3_periodLattice E C) :
    ((⌊b3Rest2_Q hE l m⌋ : ℤ) : ℝ) = b3Rest2_Q hE l m := by
  obtain ⟨k, hk⟩ := b3Rest2_Q_int hE hK l m
  rw [hk, Int.floor_intCast]

/-- **The integral intersection form** `⌊Q⌋ = Q` on the period lattice. -/
def b3Rest2_QZ (hK : b3Rest2_Key (C := C) hE) : LinearMap.BilinForm ℤ (b3_periodLattice E C) :=
  LinearMap.mk₂ ℤ (fun l m ↦ ⌊b3Rest2_Q hE l m⌋)
    (fun l l' m ↦ by
      apply Int.cast_injective (α := ℝ)
      push_cast
      rw [b3Rest2_floor_Q hE hK, b3Rest2_floor_Q hE hK, b3Rest2_floor_Q hE hK,
        b3Rest2_Q_add_left])
    (fun n l m ↦ by
      apply Int.cast_injective (α := ℝ)
      simp only [smul_eq_mul]
      push_cast
      rw [b3Rest2_floor_Q hE hK, b3Rest2_floor_Q hE hK, ← b3Rest2_QHom_apply, map_zsmul,
        AddMonoidHom.smul_apply, b3Rest2_QHom_apply, zsmul_eq_mul])
    (fun l m m' ↦ by
      apply Int.cast_injective (α := ℝ)
      push_cast
      rw [b3Rest2_floor_Q hE hK, b3Rest2_floor_Q hE hK, b3Rest2_floor_Q hE hK,
        b3Rest2_Q_add_right])
    (fun n l m ↦ by
      apply Int.cast_injective (α := ℝ)
      simp only [smul_eq_mul]
      push_cast
      rw [b3Rest2_floor_Q hE hK, b3Rest2_floor_Q hE hK, ← b3Rest2_QHom_apply, map_zsmul,
        b3Rest2_QHom_apply, zsmul_eq_mul])

theorem b3Rest2_QZ_apply (hK : b3Rest2_Key (C := C) hE) (l m : b3_periodLattice E C) :
    ((b3Rest2_QZ hE hK l m : ℤ) : ℝ) = b3Rest2_Q hE l m :=
  b3Rest2_floor_Q hE hK l m

/-- **The intersection form exists.** -/
theorem b3Rest2_isIntersectionForm (hK : b3Rest2_Key (C := C) hE) :
    b3_IsIntersectionForm E (b3Rest2_QZ hE hK) := by
  intro γ δ h
  apply Int.cast_injective (α := ℝ)
  rw [b3Rest2_QZ_apply, b3Rest2_Q_transverse hE hK γ δ h]

/-! ## The rank of the period lattice -/

theorem b3Rest2_ρ_injective {m : b3_periodLattice E C} (h : ∀ φ, (m.1 φ).re = 0) : m = 0 := by
  have hl := b3Forms_periodLattice_le_linearDual m.2
  refine Subtype.ext (funext fun φ ↦ ?_)
  have h1 := hl Complex.I φ 0
  rw [add_zero, b3Forms_linearDual_apply_zero hl, add_zero] at h1
  have h2 := h (Complex.I • φ)
  rw [h1] at h2
  apply Complex.ext
  · exact h φ
  · simpa using h2

/-- **The forms `θ_λ` span `Ω¹(C)` over `ℝ`.** -/
theorem b3Rest2_span_θ :
    Submodule.span ℝ (Set.range (b3Rest2_θ (C := C) hE)) = ⊤ := by
  haveI := b3Forms_holForm_finiteDimensional_real (C := C) hE
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne)
    inferInstance
  set ψ := ((b3Rest2_W hE).toDual (b3Rest2_W_nondegenerate hE)).symm f
  have hψf : ∀ φ, b3Rest2_W hE ψ φ = f φ := fun φ ↦ by
    have := LinearMap.BilinForm.toDual_def (B := b3Rest2_W hE) (b3Rest2_W_nondegenerate hE)
      (m := ψ) (n := φ)
    rw [← this, LinearEquiv.apply_symm_apply]
  have hψ : ψ = 0 := by
    have hper : b3Forms_PeriodsVanish (b3Forms_reForm ψ) := fun γ hp hγ ↦ by
      have hmem : b3Rest2_θ hE (b3_latticePeriod E C ⟨γ, hp, hγ⟩) ∈
          Submodule.span ℝ (Set.range (b3Rest2_θ (C := C) hE)) :=
        Submodule.subset_span ⟨_, rfl⟩
      have h0 : f (b3Rest2_θ hE (b3_latticePeriod E C ⟨γ, hp, hγ⟩)) = 0 := by
        have := Submodule.mem_map_of_mem (f := f) hmem
        rw [hf] at this
        exact (Submodule.mem_bot ℝ).1 this
      rw [← hψf, b3Rest2_W_θ] at h0
      rw [← b3Rest2_re_period ψ ⟨γ, hp, hγ⟩]
      exact h0
    obtain ⟨g, hg, hdg⟩ := b3Forms_exists_primitive (b3Forms_isSmooth_reForm ψ)
      (b3Forms_d_reForm hE ψ) hper
    exact b3Forms_hol_eq_zero_of_reForm_exact hE ψ hg hdg
  apply hf0
  ext φ
  rw [← hψf, hψ, _root_.map_zero, LinearMap.zero_apply]

/-- **`rk Λ ≤ 2 dim Ω¹(C)`**, given the local intersection computation. -/
theorem b3Rest2_finrank_le (hK : b3Rest2_Key (C := C) hE) :
    Module.finrank ℤ (b3_periodLattice E C) ≤ 2 * Module.finrank ℂ (b3_HolForm E C) := by
  haveI := b3Forms_holForm_finiteDimensional_real (C := C) hE
  haveI : FiniteDimensional ℂ (b3_HolForm E C) := b3Forms_holForm_finiteDimensional hE
  haveI : Module.Finite ℤ (b3_periodLattice E C) := b3Forms_periodLattice_finite hE
  obtain ⟨B, hBsub, hBspan, hBli⟩ := exists_linearIndependent ℝ (Set.range (b3Rest2_θ (C := C) hE))
  rw [b3Rest2_span_θ] at hBspan
  haveI : Finite B := hBli.finite
  haveI : Fintype B := Fintype.ofFinite B
  let bas : Module.Basis B ℝ (b3_HolForm E C) :=
    Module.Basis.mk hBli (by rw [Subtype.range_coe, hBspan])
  choose lb hlb using fun b : B ↦ hBsub b.2
  let e : b3_periodLattice E C →ₗ[ℤ] (B → ℤ) :=
    { toFun := fun m b ↦ ⌊b3Rest2_Q hE (lb b) m⌋
      map_add' := fun m m' ↦ by
        funext b
        apply Int.cast_injective (α := ℝ)
        simp only [Pi.add_apply]
        push_cast
        rw [b3Rest2_floor_Q hE hK, b3Rest2_floor_Q hE hK, b3Rest2_floor_Q hE hK,
          b3Rest2_Q_add_right]
      map_smul' := fun n m ↦ by
        funext b
        apply Int.cast_injective (α := ℝ)
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        push_cast
        simp only [b3Rest2_floor_Q hE hK]
        rw [← b3Rest2_QHom_apply, map_zsmul, b3Rest2_QHom_apply, zsmul_eq_mul] }
  have hinj : Function.Injective e := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    have hb : ∀ b : B, (m.1 b.1).re = 0 := fun b ↦ by
      have h1 := congrFun hm b
      have h2 := b3Rest2_floor_Q hE hK (lb b) m
      simp only [e, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at h1
      rw [h1, Int.cast_zero] at h2
      rw [← hlb b]
      exact h2.symm
    have hρ : b3Rest2_ρ m = 0 := bas.ext fun b ↦ by
      rw [Module.Basis.mk_apply, b3Rest2_ρ_apply, hb b, LinearMap.zero_apply]
    exact b3Rest2_ρ_injective fun φ ↦ by
      rw [← b3Rest2_ρ_apply, hρ, LinearMap.zero_apply]
  calc Module.finrank ℤ (b3_periodLattice E C) ≤ Module.finrank ℤ (B → ℤ) :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = Fintype.card B := Module.finrank_fintype_fun_eq_card ℤ
    _ = Module.finrank ℝ (b3_HolForm E C) := (Module.finrank_eq_card_basis bas).symm
    _ = 2 * Module.finrank ℂ (b3_HolForm E C) := finrank_real_of_complex _

/-- **`rk Λ = 2 dim Ω¹(C)`**, given the local intersection computation. -/
theorem b3Rest2_finrank_eq (hK : b3Rest2_Key (C := C) hE) :
    Module.finrank ℤ (b3_periodLattice E C) = 2 * Module.finrank ℂ (b3_HolForm E C) :=
  le_antisymm (b3Rest2_finrank_le hE hK) (b3Forms_two_mul_finrank_le_finrank_periodLattice hE)

end HodgeLean.Foundations.Program
