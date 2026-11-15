import HodgeLean.Foundations.Program.CurveJacobianAExact
import HodgeLean.Foundations.Program.CurveJacobianAFunctor

/-! # Track B3, lane A: periods span the dual, and the Abel–Jacobi map

Periods are linear functionals on `Ω¹`; on a compact connected surface they span the whole dual,
since a form annihilated by every period is zero. Hence every integral along a `C¹` path is the
period of a vector of `ℂ ⊗ Λ`, and integrating from a base point along good paths defines an
Abel–Jacobi map.
-/

noncomputable section

open Manifold Filter Topology Set
open scoped ContDiff TensorProduct

namespace HodgeLean.Foundations.Program

section Generic

/-- A `ℂ`-linear functional on `Ω¹` commutes with scalars. -/
theorem b3A_linearDual_smul {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    {u : b3_HolForm E C → ℂ} (hu : u ∈ b3_linearDual E C) (c : ℂ) (θ : b3_HolForm E C) :
    u (c • θ) = c * u θ := by
  have h0 := hu 1 0 0
  have h1 := hu c θ 0
  simp only [one_smul, add_zero, one_mul] at h0 h1
  have : u 0 = 0 := by linear_combination -h0
  rw [h1, this, add_zero]

/-- Elements of the period lattice are linear functionals. -/
theorem b3A_lattice_mem_linearDual {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    (u : b3_periodLattice E C) : (u : b3_HolForm E C → ℂ) ∈ b3_linearDual E C := by
  have : b3_periodLattice E C ≤ (b3_linearDual E C).toAddSubgroup := by
    rw [b3_periodLattice, AddSubgroup.closure_le]
    rintro _ ⟨γ, rfl⟩
    exact b3A_pathPeriod_linear γ.1 γ.2.2
  exact this u.2

/-- The complexified periods are linear functionals. -/
theorem b3A_cplxPeriod_mem_linearDual {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    (v : ℂ ⊗[ℤ] b3_periodLattice E C) : b3_cplxPeriod E C v ∈ b3_linearDual E C := by
  induction v using TensorProduct.inductionOn with
  | tmul c u => exact (b3_linearDual E C).smul_mem c (b3A_lattice_mem_linearDual u)
  | add x y hx hy => rw [map_add]; exact (b3_linearDual E C).add_mem hx hy

/-- Two classes in the Jacobian agree only if the periods differ by a lattice element. -/
theorem b3A_jacobian_eq {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    {w w' : ℂ ⊗[ℤ] b3_periodLattice E C}
    (h : (QuotientAddGroup.mk (Submodule.Quotient.mk w) : b3_Jacobian E C) =
      QuotientAddGroup.mk (Submodule.Quotient.mk w')) :
    ∃ ℓ : b3_periodLattice E C,
      b3_cplxPeriod E C w' - b3_cplxPeriod E C w = (ℓ : b3_HolForm E C → ℂ) := by
  set N := (b2_latticeMap (b3_periodLattice E C) (b3_periodF E C)).range
  set π : (ℂ ⊗[ℤ] b3_periodLattice E C) →+ b3_Jacobian E C :=
    (QuotientAddGroup.mk' N).comp (b3_periodF E C).mkQ.toAddMonoidHom
  have h0 : π (w' - w) = 0 := (map_sub π w' w).trans (sub_eq_zero_of_eq h.symm)
  obtain ⟨ℓ, hℓ⟩ := (QuotientAddGroup.eq_zero_iff (N := N) _).1 h0
  have h2 := (Submodule.Quotient.eq (b3_periodF E C)).1 hℓ
  have h3 := LinearMap.sub_mem_ker_iff.1 h2
  refine ⟨ℓ, ?_⟩
  rw [← map_sub, ← h3]
  show LinearMap.liftBaseChange ℂ _ ((1 : ℂ) ⊗ₜ[ℤ] ℓ) = _
  rw [LinearMap.liftBaseChange_tmul, one_smul]
  rfl

/-- Two classes in the Jacobian agree when the periods agree. -/
theorem b3A_jacobian_mk_eq {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    {w w' : ℂ ⊗[ℤ] b3_periodLattice E C} (h : b3_cplxPeriod E C w = b3_cplxPeriod E C w') :
    (QuotientAddGroup.mk (Submodule.Quotient.mk w) : b3_Jacobian E C) =
      QuotientAddGroup.mk (Submodule.Quotient.mk w') :=
  congrArg (fun z ↦ (QuotientAddGroup.mk z : b3_Jacobian E C))
    ((Submodule.Quotient.eq (b3_periodF E C)).2 (LinearMap.sub_mem_ker_iff.2 h))

/-- Every point of the Jacobian is the class of a vector. -/
theorem b3A_jacobian_surj {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    (j : b3_Jacobian E C) :
    ∃ w : ℂ ⊗[ℤ] b3_periodLattice E C,
      j = QuotientAddGroup.mk (Submodule.Quotient.mk w) := by
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective j
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact ⟨v, rfl⟩

end Generic

section Span

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- A linear functional on `Ω¹`, as an element of the dual. -/
def b3A_toDual : b3_linearDual E C →ₗ[ℂ] Module.Dual ℂ (b3_HolForm E C) where
  toFun u :=
    { toFun := u.1
      map_add' := fun θ η ↦ by
        have := u.2 1 θ η
        rwa [one_smul, one_mul] at this
      map_smul' := fun c θ ↦ b3A_linearDual_smul u.2 c θ }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The dual map is injective. -/
theorem b3A_toDual_injective : Function.Injective (b3A_toDual (E := E) (C := C)) := by
  intro u v h
  exact Subtype.ext (funext fun θ ↦ LinearMap.congr_fun h θ)

/-- The period of a loop is a complexified period. -/
theorem b3A_period_mem_range (γ : b3_SmoothLoop E C) :
    b3_period E C γ ∈ LinearMap.range (b3_cplxPeriod E C) :=
  ⟨(1 : ℂ) ⊗ₜ[ℤ] b3_latticePeriod E C γ, by
    rw [b3_cplxPeriod, LinearMap.liftBaseChange_tmul, one_smul]
    rfl⟩

/-- **The periods span the dual of `Ω¹`** on a compact connected surface. -/
theorem b3A_range_cplxPeriod [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) :
    LinearMap.range (b3_cplxPeriod E C) = b3_linearDual E C := by
  have : FiniteDimensional ℂ (b3_HolForm E C) := b3A_holForm_finiteDimensional hE
  refine le_antisymm (fun _ ⟨v, hv⟩ ↦ hv ▸ b3A_cplxPeriod_mem_linearDual v) fun u hu ↦ ?_
  by_contra hnot
  set W := Submodule.map b3A_toDual
    ((LinearMap.range (b3_cplxPeriod E C)).comap (b3_linearDual E C).subtype)
  have hW : W < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop ↦ hnot ?_
    obtain ⟨y, hy, hyu⟩ : b3A_toDual ⟨u, hu⟩ ∈ W := htop ▸ Submodule.mem_top
    rw [b3A_toDual_injective hyu] at hy
    exact hy
  obtain ⟨φ, hφ, hle⟩ := W.exists_le_ker_of_lt_top hW
  set θ := (Module.evalEquiv ℂ (b3_HolForm E C)).symm φ
  have hθ : θ ≠ 0 := fun h0 ↦ hφ (by
    have := (Module.evalEquiv ℂ (b3_HolForm E C)).apply_symm_apply φ
    rw [← this]
    simp only [θ] at h0
    rw [h0, map_zero])
  apply hθ
  refine b3A_eq_zero_of_periods hE θ fun γ ↦ ?_
  have hmem : b3A_toDual ⟨b3_period E C γ, b3A_pathPeriod_linear γ.1 γ.2.2⟩ ∈ W :=
    ⟨_, b3A_period_mem_range γ, rfl⟩
  have := hle hmem
  rw [LinearMap.mem_ker] at this
  rw [← Module.apply_evalEquiv_symm_apply] at this
  exact this

/-- On a compact connected surface, every integral along a `C¹` path is a complexified period. -/
theorem b3A_exists_cplxPeriod_eq [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (γ : ℝ → C) (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ) :
    ∃ v : ℂ ⊗[ℤ] b3_periodLattice E C, b3_cplxPeriod E C v = b3_pathPeriod E C γ := by
  have := b3A_pathPeriod_linear γ hγ
  rw [← b3A_range_cplxPeriod hE] at this
  exact this

/-- The class map `ℂ ⊗ Λ → J`. -/
def b3A_jacMk : (ℂ ⊗[ℤ] b3_periodLattice E C) →+ b3_Jacobian E C :=
  (QuotientAddGroup.mk' (b2_latticeMap (b3_periodLattice E C) (b3_periodF E C)).range).comp
    (b3_periodF E C).mkQ.toAddMonoidHom

/-- The class map is the quotient map. -/
theorem b3A_jacMk_apply (v : ℂ ⊗[ℤ] b3_periodLattice E C) :
    b3A_jacMk v = (QuotientAddGroup.mk (Submodule.Quotient.mk v) : b3_Jacobian E C) := rfl

/-- Lattice vectors have class zero. -/
theorem b3A_jacMk_lattice (ℓ : b3_periodLattice E C) :
    b3A_jacMk ((1 : ℂ) ⊗ₜ[ℤ] ℓ) = 0 :=
  (QuotientAddGroup.eq_zero_iff _).2 ⟨ℓ, rfl⟩

omit [IsManifold 𝓘(ℂ, E) ω C] in
/-- Group algebra for the Abel–Jacobi identity, stated for an abstract group. -/
theorem b3A_sub_sub_aux {A J : Type*} [AddCommGroup A] [AddCommGroup J] (π : A →+ J)
    (a b c w : A) (h : π (a - b - w) = 0) : π a - π c - (π b - π c) = π w := by
  rw [map_sub, map_sub] at h
  rw [sub_sub_sub_cancel_right]
  exact sub_eq_zero.1 h

/-- **Existence of an Abel–Jacobi map**: integrate from the base point along good paths. -/
theorem b3A_exists_abelJacobi [T2Space C] [CompactSpace C] [ConnectedSpace C]
    (hE : Module.finrank ℂ E = 1) (p₀ : C) : ∃ aj : C → b3_Jacobian E C, b3_IsAbelJacobi E C p₀ aj := by
  choose γp hγp using fun p : C ↦ b3A_joined (E := E) p₀ p
  choose vp hvp using fun p : C ↦ b3A_exists_cplxPeriod_eq hE (γp p) (hγp p).1
  refine ⟨fun p ↦ b3A_jacMk (vp p) - b3A_jacMk (vp p₀), sub_self _, fun γ hγ ↦ ?_⟩
  have hex := b3A_exists_cplxPeriod_eq hE γ hγ
  obtain ⟨w, hw⟩ := hex
  refine ⟨w, hw, ?_⟩
  have hg := b3A_isGoodPath_reparam γ hγ
  have hL := ((hγp (γ 0)).trans hg).trans (hγp (γ 1)).symm
  have hLint : ∀ θ : b3_HolForm E C, b3_period E C (b3A_toLoop hL) θ =
      b3_pathPeriod E C (γp (γ 0)) θ + b3_pathPeriod E C γ θ - b3_pathPeriod E C (γp (γ 1)) θ := by
    intro θ
    change b3_pathIntegral E C (b3A_toLoop hL).1 θ = _
    rw [b3A_toLoop_pathIntegral, b3A_pathIntegral_trans θ.2 ((hγp (γ 0)).trans hg)
      (hγp (γ 1)).symm, b3A_pathIntegral_trans θ.2 (hγp (γ 0)) hg,
      b3A_pathIntegral_symm θ.2 _ (hγp (γ 1)).1, b3A_pathIntegral_reparam θ.2 γ hγ]
    simp only [b3_pathPeriod]
    ring
  have hzero : b3A_jacMk (vp (γ 1) - vp (γ 0) - w) = 0 := by
    have h1 : b3_cplxPeriod E C (vp (γ 1) - vp (γ 0) - w) =
        b3_cplxPeriod E C ((1 : ℂ) ⊗ₜ[ℤ] (-b3_latticePeriod E C (b3A_toLoop hL))) := by
      rw [map_sub, map_sub, hvp, hvp, hw, b3_cplxPeriod, LinearMap.liftBaseChange_tmul, one_smul]
      funext θ
      simp only [Pi.sub_apply, AddMonoidHom.coe_toIntLinearMap, AddSubgroup.subtype_apply,
        AddSubgroup.coe_neg, Pi.neg_apply]
      rw [show (b3_latticePeriod E C (b3A_toLoop hL) : b3_HolForm E C → ℂ) θ = b3_period E C (b3A_toLoop hL) θ from rfl,
        hLint]
      ring
    exact (b3A_jacobian_mk_eq h1).trans (b3A_jacMk_lattice _)
  exact b3A_sub_sub_aux b3A_jacMk _ _ _ _ hzero

end Span

end HodgeLean.Foundations.Program
