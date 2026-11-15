import HodgeLean.Foundations.Program.CurveJacobianRest2Singular
import HodgeLean.Foundations.Program.CurveJacobianRestUnique

/-! # Track B3, lane Unimod: unimodularity of the intersection form from dual level loops

Let `Q` be the intersection form of a compact connected Riemann surface `C`, so that
`Q(λ, μ) = Re μ(θ_λ)` (`CurveJacobianRest2Rank.lean`).
* `Q` is injective: `Q(λ, ·) = 0` makes all real periods of `θ_λ` vanish, so `θ_λ = 0` and
  `Re λ(φ) = W(φ, θ_λ) = 0` for all `φ`, hence `λ = 0`;
* every `φ ∈ Hom(Λ, ℤ)` is `μ ↦ Re μ(θ)` for a holomorphic form `θ` (`b3Unimod_exists_form`): the
  real-period map `Ω¹(C) → ℝ^{2g}` on a lattice basis is injective between spaces of the same
  dimension;
* `b3Unimod_Level`: for a holomorphic form `θ` with integral real periods and finitely many loops
  `δ`, there are loops `Γ₁, …, Γ_k` (the components of a level set of `Re ∫ θ` mod `1`)
  transverse to every `δ` with `Σᵢ Γᵢ · δ = Re ∫_δ θ`. Given it, `λ = Σᵢ λ_{Γᵢ}` has
  `Q(λ, λ_δ) = φ(λ_δ)` on a finite set of loops whose periods generate `Λ`, so `Q(λ, ·) = φ`.
HC no distance; AV milestone no distance.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set Filter Manifold
open scoped Topology ContDiff

namespace HodgeLean.Foundations.Program

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- **Dual level loops**: for a holomorphic form `θ` with integral real periods and finitely many
loops `δ`, loops `Γ₁, …, Γ_k` transverse to every `δ` with `Σᵢ Γᵢ · δ = Re ∫_δ θ`. -/
def b3Unimod_Level (E C : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C] : Prop :=
  ∀ θ : b3_HolForm E C, (∀ γ : b3_SmoothLoop E C, ∃ m : ℤ, (b3_period E C γ θ).re = m) →
    ∀ D : Finset (b3_SmoothLoop E C), ∃ (k : ℕ) (Γ : Fin k → b3_SmoothLoop E C),
      ∀ δ ∈ D, (∀ i, b3_Transverse E (Γ i) δ) ∧
        ((∑ i, b3_intersection E (Γ i) δ : ℤ) : ℝ) = (b3_period E C δ θ).re

variable [T2Space C] [CompactSpace C] [ConnectedSpace C] (hE : Module.finrank ℂ E = 1)
include hE

/-- Finitely many loops whose periods span the period lattice over `ℤ`. -/
theorem b3Unimod_exists_finset_span :
    ∃ D : Finset (b3_SmoothLoop E C),
      Submodule.span ℤ (b3_latticePeriod E C '' (D : Set (b3_SmoothLoop E C))) = ⊤ := by
  classical
  have : Module.Finite ℤ (b3_periodLattice E C) := b3Forms_periodLattice_finite hE
  have htop : Submodule.span ℤ (Set.range (b3_latticePeriod E C)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    refine b3Rest2_lattice_induction (fun x ↦ x ∈ Submodule.span ℤ
      (Set.range (b3_latticePeriod E C))) (Submodule.zero_mem _)
      (fun x y hx hy ↦ Submodule.add_mem _ hx hy) (fun x hx ↦ Submodule.neg_mem _ hx)
      (fun γ ↦ Submodule.subset_span ⟨γ, rfl⟩) x
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := b3_periodLattice E C)
  have hmem : ∀ x : s, ∃ T : Finset (b3_periodLattice E C),
      (T : Set _) ⊆ Set.range (b3_latticePeriod E C) ∧ x.1 ∈ Submodule.span ℤ (T : Set _) :=
    fun x ↦ Submodule.mem_span_finite_of_mem_span (by rw [htop]; trivial)
  choose T hTsub hTmem using hmem
  have hloop : ∀ x : s, ∀ y : T x, ∃ γ : b3_SmoothLoop E C, b3_latticePeriod E C γ = y.1 :=
    fun x y ↦ hTsub x y.2
  choose γ hγ using hloop
  refine ⟨Finset.univ.biUnion fun x : s ↦ (T x).attach.image (γ x), ?_⟩
  rw [eq_top_iff, ← hs, Submodule.span_le]
  intro x hx
  refine Submodule.span_le.2 ?_ (hTmem ⟨x, hx⟩)
  intro y hy
  refine Submodule.subset_span ⟨γ ⟨x, hx⟩ ⟨y, hy⟩, ?_, hγ _ _⟩
  simp only [Finset.coe_biUnion, Finset.coe_univ, Set.mem_univ, Set.iUnion_true,
    Finset.coe_image, Set.mem_iUnion, Set.mem_image, Finset.mem_coe, Finset.mem_attach,
    true_and]
  exact ⟨⟨x, hx⟩, ⟨y, hy⟩, rfl⟩

variable [MeasurableSpace E] [BorelSpace E]

/-- **Every integral functional on the lattice is the real-period functional of a form.** -/
theorem b3Unimod_exists_form (φ : b3_periodLattice E C →+ ℝ) :
    ∃ θ : b3_HolForm E C, ∀ μ : b3_periodLattice E C, (μ.1 θ).re = φ μ := by
  have := b3Forms_holForm_finiteDimensional_real (C := C) hE
  have : FiniteDimensional ℂ (b3_HolForm E C) := b3Forms_holForm_finiteDimensional hE
  have : Module.Finite ℤ (b3_periodLattice E C) := b3Forms_periodLattice_finite hE
  have : Module.Free ℤ (b3_periodLattice E C) := b3A_periodLattice_free
  set b := Module.Free.chooseBasis ℤ (b3_periodLattice E C)
  set ι := Module.Free.ChooseBasisIndex ℤ (b3_periodLattice E C)
  let T : b3_HolForm E C →ₗ[ℝ] (ι → ℝ) :=
    { toFun := fun θ i ↦ b3Rest2_ρ (b i) θ
      map_add' := fun θ θ' ↦ by funext i; simp
      map_smul' := fun c θ ↦ by funext i; simp }
  have hρ : ∀ (μ : b3_periodLattice E C) (θ : b3_HolForm E C),
      b3Rest2_ρ μ θ = ∑ i, (b.repr μ i : ℝ) * b3Rest2_ρ (b i) θ := by
    intro μ θ
    conv_lhs => rw [← b.sum_repr μ]
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_zsmul, LinearMap.smul_apply, zsmul_eq_mul]
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro θ hθ
    refine b3Rest2_eq_of_re_period hE fun γ ↦ ?_
    have h0 : b3Rest2_ρ (b3_latticePeriod E C γ) θ = 0 := by
      rw [hρ]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      have := congrFun hθ i
      simp only [T, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply] at this
      rw [this, mul_zero]
    rw [b3Rest2_ρ_apply] at h0
    have h1 : b3_period E C γ (0 : b3_HolForm E C) = 0 := by
      exact b3Forms_linearDual_apply_zero (b3Forms_period_mem_linearDual γ)
    rw [h1]
    exact h0
  have hdim : Module.finrank ℝ (b3_HolForm E C) = Module.finrank ℝ (ι → ℝ) := by
    rw [Module.finrank_fintype_fun_eq_card, finrank_real_of_complex,
      ← b3Rest2_finrank_eq hE (b3Rest2_key hE), Module.finrank_eq_card_chooseBasisIndex]
  have hsurj : Function.Surjective T := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    hdim).1 hinj
  obtain ⟨θ, hθ⟩ := hsurj fun i ↦ φ (b i)
  refine ⟨θ, fun μ ↦ ?_⟩
  rw [← b3Rest2_ρ_apply, hρ]
  conv_rhs => rw [← b.sum_repr μ]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have := congrFun hθ i
  simp only [T, LinearMap.coe_mk, AddHom.coe_mk] at this
  rw [this, map_zsmul, zsmul_eq_mul]

/-- **Injectivity of the intersection form.** -/
theorem b3Unimod_injective (Q : LinearMap.BilinForm ℤ (b3_periodLattice E C))
    (hQ : b3_IsIntersectionForm E Q) : Function.Injective Q := by
  have hQ' := b3Rest_intersectionForm_unique hE Q _ hQ (b3Rest2_isIntersectionForm hE
    (b3Rest2_key hE))
  subst hQ'
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro l hl
  have hθ : b3Rest2_θ hE l = 0 := by
    refine b3Rest2_eq_of_re_period hE fun γ ↦ ?_
    have h1 := b3Rest2_QZ_apply hE (b3Rest2_key hE) l (b3_latticePeriod E C γ)
    rw [hl, LinearMap.zero_apply, Int.cast_zero] at h1
    have h2 : b3_period E C γ (0 : b3_HolForm E C) = 0 := by
      exact b3Forms_linearDual_apply_zero (b3Forms_period_mem_linearDual γ)
    rw [h2, Complex.zero_re]
    exact h1.symm
  refine b3Rest2_ρ_injective fun φ ↦ ?_
  rw [← b3Rest2_W_θ hE l φ, hθ, map_zero]

/-- **Surjectivity of the intersection form, given dual level loops.** -/
theorem b3Unimod_surjective (hL : b3Unimod_Level E C)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice E C))
    (hQ : b3_IsIntersectionForm E Q) : Function.Surjective Q := by
  intro φ
  obtain ⟨θ, hθ⟩ := b3Unimod_exists_form hE ((Int.castAddHom ℝ).comp φ.toAddMonoidHom)
  have hint : ∀ γ : b3_SmoothLoop E C, ∃ m : ℤ, (b3_period E C γ θ).re = m :=
    fun γ ↦ ⟨φ (b3_latticePeriod E C γ), hθ (b3_latticePeriod E C γ)⟩
  obtain ⟨D, hD⟩ := b3Unimod_exists_finset_span (E := E) (C := C) hE
  obtain ⟨k, Γ, hΓ⟩ := hL θ hint D
  refine ⟨∑ i, b3_latticePeriod E C (Γ i), ?_⟩
  refine LinearMap.ext_on hD ?_
  rintro _ ⟨δ, hδ, rfl⟩
  obtain ⟨htr, hsum⟩ := hΓ δ hδ
  apply Int.cast_injective (α := ℝ)
  rw [map_sum, LinearMap.sum_apply]
  simp_rw [hQ _ δ (htr _)]
  rw [hsum]
  exact hθ (b3_latticePeriod E C δ)

/-- **The intersection form is unimodular, given dual level loops.** -/
theorem b3Unimod_bijective_of_level (hL : b3Unimod_Level E C)
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice E C))
    (hQ : b3_IsIntersectionForm E Q) : Function.Bijective Q :=
  ⟨b3Unimod_injective hE Q hQ, b3Unimod_surjective hE hL Q hQ⟩

end HodgeLean.Foundations.Program
