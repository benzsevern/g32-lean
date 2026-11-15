import HodgeLean.Foundations.Program.PrymVariationCentreIsotypic

noncomputable section
namespace HodgeLean.Foundations.Program

theorem b63d_homG_evaluation_injective {G U M : Type} [Group G]
    [AddCommGroup U] [Module ℂ U] [AddCommGroup M] [Module ℂ M]
    (ρ : Representation ℂ G U) [ρ.IsIrreducible] (σ : Representation ℂ G M)
    (W : Submodule ℂ M) (v₀ : U) (hv₀ : v₀ ≠ 0) :
    Function.Injective (fun φ : b4_HomG ρ (fun g ↦ σ g) W ↦ φ.val v₀) := by
  intro φ ψ he
  let ξ : Representation.IntertwiningMap ρ σ :=
    { toLinearMap := (φ - ψ).val
      isIntertwining' g := LinearMap.ext (fun v ↦ (φ - ψ).property.2 g v) }
  have hzero : ξ v₀ = 0 := sub_eq_zero.mpr he
  rcases Representation.IsIrreducible.injective_or_eq_zero ξ with hi | hz
  · exact False.elim (hv₀ (hi (hzero.trans (map_zero ξ).symm)))
  · apply Subtype.ext
    apply LinearMap.ext
    intro v
    have h := congrArg (fun η : Representation.IntertwiningMap ρ σ ↦ η v) hz
    change φ.val v - ψ.val v = 0 at h
    exact sub_eq_zero.mp h

theorem b63d_eigen_lower_bound {G U M K : Type} [Group G] [Fintype G]
    [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
    [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    [AddCommGroup K] [Module ℂ K] [FiniteDimensional ℂ K]
    (ρ : Representation ℂ G U) [ρ.IsIrreducible] (σ : Representation ℂ G M)
    (W : Submodule ℂ M) (I : K →ₗ[ℂ] M) (a : G → ℂ)
    (hI : LinearMap.range I = LinearMap.range (∑ g, a g • σ g))
    (s : G) (z D : ℂ) (hD : D ≠ 0) (v₀ : U) (hv₀ : v₀ ≠ 0)
    (hp : (∑ g, a g • ρ g) v₀ = D • v₀) (hz : ρ s v₀ = z • v₀) :
    Module.finrank ℂ (b4_HomG ρ (fun g ↦ σ g) W) ≤
      Module.finrank ℂ ↥(W.comap I ⊓ (LinearMap.ker (σ s - z • LinearMap.id)).comap I) := by
  let ev : b4_HomG ρ (fun g ↦ σ g) W →ₗ[ℂ] M :=
    { toFun := fun φ ↦ φ.val v₀
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hi : Function.Injective ev := b63d_homG_evaluation_injective ρ σ W v₀ hv₀
  have hL : LinearMap.range ev ≤
      (W.comap I ⊓ (LinearMap.ker (σ s - z • LinearMap.id)).comap I).map I := by
    rintro y ⟨φ, rfl⟩
    have hA : (∑ g, a g • σ g) (ev φ) = D • ev φ := by
      calc
        (∑ g, a g • σ g) (ev φ) = φ.val ((∑ g, a g • ρ g) v₀) := by
          simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
          apply Finset.sum_congr rfl
          intro g hg
          exact congrArg (fun v : M ↦ a g • v) (φ.property.2 g v₀).symm
        _ = D • ev φ := by rw [hp, map_smul]; rfl
    have hmem : ev φ ∈ LinearMap.range I := by
      rw [hI]
      refine ⟨D⁻¹ • ev φ, ?_⟩
      rw [map_smul, hA, inv_smul_smul₀ hD]
    obtain ⟨u, hu⟩ := hmem
    refine ⟨u, ⟨?_, ?_⟩, hu⟩
    · change I u ∈ W
      rw [hu]
      exact φ.property.1 v₀
    · change (σ s - z • (LinearMap.id : M →ₗ[ℂ] M)) (I u) = 0
      rw [hu]
      have hσ : σ s (ev φ) = z • ev φ := by
        change σ s (φ.val v₀) = z • φ.val v₀
        rw [← φ.property.2 s v₀, hz, map_smul]
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hσ, sub_self]
  calc
    Module.finrank ℂ (b4_HomG ρ (fun g ↦ σ g) W) = Module.finrank ℂ (LinearMap.range ev) :=
      (LinearMap.finrank_range_of_inj hi).symm
    _ ≤ Module.finrank ℂ ((W.comap I ⊓ (LinearMap.ker (σ s - z • LinearMap.id)).comap I).map I) :=
      Submodule.finrank_mono hL
    _ ≤ _ := Submodule.finrank_map_le I _

end HodgeLean.Foundations.Program
