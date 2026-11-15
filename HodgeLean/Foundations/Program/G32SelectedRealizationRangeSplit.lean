import Mathlib.LinearAlgebra.Projection

noncomputable section
namespace HodgeLean.Foundations.Program

theorem g32y_range_complement {K V W : Type*} [Field K]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (j : V →ₗ[K] W) (hj : Function.Injective j) (T : W →ₗ[K] W)
    (hR : LinearMap.range T = LinearMap.range j)
    (H₀ H₁ : Submodule K W) (hH : IsCompl H₀ H₁)
    (hp₀ : H₀.map T ≤ H₀) (hp₁ : H₁.map T ≤ H₁) :
    IsCompl (H₀.comap j) (H₁.comap j) := by
  constructor
  · apply Submodule.disjoint_def.mpr
    intro v hv₀ hv₁
    have hh : j v = 0 := by
      have hm : j v ∈ H₀ ⊓ H₁ := ⟨hv₀, hv₁⟩
      rw [hH.disjoint.eq_bot] at hm
      exact hm
    exact hj (hh.trans (j.map_zero).symm)
  · apply codisjoint_iff.mpr
    apply top_unique
    intro v _
    have hv : j v ∈ LinearMap.range T := hR.symm ▸ LinearMap.mem_range_self j v
    obtain ⟨w, hw⟩ := hv
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp
      (show w ∈ H₀ ⊔ H₁ by rw [hH.sup_eq_top]; trivial)
    have hra : T a ∈ LinearMap.range j := hR ▸ LinearMap.mem_range_self T a
    have hrb : T b ∈ LinearMap.range j := hR ▸ LinearMap.mem_range_self T b
    obtain ⟨u, hu⟩ := hra
    obtain ⟨z, hz⟩ := hrb
    apply Submodule.mem_sup.mpr
    refine ⟨u, ?_, z, ?_, ?_⟩
    · change j u ∈ H₀
      rw [hu]
      exact hp₀ ⟨a, ha, rfl⟩
    · change j z ∈ H₁
      rw [hz]
      exact hp₁ ⟨b, hb, rfl⟩
    · apply hj
      rw [map_add, hu, hz, ← map_add, hab, hw]

end HodgeLean.Foundations.Program
