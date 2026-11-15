import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.HolomorphicRoots

/-! # Local operations on holomorphic functions

HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped Classical
set_option maxHeartbeats 400000
open Set Filter Topology HodgeLean.Foundations.Analytic
namespace AlgebraicGeometry.SingularCycles

/-- A nowhere vanishing holomorphic function has holomorphic reciprocal.
Source: Grauert–Remmert, Coherent Analytic Sheaves, §1.1.5; analytic inversion in charts. -/
theorem holFun_inv {M : Type*} [TopologicalSpace M] (S : an_ReducedSpace M)
    {U : Set M} (g : U → ℂ) (hg : S.IsHolFun g) (hne : ∀ y, g y ≠ 0) :
    S.IsHolFun (fun y => (g y)⁻¹) := by
  intro x i hxi
  obtain ⟨N, hNo, hxN, G, hG, heq⟩ := hg x i hxi
  have hGx : G ((S.atlas.chart i).toFun x) ≠ 0 := by
    rw [← heq x ⟨hxN, hxi⟩]
    exact hne x
  refine ⟨N, hNo, hxN, fun w => (G w)⁻¹, hG.inv hGx, ?_⟩
  intro y hy
  exact congrArg Inv.inv (heq y hy)

/-- Holomorphicity can be checked on open neighbourhoods of each point of the domain.
Source: Grauert–Remmert, Coherent Analytic Sheaves, §1.1.5; the local atlas definition. -/
theorem holFun_of_local {M : Type*} [TopologicalSpace M] (S : an_ReducedSpace M)
    {U : Set M} (g : U → ℂ)
    (hg : ∀ x : U, ∃ (V : Set M) (hVU : V ⊆ U), IsOpen V ∧ (x : M) ∈ V ∧
      S.IsHolFun (fun y : V => g ⟨y, hVU y.2⟩)) :
    S.IsHolFun g := by
  intro x i hxi
  obtain ⟨V, hVU, hVo, hxV, hV⟩ := hg x
  obtain ⟨N, hNo, hxN, G, hG, heq⟩ := hV ⟨x, hxV⟩ i hxi
  refine ⟨N ∩ V, hNo.inter hVo, ⟨hxN, hxV⟩, G, hG, ?_⟩
  intro y hy
  exact heq ⟨y, hy.1.2⟩ ⟨hy.1.1, hy.2⟩

end AlgebraicGeometry.SingularCycles
