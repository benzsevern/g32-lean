import HodgeLean.Foundations.Program.HurwitzPrym

noncomputable section
open Manifold
open scoped ContDiff
namespace HodgeLean.Foundations.Program

theorem g32y_stabilizer_trivial_off_branch
    {E C E' B G : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [NormedAddCommGroup E'] [NormedSpace ℂ E']
    [TopologicalSpace B] [ChartedSpace E' B] [IsManifold 𝓘(ℂ, E') ω B]
    [T2Space B] [ConnectedSpace B]
    [Group G] [Finite G] [MulAction G C] [FaithfulSMul G C]
    (hE : Module.finrank ℂ E = 1) (hB : Module.finrank ℂ E' = 1)
    (hG : ∀ a : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun y : C ↦ a • y))
    (f : C → B) (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f)
    (hgal : b4_IsGaloisCover G f) (y : C)
    (hy : f y ∉ b4_branchSet E E' f) : MulAction.stabilizer G y = ⊥ := by
  apply Subgroup.eq_bot_of_card_le
  have hn : ¬ 2 ≤ b4_ramIndex E E' f y := fun h ↦ hy ⟨y, h, rfl⟩
  have he := b4_ramIndex_galois hE hB hG f hf hgal y
  omega

end HodgeLean.Foundations.Program
