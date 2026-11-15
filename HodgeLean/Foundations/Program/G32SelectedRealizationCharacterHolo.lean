import HodgeLean.Foundations.Program.G32SelectedRealizationLinearAge

noncomputable section
open Manifold TopologicalSpace HodgeLean.Papers HodgeLean.RealDefs HodgeLean.Foundations
open scoped ContDiff
namespace HodgeLean.Foundations.Program

theorem g32y_character_holomorphic_dimension
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {C : Type} [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    {G : Type} [Group G] [Fintype G] [MulAction G C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C] [FaithfulSMul G C]
    (hE : Module.finrank ℂ E = 1)
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (fun x : C ↦ g • x))
    (h : C → G) (hh : ∀ x, b4_IsRotGen E x (h x))
    (χ : G →* ℂˣ) (hχ : ∃ g, χ g ≠ 1) :
    (Module.finrank ℂ ↥(b3_HolForm E C ⊓
      ⨅ g, Module.End.eigenspace (b4_formAct E (C := C) g) (χ g : ℂ)) : ℝ) =
      (Module.finrank ℂ (Representation.invariants (b4_formRepresentation hG)) : ℝ) - 1 +
        ∑ᶠ x : C, (Nat.card (MulAction.stabilizer G x) : ℝ) / Fintype.card G *
          g32h_angle (χ (h x) : ℂ) := by
  let ρ : Representation ℂ G ℂ := (papersLinRep χ).ρ
  have hm := g32y_chevalleyWeil_holo hE hG h hh ρ
    (g32y_linear_character_invariants χ hχ)
  have hdim := g32y_linear_character_multiplicity χ
    (fun g ↦ b4_formAct E (C := C) g) (b3_HolForm E C)
  have hage (g : G) : b4_age (ρ g) = g32h_angle (χ g : ℂ) := g32y_scalar_age _
  change Module.finrank ℂ (b4_HomG ρ
    (fun g ↦ b4_formAct E (C := C) g) (b3_HolForm E C)) = _ at hdim
  rw [hdim] at hm
  simpa only [Module.finrank_self, Nat.cast_one, one_mul, hage] using hm

end HodgeLean.Foundations.Program
