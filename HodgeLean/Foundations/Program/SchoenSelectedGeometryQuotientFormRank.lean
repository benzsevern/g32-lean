import HodgeLean.Foundations.Program.HurwitzPrym

noncomputable section
set_option maxHeartbeats 400000
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- Invariant holomorphic representation dimension equals the genus of the quotient curve. -/
theorem s0_quotient_form_rank
    {C Y G : Type} [Group G] [Finite G] [MulAction G C] [FaithfulSMul G C]
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [T2Space C] [CompactSpace C] [ConnectedSpace C]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]
    [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
    (hG : ∀ g : G, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hgal : b4_IsGaloisCover G f) :
    Module.finrank ℂ (Representation.invariants (b4_formRepresentation hG)) =
      Module.finrank ℂ (b3_HolForm ℂ Y) := by
  let e : Representation.invariants (b4_formRepresentation hG) ≃ₗ[ℂ]
      b4_invariantForms ℂ C G := {
    toFun := fun v ↦ ⟨v.val.val, v.val.property, (Submodule.mem_iInf _).mpr fun g ↦ by
      change b4_formAct ℂ g v.val.val - v.val.val = 0
      exact sub_eq_zero.mpr (congrArg Subtype.val (v.property g))⟩
    invFun := fun v ↦ ⟨⟨v.val, v.property.1⟩, fun g ↦ by
      apply Subtype.ext
      have hh := (Submodule.mem_iInf _).mp v.property.2 g
      change b4_formAct ℂ g v.val - v.val = 0 at hh
      exact sub_eq_zero.mp hh⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl }
  exact e.finrank_eq.trans (b4_invariantForms_galois
    (Module.finrank_self ℂ) (Module.finrank_self ℂ) hG f hf hgal)

#print axioms s0_quotient_form_rank
end HodgeLean.Foundations.Program
