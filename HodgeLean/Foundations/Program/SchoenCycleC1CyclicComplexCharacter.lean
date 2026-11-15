import HodgeLean.Foundations.Program.SchoenCycleC1FaithfulCharacterRoot
import Mathlib.RingTheory.RootsOfUnity.Complex

noncomputable section
namespace HodgeLean.Foundations.Program

/-- A finite cyclic group admits a faithful complex character, retaining a
generator whose character value has the full original group order. -/
theorem s2e_c1_cyclic_complex_character
    (G : Type*) [Group G] [Finite G] [IsCyclic G] :
    ∃ (χ : G →* ℂˣ) (g : G), Function.Injective χ ∧
      orderOf g = Nat.card G ∧ IsPrimitiveRoot (χ g : ℂ) (Nat.card G) := by
  letI : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  let E : G ≃* rootsOfUnity (Nat.card G) ℂ :=
    mulEquivOfCyclicCardEq (Complex.card_rootsOfUnity (Nat.card G)).symm
  let χ : G →* ℂˣ := (rootsOfUnity (Nat.card G) ℂ).subtype.comp E.toMonoidHom
  have hχ : Function.Injective χ := Subtype.val_injective.comp E.injective
  obtain ⟨g, hg⟩ := s2e_c1_faithful_character_primitive_value χ hχ
  refine ⟨χ, g, hχ, ?_, hg⟩
  let f : G →* ℂ := (Units.coeHom ℂ).comp χ
  exact (orderOf_injective f (Units.val_injective.comp hχ) g).symm.trans hg.eq_orderOf.symm

end HodgeLean.Foundations.Program
