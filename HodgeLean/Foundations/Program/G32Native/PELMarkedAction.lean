import HodgeLean.Foundations.Program.G32Native.PELQuaternionCoordinates

noncomputable section
namespace HodgeLean.Foundations.Program.GeneralTypeIII

variable {D U V : Type*} [Ring D] [Algebra ℚ D]
  [AddCommGroup U] [Module ℚ U] [AddCommGroup V] [Module ℚ V]

/-- Transport the contravariant rational order action through a marking.
The opposite multiplication retains the pullback convention on H¹.
Source: Birkenhake–Lange, Complex Abelian Varieties, second edition, §§1.2, 5.5, 9.6. -/
def markedAction (ρ : D →ₐ[ℚ] (Module.End ℚ U)ᵐᵒᵖ) (m : U ≃ₗ[ℚ] V) :
    D →ₐ[ℚ] (Module.End ℚ V)ᵐᵒᵖ :=
  (m.conjAlgEquiv ℚ).op.toAlgHom.comp ρ

/-- A marking transports each retained operator on vectors.
Source: Birkenhake–Lange, Complex Abelian Varieties, second edition, §1.2. -/
theorem markedAction_apply (ρ : D →ₐ[ℚ] (Module.End ℚ U)ᵐᵒᵖ)
    (m : U ≃ₗ[ℚ] V) (d : D) (x : U) :
    (markedAction ρ m d).unop (m x) = m ((ρ d).unop x) := by
  simp [markedAction, LinearEquiv.conjAlgEquiv_apply]

/-- The Rosati identity is unchanged when both the action and polarization
are transported through the same rational marking.
Source: Birkenhake–Lange, Complex Abelian Varieties, second edition, §§5.2, 5.5. -/
theorem markedAction_rosati [Star D]
    (ρ : D →ₐ[ℚ] (Module.End ℚ U)ᵐᵒᵖ) (m : U ≃ₗ[ℚ] V)
    (E : LinearMap.BilinForm ℚ U)
    (hE : ∀ d x y, E ((ρ d).unop x) y = E x ((ρ (star d)).unop y))
    (d : D) (x y : V) :
    E (m.symm ((markedAction ρ m d).unop x)) (m.symm y) =
      E (m.symm x) (m.symm ((markedAction ρ m (star d)).unop y)) := by
  obtain ⟨x, rfl⟩ := m.surjective x
  obtain ⟨y, rfl⟩ := m.surjective y
  simpa only [markedAction_apply, LinearEquiv.symm_apply_apply] using hE d x y

/-- A retained quadratic generator is identified with its marked operator.
Source: Birkenhake–Lange, Complex Abelian Varieties, second edition, §§5.5, 9.6. -/
theorem markedAction_generator (ρ : D →ₐ[ℚ] (Module.End ℚ U)ᵐᵒᵖ)
    (m : U ≃ₗ[ℚ] V) (u : D) :
    (markedAction ρ m u).unop = m.conjAlgEquiv ℚ (ρ u).unop := rfl

/-- Fullness of a subalgebra action follows from its image containing the
faithful ambient action. This separates the commutant calculation from the
formal passage from an order action to an exact endomorphism presentation.
Source: Mumford, Abelian Varieties, §§19, 22; Birkenhake–Lange, §5.5. -/
theorem action_surjective_of_range {B T : Type*} [Ring B] [Algebra ℚ B]
    [Ring T] [Algebra ℚ T] (ι : D →ₐ[ℚ] B) (σ : B →ₐ[ℚ] T)
    (hσ : Function.Injective σ) (hrange : σ.range ≤ (σ.comp ι).range) :
    Function.Surjective ι := by
  intro b
  obtain ⟨d, hd⟩ := hrange (show σ b ∈ σ.range from ⟨b, rfl⟩)
  exact ⟨d, hσ hd⟩

#print axioms markedAction
#print axioms markedAction_apply
#print axioms markedAction_rosati
#print axioms markedAction_generator
#print axioms action_surjective_of_range
end HodgeLean.Foundations.Program.GeneralTypeIII
