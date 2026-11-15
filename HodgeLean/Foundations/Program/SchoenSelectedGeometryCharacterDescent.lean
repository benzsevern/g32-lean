import Mathlib.Algebra.Category.Grp.Injective
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Data.Rat.Cast.CharZero

noncomputable section
namespace HodgeLean.Foundations.Program

/-- A rational character vanishing on a kernel extends across the corresponding homomorphism. -/
theorem s0_rational_character_descends
    {L M : Type} [AddCommGroup L] [AddCommGroup M]
    (g : L →+ M) (a : L →+ ℚ) (h : ∀ l, g l = 0 → a l = 0) :
    ∃ b : M →+ ℚ, b.comp g = a := by
  let G := g.toIntLinearMap
  let A := a.toIntLinearMap
  have hk : LinearMap.ker G ≤ LinearMap.ker A := h
  let d : LinearMap.range G →ₗ[ℤ] ℚ :=
    ((LinearMap.ker G).liftQ A hk).comp G.quotKerEquivRange.symm.toLinearMap
  obtain ⟨b, hb⟩ := (Module.Baer.of_divisible ℚ).extension_property
    (LinearMap.range G).subtype (LinearMap.range G).injective_subtype d
  refine ⟨b.toAddMonoidHom, ?_⟩
  ext l
  have hh := LinearMap.congr_fun hb (G.rangeRestrict l)
  change b (G l) = _ at hh
  change b (G l) = A l
  rw [hh]
  dsimp only [d, LinearMap.comp_apply, LinearEquiv.coe_coe]
  change (LinearMap.ker G).liftQ A hk (G.quotKerEquivRange.symm ⟨G l, G.mem_range_self l⟩) = A l
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

#print axioms s0_rational_character_descends
end HodgeLean.Foundations.Program
