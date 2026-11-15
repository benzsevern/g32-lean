import HodgeLean.Foundations.Program.SchoenCycleC1RationalSectionPullback
import HodgeLean.Foundations.Program.SchoenCycleC1RationalRestriction

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual restricted section map retains the original rational pullback
on every nonempty source chart inside an inverse-image open. -/
theorem s2e_c1_rational_section_pullbackLE
    {X Y : Scheme} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    (φ : Y.functionField →+* X.functionField)
    (hφ : ∀ (p : X) (r : Y.presheaf.stalk (f p)),
      φ (algebraMap (Y.presheaf.stalk (f p)) Y.functionField r) =
        algebraMap (X.presheaf.stalk p) X.functionField ((f.stalkMap p).hom r))
    (U : Y.Opens) (V : X.Opens) [Nonempty U] [Nonempty V]
    (hVU : V ≤ f ⁻¹ᵁ U) (s : Γ(Y, U)) :
    φ (Y.germToFunctionField U s) =
      X.germToFunctionField V (f.appLE U V hVU s) := by
  letI : Nonempty (f ⁻¹ᵁ U) := by
    obtain ⟨p, hp⟩ := ‹Nonempty V›
    exact ⟨⟨p, hVU hp⟩⟩
  rw [s2e_c1_rational_section_pullback f φ hφ U s]
  exact (s2e_c1_rational_section_restriction X (f ⁻¹ᵁ U) V hVU (f.app U s)).symm

end HodgeLean.Foundations.Program
