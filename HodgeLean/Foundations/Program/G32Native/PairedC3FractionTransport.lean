import HodgeLean.Foundations.Program.G32Native.PairedC3NegativeFractionCoordinates

/-! # Representative data under graded-module transport -/
noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program.G32Native
open ProjSpaceCech
attribute [local instance] GradedModule.acg GradedModule.modR GradedModule.Frac.setoid
  GradedModule.sec.instAddCommGroup GradedModule.sec.instModule

/-- Graded-module transport preserves the actual fraction representative
inside the quotient of homogeneous fractions. -/
theorem paired_c3_fraction_eq_mk {R : Type} [CommRing R] {n : ℕ}
    {D E : GradedModule R n} (h : D = E) (I : Finset (Fin (n + 1)))
    (q : GradedModule.Frac D I) :
    pairedC3FractionEquivOfEq h I (GradedModule.sec.mk D I q) =
      GradedModule.sec.mk E I (h ▸ q) := by
  subst E
  rfl

#print axioms paired_c3_fraction_eq_mk
/-- Transport keeps the denominator exponents and the numerator, with
heterogeneous equality recording the possible change of carrier type. -/
theorem paired_c3_fraction_eq_data {R : Type} [CommRing R] {n : ℕ}
    {D E : GradedModule R n} (h : D = E) (I : Finset (Fin (n + 1)))
    (q : GradedModule.Frac D I) :
    (h ▸ q).denExp = q.denExp ∧ HEq (h ▸ q).num q.num := by
  subst E
  exact ⟨rfl, HEq.rfl⟩

#print axioms paired_c3_fraction_eq_data
end HodgeLean.Foundations.Program.G32Native
