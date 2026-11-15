import HodgeLean.Foundations.Program.G32PropFourSixPacked0451
import HodgeLean.Foundations.Program.G32PropFourSixPacked0440
import HodgeLean.Foundations.Program.G32PropFourSixPacked0448

/-! Finite character comparison interface. HC no distance; AV milestone no distance. -/
noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory HodgeLean.Papers
set_option maxHeartbeats 400000

/-- Actual conjugacy labels and generator traces for the printed table.
Source: G32 v0.16, Appendix A and Appendix B. -/
theorem g32cc_class_data_aux : ∃ D : g32p_familiesClassData,
      (∀ c, D.label (g32p_literalRepresentative c) = c) ∧
      (∀ g, IsConj g (g32p_literalRepresentative (D.label g))) ∧
      (∀ g, D.label (g * g) = g32p_familiesSquare (D.label g)) ∧
      (∀ j, D.label (g32p_classDatum j) = g32p_familyCWBranchClass j) ∧
      (∀ k c, (g32p_recordedInductionGenerators k).character
        (g32p_literalRepresentative c) =
          HurwitzPrymRex_ev g32h_omega (g32p_literalTraceValue k c)) := by
  exact ⟨g32p_integrationClassData, g32p_integrationLabel_rep,
    g32p_integrationLabel_conj, g32p_integrationLabel_square,
    g32p_integrationLabel_branch, g32p_recordedInductionGenerators_literalTrace_actual⟩

end HodgeLean.Foundations.Program
