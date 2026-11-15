import HodgeLean.Foundations.Program.G32Native.UnionConormalUnitOpenRestriction
import HodgeLean.Foundations.Program.G32Native.UnionConormalLocalExact

/-! # Unit epimorphy from local units -/
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Unit epimorphy can be checked on open neighborhoods in the source module scheme. -/
lemma unionConormal_unit_epi_of_open_neighborhoods
    {X Y : Scheme.{0}} (f : X ⟶ Y) (M : Y.Modules)
    (h : ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧
      Epi ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app
        ((Scheme.Modules.restrictFunctor U.ι).obj M))) :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) := by
  apply unionConormal_epi_of_open_neighborhoods
  intro y
  obtain ⟨U, hy, hU⟩ := h y
  haveI := hU
  exact ⟨U, hy, unionConormal_unit_restrict_epi f U M⟩

end HodgeLean.Foundations.Program.G32Native
