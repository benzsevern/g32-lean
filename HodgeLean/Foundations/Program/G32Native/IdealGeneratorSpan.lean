import HodgeLean.Foundations.Program.G32Native.IdealModuleGenerators

/-! Ideal generators also generate the ideal as its own module. -/
noncomputable section
namespace HodgeLean.Foundations.Program

/-- A spanning family for an ideal generates its underlying module. -/
theorem g32l4_ideal_generators_span_top {R K : Type} [CommRing R] (I : Ideal R)
    (g : K → I) (hg : Ideal.span (Set.range (fun k => (g k : R))) = I) :
    Submodule.span R (Set.range g) = ⊤ := by
  apply Submodule.map_injective_of_injective I.injective_subtype
  rw [Submodule.map_span, ← Set.range_comp', Submodule.map_top, Submodule.range_subtype]
  exact hg

end HodgeLean.Foundations.Program
