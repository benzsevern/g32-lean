import HodgeLean.Foundations.Program.G32SelectedRealizationProjector

noncomputable section
open Manifold HodgeLean.Papers
open scoped ContDiff
namespace HodgeLean.Foundations.Program

section
variable {E C : Type} {G : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
  [Group G] [MulAction G C]

theorem g32y_subgroup_latticeAct (H : Subgroup G) (h : H) :
    b4_latticeAct E (C := C) h = b4_latticeAct E (C := C) (h : G) := rfl

theorem g32y_subgroup_cplxAct (H : Subgroup G) (h : H) :
    b4_cplxAct E (C := C) h = b4_cplxAct E (C := C) (h : G) := rfl

theorem g32y_subgroup_formAct (H : Subgroup G) (h : H) :
    b4_formAct E (C := C) h = b4_formAct E (C := C) (h : G) := rfl

end
end HodgeLean.Foundations.Program
