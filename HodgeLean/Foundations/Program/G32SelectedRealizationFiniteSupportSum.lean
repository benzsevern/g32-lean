import HodgeLean.Foundations.Program.G32SelectedRealizationProjector

noncomputable section
namespace HodgeLean.Foundations.Program

theorem g32y_finsum_eq_sum_injective {I X R : Type*} [Fintype I] [AddCommMonoid R]
    (p : I → X) (hp : Function.Injective p) (w : X → R)
    (hw : ∀ x, x ∉ Set.range p → w x = 0) :
    ∑ᶠ x, w x = ∑ i, w (p i) := by
  classical
  have hi : (Set.range p).indicator w = w := by
    funext x
    by_cases hx : x ∈ Set.range p
    · simp [hx]
    · simp [hx, hw x hx]
  calc
    _ = ∑ᶠ x ∈ Set.range p, w x := by rw [finsum_mem_def, hi]
    _ = ∑ᶠ i, w (p i) := finsum_mem_range hp
    _ = _ := finsum_eq_sum_of_fintype _

end HodgeLean.Foundations.Program
