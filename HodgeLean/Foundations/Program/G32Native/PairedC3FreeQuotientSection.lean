import HodgeLean.Foundations.Program.G32Native.PairedConormalUnitLift

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Surjectivity on global sections gives a section for a free quotient.
The section is for the supplied arrow and the supplied quotient frame. -/
theorem paired_c3_free_quotient_section {X : Scheme.{0}} {M N : X.Modules}
    (p : M ⟶ N) (hp : Function.Surjective (p.app ⊤))
    (J : Type) (e : N ≅ SheafOfModules.free J) :
    ∃ s : N ⟶ M, s ≫ p = 𝟙 _ := by
  have hlift (j : J) := conormal_unit_lift_of_top_surjective p hp
    (SheafOfModules.ιFree j ≫ e.inv)
  choose l hl using hlift
  let a : SheafOfModules.free J ⟶ M := Sigma.desc l
  have ha : a ≫ p = e.inv := by
    apply Sigma.hom_ext
    intro j
    simpa only [a, Category.assoc, Sigma.ι_desc_assoc, SheafOfModules.ιFree] using hl j
  refine ⟨e.hom ≫ a, ?_⟩
  rw [Category.assoc, ha, e.hom_inv_id]

end HodgeLean.Foundations.Program.G32Native
