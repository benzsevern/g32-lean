import HodgeLean.Foundations.QuotientDuality.PersistenceCokernelComposite

/-! Cokernel sequences retaining the specified literal composite map. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual cokernel sequence with the specified composite as its middle presentation. -/
def persistenceCokernelFactorSequence
    {C : Type*} [Category* C] [Abelian C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (hfg : f ≫ g = h) : ShortComplex C where
  X₁ := cokernel f
  X₂ := cokernel h
  X₃ := cokernel g
  f := cokernel.map f h (𝟙 X) g (by simpa using hfg)
  g := cokernel.map h g f (𝟙 Z) (by simpa using hfg.symm)
  zero := by
    apply (cancel_epi (cokernel.π f)).mp
    simp [cokernel.map, Category.assoc]

lemma persistence_cokernel_factor_sequence_shortExact
    {C : Type*} [Category* C] [Abelian C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (hfg : f ≫ g = h) [Mono g] :
    (persistenceCokernelFactorSequence f g h hfg).ShortExact := by
  cases hfg
  exact persistence_cokernel_composite_sequence_shortExact f g

end HodgeLean.Foundations.QuotientDuality
