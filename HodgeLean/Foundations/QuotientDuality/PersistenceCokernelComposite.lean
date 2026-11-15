import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! Actual cokernel sequences for the composable inclusion maps. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.QuotientDuality

/-- The canonical cokernel sequence for the literal composable maps. -/
def persistenceCokernelCompositeSequence
    {C : Type*} [Category* C] [Abelian C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    ShortComplex C := (kernelCokernelCompSequence.snakeInput f g).L₃

lemma persistence_cokernel_composite_sequence_exact
    {C : Type*} [Category* C] [Abelian C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (persistenceCokernelCompositeSequence f g).Exact :=
  (kernelCokernelCompSequence.snakeInput f g).L₃_exact

lemma persistence_cokernel_composite_sequence_shortExact
    {C : Type*} [Category* C] [Abelian C] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Mono g] :
    (persistenceCokernelCompositeSequence f g).ShortExact := by
  let S := kernelCokernelCompSequence.snakeInput f g
  have hδ : S.δ = 0 := (isZero_kernel_of_mono g).eq_of_src _ _
  have hm : Mono S.L₃.f := (S.L₂'.exact_iff_mono hδ).mp S.L₂'_exact
  exact {
    exact := S.L₃_exact
    mono_f := hm
    epi_g := by
      exact inferInstanceAs (Epi ((kernelCokernelCompSequence f g).map' 4 5)) }

end HodgeLean.Foundations.QuotientDuality
