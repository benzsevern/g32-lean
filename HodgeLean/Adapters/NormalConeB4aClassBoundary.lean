import HodgeLean.Adapters.NormalConeB4aClassSupport
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Support

/-! # Algebraic boundaries for the regular cycle locus

Route: the reduced closure of a point is integral. Its generic point is
smooth over the perfect ground field, so the singular remainder excludes
that point. Strict specialization then raises its ambient codimension.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry TopologicalSpace

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A component's generic point is outside the singular remainder of its
reduced closure, without projectivity or ambient integrality. -/
theorem a3b4a_classComponent_generic_not_mem_boundary
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType q] (x : Z) :
    x ∉ reducedClosedSingularRemainder q ⟨closure {x}, isClosed_closure⟩ := by
  let S : Closeds Z := ⟨closure {x}, isClosed_closure⟩
  let Y := reducedClosedSubscheme S
  let i := reducedClosedSubschemeι S
  letI : IsIntegral Y := inferInstanceAs (IsIntegral (cycleComponent Z x))
  have hg : i (genericPoint Y) = x := by
    have hr : Set.range (fun y : Y => i y) = closure ({x} : Set Z) :=
      range_reducedClosedSubschemeι S
    have hh : IsGenericPoint (i (genericPoint Y)) (closure (Set.range (fun y : Y => i y))) := by
      simpa only [Set.image_univ] using (genericPoint_spec Y).image i.continuous
    rw [hr, closure_closure] at hh
    exact hh.eq isGenericPoint_closure
  rintro ⟨y, hy, he⟩
  have hey : y = genericPoint Y := i.isClosedEmbedding.injective (he.trans hg.symm)
  subst y
  exact hy (reducedClosedStructureMap q S).genericPoint_mem_smoothLocus_of_perfectField

/-- Singular points on a component have ambient codimension at least one
higher than any lower bound at its generic point. -/
theorem a3b4a_classComponent_boundary_coheight
    {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType q]
    (x : Z) (c : ℕ) (hc : (c : ℕ∞) ≤ Order.coheight x)
    (z : Z) (hz : z ∈ reducedClosedSingularRemainder q ⟨closure {x}, isClosed_closure⟩) :
    ((c + 1 : ℕ) : ℕ∞) ≤ Order.coheight z := by
  have hzx : z ≤ x := Scheme.le_iff_specializes.mpr
    (specializes_iff_mem_closure.mpr (reducedClosedSingularRemainder_le q _ hz))
  have hlt : z < x := lt_iff_le_not_ge.mpr ⟨hzx, fun hxz => by
    have he : z = x := ((Scheme.le_iff_specializes.mp hxz).antisymm
      (Scheme.le_iff_specializes.mp hzx)).eq
    exact a3b4a_classComponent_generic_not_mem_boundary q x (he ▸ hz)⟩
  calc
    ((c + 1 : ℕ) : ℕ∞) = (c : ℕ∞) + 1 := by norm_cast
    _ ≤ Order.coheight x + 1 := by simpa only [add_comm] using add_le_add_right hc 1
    _ ≤ Order.coheight z := Order.coheight_add_one_le hlt

end HodgeLean.Adapters
