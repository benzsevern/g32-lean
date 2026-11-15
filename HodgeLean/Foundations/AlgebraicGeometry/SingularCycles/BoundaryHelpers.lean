import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.BoundaryDefs

noncomputable section
open CategoryTheory TopologicalSpace
open HodgeLean.Adapters
open scoped Classical
namespace AlgebraicGeometry.SingularCycles

theorem boundary_collected_apply {Z : Scheme} (b : Z →₀ ℚ) (p : Z) :
    collectedCycle b p = b p := by
  classical
  simp only [collectedCycle, Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply,
    Function.locallyFinsuppWithin.single_apply]
  by_cases hp : p ∈ b.support
  · rw [Finset.sum_eq_single p]
    · simp
    · intro q _ hqp
      simp [Ne.symm hqp]
    · exact fun h => (h hp).elim
  · have hz := Finsupp.notMem_support_iff.mp hp
    rw [hz]
    apply Finset.sum_eq_zero
    intro q hq
    have hqp : q ≠ p := fun h => hp (h ▸ hq)
    simp [Ne.symm hqp]

theorem boundary_collected_support {Z : Scheme} (b : Z →₀ ℚ) (p : Z) :
    p ∈ (collectedCycle b).support ↔ p ∈ b.support := by
  change collectedCycle b p ≠ 0 ↔ _
  rw [boundary_collected_apply, Finsupp.mem_support_iff]

theorem boundary_generic_component {Z : Scheme} (z : Z)
    (hz : Order.coheight z = 0) : closure ({z} : Set Z) ∈ irreducibleComponents Z := by
  let C := irreducibleComponent z
  have hC := isIrreducible_irreducibleComponent (x := z)
  have hclosed := isClosed_irreducibleComponent (x := z)
  have hgen := hC.isGenericPoint_genericPoint hclosed
  have hle : z ≤ hC.genericPoint :=
    Scheme.le_iff_specializes.mpr (hgen.specializes mem_irreducibleComponent)
  have hge : hC.genericPoint ≤ z := (Order.coheight_eq_zero.mp hz) hle
  have he : z = hC.genericPoint :=
    ((Scheme.le_iff_specializes.mp hge).antisymm
      (Scheme.le_iff_specializes.mp hle)).eq
  rw [he, hgen]
  exact irreducibleComponent_mem_irreducibleComponents z

set_option backward.isDefEq.respectTransparency false in
theorem boundary_generic_smooth {Z : Scheme.{0}}
    (q : Z ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFinitePresentation q]
    [IsReduced Z] (z : Z) (hz : Order.coheight z = 0) : z ∈ q.smoothLocus := by
  have := LocallyOfFiniteType.stalkMap q z
  rw [Scheme.Hom.mem_smoothLocus]
  algebraize [(q.stalkMap z).hom]
  let K' := (Spec.structureSheaf ℂ).presheaf.stalk (q z)
  let e : ℂ ≃ₐ[ℂ] K' := IsLocalization.atUnits _ (q z).asIdeal.primeCompl
    (fun x hx ↦ by aesop (add simp IsUnit.mem_submonoid_iff))
  have : Algebra.IsAlgebraic ℂ K' :=
    .of_injective e.symm.toAlgHom e.symm.injective
  let : Field K' := (e.toRingEquiv.symm.isField (Field.toIsField ℂ)).toField
  let : Field ((Spec (CommRingCat.of ℂ)).presheaf.stalk (q z)) := this
  have : PerfectField ((Spec (CommRingCat.of ℂ)).presheaf.stalk (q z)) :=
    Algebra.IsAlgebraic.perfectField (K := ℂ)
      (L := (Spec.structureSheaf ℂ).presheaf.stalk (q z))
  let : Field (Z.presheaf.stalk z) :=
    (isField_stalk_of_closure_mem_irreducibleComponents Z z
      (boundary_generic_component z hz)).toField
  exact Algebra.FormallySmooth.of_perfectField

end AlgebraicGeometry.SingularCycles
