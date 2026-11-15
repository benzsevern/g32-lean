import HodgeLean.Foundations.Program.G32Native.PairedC3ResidualCoverComplex
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Coverage of the residual base by charts chosen on the slice -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native

/-- Charts chosen at complex points of the centre on the slice cover the
entire centre–slice intersection in the ambient scheme. This also covers
its nonclosed points. -/
theorem pairedC3_slice_charts_cover_base
    {Q X : Over (Spec ↧ℂ)} [LocallyOfFiniteType Q.hom]
    [LocallyOfFiniteType X.hom] (i : Q ⟶ X) [IsClosedImmersion i.left]
    (K : X.left.IdealSheafData) {ι : Type*} (U : ι → X.left.Opens)
    (h : ∀ q : ComplexPoint Q, q.underlying ∈ (K.comap i.left).support →
      ∃ j, (Point.map i q).underlying ∈ U j) :
    ((K ⊔ i.left.ker).support : Set X.left) ⊆ ⋃ j, (U j : Set X.left) := by
  letI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  apply pairedC3_closed_subset_iUnion_of_closed_points
    (K ⊔ i.left.ker).support.isClosed _ (fun j => (U j).isOpen)
  intro x hx hc
  have hx' : x ∈ (K.support : Set X.left) ∧
      x ∈ (i.left.ker.support : Set X.left) := by
    simpa only [Scheme.IdealSheafData.support_sup, TopologicalSpace.Closeds.coe_inf,
      Set.mem_inter_iff] using hx
  have hr : x ∈ Set.range i.left := by
    have hker := hx'.2
    rw [Scheme.Hom.support_ker, i.left.isClosedEmbedding.isClosed_range.closure_eq] at hker
    exact hker
  obtain ⟨q, hq⟩ := hr
  have hqc : IsClosed ({q} : Set Q.left) := by
    have he : i.left ⁻¹' ({x} : Set X.left) = {q} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, ← hq,
        i.left.isClosedEmbedding.injective.eq_iff]
    rw [← he]
    exact hc.preimage i.left.continuous
  let a : ComplexPoint Q := Over.homMk (pointOfClosedPoint Q.hom q hqc)
    (pointOfClosedPoint_comp Q.hom q hqc)
  have ha : a.underlying = q := pointOfClosedPoint_apply Q.hom q hqc _
  have haK : a.underlying ∈ (K.comap i.left).support := by
    rw [Scheme.IdealSheafData.support_comap]
    change i.left a.underlying ∈ K.support
    rw [ha, hq]
    exact hx'.1
  obtain ⟨j, hj⟩ := h a haK
  refine ⟨j, ?_⟩
  change i.left a.underlying ∈ (U j : Set X.left) at hj
  rw [ha, hq] at hj
  exact hj

#print axioms pairedC3_slice_charts_cover_base
end HodgeLean.Foundations.Program.G32Native
