import HodgeLean.Foundations.Program.G32Native.FiniteIntersectionStalks
import Mathlib.Basic.Complex.Basic
import HodgeLean.Ported.Hironaka.Scheme.Snc.Defs
import HodgeLean.Ported.Hironaka.Scheme.Smooth.AdaptedCoordinates
import HodgeLean.Ported.Hironaka.Algebra.RegularSmooth.QuotientRegular

/-! Regular quotient stalks and their codimensions for finite SNC intersections. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry IsLocalRing
namespace HodgeLean.Foundations.Program

/-- Every finite SNC intersection has regular quotient stalk and its labelled codimension. -/
theorem g32l4_snc_intersection_stalk
    (B : Over (Spec ↧ℂ)) [Smooth B.hom]
    (E : Scheme.DivisorFamily B.left) (hE : E.IsSnc)
    (J : Finset E.ι) (x : B.left) (hx : x ∈ (J.sup E.component).support) :
    IsRegularLocalRing (B.left.presheaf.stalk x ⧸ (J.sup E.component).stalkIdeal x) ∧
      ringKrullDim (B.left.presheaf.stalk x ⧸ (J.sup E.component).stalkIdeal x) + J.card =
        ringKrullDim (B.left.presheaf.stalk x) := by
  classical
  letI : IsRegularLocalRing (B.left.presheaf.stalk x) := isRegularLocalRing_stalk B.hom x
  have hbranches := (g32l4_mem_support_finset_sup E.component J x).mp hx
  obtain ⟨m, z, hz, c, hc, hD⟩ := hE.2 x
  let a : J → Fin m := fun i => c ⟨i.val, hbranches i.val i.property⟩
  let f : J → B.left.presheaf.stalk x := fun i => z (a i)
  have ha : Function.Injective a := by
    intro i j hij
    apply Subtype.ext
    have h := hc hij
    exact congrArg (fun k : {i : E.ι // x ∈ (E.component i).support} => k.val) h
  have hf : ∀ i, f i ∈ maximalIdeal (B.left.presheaf.stalk x) :=
    fun i => x_mem_maximalIdeal_of_span_eq z hz.1.symm (a i)
  obtain ⟨b, hb⟩ := exists_basis_cotangentSpace_of_span_eq z hz.1.symm hz.2
  have hli : LinearIndependent (ResidueField (B.left.presheaf.stalk x))
      (fun i => (maximalIdeal (B.left.presheaf.stalk x)).toCotangent ⟨f i, hf i⟩) := by
    have h := b.linearIndependent.comp a ha
    simpa only [Function.comp_def, hb] using h
  have hgen : Ideal.span (Set.range f) = (J.sup E.component).stalkIdeal x := by
    rw [g32l4_stalkIdeal_finset_sup]
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      have hi : f i ∈ (E.component i.val).stalkIdeal x := by
        rw [hD ⟨i.val, hbranches i.val i.property⟩]
        exact Ideal.subset_span (Set.mem_singleton _)
      exact (Finset.le_sup (f := fun i => (E.component i).stalkIdeal x)
        (b := i.val) i.property) hi
    · apply Finset.sup_le
      intro i hi
      rw [hD ⟨i, hbranches i hi⟩]
      apply Ideal.span_le.mpr
      exact Set.singleton_subset_iff.mpr (Ideal.subset_span ⟨⟨i, hi⟩, rfl⟩)
  have h := IsRegularLocalRing.quotient_span_range_of_linearIndependent f hf hli
  rw [hgen] at h
  simpa only [Fintype.card_coe] using h

end HodgeLean.Foundations.Program
