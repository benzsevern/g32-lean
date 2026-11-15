import HodgeLean.Foundations.QuotientDuality.PersistenceCollapse
import Mathlib.Topology.LocalAtTarget

/-! The actual quotient projection away from its collapsed locus. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Topology
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_collapse_locus_preimage {X : Type*} (A : Set X) :
    (Quotient.mk (persistenceCollapseSetoid A)) ⁻¹'
      ((Quotient.mk (persistenceCollapseSetoid A)) '' A) = A := by
  ext x
  constructor
  · rintro ⟨a, ha, heq⟩
    rcases (persistence_collapse_eq_iff A a x).mp heq with rfl | ⟨_, hx⟩
    · exact ha
    · exact hx
  · intro hx
    exact ⟨x, hx, rfl⟩

lemma persistence_collapse_complement_restriction_isHomeomorph
    {X : Type*} [TopologicalSpace X] (A : Set X) (hA : IsClosed A) :
    IsHomeomorph
      (((Quotient.mk (persistenceCollapseSetoid A)) '' A)ᶜ.restrictPreimage
        (Quotient.mk (persistenceCollapseSetoid A))) := by
  let q := Quotient.mk (persistenceCollapseSetoid A)
  let V := (q '' A)ᶜ
  apply isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
  refine ⟨continuous_quotient_mk'.restrictPreimage,
    (persistence_collapse_isClosedMap A hA).restrictPreimage V, ?_, ?_⟩
  · intro x y heq
    apply Subtype.ext
    have hxy : q x.val = q y.val := congrArg Subtype.val heq
    rcases (persistence_collapse_eq_iff A x.val y.val).mp hxy with heq | ⟨hx, _⟩
    · exact heq
    · exact (x.property ⟨x.val, hx, rfl⟩).elim
  · intro y
    obtain ⟨x, hx⟩ := Quotient.mk_surjective y.val
    change q x = y.val at hx
    exact ⟨⟨x, by change q x ∈ V; rw [hx]; exact y.property⟩, Subtype.ext hx⟩

/-- The actual quotient projection as a homeomorphism on the locus complements. -/
def persistenceCollapseComplementHomeomorph
    {X : Type*} [TopologicalSpace X] (A : Set X) (hA : IsClosed A) :
    ↥(Aᶜ : Set X) ≃ₜ ↥(((Quotient.mk (persistenceCollapseSetoid A)) '' A)ᶜ) :=
  (Homeomorph.setCongr (by
    rw [Set.preimage_compl, persistence_collapse_locus_preimage])).trans
    (IsHomeomorph.homeomorph _
      (persistence_collapse_complement_restriction_isHomeomorph A hA))

lemma persistence_collapse_neighbourhood_preimage
    {X : Type*} (A U : Set X) (hAU : A ⊆ U) :
    (Quotient.mk (persistenceCollapseSetoid A)) ⁻¹'
      ((Quotient.mk (persistenceCollapseSetoid A)) '' U) = U := by
  ext x
  constructor
  · rintro ⟨u, hu, heq⟩
    rcases (persistence_collapse_eq_iff A u x).mp heq with rfl | ⟨_, hx⟩
    · exact hu
    · exact hAU hx
  · intro hx
    exact ⟨x, hx, rfl⟩

lemma persistence_collapse_neighbourhood_isOpen
    {X : Type*} [TopologicalSpace X] (A U : Set X) (hAU : A ⊆ U)
    (hU : IsOpen U) :
    IsOpen ((Quotient.mk (persistenceCollapseSetoid A)) '' U) := by
  apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
  change IsOpen ((Quotient.mk (persistenceCollapseSetoid A)) ⁻¹'
    ((Quotient.mk (persistenceCollapseSetoid A)) '' U))
  rw [persistence_collapse_neighbourhood_preimage A U hAU]
  exact hU

end HodgeLean.Foundations.QuotientDuality
