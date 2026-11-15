import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.LinearAlgebra.Isomorphisms

/-! # A quotient presentation for an ideal's conormal cokernel -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program.G32Native
variable {B : Type*} [CommRing B]

/-- The ideal modulo an older ideal and its own square. -/
abbrev pairedConormalIdealQuotient (I J : Ideal B) :=
  J ⧸ (show Submodule B B from I ⊔ J ^ 2).comap J.subtype

/-- The original conormal projects to the ideal quotient. -/
def pairedConormalIdealProjection (I J : Ideal B) :
    J.Cotangent →ₗ[B] pairedConormalIdealQuotient I J := by
  refine (J • ⊤ : Submodule B J).liftQ
    ((show Submodule B B from I ⊔ J ^ 2).comap J.subtype).mkQ ?_
  intro a ha
  rw [Submodule.ker_mkQ]
  change a.1 ∈ I ⊔ J ^ 2
  apply Submodule.mem_sup_right
  apply (J.toCotangent_eq_zero a).mp
  exact (Submodule.Quotient.mk_eq_zero _).mpr ha

/-- The projection retains representatives in the actual ideal. -/
theorem paired_conormal_ideal_projection_mk (I J : Ideal B) (a : J) :
    pairedConormalIdealProjection I J (J.toCotangent a) =
      Submodule.Quotient.mk a := rfl

/-- Every ideal quotient class has a conormal representative. -/
theorem paired_conormal_ideal_projection_surjective (I J : Ideal B) :
    Function.Surjective (pairedConormalIdealProjection I J) := by
  intro z
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective
    ((show Submodule B B from I ⊔ J ^ 2).comap J.subtype) z
  exact ⟨J.toCotangent a, rfl⟩

/-- The kernel is exactly the image of the older ideal's natural conormal
map, with no choice of generators. -/
theorem paired_conormal_ideal_projection_kernel (I J : Ideal B) (h : I ≤ J) :
    LinearMap.ker (pairedConormalIdealProjection I J) =
      LinearMap.range (Ideal.mapCotangent I J (AlgHom.id B B) h) := by
  ext z
  obtain ⟨a, rfl⟩ := J.toCotangent_surjective z
  change pairedConormalIdealProjection I J (J.toCotangent a) = 0 ↔ _
  rw [paired_conormal_ideal_projection_mk, Submodule.Quotient.mk_eq_zero]
  constructor
  · intro ha
    obtain ⟨i, hi, w, hw, he⟩ := Submodule.mem_sup.mp ha
    refine ⟨I.toCotangent ⟨i, hi⟩, ?_⟩
    rw [Ideal.mapCotangent_toCotangent]
    apply (J.toCotangent_eq).mpr
    change i - a.1 ∈ J ^ 2
    change i + w = a.1 at he
    have he' : i - a.1 = -w := by rw [← he]; simp only [sub_add_eq_sub_sub, sub_self, zero_sub]
    rw [he']
    exact (J ^ 2).neg_mem hw
  · rintro ⟨z, hz⟩
    obtain ⟨i, rfl⟩ := I.toCotangent_surjective z
    rw [Ideal.mapCotangent_toCotangent] at hz
    have hm := (J.toCotangent_eq).mp hz
    change i.1 - a.1 ∈ J ^ 2 at hm
    change a.1 ∈ I ⊔ J ^ 2
    have he : a.1 = i.1 - (i.1 - a.1) := (sub_sub_cancel _ _).symm
    rw [he]
    exact (I ⊔ J ^ 2).sub_mem (Submodule.mem_sup_left i.2)
      (Submodule.mem_sup_right hm)

/-- The conormal cokernel is the ideal quotient, using the original
ideal-inclusion map rather than a separately chosen diagonal map. -/
def pairedConormalCokernelIdealEquiv (I J : Ideal B) (h : I ≤ J) :
    (J.Cotangent ⧸ LinearMap.range (Ideal.mapCotangent I J (AlgHom.id B B) h)) ≃ₗ[B]
      pairedConormalIdealQuotient I J :=
  (Submodule.quotEquivOfEq _ _ (paired_conormal_ideal_projection_kernel I J h).symm).trans
    ((pairedConormalIdealProjection I J).quotKerEquivOfSurjective
      (paired_conormal_ideal_projection_surjective I J))

/-- The quotient identification keeps the original conormal representative. -/
theorem paired_conormal_cokernel_ideal_mk (I J : Ideal B) (h : I ≤ J) (a : J) :
    pairedConormalCokernelIdealEquiv I J h
      (Submodule.Quotient.mk (J.toCotangent a)) = Submodule.Quotient.mk a := rfl

/-- Two normalized local representatives have the same actual cokernel
class whenever their difference comes from the original ideal. -/
theorem paired_conormal_cokernel_change_lift (I J : Ideal B) (h : I ≤ J)
    (a b : J) (hab : a.1 - b.1 ∈ I) :
    (Submodule.Quotient.mk (J.toCotangent a) :
      J.Cotangent ⧸ LinearMap.range (Ideal.mapCotangent I J (AlgHom.id B B) h)) =
        Submodule.Quotient.mk (J.toCotangent b) := by
  apply (pairedConormalCokernelIdealEquiv I J h).injective
  rw [paired_conormal_cokernel_ideal_mk, paired_conormal_cokernel_ideal_mk]
  apply (Submodule.Quotient.eq _).mpr
  exact Submodule.mem_sup_left hab

end HodgeLean.Foundations.Program.G32Native
