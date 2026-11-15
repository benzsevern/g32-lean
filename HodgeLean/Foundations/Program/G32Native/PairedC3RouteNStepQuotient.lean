import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNStepRelations
import Mathlib.LinearAlgebra.Isomorphisms

/-! # The actual cyclic quotient of the strict-transform ideal -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.Program.G32Native
variable {B : Type*} [CommRing B]

/-- The strict-transform ideal modulo the total transform and its square. -/
abbrev pairedC3ChartIdealQuotient (K : Ideal B) (s v : B) :=
  ↥(K ⊔ Ideal.span {v} : Ideal B) ⧸
    ((show Submodule B B from ((K ⊔ Ideal.span {s * v}) ⊔ (K ⊔ Ideal.span {v}) ^ 2)).comap
      (K ⊔ Ideal.span {v}).subtype)

/-- The specified ratio supplies the cyclic generator of the chart quotient. -/
def pairedC3ChartIdealGenerator (K : Ideal B) (s v : B) :
    B →ₗ[B] pairedC3ChartIdealQuotient K s v :=
  LinearMap.toSpanSingleton B _
    (Submodule.Quotient.mk ⟨v, Submodule.mem_sup_right (Ideal.subset_span (Set.mem_singleton _))⟩)

/-- The generator has exactly the reduced intersection ideal as relations. -/
theorem paired_c3_chart_ideal_generator_kernel (K : Ideal B) (s v : B)
    (hv : ∀ b : B, v * b ∈ K → b ∈ K) :
    LinearMap.ker (pairedC3ChartIdealGenerator K s v) = K ⊔ Ideal.span {s, v} := by
  ext a
  change (Submodule.Quotient.mk (a •
    (⟨v, Submodule.mem_sup_right (Ideal.subset_span (Set.mem_singleton _))⟩ : ↥(K ⊔ Ideal.span {v} : Ideal B))) : pairedC3ChartIdealQuotient K s v) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  exact paired_c3_chart_generator_relations K s v a hv

/-- The transverse equations vanish in this quotient, leaving only the
class of the ratio coordinate. -/
theorem paired_c3_chart_ideal_generator_surjective (K : Ideal B) (s v : B) :
    Function.Surjective (pairedC3ChartIdealGenerator K s v) := by
  intro q
  obtain ⟨⟨a, ha⟩, rfl⟩ := Submodule.mkQ_surjective
    ((show Submodule B B from ((K ⊔ Ideal.span {s * v}) ⊔ (K ⊔ Ideal.span {v}) ^ 2)).comap
      (K ⊔ Ideal.span {v}).subtype) q
  obtain ⟨k, hk, w, hw, he⟩ := Submodule.mem_sup.mp ha
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp hw
  refine ⟨b, ?_⟩
  change Submodule.Quotient.mk (b •
    (⟨v, Submodule.mem_sup_right (Ideal.subset_span (Set.mem_singleton _))⟩ : ↥(K ⊔ Ideal.span {v} : Ideal B))) =
      Submodule.Quotient.mk ⟨a, ha⟩
  apply (Submodule.Quotient.eq _).mpr
  change b * v - a ∈ (K ⊔ Ideal.span {s * v}) ⊔ (K ⊔ Ideal.span {v}) ^ 2
  have he' : b * v - a = -k := by rw [← he]; ring
  rw [he']
  exact Submodule.mem_sup_left (Submodule.mem_sup_left (K.neg_mem hk))

/-- The chart cokernel is the structure module of the reduced intersection,
with no tensor factor; its generator remains the class of the ratio. -/
def pairedC3ChartIdealQuotientEquiv (K : Ideal B) (s v : B)
    (hv : ∀ b : B, v * b ∈ K → b ∈ K) :
    (B ⧸ (K ⊔ Ideal.span {s, v})) ≃ₗ[B] pairedC3ChartIdealQuotient K s v :=
  (Submodule.quotEquivOfEq _ _ (paired_c3_chart_ideal_generator_kernel K s v hv).symm).trans
    ((pairedC3ChartIdealGenerator K s v).quotKerEquivOfSurjective
      (paired_c3_chart_ideal_generator_surjective K s v))

end HodgeLean.Foundations.Program.G32Native
