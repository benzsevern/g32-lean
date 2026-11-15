import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNReesCokernel

/-! # The scale of the original Rees conormal cokernel generator -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Polynomial
namespace HodgeLean.Foundations.Program.G32Native
variable {A B : Type*} [CommRing A] [CommRing B]

/-- The original translated ratio generator maps to exactly its scalar
coefficient in the reduced intersection quotient. This fixes both sign
and scale before normalizing and gluing the chart classes.
Source: Hartshorne, Algebraic Geometry, II.7.13 and II.8. -/
theorem paired_c3_rees_conormal_cokernel_generator
    (f : A →+* B) (u v a : A) (t : B) (I : Ideal A)
    (hs : Function.Surjective (eval₂RingHom f t))
    (hk : RingHom.ker (eval₂RingHom f t) = Ideal.span {C v - X * C u})
    (ha : v - a * u ∈ I) (b : B) :
    pairedC3ReesConormalCokernelEquiv f u v a t I hs hk ha
      (Submodule.Quotient.mk ((I.map f ⊔ Ideal.span {t - f a}).toCotangent
        (b • (⟨t - f a, Submodule.mem_sup_right
          (Ideal.subset_span (Set.mem_singleton _))⟩ :
            ↥(I.map f ⊔ Ideal.span {t - f a} : Ideal B))))) =
      Ideal.Quotient.mk (I.map f ⊔ Ideal.span {f u, t - f a}) b := by
  unfold pairedC3ReesConormalCokernelEquiv
  rw [LinearEquiv.trans_apply, paired_conormal_cokernel_ideal_mk]
  apply (pairedC3ReesChartIdealEquiv f u v a t I hs hk ha).injective
  rw [LinearEquiv.apply_symm_apply]
  simp only [pairedC3ReesChartIdealEquiv, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl

#print axioms paired_c3_rees_conormal_cokernel_generator
end HodgeLean.Foundations.Program.G32Native
