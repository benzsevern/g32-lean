import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.Regular.RegularSequence

/-! # Ideal base change across a relation regular on the slice -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native
variable {A : Type*} [CommRing A]

/-- The original ideal map into its image after imposing one relation. -/
def pairedC3QuotientIdealMap (I : Ideal A) (r : A) :
    I →ₗ[A] I.map (Ideal.Quotient.mk (Ideal.span {r})) where
  toFun x := ⟨Ideal.Quotient.mk _ x.1, Ideal.mem_map_of_mem _ x.2⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' a x := Subtype.ext (map_mul _ _ _)

/-- Surjectivity of the original coefficient quotient gives surjectivity
on the actual ideal modules. -/
theorem paired_c3_quotient_ideal_map_surjective (I : Ideal A) (r : A) :
    Function.Surjective (pairedC3QuotientIdealMap I r) := by
  intro y
  obtain ⟨x, hx, he⟩ := (Ideal.mem_map_iff_of_surjective
    (Ideal.Quotient.mk (Ideal.span {r})) Ideal.Quotient.mk_surjective).mp y.2
  exact ⟨⟨x, hx⟩, Subtype.ext he⟩

/-- Regularity of the relation on the original slice identifies the
ideal-map kernel with the scalar relation submodule. -/
theorem paired_c3_quotient_ideal_map_kernel (I : Ideal A) (r : A)
    (hr : IsSMulRegular (A ⧸ I) r) :
    LinearMap.ker (pairedC3QuotientIdealMap I r) =
      Ideal.span {r} • (⊤ : Submodule A I) := by
  ext x
  change pairedC3QuotientIdealMap I r x = 0 ↔ _
  rw [Subtype.ext_iff]
  change Ideal.Quotient.mk (Ideal.span {r}) x.1 = 0 ↔ _
  constructor
  · intro hx
    have hx' := Ideal.Quotient.eq_zero_iff_mem.mp hx
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hx'
    have hbI : b ∈ I := mem_of_isSMulRegular_quotient_of_smul_mem hr (by
      change r * b ∈ I
      rw [← hb]
      exact x.2)
    have he : x = r • (⟨b, hbI⟩ : I) := Subtype.ext hb
    rw [he]
    exact Submodule.smul_mem_smul (Ideal.subset_span (Set.mem_singleton _)) (Submodule.mem_top)
  · intro hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro a ha b _
      change Ideal.Quotient.mk (Ideal.span {r}) (a * b.1) = 0
      rw [map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_mul]
    · intro a b ha hb
      change Ideal.Quotient.mk (Ideal.span {r}) (a.1 + b.1) = 0
      rw [map_add, ha, hb, add_zero]

/-- Scalar extension of the original ideal is its actual image ideal
across a principal relation regular on the slice. Ambient flatness is not
assumed.
Source: Hartshorne, Algebraic Geometry, II.5 and II.8. -/
def pairedC3QuotientIdealTensorEquiv (I : Ideal A) (r : A)
    (hr : IsSMulRegular (A ⧸ I) r) :
    ((A ⧸ Ideal.span {r}) ⊗[A] I) ≃ₗ[A]
      I.map (Ideal.Quotient.mk (Ideal.span {r})) :=
  (TensorProduct.quotTensorEquivQuotSMul I (Ideal.span {r})).trans
    ((Submodule.quotEquivOfEq _ _ (paired_c3_quotient_ideal_map_kernel I r hr).symm).trans
      ((pairedC3QuotientIdealMap I r).quotKerEquivOfSurjective
        (paired_c3_quotient_ideal_map_surjective I r)))

/-- The same original ideal comparison is linear over the chart quotient. -/
def pairedC3QuotientIdealBaseChange (I : Ideal A) (r : A)
    (hr : IsSMulRegular (A ⧸ I) r) :
    ((A ⧸ Ideal.span {r}) ⊗[A] I) ≃ₗ[A ⧸ Ideal.span {r}]
      I.map (Ideal.Quotient.mk (Ideal.span {r})) :=
  (pairedC3QuotientIdealTensorEquiv I r hr).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective

/-- Each original ideal element maps to its actual coefficient image under
the quotient ideal base-change isomorphism. -/
theorem paired_c3_quotient_ideal_baseChange_one_tmul (I : Ideal A) (r : A)
    (hr : IsSMulRegular (A ⧸ I) r) (x : I) :
    pairedC3QuotientIdealBaseChange I r hr ((1 : A ⧸ Ideal.span {r}) ⊗ₜ[A] x) =
      ⟨Ideal.Quotient.mk _ x.1, Ideal.mem_map_of_mem _ x.2⟩ := by
  change pairedC3QuotientIdealTensorEquiv I r hr (1 ⊗ₜ[A] x) = _
  simp only [pairedC3QuotientIdealTensorEquiv, LinearEquiv.trans_apply,
    TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl

end HodgeLean.Foundations.Program.G32Native
