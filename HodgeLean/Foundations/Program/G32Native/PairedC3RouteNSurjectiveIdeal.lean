import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNQuotientIdeal

/-! # Ideal base change for an arbitrary supplied principal quotient -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- The coefficient map on an ideal with its actual image as codomain. -/
def pairedC3ImageIdealMap (I : Ideal A) : I →ₗ[A] I.map (algebraMap A B) where
  toFun x := ⟨algebraMap A B x.1, Ideal.mem_map_of_mem _ x.2⟩
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' a x := by
    apply Subtype.ext
    change algebraMap A B (a * x.1) = a • algebraMap A B x.1
    rw [map_mul, Algebra.smul_def]

/-- The ideal map is onto for a surjective coefficient map. -/
theorem paired_c3_image_ideal_map_surjective
    (hf : Function.Surjective (algebraMap A B)) (I : Ideal A) :
    Function.Surjective (pairedC3ImageIdealMap (B := B) I) := by
  intro y
  obtain ⟨x, hx, he⟩ := (Ideal.mem_map_iff_of_surjective (algebraMap A B) hf).mp y.2
  exact ⟨⟨x, hx⟩, Subtype.ext he⟩

/-- A principal kernel regular on the original slice gives exactly the
scalar-relation kernel on its original ideal module. -/
theorem paired_c3_image_ideal_map_kernel (I : Ideal A) (r : A)
    (hk : RingHom.ker (algebraMap A B) = Ideal.span {r})
    (hr : IsSMulRegular (A ⧸ I) r) :
    LinearMap.ker (pairedC3ImageIdealMap (B := B) I) =
      Ideal.span {r} • (⊤ : Submodule A I) := by
  ext x
  change pairedC3ImageIdealMap (B := B) I x = 0 ↔ _
  rw [Subtype.ext_iff]
  change algebraMap A B x.1 = 0 ↔ _
  constructor
  · intro hx
    have hx' : x.1 ∈ Ideal.span {r} := by
      rw [← hk]
      exact hx
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hx'
    have hbI : b ∈ I := mem_of_isSMulRegular_quotient_of_smul_mem hr (by
      change r * b ∈ I
      rw [← hb]
      exact x.2)
    have he : x = r • (⟨b, hbI⟩ : I) := Subtype.ext hb
    rw [he]
    exact Submodule.smul_mem_smul (Ideal.subset_span (Set.mem_singleton _)) Submodule.mem_top
  · intro hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro a ha b _
      have hz : algebraMap A B a = 0 := by
        change a ∈ RingHom.ker (algebraMap A B)
        rwa [hk]
      change algebraMap A B (a * b.1) = 0
      rw [map_mul, hz, zero_mul]
    · intro a b ha hb
      change algebraMap A B (a.1 + b.1) = 0
      rw [map_add, ha, hb, add_zero]

/-- The supplied principal quotient identifies the scalar-extended ideal
with its actual image, over the original coefficient ring. -/
def pairedC3SurjectiveIdealTensorEquiv
    (hf : Function.Surjective (algebraMap A B)) (I : Ideal A) (r : A)
    (hk : RingHom.ker (algebraMap A B) = Ideal.span {r})
    (hr : IsSMulRegular (A ⧸ I) r) :
    (B ⊗[A] I) ≃ₗ[A] I.map (algebraMap A B) := by
  let e : (A ⧸ Ideal.span {r}) ≃ₐ[A] B :=
    (Ideal.quotientEquivAlgOfEq A hk.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A B) hf)
  exact (TensorProduct.congr e.symm.toLinearEquiv (LinearEquiv.refl A I)).trans
    ((TensorProduct.quotTensorEquivQuotSMul I (Ideal.span {r})).trans
      ((Submodule.quotEquivOfEq _ _ (paired_c3_image_ideal_map_kernel (B := B) I r hk hr).symm).trans
        ((pairedC3ImageIdealMap (B := B) I).quotKerEquivOfSurjective
          (paired_c3_image_ideal_map_surjective hf I))))

/-- The ideal base-change isomorphism is linear over the supplied chart
ring. No flatness of that ring over the ambient ring is assumed.
Source: Hartshorne, Algebraic Geometry, II.5 and II.8. -/
def pairedC3SurjectiveIdealBaseChange
    (hf : Function.Surjective (algebraMap A B)) (I : Ideal A) (r : A)
    (hk : RingHom.ker (algebraMap A B) = Ideal.span {r})
    (hr : IsSMulRegular (A ⧸ I) r) :
    (B ⊗[A] I) ≃ₗ[B] I.map (algebraMap A B) :=
  (pairedC3SurjectiveIdealTensorEquiv hf I r hk hr).extendScalarsOfSurjective hf

/-- The supplied-quotient isomorphism retains every original ideal element. -/
theorem paired_c3_surjective_ideal_baseChange_one_tmul
    (hf : Function.Surjective (algebraMap A B)) (I : Ideal A) (r : A)
    (hk : RingHom.ker (algebraMap A B) = Ideal.span {r})
    (hr : IsSMulRegular (A ⧸ I) r) (x : I) :
    pairedC3SurjectiveIdealBaseChange hf I r hk hr ((1 : B) ⊗ₜ[A] x) =
      ⟨algebraMap A B x.1, Ideal.mem_map_of_mem _ x.2⟩ := by
  change pairedC3SurjectiveIdealTensorEquiv hf I r hk hr (1 ⊗ₜ[A] x) = _
  simp only [pairedC3SurjectiveIdealTensorEquiv, LinearEquiv.trans_apply,
    TensorProduct.congr_tmul, AlgEquiv.toLinearEquiv_apply, LinearEquiv.refl_apply,
    map_one, TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul,
    Submodule.quotEquivOfEq_mk, LinearMap.quotKerEquivOfSurjective_apply_mk]
  rfl

end HodgeLean.Foundations.Program.G32Native
