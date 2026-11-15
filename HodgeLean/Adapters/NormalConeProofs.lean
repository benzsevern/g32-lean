import HodgeLean.Adapters.NormalConeB1Regular

/-! # Affine normal cone proof obligations -/

noncomputable section
namespace HodgeLean.Adapters

theorem a3b1_parameter_polynomial_injective_aux
    (k R : Type*) [Field k] [CommRing R] [Algebra k R] (I : Ideal R)
    (p : Polynomial k) (hp : p ≠ 0) :
    Function.Injective (fun d : a3cc3_deformationAlgebra I =>
      a3b1_parameterMap k R I p * d) := by
  intro d e h
  apply Subtype.ext
  apply a3b1_toLaurent_map_mul_injective k R p hp
  simpa only [a3b1_parameterMap_coe, Subalgebra.coe_mul] using congrArg Subtype.val h

theorem a3b1_flat_aux
    (k R : Type*) [Field k] [CommRing R] [Algebra k R] (I : Ideal R) :
    letI : Algebra (Polynomial k) (a3cc3_deformationAlgebra I) :=
      (a3b1_parameterMap k R I).toAlgebra
    Module.Flat (Polynomial k) (a3cc3_deformationAlgebra I) := by
  letI : Algebra (Polynomial k) (a3cc3_deformationAlgebra I) :=
    (a3b1_parameterMap k R I).toAlgebra
  letI : Module.IsTorsionFree (Polynomial k) (a3cc3_deformationAlgebra I) :=
    ⟨by
      intro p hp
      change Function.Injective (fun d : a3cc3_deformationAlgebra I => p • d)
      change Function.Injective (fun d : a3cc3_deformationAlgebra I =>
        a3b1_parameterMap k R I p * d)
      exact a3b1_parameter_polynomial_injective_aux k R I p
        (by simpa only [isRegular_iff_ne_zero] using hp)⟩
  infer_instance

theorem a3b1_genericFiber_aux (R : Type*) [CommRing R] (I : Ideal R) :
    ∃ e : Localization.Away (a3cc3_parameter I) ≃+* LaurentPolynomial R,
      ∀ d : a3cc3_deformationAlgebra I,
        e (algebraMap _ (Localization.Away (a3cc3_parameter I)) d) =
          (d : LaurentPolynomial R) := by
  letI := a3b1_laurentAlgebra R I
  letI : IsLocalization.Away (a3cc3_parameter I) (LaurentPolynomial R) :=
    a3b1_laurent_isLocalization R I
  let e := IsLocalization.algEquiv (Submonoid.powers (a3cc3_parameter I))
    (Localization.Away (a3cc3_parameter I)) (LaurentPolynomial R)
  refine ⟨e.toRingEquiv, fun d => ?_⟩
  change e (algebraMap _ (Localization.Away (a3cc3_parameter I)) d) = _
  rw [e.commutes]
  rfl

theorem a3b1_specialFiber_aux (R : Type*) [CommRing R] (I : Ideal R) :
    ∃ e : a3cc3_specialFiber I ≃ₐ[R] a3cc3_normalConeRing I,
      ∀ a : I, e (Ideal.Quotient.mk _ (a3b1_fractionGenerator R I a)) =
        a3b1_coneMonomial R I 1 ⟨a.val, by simpa only [pow_one] using a.property⟩ := by
  refine ⟨a3b1_specialFiberAlgEquiv R I, fun a => ?_⟩
  apply a3b1_normalConeToSpecialFiber_injective R I
  rw [a3b1_normalConeToSpecialFiber_monomial_one]
  change (a3b1_specialFiberAlgEquiv R I).symm
    ((a3b1_specialFiberAlgEquiv R I)
      (Ideal.Quotient.mk _ (a3b1_fractionGenerator R I a))) = _
  exact (a3b1_specialFiberAlgEquiv R I).symm_apply_apply _

theorem a3b1_regularSequence_normalBundle_aux
    (R : Type*) [CommRing R] (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) :
    ∃ e : MvPolynomial (Fin rs.length) (R ⧸ Ideal.ofList rs) ≃ₐ[R]
        a3cc3_normalConeRing (Ideal.ofList rs),
      ∀ j : Fin rs.length, e (MvPolynomial.X j) =
        a3b1_coneMonomial R (Ideal.ofList rs) 1
          ⟨rs.get j, by
            rw [pow_one]
            exact Ideal.subset_span (List.get_mem rs j)⟩ := by
  let e := AlgEquiv.ofBijective (a3b1_regularSequence_normalConeMap R rs)
    (a3b1_regularSequence_normalConeMap_bijective R rs hreg)
  refine ⟨e.restrictScalars R, fun j ↦ ?_⟩
  exact a3b1_regularSequence_normalConeMap_X R rs j

end HodgeLean.Adapters
