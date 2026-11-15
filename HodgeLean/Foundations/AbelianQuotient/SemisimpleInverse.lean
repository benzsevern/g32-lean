import HodgeLean.Foundations.Program.MilneFactorsHodgeSemisimple
import HodgeLean.Foundations.AbelianQuotient.H1Helpers

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Adapters
open scoped CategoryTheory.MonObj
namespace HodgeLean.Foundations.AbelianQuotient

/-- Every element of a semisimple ring has an inner inverse. -/
theorem exists_inner_inverse {R : Type*} [Ring R] [IsSemisimpleRing R] (a : R) :
    ∃ b : R, a * b * a = a := by
  obtain ⟨e, he, heq⟩ := IsSemisimpleRing.ideal_eq_span_idempotent (Ideal.span ({a} : Set R))
  have hea : e ∈ Ideal.span ({a} : Set R) := by
    rw [heq]
    exact Ideal.subset_span (Set.mem_singleton e)
  have hae : a ∈ Ideal.span ({e} : Set R) := by
    rw [← heq]
    exact Ideal.subset_span (Set.mem_singleton a)
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hea
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hae
  refine ⟨b, ?_⟩
  calc
    a * b * a = a * (b * a) := mul_assoc _ _ _
    _ = a * e := by rw [hb]
    _ = a := by rw [← hc, mul_assoc, he]

set_option maxRecDepth 2000 in
/-- A positive multiple of an algebraic endomorphism has an algebraic inner inverse. -/
theorem algebraic_inner_inverse (X : Variety) (u : AbelianEnd X.X) :
    ∃ (N : ℕ) (v : AbelianEnd X.X), 0 < N ∧
      u.hom ≫ v.hom ≫ u.hom = u.hom ^ (N : ℤ) := by
  obtain ⟨pol, hpol⟩ := Program.m1_exists_positive_polarization X.X
  letI := Program.m1_hodgeEnd_semisimple_of_polarization X.X hpol
  let U : hodgeEndH1 X.X := ⟨abelianEndAction X.X u, spec_abelianEndAction_hodge X.X u⟩
  obtain ⟨V, hV⟩ := exists_inner_inverse U
  obtain ⟨N, hN, v, hv⟩ := spec_exists_abelianEnd_of_hodge X.X (gagam_hAlg X.X)
    V.val V.property.1
  refine ⟨N, v, hN, ?_⟩
  have hh : (⟨u.hom ≫ v.hom ≫ u.hom, inferInstance⟩ : AbelianEnd X.X) =
      ⟨u.hom ≫ (multiplication X N).hom, inferInstance⟩ := by
    apply spec_abelianEndAction_injective X.X
    change homPullback (u.hom ≫ v.hom ≫ u.hom) 1 = homPullback (u.hom ≫ (multiplication X N).hom) 1
    rw [spec_homPullback_comp, spec_homPullback_comp, spec_homPullback_comp,
      multiplication_nat_hom, spec_homPullback_zpow, spec_homPullback_id,
      Int.cast_natCast, LinearMap.comp_smul, LinearMap.comp_id]
    change (abelianEndAction X.X u).comp
      ((abelianEndAction X.X v).comp (abelianEndAction X.X u)) = _
    rw [hv, LinearMap.smul_comp, LinearMap.comp_smul]
    congr 1
    have hV' := congrArg Subtype.val hV
    change ((abelianEndAction X.X u).comp V.val).comp (abelianEndAction X.X u) =
      abelianEndAction X.X u at hV'
    simpa only [LinearMap.comp_assoc, abelianEndAction, complexPointPullback, homPullback] using hV'
  have hhom := congrArg AbelianEnd.hom hh
  change u.hom ≫ v.hom ≫ u.hom = u.hom ≫ (multiplication X N).hom at hhom
  rw [multiplication_nat_hom, GrpObj.comp_zpow, Category.comp_id] at hhom
  exact hhom

end HodgeLean.Foundations.AbelianQuotient
