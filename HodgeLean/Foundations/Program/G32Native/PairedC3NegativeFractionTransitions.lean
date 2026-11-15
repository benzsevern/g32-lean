import HodgeLean.Foundations.Program.G32Native.PairedC3NegativeFractionEvaluation

/-! # The actual dual-coordinate transition of negative fraction coefficients -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
namespace HodgeLean.Foundations.Program.G32Native
open ProjSpaceCech AlgebraicGeometry.ProjSpace Scheme.Modules.GlueOfCocycle
open AlgebraicCurves.Cohomology.Cech.Proofs
open OModulePresheaf_cechFinite_unit_of_isClosedImmersion_proj.AlgebraicGeometry.ProjSpace
attribute [local instance] GradedModule.acg GradedModule.modR GradedModule.Frac.setoid
  GradedModule.sec.instAddCommGroup GradedModule.sec.instModule
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The negative-fraction coefficients transform by the positive coordinate
ratio, exactly as evaluation coordinates on the native dual frame do. -/
theorem paired_c3_negative_coefficient_transition (R : Type) [CommRing R] (n : ℕ)
    {I : Finset (Fin (n + 1))} (i : Fin (n + 1)) (hi : i ∈ I)
    (j : Fin (n + 1)) (hj : j ∈ I)
    (z : GradedModule.sec (GradedModule.FD R n (-1)) I) :
    (show Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R), coordinateIntersection R n I) from
      pairedC3NegativeFractionCoefficient R n j hj z) =
      rO (coordinateIntersection_le_standardOpen R n hi) (coordinateRatioSection R n i j) *
        (show Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R), coordinateIntersection R n I) from
          pairedC3NegativeFractionCoefficient R n i hi z) := by
  obtain ⟨q, rfl⟩ := Quotient.exists_rep z
  let ci : Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R), coordinateIntersection R n I) :=
    pairedC3NegativeFractionCoefficient R n i hi (GradedModule.sec.mk _ I q)
  let cj : Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R), coordinateIntersection R n I) :=
    pairedC3NegativeFractionCoefficient R n j hj (GradedModule.sec.mk _ I q)
  let qi := pairedC3NegativeRaisedFraction R n i q
  let qj := pairedC3NegativeRaisedFraction R n j q
  let ui : Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R), coordinateIntersection R n I) :=
    unitFreeFractionEquiv R n I ⟨i, hi⟩ (GradedModule.sec.mk _ I qi)
  let uj : Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R), coordinateIntersection R n I) :=
    unitFreeFractionEquiv R n I ⟨j, hj⟩ (GradedModule.sec.mk _ I qj)
  have hci : ci = ui := paired_c3_negative_coefficient_mk R n i hi q
  have hcj : cj = uj := paired_c3_negative_coefficient_mk R n j hj q
  change cj = rO (coordinateIntersection_le_standardOpen R n hi) (coordinateRatioSection R n i j) * ci
  rw [hci, hcj]
  apply Subtype.ext
  funext x
  let A := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R
  let P : ProjectiveSpectrum A := x.val
  have : P.asHomogeneousIdeal.toIdeal.IsPrime := P.isPrime
  have hxi : (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) R) ∈
      P.asHomogeneousIdeal.toIdeal.primeCompl :=
    coordinateIntersection_le_standardOpen R n hi x.property
  let vi : HomogeneousLocalization A P.asHomogeneousIdeal.toIdeal.primeCompl := ui.val x
  let vj : HomogeneousLocalization A P.asHomogeneousIdeal.toIdeal.primeCompl := uj.val x
  let vr : HomogeneousLocalization A P.asHomogeneousIdeal.toIdeal.primeCompl :=
    (rO (coordinateIntersection_le_standardOpen R n hi) (coordinateRatioSection R n i j)).val x
  let p : MvPolynomial (Fin (n + 1)) R := q.num
  let den : P.asHomogeneousIdeal.toIdeal.primeCompl :=
    ⟨∏ k, (MvPolynomial.X k : MvPolynomial (Fin (n + 1)) R) ^ q.denExp k,
      coordinateMonomial_mem_of_supported R n _ I q.denExp q.hden
        (fun k hk => coordinateIntersection_le_standardOpen R n (i := k) hk x.property)⟩
  have hvi : vi.val = Localization.mk (S := P.asHomogeneousIdeal.toIdeal.primeCompl)
      (MvPolynomial.X i * p) den := unitFreeFractionEquiv_apply_mk_val R n I ⟨i, hi⟩ qi x
  have hvj : vj.val = Localization.mk (S := P.asHomogeneousIdeal.toIdeal.primeCompl)
      (MvPolynomial.X j * p) den := unitFreeFractionEquiv_apply_mk_val R n I ⟨j, hj⟩ qj x
  have hratio : vr.val =
      Localization.mk (S := P.asHomogeneousIdeal.toIdeal.primeCompl) (MvPolynomial.X j)
        ⟨(MvPolynomial.X i) ^ 1, pow_mem hxi 1⟩ := rfl
  apply HomogeneousLocalization.val_injective
  change vj.val = (vr * vi).val
  rw [HomogeneousLocalization.val_mul, hvi, hvj, hratio,
    Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, Submonoid.coe_mul, pow_one, one_mul]
  ring

#print axioms paired_c3_negative_coefficient_transition
end HodgeLean.Foundations.Program.G32Native
