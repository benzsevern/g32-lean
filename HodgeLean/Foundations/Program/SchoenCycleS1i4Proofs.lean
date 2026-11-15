import HodgeLean.Foundations.Program.SchoenCycleS1i4PreProofs
import HodgeLean.Foundations.Program.SchoenCycleRegularChartAnalytic
import HodgeLean.Foundations.Program.SchoenCyclePreparedResidues

/-! # Analytic unit comparison detects actual principal stalk ideals
First infrastructure part. HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Adapters
open scoped Classical BigOperators
namespace HodgeLean.Foundations.Program

/-- Analytic unit comparison detects actual principal stalk ideals.
Source: Serre, Géométrie algébrique et géométrie analytique,
Annales de l’Institut Fourier 6 (1956), §2, no. 6, Proposition 3 and Corollary 1, printed pp. 9–11. -/
theorem s2e_analytic_unit_descends_principal_ideal_aux
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (U : X.left.Opens) (hp : p.underlying ∈ U)
    (s t : Γ(X.left, U)) (η : (Fin d → ℂ) → ℂ)
    (hη : AnalyticAt ℂ η 0) (hη0 : η 0 ≠ 0)
    (he : (fun z => Point.evaluate U s ((ComplexPoint.localChart X d p).symm
        (ComplexPoint.localChart X d p p + z))) =ᶠ[nhds 0]
      (fun z => η z * Point.evaluate U t ((ComplexPoint.localChart X d p).symm
        (ComplexPoint.localChart X d p p + z)))) :
    Ideal.span {X.left.presheaf.germ U p.underlying hp s} =
      Ideal.span {X.left.presheaf.germ U p.underlying hp t} := by
  have horder (N : ℕ) (a : X.left.presheaf.stalk p.underlying)
      (ha : s2e_stalk_nativeAnalyticGerm X d p a ∈
        IsLocalRing.maximalIdeal (s2e_nativeAnalyticGermRing d) ^ N) :
      a ∈ IsLocalRing.maximalIdeal (X.left.presheaf.stalk p.underlying) ^ N :=
    s2e_s1i4_order_reflection_aux X d p N
      (s2e_s1i4_algebraic_representatives_aux X d p N) a ha
  have hflat := s2e_s1i4_native_flat_aux X d p
    (s2e_s1i4_native_noetherian_aux d) (s2e_s1i4_extended_maximal_aux X d p)
    (s2e_actualAnalytic_adic_stalkMap_of X d p)
    (s2e_s1i4_adic_bijective_aux X d p horder)
  exact s2e_s1i4_native_assembly_aux X d p
    (s2e_s1i4_native_faithfullyFlat_aux X d p hflat) U hp s t η hη hη0 he

end HodgeLean.Foundations.Program
