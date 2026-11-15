import HodgeLean.Foundations.Program.SchoenCycleS1i4Proofs

/-! # Analytic unit comparison detects actual principal stalk ideals
Implication from the explicit inputs to the first infrastructure part.
Further comparison steps are listed in docs/specs/s2e-s1bci.md.
HC no distance; AV milestone no distance.
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
theorem s2e_analytic_unit_descends_principal_ideal
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (p : ComplexPoint X) (U : X.left.Opens) (hp : p.underlying ∈ U)
    (s t : Γ(X.left, U)) (η : (Fin d → ℂ) → ℂ)
    (hη : AnalyticAt ℂ η 0) (hη0 : η 0 ≠ 0)
    (he : (fun z => Point.evaluate U s ((ComplexPoint.localChart X d p).symm
        (ComplexPoint.localChart X d p p + z))) =ᶠ[nhds 0]
      (fun z => η z * Point.evaluate U t ((ComplexPoint.localChart X d p).symm
        (ComplexPoint.localChart X d p p + z)))) :
    Ideal.span {X.left.presheaf.germ U p.underlying hp s} =
      Ideal.span {X.left.presheaf.germ U p.underlying hp t} :=
  s2e_analytic_unit_descends_principal_ideal_aux X d p U hp s t η hη hη0 he

example := @s2e_analytic_unit_descends_principal_ideal

end HodgeLean.Foundations.Program
