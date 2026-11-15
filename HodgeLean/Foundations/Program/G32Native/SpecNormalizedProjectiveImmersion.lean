import HodgeLean.Foundations.Program.G32Native.SpecGeneratorImmersion
import HodgeLean.Foundations.Program.G32Native.NormalizedProjectiveChartImmersion

/-! Normalized projective coordinate graphs of spectra. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
namespace HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Normalized algebra generators give a projective-space immersion of a spectrum. -/
theorem g32l4_spec_normalized_projective_immersion {R A : Type} [CommRing R] [CommRing A]
    [Algebra R A] (m : ℕ) (v : Fin (m + 1) → A) (p : Fin (m + 1))
    (hp : (Scheme.ΓSpecIso (.of A)).inv.hom (v p) = 1)
    (hv : Algebra.adjoin R (Set.range v) = ⊤) :
    IsImmersion (pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Proj.fromOfGlobalSections (homogeneousSubmodule (Fin (m + 1)) (ULift.{0} ℤ))
        (eval₂Hom ((Int.castRingHom _).comp ULift.ringEquiv.toRingHom)
          (fun k => (Scheme.ΓSpecIso (.of A)).inv.hom (v k)))
        (n2b_polynomial_evaluation_irrelevant _ _ p hp))
      (show Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ terminal.from (Spec (.of R)) =
        _ ≫ terminal.from (Proj (homogeneousSubmodule (Fin (m + 1)) (ULift.{0} ℤ))) from
        Subsingleton.elim _ _) : Spec (.of A) ⟶ ProjectiveSpace (Fin (m + 1)) (Spec (.of R))) := by
  haveI := g32l4_spec_generator_closedImmersion v hv
  exact g32l4_normalized_projective_chart_immersion
    (Spec.map (CommRingCat.ofHom (algebraMap R A)))
    ((Int.castRingHom _).comp ULift.ringEquiv.toRingHom)
    (fun k => (Scheme.ΓSpecIso (.of A)).inv.hom (v k)) p hp
    (m + 1) (fun k => (Scheme.ΓSpecIso (.of A)).inv.hom (v k)) id (fun _ => rfl)

end HodgeLean.Foundations.Program
