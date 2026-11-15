import HodgeLean.Foundations.Program.G32Native.CanonicalPeriodLocalHomeomorph
import HodgeLean.Foundations.Program.G32Native.LocalLiftDerivative
import HodgeLean.Foundations.Program.G32Native.CanonicalAbelDescent

/-! # Independence of the Abel differential from the local lift -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.Foundations.Curves.AbelAdapter
open scoped BigOperators Topology
namespace HodgeLean.Foundations.Program.G32Native

/-- The coefficient differential depends only on the local quotient germ. -/
theorem canonicalAbelDifferential_eq_of_quotient_germ (G : CanonicalAbelGeometry)
    (F H : ComplexPoint G.Q → (Fin (G.k + G.k) → ℂ) → (Fin (G.k + 1) → ℂ))
    (x : ComplexPoint G.Q)
    (hF : DifferentiableAt ℂ (F x)
      (localChart G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι x)))
    (hH : DifferentiableAt ℂ (H x)
      (localChart G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι x)))
    (he : ∀ᶠ u in 𝓝
        (localChart G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι x)),
      canonicalPeriodQuotient G (F x u) = canonicalPeriodQuotient G (H x u)) :
    canonicalAbelDifferential G F x = canonicalAbelDifferential G H x := by
  have h := local_lift_fderiv_eq (canonicalPeriodHom G)
    (canonicalPeriodQuotient_isLocalHomeomorph G) hF hH he
  unfold canonicalAbelDifferential
  rw [h]

/-- Equal quotient values near the original ambient point give the same coefficient differential. -/
theorem canonicalAbelDifferential_eq_of_ambient_germ (G : CanonicalAbelGeometry)
    (F H : ComplexPoint G.Q → (Fin (G.k + G.k) → ℂ) → (Fin (G.k + 1) → ℂ))
    (x : ComplexPoint G.Q)
    (hF : DifferentiableAt ℂ (F x)
      (localChart G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι x)))
    (hH : DifferentiableAt ℂ (H x)
      (localChart G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι x)))
    (he : ∀ᶠ w in 𝓝 (Point.map G.ι x),
      canonicalPeriodQuotient G (F x (localChart G.W (G.k + G.k) (Point.map G.ι x) w)) =
      canonicalPeriodQuotient G (H x (localChart G.W (G.k + G.k) (Point.map G.ι x) w))) :
    canonicalAbelDifferential G F x = canonicalAbelDifferential G H x := by
  apply canonicalAbelDifferential_eq_of_quotient_germ G F H x hF hH
  let C := localChart G.W (G.k + G.k) (Point.map G.ι x)
  have hs : Point.map G.ι x ∈ C.source := mem_localChart_source _ _ _
  have ht : C (Point.map G.ι x) ∈ C.target := C.map_source hs
  have hi := (C.continuousAt_symm ht).tendsto
  rw [C.left_inv hs] at hi
  have hh := hi.eventually he
  filter_upwards [hh, C.open_target.mem_nhds ht] with u hu huC
  change canonicalPeriodQuotient G (F x (C (C.symm u))) =
    canonicalPeriodQuotient G (H x (C (C.symm u))) at hu
  rwa [C.right_inv huC] at hu

/-- The all-tuples lift equation determines the actual symmetric Abel germ. -/
theorem canonical_lift_quotient_germ (G : CanonicalAbelGeometry) (p : ComplexPoint G.Z)
    (x : ComplexPoint G.Q) (f : (Fin (G.k + G.k) → ℂ) → (Fin (G.k + 1) → ℂ))
    (hf : ∀ᶠ w in 𝓝 (Point.map G.ι x), ∀ z : Fin (2 * G.k) → ComplexPoint G.Z,
      Point.map G.γ (s2_lift (2 * G.k) z) = Point.map G.β w →
      canonicalPeriodQuotient G (f (localChart G.W (G.k + G.k) (Point.map G.ι x) w)) =
        ∑ i, analyticAbel (Module.finrank_fin_fun (n := 1) ℂ) p (z i)) :
    ∀ᶠ w in 𝓝 (Point.map G.ι x),
      canonicalPeriodQuotient G (f (localChart G.W (G.k + G.k) (Point.map G.ι x) w)) =
        canonicalSymmetricAbel G p (Point.map G.β w) := by
  filter_upwards [hf] with w hw
  obtain ⟨z, hz⟩ := canonical_quotient_tuple_exists G (Point.map G.β w)
  rw [hw z hz, ← hz, canonicalSymmetricAbel_tuple]

#print axioms canonical_lift_quotient_germ
#print axioms canonicalAbelDifferential_eq_of_quotient_germ
#print axioms canonicalAbelDifferential_eq_of_ambient_germ
end HodgeLean.Foundations.Program.G32Native
