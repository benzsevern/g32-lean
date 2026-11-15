import HodgeLean.Foundations.Program.G32Native.CanonicalAbelDifferentialDefs
import HodgeLean.Foundations.Program.SchoenCycleStep1
import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.IntegralSource

/-! # Symmetric sums on the retained quotient -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.Foundations.Curves.AbelAdapter
open HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
open scoped BigOperators Topology
namespace HodgeLean.Foundations.Program.G32Native

/-- Symmetric sums agree on every fibre, including tuples with repeated entries. -/
theorem canonical_sum_eq_of_quotient_eq (G : CanonicalAbelGeometry)
    {A : Type*} [AddCommMonoid A] (f : ComplexPoint G.Z → A)
    (z t : Fin (2 * G.k) → ComplexPoint G.Z)
    (h : Point.map G.γ (s2_lift (2 * G.k) z) =
      Point.map G.γ (s2_lift (2 * G.k) t)) :
    ∑ i, f (z i) = ∑ i, f (t i) := by
  classical
  letI : Smooth G.B.hom := SmoothOfRelativeDimension.smooth (G.k + G.k) G.B.hom
  obtain ⟨σ, hσ⟩ := s2e_step1_retained_symmetric_orbits G.Z G.B (2 * G.k)
    G.γ G.surjectiveγ G.invariantγ G.quotientγ _ _ h
  change s2_lift (2 * G.k) z ≫ s2_permute G.Z (2 * G.k) σ =
    s2_lift (2 * G.k) t at hσ
  rw [s2e_lift_permute] at hσ
  have ht : ∀ i, z (σ.symm i) = t i := by
    intro i
    have hi := congrArg (fun w => w ≫ g3_proj G.Z (2 * G.k) i) hσ
    simpa only [s2_check_lift_proj] using hi
  calc
    ∑ i, f (z i) = ∑ i, f (z (σ.symm i)) := (Equiv.sum_comp σ.symm _).symm
    _ = ∑ i, f (t i) := Finset.sum_congr rfl (fun i _ => congrArg f (ht i))

/-- The retained quotient has an ordered tuple above every complex point. -/
theorem canonical_quotient_tuple_exists (G : CanonicalAbelGeometry) (b : ComplexPoint G.B) :
    ∃ z : Fin (2 * G.k) → ComplexPoint G.Z,
      Point.map G.γ (s2_lift (2 * G.k) z) = b := by
  obtain ⟨u, hu⟩ := G.surjectiveγ b
  refine ⟨fun i => Point.map (g3_proj G.Z (2 * G.k) i) u, ?_⟩
  change Point.map G.γ (s2_lift (2 * G.k) (fun i => u ≫ g3_proj G.Z (2 * G.k) i)) = b
  rw [s2e_lift_coordinates]
  exact hu

/-- Descend a symmetric sum using the specified quotient, independently of enumeration. -/
def canonicalDescendedSum (G : CanonicalAbelGeometry)
    {A : Type*} [AddCommMonoid A] (f : ComplexPoint G.Z → A) (b : ComplexPoint G.B) : A :=
  ∑ i, f ((canonical_quotient_tuple_exists G b).choose i)

/-- Evaluation on any ordered representative returns the original sum. -/
theorem canonicalDescendedSum_tuple (G : CanonicalAbelGeometry)
    {A : Type*} [AddCommMonoid A] (f : ComplexPoint G.Z → A)
    (z : Fin (2 * G.k) → ComplexPoint G.Z) :
    canonicalDescendedSum G f (Point.map G.γ (s2_lift (2 * G.k) z)) = ∑ i, f (z i) := by
  exact canonical_sum_eq_of_quotient_eq G f _ z
    (canonical_quotient_tuple_exists G _).choose_spec

/-- Pointwise descent of the original curve Abel map in its original period quotient. -/
def canonicalSymmetricAbel (G : CanonicalAbelGeometry) (p : ComplexPoint G.Z) :
    ComplexPoint G.B → b3_Jacobian (Fin 1 → ℂ) (ComplexPoint G.Z) :=
  canonicalDescendedSum G (analyticAbel (Module.finrank_fin_fun (n := 1) ℂ) p)

/-- The descended Abel map retains every ordered representative of the divisor. -/
theorem canonicalSymmetricAbel_tuple (G : CanonicalAbelGeometry) (p : ComplexPoint G.Z)
    (z : Fin (2 * G.k) → ComplexPoint G.Z) :
    canonicalSymmetricAbel G p (Point.map G.γ (s2_lift (2 * G.k) z)) =
      ∑ i, analyticAbel (Module.finrank_fin_fun (n := 1) ℂ) p (z i) :=
  canonicalDescendedSum_tuple G _ z

#print axioms canonical_sum_eq_of_quotient_eq
#print axioms canonical_quotient_tuple_exists
#print axioms canonicalDescendedSum
#print axioms canonicalDescendedSum_tuple
#print axioms canonicalSymmetricAbel
#print axioms canonicalSymmetricAbel_tuple
end HodgeLean.Foundations.Program.G32Native
