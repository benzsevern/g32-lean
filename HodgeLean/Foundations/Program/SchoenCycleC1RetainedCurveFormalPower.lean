import HodgeLean.Foundations.Program.SchoenCycleC1OrbitFormalPower
import HodgeLean.Foundations.Program.SchoenCycleC11DegreeHelpers
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Equidimensional

/-! # Formal power coordinates under the retained curve hypotheses -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open scoped Pointwise
namespace HodgeLean.Foundations.Program

/-- The retained dimension-one smooth curve hypotheses and surjectivity on
complex points supply formal power coordinates for the actual orbit projection. -/
theorem s2e_c1_retained_curve_projection_formal_power
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] [IsIntegral Y.left] [Smooth Y.hom]
    (hdim : TopologicalSpace.dim X.left = 1)
    (G : Type) [Group G] [Fintype G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u) (hinj : Function.Injective a)
    (q : X ⟶ Y) [IsFinite q.left]
    (hsurj : Function.Surjective (Point.map q))
    (hinv : ∀ u, a u ≫ q = q)
    (horbit : ∀ x z : ComplexPoint X, Point.map q x = Point.map q z ↔
      ∃ u, Point.map (a u) x = z)
    (U : Y.left.Opens) (hU : IsAffineOpen U)
    (x : ComplexPoint X) (hx : x.underlying ∈ q.left ⁻¹ᵁ U) :
    letI : SmoothOfRelativeDimension 1 X.hom := by rw [← hdim]; infer_instance
    letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
    let P := ((hU.preimage q.left).primeIdealOf ⟨x.underlying, hx⟩).asIdeal
    let o : MulAction.orbit G P := ⟨P, MulAction.mem_orbit_self P⟩
    let H := MulAction.stabilizer G o
    let S := Y.left.presheaf.stalk (q.left x.underlying)
    letI : Algebra ℂ S := (HodgeLean.Foundations.Curves.stalkC (q.left x.underlying)).toAlgebra
    let R := X.left.presheaf.stalk x.underlying
    letI : Algebra ℂ R := (HodgeLean.Foundations.Curves.stalkC x.underlying).toAlgebra
    ∃ u : Rˣ,
    ∃ ER : PowerSeries ℂ ≃ₐ[ℂ] AdicCompletion (IsLocalRing.maximalIdeal R) R,
    ∃ ES : PowerSeries ℂ ≃ₐ[ℂ] AdicCompletion (IsLocalRing.maximalIdeal S) S,
      (∀ p : Polynomial ℂ, ER (p : PowerSeries ℂ) = AdicCompletion.of _ _
        (Polynomial.aeval (s2e_native_curve_parameter X x * (u : R)) p)) ∧
      ∀ f, s2e_formal_stalk_pullback X Y q x.underlying (ES f) =
        ER (PowerSeries.expand (Nat.card H) Nat.card_pos.ne' f) := by
  letI : SmoothOfRelativeDimension 1 X.hom := by rw [← hdim]; infer_instance
  letI : Surjective q.left := s2e_c11_surjective_of_complex_points X Y q
    q.left.isClosedMap.isClosed_range hsurj
  exact s2e_c1_curve_orbit_projection_formal_power
    X Y G a ha1 hamul hinj q hinv horbit U hU x hx

end HodgeLean.Foundations.Program
