import HodgeLean.Foundations.Program.SchoenCycleC1SmoothMeasuredFormalPower
import HodgeLean.Foundations.Program.SchoenCycleC1OrbitMeasuredFibres
import HodgeLean.Foundations.Program.SchoenGenericPointMorphisms

/-! # Formal curve power equations from actual orbit fibres -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open scoped Pointwise
namespace HodgeLean.Foundations.Program

/-- A faithful finite deck action whose orbits are the actual complex fibres
gives formal coordinates for the specified projection and native parameter. -/
theorem s2e_c1_curve_orbit_projection_formal_power
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom] [IsIntegral Y.left] [Smooth Y.hom]
    (G : Type) [Group G] [Fintype G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u) (hinj : Function.Injective a)
    (q : X ⟶ Y) [IsFinite q.left] [Surjective q.left]
    (hinv : ∀ u, a u ≫ q = q)
    (horbit : ∀ x z : ComplexPoint X, Point.map q x = Point.map q z ↔
      ∃ u, Point.map (a u) x = z)
    (U : Y.left.Opens) (hU : IsAffineOpen U)
    (x : ComplexPoint X) (hx : x.underlying ∈ q.left ⁻¹ᵁ U) :
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
  letI : Smooth X.hom := SmoothOfRelativeDimension.smooth 1 X.hom
  have hcx : IsClosed ({x.underlying} : Set X.left) :=
    ((pointEquivClosedPoint X.hom) ⟨x.left, by simp⟩).2
  have hcy : IsClosed ({q.left x.underlying} : Set Y.left) := by
    simpa only [Set.image_singleton] using q.left.isClosedMap {x.underlying} hcx
  have hg := s2_dominant_genericPoint q.left
  apply s2e_c1_smooth_cover_formal_power_of_measured_fibres
    X Y G a ha1 hamul hinj q hinv hg
    (s2e_c1_orbit_fibres_measured_in_every_open X Y G a ha1 hamul hinj q hinv horbit)
    U hU x hx hcx hcy

end HodgeLean.Foundations.Program
