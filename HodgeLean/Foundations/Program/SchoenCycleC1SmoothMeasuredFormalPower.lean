import HodgeLean.Foundations.Program.SchoenCycleC1ActualMeasuredFormalPower
import HodgeLean.Foundations.Program.SchoenCycleC1ActualFieldDegreeHelpers
import HodgeLean.Foundations.Program.SchoenQuotientNormality

/-! # Formal curve power equations from actual measured fibres -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open scoped Pointwise
namespace HodgeLean.Foundations.Program

/-- Smoothness of the actual base and measured complex fibres supply the
normality and finite generic degree used in the actual formal power equation. -/
theorem s2e_c1_smooth_cover_formal_power_of_measured_fibres
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom] [IsIntegral Y.left] [Smooth Y.hom]
    (G : Type) [Group G] [Fintype G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u) (hinj : Function.Injective a)
    (q : X ⟶ Y) [IsFinite q.left] [Surjective q.left]
    (hinv : ∀ u, a u ≫ q = q)
    (hg : q.left (genericPoint X.left) = genericPoint Y.left)
    (hmeas : ∀ V : Y.left.Opens, (V : Set Y.left).Nonempty →
      ∃ y : ComplexPoint Y, y.underlying ∈ V ∧ Nat.card ((Point.map q) ⁻¹' {y}) = Nat.card G)
    (U : Y.left.Opens) (hU : IsAffineOpen U)
    (x : ComplexPoint X) (hx : x.underlying ∈ q.left ⁻¹ᵁ U)
    (hcx : IsClosed ({x.underlying} : Set X.left))
    (hcy : IsClosed ({q.left x.underlying} : Set Y.left)) :
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
  letI : Nonempty U := ⟨⟨q.left x.underlying, hx⟩⟩
  letI : Nonempty (q.left ⁻¹ᵁ U) := ⟨⟨x.underlying, hx⟩⟩
  letI : IsIntegrallyClosed Γ(Y.left, U) :=
    s2_affineOpen_sections_integrallyClosed (zmtiso_normal_of_smooth Y.left Y.hom) hU
  letI : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  let φ := (eqToHom (congrArg Y.left.presheaf.stalk hg.symm) ≫
    q.left.stalkMap (genericPoint X.left)).hom
  letI := φ.toAlgebra
  have hd : Module.finrank Y.left.functionField X.left.functionField = Nat.card G :=
    s2e_c1_actual_fieldDegree_of_measured_fibres X Y q hg (Nat.card G) hmeas
  letI : Module.Finite Y.left.functionField X.left.functionField :=
    Module.finite_of_finrank_pos (by rw [hd]; exact Nat.card_pos)
  exact s2e_c1_actual_measured_cover_formal_power_equation
    X Y G a ha1 hamul hinj q hinv hg U hU x hx hcx hcy hd

end HodgeLean.Foundations.Program
