import HodgeLean.Foundations.Program.SchoenTowerI2bPointEvaluation
import HodgeLean.Foundations.Program.SchoenTowerI2bSpecInertia

/-! Evaluation at the actual point of a retained normalization chart.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
universe u
namespace HodgeLean.Foundations.Program

/-- Evaluation through the specified normalization chart extends evaluation at its actual base point.
Source: the retained normalization base square and full faithfulness of spectrum. -/
theorem s2v_i2b_normalized_chart_evaluation_base
    (U : Scheme.{u}) [IsAffine U] (K L : Type u) [CommRing K] [CommRing L]
    [Algebra Γ(U, ⊤) K] (Q : Scheme.{u}) (π : Q ⟶ U)
    (e : Q ≅ Spec ↧(integralClosure Γ(U, ⊤) K))
    (hbase : π ≫ U.toSpecΓ = e.hom ≫ Spec.map
      (CommRingCat.ofHom (algebraMap Γ(U, ⊤) (integralClosure Γ(U, ⊤) K))))
    (q : Spec ↧L ⟶ Q) (p : Spec ↧L ⟶ U) (hq : q ≫ π = p) :
    (Spec.homEquivRingHom (q ≫ e.hom)).comp
      (algebraMap Γ(U, ⊤) (integralClosure Γ(U, ⊤) K)) =
      (p.appTop ≫ (Scheme.ΓSpecIso ↧L).hom).hom := by
  have hs : (q ≫ e.hom) ≫ Spec.map
      (CommRingCat.ofHom (algebraMap Γ(U, ⊤) (integralClosure Γ(U, ⊤) K))) =
      p ≫ U.toSpecΓ := by
    calc
      _ = q ≫ (π ≫ U.toSpecΓ) := by simp only [Category.assoc, hbase]
      _ = p ≫ U.toSpecΓ := by rw [← Category.assoc, hq]
  rw [s2v_i2b_field_chart_toSpecΓ p] at hs
  have hr := congrArg (fun f : Spec ↧L ⟶ Spec Γ(U, ⊤) => (Spec.preimage f).hom) hs
  simp only [Spec.preimage_comp, Spec.preimage_map, CommRingCat.hom_comp] at hr
  exact hr

/-- Evaluation at the actual normalization-chart point respects the specified complex scalars.
Source: the normalization base square and the actual complex-point structure equation. -/
theorem s2v_i2b_normalized_chart_complex_evaluation
    (U : Over (Spec ↧ℂ)) [IsAffine U.left]
    [Algebra ℂ Γ(U.left, ⊤)]
    (hscalar : algebraMap ℂ Γ(U.left, ⊤) =
      ((Scheme.ΓSpecIso ↧ℂ).inv ≫ U.hom.appTop).hom)
    (K : Type) [Field K] [Algebra Γ(U.left, ⊤) K] [Algebra ℂ K]
    [IsScalarTower ℂ Γ(U.left, ⊤) K]
    (Q : Scheme) (π : Q ⟶ U.left)
    (e : Q ≅ Spec ↧(integralClosure Γ(U.left, ⊤) K))
    (hbase : π ≫ U.left.toSpecΓ = e.hom ≫ Spec.map
      (CommRingCat.ofHom (algebraMap Γ(U.left, ⊤) (integralClosure Γ(U.left, ⊤) K))))
    (q : Spec ↧ℂ ⟶ Q) (p : ComplexPoint U) (hq : q ≫ π = p.left) :
    ∃ P : integralClosure Γ(U.left, ⊤) K →ₐ[ℂ] ℂ,
      P.toRingHom = Spec.homEquivRingHom (q ≫ e.hom) ∧
      P.toRingHom.comp (algebraMap Γ(U.left, ⊤) (integralClosure Γ(U.left, ⊤) K)) =
        (p.left.appTop ≫ (Scheme.ΓSpecIso ↧ℂ).hom).hom := by
  let θ := Spec.homEquivRingHom (q ≫ e.hom)
  have hθ := s2v_i2b_normalized_chart_evaluation_base U.left K ℂ Q π e hbase q p.left hq
  let P : integralClosure Γ(U.left, ⊤) K →ₐ[ℂ] ℂ :=
    { toRingHom := θ
      commutes' := by
        intro c
        change θ (algebraMap ℂ (integralClosure Γ(U.left, ⊤) K) c) = c
        calc
          _ = θ (algebraMap Γ(U.left, ⊤) (integralClosure Γ(U.left, ⊤) K)
              (algebraMap ℂ Γ(U.left, ⊤) c)) := by
                rw [IsScalarTower.algebraMap_apply ℂ Γ(U.left, ⊤)
                  (integralClosure Γ(U.left, ⊤) K) c]
          _ = (p.left.appTop ≫ (Scheme.ΓSpecIso ↧ℂ).hom).hom
              (algebraMap ℂ Γ(U.left, ⊤) c) :=
            congrArg (fun f : Γ(U.left, ⊤) →+* ℂ => f (algebraMap ℂ Γ(U.left, ⊤) c)) hθ
          _ = c := by
            rw [hscalar]
            exact s2v_i2b_complex_point_scalar_compatible U p c }
  exact ⟨P, rfl, hθ⟩

end HodgeLean.Foundations.Program
