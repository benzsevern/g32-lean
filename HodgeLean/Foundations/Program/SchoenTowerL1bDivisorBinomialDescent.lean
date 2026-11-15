import HodgeLean.Foundations.Program.SchoenTowerL1bKummerGeneratorQuotient
import HodgeLean.Foundations.Program.SchoenTowerL1bTransportQuotientAction

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The power of a character function descends along the actual categorical quotient. -/
theorem s2v_l1b_divisor_generator_binomial
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsIntegral Y.left]
    (β : X ⟶ Y) [IsFinite β.left] [IsDominant β.left]
    (d : X ⟶ X) [IsIso d] (hd : d ≫ β = β)
    (hcat : ∀ (T : Over (Spec ↧ℂ)) (f : X ⟶ T),
      d ≫ f = f → ∃! u : Y ⟶ T, β ≫ u = f)
    (U : Y.left.affineOpens) [Nonempty U.1]
    (τ : X.left.functionField ≃+* X.left.functionField)
    (hτ : Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
      X.left.fromSpecStalk (genericPoint X.left) =
      X.left.fromSpecStalk (genericPoint X.left) ≫ d.left)
    (t ξ : X.left.functionField) (m : ℕ) (hξ : ξ ^ m = 1)
    (htξ : τ t = ξ * t) :
    ∃ v : Y.left.functionField, s2v_l1b_functionFieldPullback β.left v = t ^ m := by
  letI := (s2v_l1b_functionFieldPullback β.left).hom.toAlgebra
  obtain ⟨τA, hτA⟩ := s2v_l1b_cover_field_algEquiv β.left d.left
    (congrArg Over.Hom.left hd)
  have heq : τA.toRingHom = τ.toRingHom := by
    rw [hτA]
    exact congrArg CommRingCat.Hom.hom
      (s2v_l1b_transport_symmetry_eq_pullback X.left d.left τ.toRingHom hτ).symm
  have hfix : τA (t ^ m) = t ^ m := by
    rw [map_pow]
    change τA.toRingHom t ^ m = t ^ m
    rw [heq]
    change (τ t) ^ m = t ^ m
    rw [htξ, mul_pow, hξ, one_mul]
  exact s2v_l1b_categorical_quotient_fixed_rational_function X Y β
    (fun _ : Unit => d) (fun _ => hd)
    (fun T f hf => hcat T f (hf ())) U
    (fun _ => τA) (fun _ => hτA) (t ^ m) (fun _ => hfix)

end HodgeLean.Foundations.Program
