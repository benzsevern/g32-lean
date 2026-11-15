import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeDimension
import HodgeLean.Adapters.NormalConeB4aGysinBridge2LocalLength

/-! # Algebraic length at a regular point of an analytic fibre

An invertible analytic Jacobian makes the algebraic parameter germs generate
the source maximal ideal. Their quotient therefore has length one.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters Point
set_option maxHeartbeats 400000
namespace AlgebraicGeometry.SingularCycles

theorem parameter_quotient_length_one_of_invertible_jacobian
    (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] [LocallyOfFiniteType X.hom]
    (x j : ComplexPoint X) (hxj : x ∈ (chartAt (Fin d → ℂ) j).source)
    (V : X.left.Opens) (hxV : x.underlying ∈ V)
    (s : Fin d → Γ(X.left, V)) (hs0 : ∀ k, evaluate V (s k) x = 0)
    (hunit : IsUnit (fderiv ℂ (fun a k => evaluate V (s k)
        ((chartAt (Fin d → ℂ) j).symm a)) ((chartAt (Fin d → ℂ) j) x))) :
    Module.length (X.left.presheaf.stalk x.underlying)
      (X.left.presheaf.stalk x.underlying ⧸
        Ideal.span (Set.range fun k => X.left.presheaf.germ V x.underlying hxV (s k))) = 1 := by
  rw [a3b4g_span_germ_eq_maximalIdeal_of_isUnit_fderiv X x j hxj V hxV s hs0 hunit]
  exact a3b4g_length_quotient_maximalIdeal _

theorem sliceLength_one_of_invertible_jacobian
    {Z K : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of ℂ)) (i : K ⟶ Z) (d : ℕ)
    [SmoothOfRelativeDimension d (Over.mk (i ≫ q)).hom]
    [LocallyOfFiniteType (Over.mk (i ≫ q)).hom]
    (w j : ComplexPoint (Over.mk (i ≫ q)))
    (hwj : w ∈ (chartAt (Fin d → ℂ) j).source)
    (U : Z.Opens) (g : Fin d → Γ(Z, U)) (a : Fin d → ℂ)
    (hwU : i w.underlying ∈ U) :
    let s : Fin d → Γ(K, i ⁻¹ᵁ U) :=
      fun k => i.app U (g k - a3b4a_gysin_sectionConst q U (a k))
    (∀ k, evaluate (i ⁻¹ᵁ U) (s k) w = 0) →
    IsUnit (fderiv ℂ (fun v k => evaluate (i ⁻¹ᵁ U) (s k)
      ((chartAt (Fin d → ℂ) j).symm v)) ((chartAt (Fin d → ℂ) j) w)) →
      a3b4a_gysin_sliceLength q i U g a w = 1 := by
  dsimp only
  intro hzero hunit
  have h := parameter_quotient_length_one_of_invertible_jacobian
    (Over.mk (i ≫ q)) d w j hwj (i ⁻¹ᵁ U) hwU
    (fun k => i.app U (g k - a3b4a_gysin_sectionConst q U (a k))) hzero hunit
  unfold a3b4a_gysin_sliceLength
  rw [dif_pos hwU]
  have hi : Ideal.ofList (a3b4a_gysin_sliceSequence q i U g a w.underlying hwU) =
      Ideal.span (Set.range fun k => K.presheaf.germ (i ⁻¹ᵁ U) w.underlying hwU
        (i.app U (g k - a3b4a_gysin_sectionConst q U (a k)))) := by
    apply congrArg Ideal.span
    ext t
    simp [a3b4a_gysin_sliceSequence]
  rw [hi]
  exact h

end AlgebraicGeometry.SingularCycles
