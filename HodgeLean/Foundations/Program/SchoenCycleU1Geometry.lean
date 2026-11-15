import HodgeLean.Foundations.Program.SchoenCycleU1Local
import HodgeLean.Foundations.Program.SchoenCycleCanonicalGraphAlgebraic

/-! # Point separation and finiteness for the specified canonical map -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters
open scoped BigOperators ContDiff Manifold
namespace HodgeLean.Foundations.Program

/-- The specified canonical morphism is finite and separates complex points.
Source: Schoen, Compositio Mathematica 65 (1988), p. 13;
ACGH, Geometry of Algebraic Curves I, Chapter I, canonical linear systems. -/
theorem s2e_u1_canonical_point_separation_finite
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (k : ℕ) (γ : g3_power Z (2 * k) ⟶ B) [IsFinite γ.left]
    (hsurj : Function.Surjective (Point.map γ))
    (hγ : ∀ σ, s2_permute Z (2 * k) σ ≫ γ = γ)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z (2 * k) ⟶ T),
      (∀ σ, s2_permute Z (2 * k) σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (hg : ((2 * k : ℕ) : ℤ) = 2 * (Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) : ℤ) - 2)
    (hd : Module.finrank ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) = k + 1)
    (ℓ : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ B)
    (hℓ : letI : FiniteDimensional ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) :=
        Module.finite_of_finrank_pos (by rw [hd]; omega)
      let ep := s2e_finiteDimensionalProjectivePointEquiv
        (V := b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) k hd
      Point.map ℓ = fun R => s2e_canonicalQuotientPoint Z B (2 * k) γ hg (ep.symm R)) :
    Function.Injective (Point.map ℓ) ∧ IsFinite ℓ.left := by
  letI : FiniteDimensional ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) :=
    Module.finite_of_finrank_pos (by rw [hd]; omega)
  let ep := s2e_finiteDimensionalProjectivePointEquiv
    (V := b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) k hd
  change Point.map ℓ = (fun R => s2e_canonicalQuotientPoint Z B (2 * k) γ hg (ep.symm R)) at hℓ
  have hinj : Function.Injective (s2e_canonicalQuotientPoint Z B (2 * k) γ hg) :=
    s2e_canonicalQuotientPoint_injective_of_orbits Z B (2 * k) γ hγ
      (fun x y hxy => s2e_step1_retained_symmetric_orbits Z B (2 * k) γ hsurj hγ hquot x y hxy) hg
  refine ⟨?_, ?_⟩
  · rw [hℓ]
    exact hinj.comp ep.symm.injective
  · let PP := Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
    letI : IsProjective PP.hom := ⟨⟨⟨k, 𝟙 _, Category.id_comp _⟩⟩⟩
    letI : IsProper (ℓ.left ≫ B.hom) := by rw [Over.w ℓ]; infer_instance
    letI : IsProper ℓ.left := IsProper.of_comp ℓ.left B.hom
    apply s2e_isFinite_of_proper_complexPoint_fibres ℓ
    intro b
    rw [hℓ]
    exact (s2e_canonicalQuotientPoint_finite_fibre Z B (2 * k) γ hγ hg b).preimage
      ep.symm.injective.injOn

end HodgeLean.Foundations.Program
