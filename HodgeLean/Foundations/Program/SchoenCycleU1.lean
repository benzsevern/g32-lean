import HodgeLean.Foundations.Program.SchoenCycleU1Proofs

/-! # U1 cycle chain statements
Implication from the retained symmetric quotient and native genus to canonical
first-order separation, immersion and exact range. No tower parameters occur.
Residual torsor construction is a separate review unit.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters
open scoped BigOperators ContDiff Manifold
namespace HodgeLean.Foundations.Program

/-- The retained canonical map separates complex first-order points, including collisions.
Source: Schoen, Compositio Mathematica 65 (1988), p. 13;
ACGH, Geometry of Algebraic Curves I, Chapter IV, Abel-map fibres. -/
theorem s2e_chain_canonical_first_order_separation
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
    let D : Over (Spec ↧ℂ) := Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ))))
    Function.Injective (fun f : D ⟶ Over.mk
      (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) => f ≫ ℓ) :=
  s2e_chain_canonical_first_order_separation_aux Z B k γ hsurj hγ hquot hg hd ℓ hℓ

example := @s2e_chain_canonical_first_order_separation

/-- The same canonical morphism is a scheme immersion with proper image.
Source: Schoen, Compositio Mathematica 65 (1988), p. 13;
ACGH, Geometry of Algebraic Curves I, Chapter IV, Abel-map fibres. -/
theorem s2e_chain_canonical_immersion
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
    IsClosedImmersion ℓ.left :=
  s2e_chain_canonical_immersion_aux Z B k γ hsurj hγ hquot hg hd ℓ hℓ

example := @s2e_chain_canonical_immersion

/-- The range of that very morphism is the native canonical divisor locus.
Source: Schoen, Compositio Mathematica 65 (1988), p. 13;
ACGH, Geometry of Algebraic Curves I, Chapter IV, Abel-map fibres. -/
theorem s2e_chain_canonical_range_exact
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
    ∀ b : ComplexPoint B, b ∈ Set.range (Point.map ℓ) ↔
      ∃ z : Fin (2 * k) → ComplexPoint Z,
        Point.map γ (s2_lift (2 * k) z) = b ∧
        ∃ θ : b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z), θ ≠ 0 ∧
          b4c_divForm (E := Fin 1 → ℂ) (C := ComplexPoint Z)
            (hE := Module.finrank_fin_fun (n := 1) ℂ) θ =
              ∑ t, Finsupp.single (z t) (1 : ℤ) :=
  s2e_chain_canonical_range_exact_aux Z B k γ hsurj hγ hquot hg hd ℓ hℓ

example := @s2e_chain_canonical_range_exact

/-- Empty branch data transport the selected genus to native canonical parameters.
Source: Schoen, Compositio Mathematica 65 (1988), p. 13;
s2e_scheme_curve_relativeDimension and s2e_scheme_holForm_finrank_homeomorph. -/
theorem s2e_chain_unramified_native_genus
    {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C]
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (hdim : TopologicalSpace.dim Z.left = 1) (eZ : C ≃ₜ ComplexPoint Z)
    (k r : ℕ) (hr : r = 0)
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ (b3_HolForm ℂ C) + 2 * r) :
    ∃ hZ : SmoothOfRelativeDimension 1 Z.hom,
      letI := hZ
      Module.finrank ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) = k + 1 ∧
      ((2 * k : ℕ) : ℤ) = 2 * (Module.finrank ℂ
        (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) : ℤ) - 2 :=
  s2e_chain_unramified_native_genus_aux Z hdim eZ k r hr hgenus

example := @s2e_chain_unramified_native_genus

end HodgeLean.Foundations.Program
