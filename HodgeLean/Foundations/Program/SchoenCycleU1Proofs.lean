import HodgeLean.Foundations.Program.SchoenCycleU1SchemeStationaryKernel
import HodgeLean.Foundations.Program.SchoenCycleU1CanonicalProjectiveDualKernel
import HodgeLean.Foundations.Program.SchoenCycleU1ProjectiveZero
import HodgeLean.Foundations.Program.SchoenCycleU1Geometry
import HodgeLean.Foundations.Program.SchoenCycleU1Immersion
import HodgeLean.Foundations.Program.SchoenCycleU1SchemeDualCriterion
import HodgeLean.Foundations.Program.SchoenCycleU1Local
import HodgeLean.Foundations.Program.SchoenCycleU1Variation
import HodgeLean.Foundations.Program.SchoenCycleStep1
import HodgeLean.Foundations.Program.SchoenCycleCanonicalGraphAlgebraic
import HodgeLean.Foundations.Program.SchoenCycleGenusTransport
import HodgeLean.Foundations.Program.SchoenCycleU1Checks

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

theorem s2e_chain_canonical_first_order_separation_aux
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
      (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) => f ≫ ℓ) := by
  by_cases hk : k = 0
  · subst k
    dsimp only
    intro f g _
    exact s2e_u1_projective_zero_algebra_point_unique (DualNumber ℂ) f g
  · exact s2e_u1_scheme_dual_injective_of_stationary_kernel _ B ℓ
      (s2e_u1_canonical_point_separation_finite Z B k γ hsurj hγ hquot hg hd ℓ hℓ).1
      (fun f hf => s2e_u1_canonical_projective_dual_kernel
        Z B k γ hsurj hγ hquot hg hd ℓ hℓ f hf)

theorem s2e_chain_canonical_immersion_aux
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
    IsClosedImmersion ℓ.left := by
  let PP := Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
  letI : IsProjective PP.hom := ⟨⟨⟨k, 𝟙 _, Category.id_comp _⟩⟩⟩
  have hp := s2e_u1_canonical_point_separation_finite Z B k γ hsurj hγ hquot hg hd ℓ hℓ
  letI : IsFinite ℓ.left := hp.2
  have hsep := s2e_chain_canonical_first_order_separation_aux Z B k γ hsurj hγ hquot hg hd ℓ hℓ
  letI : FormallyUnramified ℓ.left :=
    s2e_u1_formallyUnramified_of_dual_separation PP B ℓ hsep
  exact s2e_u1_finite_unramified_point_separation_immersion PP B ℓ hp.1

theorem s2e_chain_canonical_range_exact_aux
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
              ∑ t, Finsupp.single (z t) (1 : ℤ) := by
  letI : FiniteDimensional ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) :=
    Module.finite_of_finrank_pos (by rw [hd]; omega)
  let ep := s2e_finiteDimensionalProjectivePointEquiv
    (V := b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) k hd
  change Point.map ℓ = (fun R => s2e_canonicalQuotientPoint Z B (2 * k) γ hg (ep.symm R)) at hℓ
  intro b
  rw [hℓ]
  have hrange : Set.range (fun R => s2e_canonicalQuotientPoint Z B (2 * k) γ hg (ep.symm R)) =
      Set.range (s2e_canonicalQuotientPoint Z B (2 * k) γ hg) := by
    ext b'
    constructor
    · rintro ⟨R, rfl⟩
      exact ⟨ep.symm R, rfl⟩
    · rintro ⟨R, rfl⟩
      exact ⟨ep R, congrArg (s2e_canonicalQuotientPoint Z B (2 * k) γ hg)
        (ep.symm_apply_apply R)⟩
  rw [hrange]
  exact s2e_canonicalQuotientPoint_range Z B (2 * k) γ hγ hg b

theorem s2e_chain_unramified_native_genus_aux
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
        (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) : ℤ) - 2 := by
  let hZ := s2e_scheme_curve_relativeDimension Z hdim
  letI := hZ
  refine ⟨hZ, ?_⟩
  have ht := s2e_scheme_holForm_finrank_homeomorph Z eZ
  have hd : Module.finrank ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) = k + 1 := by
    rw [hr, ht] at hgenus
    omega
  refine ⟨hd, ?_⟩
  rw [hd]
  push_cast
  omega

end HodgeLean.Foundations.Program
