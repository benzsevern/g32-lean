import HodgeLean.Foundations.Program.SchoenCycleS1bProjectiveDualKernel
import HodgeLean.Foundations.Program.SchoenCycleU1SchemeStationaryKernel
import HodgeLean.Foundations.Program.SchoenCycleU1ProjectiveZero
import HodgeLean.Foundations.Program.SchoenCyclePairedPointGeometry
import HodgeLean.Foundations.Program.SchoenCycleU1Immersion
import HodgeLean.Foundations.Program.SchoenCycleU1SchemeDualCriterion
import HodgeLean.Foundations.Program.SchoenCycleS1
import HodgeLean.Foundations.Program.SchoenCycleStep1
import HodgeLean.Foundations.Program.SchoenCycleS1bChecks
import HodgeLean.Foundations.Program.SchoenCycleRegularRatio

/-! # Paired slice geometry
Implication from the native paired family and retained finite categorical quotient
to the stated slice geometry. HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters
open scoped BigOperators ContDiff
namespace HodgeLean.Foundations.Program

/-- A variation locally divisible by the original differential is scalar.
Source: ACGH, Geometry of Algebraic Curves I, Chapter IV, tangent spaces to Abel fibres. -/
theorem s2e_chain_paired_regular_quotient_aux
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (k r : ℕ) (hr : 0 < r)
    [FiniteDimensional ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z))]
    (y : Fin (2 * r) → ComplexPoint Z) (hy : Function.Injective y)
    (w : Fin r → b4c_MeroForm (Fin 1 → ℂ) (ComplexPoint Z)
      (Module.finrank_fin_fun (n := 1) ℂ))
    (hres : ∀ i j, b4c_res (hE := Module.finrank_fin_fun (n := 1) ℂ)
      (w i) (y ⟨2 * j.val + 1, by omega⟩) = if i = j then 1 else 0)
    (horder : ∀ i p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt
      (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) (w i) p) 0)
    (hout : ∀ i p, p ∉ Set.range y → AnalyticAt ℂ
      (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) (w i) p) 0)
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) + 2 * r)
    (hd : Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin r → ℂ)) = k + 1)
    (v δ : b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin r → ℂ))
    (hv : v ≠ 0)
    (hdiv : ∀ p : ComplexPoint Z, ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧
      Filter.Eventually (fun z =>
        HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ)
          (s2e_pairedDifferentialLinear (Module.finrank_fin_fun (n := 1) ℂ) w δ) p z =
        g z * HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ)
          (s2e_pairedDifferentialLinear (Module.finrank_fin_fun (n := 1) ℂ) w v) p z)
        (nhdsWithin (0 : ℂ) {0}ᶜ)) :
    ∃ c : ℂ, δ = c • v := by
  letI : ConnectedSpace (ComplexPoint Z) :=
    AlgebraicGeometry.ComplexPoint.connectedSpace Z
  exact s2e_divisible_paired_parameters_proportional
    (Module.finrank_fin_fun (n := 1) ℂ) w
    (fun j => y ⟨2 * j.val + 1, by omega⟩) hres δ v hv hdiv

/-- Composition with the exact paired divisor map separates dual-number points.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, pp. 13–14;
ACGH, Geometry of Algebraic Curves I, Chapter IV, Abel map and its fibres. -/
theorem s2e_chain_paired_first_order_separation_aux
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (k r : ℕ) (hr : 0 < r)
    [FiniteDimensional ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z))]
    (y : Fin (2 * r) → ComplexPoint Z) (hy : Function.Injective y)
    (w : Fin r → b4c_MeroForm (Fin 1 → ℂ) (ComplexPoint Z)
      (Module.finrank_fin_fun (n := 1) ℂ))
    (hres : ∀ i j, b4c_res (hE := Module.finrank_fin_fun (n := 1) ℂ)
      (w i) (y ⟨2 * j.val + 1, by omega⟩) = if i = j then 1 else 0)
    (horder : ∀ i p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt
      (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) (w i) p) 0)
    (hout : ∀ i p, p ∉ Set.range y → AnalyticAt ℂ
      (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) (w i) p) 0)
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) + 2 * r)
    (hd : Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin r → ℂ)) = k + 1)
    (γ : g3_power Z (2 * k) ⟶ B) [IsFinite γ.left]
    (hγ : ∀ σ, s2_permute Z (2 * k) σ ≫ γ = γ)
    (hsurj : Function.Surjective (Point.map γ))
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z (2 * k) ⟶ T),
      (∀ σ, s2_permute Z (2 * k) σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (ℓ : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ B)
    (hℓ : let : ConnectedSpace (ComplexPoint Z) :=
        AlgebraicGeometry.ComplexPoint.connectedSpace Z
      let ep := s2e_finiteDimensionalProjectivePointEquiv
        (V := b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin r → ℂ)) k hd
      Point.map ℓ = fun R => s2e_projectiveDifferentialQuotientPoint
        (Module.finrank_fin_fun (n := 1) ℂ) w
        (fun j => y ⟨2 * j.val + 1, by omega⟩) hres y hy horder hout hgenus γ id
        (ep.symm R)) :
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
      (s2e_paired_point_separation_finite Z B k r hr y hy w hres horder hout
        hgenus hd γ hγ hsurj hquot ℓ hℓ).1
      (fun f hf => s2e_paired_projective_dual_kernel Z B k r hr y hy w hres
        horder hout hgenus hd γ hγ hsurj hquot ℓ hℓ f hf)

/-- The exact paired moving-divisor map is a scheme immersion with proper image.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, pp. 13–14;
Hartshorne, Algebraic Geometry, II.4 and II.8. -/
theorem s2e_chain_paired_immersion_aux
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (k r : ℕ) (hr : 0 < r)
    [FiniteDimensional ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z))]
    (y : Fin (2 * r) → ComplexPoint Z) (hy : Function.Injective y)
    (w : Fin r → b4c_MeroForm (Fin 1 → ℂ) (ComplexPoint Z)
      (Module.finrank_fin_fun (n := 1) ℂ))
    (hres : ∀ i j, b4c_res (hE := Module.finrank_fin_fun (n := 1) ℂ)
      (w i) (y ⟨2 * j.val + 1, by omega⟩) = if i = j then 1 else 0)
    (horder : ∀ i p, (-1 : WithTop ℤ) ≤ meromorphicOrderAt
      (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) (w i) p) 0)
    (hout : ∀ i p, p ∉ Set.range y → AnalyticAt ℂ
      (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) (w i) p) 0)
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) + 2 * r)
    (hd : Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin r → ℂ)) = k + 1)
    (γ : g3_power Z (2 * k) ⟶ B) [IsFinite γ.left]
    (hγ : ∀ σ, s2_permute Z (2 * k) σ ≫ γ = γ)
    (hsurj : Function.Surjective (Point.map γ))
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z (2 * k) ⟶ T),
      (∀ σ, s2_permute Z (2 * k) σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)
    (ℓ : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ B)
    (hℓ : let : ConnectedSpace (ComplexPoint Z) :=
        AlgebraicGeometry.ComplexPoint.connectedSpace Z
      let ep := s2e_finiteDimensionalProjectivePointEquiv
        (V := b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin r → ℂ)) k hd
      Point.map ℓ = fun R => s2e_projectiveDifferentialQuotientPoint
        (Module.finrank_fin_fun (n := 1) ℂ) w
        (fun j => y ⟨2 * j.val + 1, by omega⟩) hres y hy horder hout hgenus γ id
        (ep.symm R)) :
    IsClosedImmersion ℓ.left := by
  let PP := Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
  letI : IsProjective PP.hom := ⟨⟨⟨k, 𝟙 _, Category.id_comp _⟩⟩⟩
  have hp := s2e_paired_point_separation_finite Z B k r hr y hy w hres horder hout
    hgenus hd γ hγ hsurj hquot ℓ hℓ
  letI : IsFinite ℓ.left := hp.2
  have hsep := s2e_chain_paired_first_order_separation_aux Z B k r hr y hy w hres
    horder hout hgenus hd γ hγ hsurj hquot ℓ hℓ
  letI : FormallyUnramified ℓ.left :=
    s2e_u1_formallyUnramified_of_dual_separation PP B ℓ hsep
  exact s2e_u1_finite_unramified_point_separation_immersion PP B ℓ hp.1

end HodgeLean.Foundations.Program
