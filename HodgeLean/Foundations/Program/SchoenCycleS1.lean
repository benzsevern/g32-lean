import HodgeLean.Foundations.Program.SchoenCycleS1Proofs

/-! # S1 cycle chain statements
Implication from the native paired differential family to its analytic incidence
and algebraic map. First unit only; tangent and branch-ideal geometry are deferred.
HC no distance; AV milestone no distance.
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

/-- The paired moving-divisor incidence is analytic, retaining zero multiplicities.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, pp. 13–14;
ACGH, Geometry of Algebraic Curves I, Chapter I, divisors and linear systems. -/
theorem s2e_chain_paired_divisor_graph
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
    (γ : g3_power Z (2 * k) ⟶ B)
    (hγ : ∀ σ, s2_permute Z (2 * k) σ ≫ γ = γ)
    (T : Over (Spec ↧ℂ)) (t : ℕ) [SmoothOfRelativeDimension t T.hom]
    (u : T ⟶ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (v : T ⟶ B) :
    letI : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
    let ep := s2e_finiteDimensionalProjectivePointEquiv
      (V := b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin r → ℂ)) k hd
    let F := s2e_projectiveDifferentialQuotientPoint
      (Module.finrank_fin_fun (n := 1) ℂ) w
      (fun j => y ⟨2 * j.val + 1, by omega⟩) hres y hy horder hout hgenus γ id
    IsClosedAnalytic (Fin t → ℂ)
      {x : ComplexPoint T | F (ep.symm (Point.map u x)) = Point.map v x} :=
  s2e_chain_paired_divisor_graph_aux Z B k r hr y hy w hres horder hout hgenus hd γ hγ T t u v

example := @s2e_chain_paired_divisor_graph

/-- The actual paired quotient evaluation is induced by an algebraic morphism.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.3, pp. 13–14;
ACGH, Geometry of Algebraic Curves I, Chapter I, divisors and linear systems. -/
theorem s2e_chain_paired_divisor_morphism
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
    (γ : g3_power Z (2 * k) ⟶ B)
    (hγ : ∀ σ, s2_permute Z (2 * k) σ ≫ γ = γ)
    :
    letI : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
    let ep := s2e_finiteDimensionalProjectivePointEquiv
      (V := b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z) × (Fin r → ℂ)) k hd
    let F := s2e_projectiveDifferentialQuotientPoint
      (Module.finrank_fin_fun (n := 1) ℂ) w
      (fun j => y ⟨2 * j.val + 1, by omega⟩) hres y hy horder hout hgenus γ id
    ∃ ℓ : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ B,
      Point.map ℓ = fun R => F (ep.symm R) :=
  s2e_chain_paired_divisor_morphism_aux Z B k r hr y hy w hres horder hout hgenus hd γ hγ

example := @s2e_chain_paired_divisor_morphism

end HodgeLean.Foundations.Program
