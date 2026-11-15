import HodgeLean.Foundations.Program.SchoenTowerN2bHomogeneousGluing
import HodgeLean.Foundations.Program.SchoenTowerN2bSourceCover

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Regularized sections on the actual nonempty charts determine a global homogeneous map. -/
theorem n2b_regularized_global_map
    {X : Scheme.{0}} [IsIntegral X] {n : ℕ} (ψ : X ⟶ g3c_P n)
    {κ : Type}
    [∀ i : {i : Fin (n + 1) // Nonempty (n2b_pullbackChart ψ i)},
      Nonempty (n2b_pullbackChart ψ i.val)]
    (c : κ → {i : Fin (n + 1) // Nonempty (n2b_pullbackChart ψ i)})
    (z : ∀ k, Γ(n2b_pullbackChart ψ (c k).val, ⊤))
    (N : ℕ)
    (a : ∀ k (b : {i : Fin (n + 1) // Nonempty (n2b_pullbackChart ψ i)}),
      Γ(n2b_pullbackChart ψ b.val, ⊤))
    (ha : ∀ (k : κ) (b : {i : Fin (n + 1) // Nonempty (n2b_pullbackChart ψ i)}),
      n2b_openChartRationalMap (n2b_pullbackChartι ψ (c k).val) (z k) *
          n2b_pullbackRationalCoord ψ (c k).val b.val ^ N =
        n2b_openChartRationalMap (n2b_pullbackChartι ψ b.val) (a k b))
    (q : ∀ (i : {i : Fin (n + 1) // Nonempty (n2b_pullbackChart ψ i)}),
      ULift.{0} ℤ →+* Γ(n2b_pullbackChart ψ i.val, ⊤))
    (pure : {i : Fin (n + 1) // Nonempty (n2b_pullbackChart ψ i)} → κ)
    (hpure : ∀ i, a (pure i) i = 1) :
    let 𝒰 := n2b_nonemptyPullbackChartCover ψ
    ∃ g : X ⟶ Proj (homogeneousSubmodule κ (ULift.{0} ℤ)), ∀ i,
      𝒰.f i ≫ g = Proj.fromOfGlobalSections (X := 𝒰.X i)
        (homogeneousSubmodule κ (ULift.{0} ℤ)) (eval₂Hom (q i) (fun k => a k i))
        (n2b_polynomial_evaluation_irrelevant (q i) (fun k => a k i) (pure i) (hpure i)) := by
  classical
  dsimp only
  refine n2b_glue_homogeneous_evaluations (X := X) (κ := κ) (n2b_nonemptyPullbackChartCover ψ)
    q
    (fun i k => a k i) pure hpure ?_
  intro i j
  dsimp only [n2b_nonemptyPullbackChartCover, Scheme.Cover.mkOfCovers]
  exact n2b_regularized_chart_unit_transition ψ
    (fun i : {i : Fin (n + 1) // Nonempty (n2b_pullbackChart ψ i)} => i.val)
    c z N a ha i j

end HodgeLean.Foundations.Program
