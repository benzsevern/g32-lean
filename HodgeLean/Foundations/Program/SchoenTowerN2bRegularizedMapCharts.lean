import HodgeLean.Foundations.Program.SchoenTowerN2bRegularizedMap

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open HodgeLean.Foundations
namespace HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The pure regularized coordinates recover precisely the actual source charts. -/
theorem n2b_regularized_map_preimage_chart
    {X : Scheme.{0}} {n : ℕ} (ψ : X ⟶ g3c_P n) {κ : Type}
    (g : X ⟶ Proj (homogeneousSubmodule κ (ULift.{0} ℤ)))
    (a : ∀ (i : {i : Fin (n + 1) // Nonempty (n2b_pullbackChart ψ i)}),
      κ → Γ(n2b_pullbackChart ψ i.val, ⊤))
    (q : ∀ (i : {i : Fin (n + 1) // Nonempty (n2b_pullbackChart ψ i)}),
      ULift.{0} ℤ →+* Γ(n2b_pullbackChart ψ i.val, ⊤))
    (pure : {i : Fin (n + 1) // Nonempty (n2b_pullbackChart ψ i)} → κ)
    (hself : ∀ i, a i (pure i) = 1)
    (hlocal : ∀ (i : {i : Fin (n + 1) // Nonempty (n2b_pullbackChart ψ i)}), n2b_pullbackChartι ψ i.val ≫ g =
      Proj.fromOfGlobalSections (X := n2b_pullbackChart ψ i.val)
        (homogeneousSubmodule κ (ULift.{0} ℤ)) (eval₂Hom (q i) (a i))
        (n2b_polynomial_evaluation_irrelevant (q i) (a i) (pure i) (hself i)))
    (N : ℕ) (hN : 0 < N)
    (hpure : ∀ (i j : {i : Fin (n + 1) // Nonempty (n2b_pullbackChart ψ i)}), a j (pure i) = n2b_pullbackChartCoord ψ j.val i.val ^ N)
    (i : {i : Fin (n + 1) // Nonempty (n2b_pullbackChart ψ i)}) :
    (n2b_pullbackChartι ψ i.val).opensRange =
      g ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule κ (ULift.{0} ℤ)) (MvPolynomial.X (pure i)) := by
  apply n2b_opens_eq_of_cover_preimage (n2b_nonemptyPullbackChartCover ψ)
  intro j
  change n2b_pullbackChartι ψ j.val ⁻¹ᵁ _ = n2b_pullbackChartι ψ j.val ⁻¹ᵁ _
  rw [← Scheme.Hom.comp_preimage, hlocal j,
    n2b_homogeneous_evaluation_preimage _ (q j) (a j) (pure j) (hself j) (pure i), hpure,
    Scheme.basicOpen_pow _ _ hN, n2b_pullbackChart_preimage_chart]

end HodgeLean.Foundations.Program
