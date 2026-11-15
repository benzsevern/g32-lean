import HodgeLean.Foundations.Program.G32Native.NormalizedGeneratorTransition
import HodgeLean.Foundations.Program.G32Native.OpenImmersionRegularSection
import HodgeLean.Foundations.Program.SchoenTowerN2bHomogeneousGluing

/-! Projective gluing from regular multiples of normalized coordinates. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
namespace HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Regular multiples of normalized coordinates give one global projective morphism. -/
theorem g32l4_glue_normalized_generator_maps {X : Scheme.{0}} (𝒰 : X.OpenCover)
    [∀ i, IsAffine (𝒰.X i)] {K : Type}
    (q : ∀ i, ULift.{0} ℤ →+* Γ(𝒰.X i, ⊤))
    (a : ∀ i, K → Γ(𝒰.X i, ⊤)) (k : 𝒰.I₀ → K)
    (hk : ∀ i, a i (k i) = 1)
    (s : ∀ i, Γ(𝒰.X i, ⊤)) (hs : ∀ i, s i ∈ nonZeroDivisors Γ(𝒰.X i, ⊤))
    (hscale : ∀ i j, ∃ b : Γ(pullback (𝒰.f i) (𝒰.f j), ⊤), ∀ t,
      (pullback.fst (𝒰.f i) (𝒰.f j)).appTop.hom (s i) *
          (pullback.fst (𝒰.f i) (𝒰.f j)).appTop.hom (a i t) =
        b * (pullback.snd (𝒰.f i) (𝒰.f j)).appTop.hom (a j t)) :
    ∃ g : X ⟶ Proj (homogeneousSubmodule K (ULift.{0} ℤ)), ∀ i,
      𝒰.f i ≫ g = Proj.fromOfGlobalSections
        (homogeneousSubmodule K (ULift.{0} ℤ)) (eval₂Hom (q i) (a i))
        (n2b_polynomial_evaluation_irrelevant (q i) (a i) (k i) (hk i)) := by
  apply n2b_glue_homogeneous_evaluations 𝒰 q a k hk
  intro i j
  obtain ⟨b, hb⟩ := hscale i j
  have hreg := g32l4_openImmersion_regular_section
    (pullback.fst (𝒰.f i) (𝒰.f j)) ⟨⊤, isAffineOpen_top (𝒰.X i)⟩ (s i) (hs i)
  obtain ⟨u, hu⟩ := g32l4_normalized_generator_transition _ _ (k i) (k j) _ b hreg
    (by rw [hk i, map_one]) (by rw [hk j, map_one]) hb
  refine ⟨u⁻¹, fun t => ?_⟩
  rw [hu t, ← mul_assoc, Units.inv_mul, one_mul]

end HodgeLean.Foundations.Program
