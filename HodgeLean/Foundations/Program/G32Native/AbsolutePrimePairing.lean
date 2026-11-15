import HodgeLean.Foundations.QuotientDuality.RetainedCycleIntrinsicDegree
import HodgeLean.Foundations.QuotientDuality.RetainedCyclePrimePushforward

/-! Absolute prime comparison with intrinsic integration inputs retained explicitly. -/
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
open HodgeLean.Foundations.QuotientDuality
open scoped BigOperators Classical
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program.G32Native

/-- The absolute pairing of the source prime equals the residue-degree weighted
pairing of its image prime, for classes with the specified intrinsic normalization.
Source: Fulton, Intersection Theory, second edition, 19.1–19.2.
Proof plan: substitute the two intrinsic integration equations and apply the
proper intrinsic component degree formula. -/
theorem absolute_prime_pairing
    {W W₀ : Over (Spec ↧ℂ)} [IsIntegral W.left] [IsIntegral W₀.left]
    [IsProjective W.hom] [IsProjective W₀.hom]
    (f : W ⟶ W₀) [IsProper f.left] (k : ℕ)
    (hW : TopologicalSpace.dim W.left = 2*k)
    (h₀ : TopologicalSpace.dim W₀.left = 2*k)
    (cW : Homology ℚ (a3b4_an W.hom) (2*(2*k)))
    (c₀ : Homology ℚ (a3b4_an W₀.hom) (2*(2*k)))
    (ξ : W.left) (hc : Order.coheight ξ = k) (hd : 0 < a1p_degree f.left ξ)
    (a : s2e_supportedClass W (properPrime ξ) k)
    (b : s2e_supportedClass W₀ (properPrime (f.left ξ)) k)
    (hnW : ∀ u, properCyclePairing (a3b4_an W.hom) k cW
      (s2e_classToAbsolute W (properPrime ξ) k a) u =
      orientationIntegral (a3b4_an (intrinsicComponent W ξ).hom) (2*k)
        (retainedIntrinsicFundamentalClass W k hW ξ hc)
        (s2e_pullback ℚ (intrinsicComponentInclusion W ξ) (2*k) u))
    (hn₀ : ∀ u, properCyclePairing (a3b4_an W₀.hom) k c₀
      (s2e_classToAbsolute W₀ (properPrime (f.left ξ)) k b) u =
      orientationIntegral (a3b4_an (intrinsicComponent W₀ (f.left ξ)).hom) (2*k)
        (retainedIntrinsicFundamentalClass W₀ k h₀ (f.left ξ)
          ((retained_positive_degree_coheight f (2*k) hW h₀ ξ hd).trans hc))
        (s2e_pullback ℚ (intrinsicComponentInclusion W₀ (f.left ξ)) (2*k) u)) :
    ∀ u, properCyclePairing (a3b4_an W₀.hom) k c₀
      ((a1p_degree f.left ξ : ℚ) • s2e_classToAbsolute W₀ (properPrime (f.left ξ)) k b) u =
      properCyclePairing (a3b4_an W.hom) k cW
        (s2e_classToAbsolute W (properPrime ξ) k a) (s2e_pullback ℚ f (2*k) u) := by
  intro u
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, hn₀, hnW]
  exact (retained_intrinsic_degree_integral f k hW h₀ ξ hc hd u).symm

/-- Finite rational combinations preserve an all-test-class pairing equation.
Source: Fulton, Intersection Theory, second edition, 19.1–19.2, rational linearity.
Proof plan: distribute the two linear pairings over the finite weighted sums. -/
theorem absolute_pairing_rational_family
    {V U : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup U] [Module ℚ U]
    (BV : V →ₗ[ℚ] Module.Dual ℚ V) (BU : U →ₗ[ℚ] Module.Dual ℚ U)
    (f : U →ₗ[ℚ] V) {I : Type*} [Fintype I] (a : I → V) (b : I → U)
    (h : ∀ i u, BU (b i) u = BV (a i) (f u)) (q : I → ℚ) :
    ∀ u, BU (∑ i, q i • b i) u = BV (∑ i, q i • a i) (f u) := by
  intro u
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Finset.sum_congr rfl (fun i _ => congrArg (fun z => q i • z) (h i u))

/-- The exact intrinsic prime supplier outputs yield normalized source and image
witnesses with the residue-degree absolute pairing equation.
Source: Fulton, Intersection Theory, second edition, 19.1–19.2.
Proof plan: retain the two supplied normalized witnesses and apply intrinsic degree.
The source and target arguments are the outputs of stage nine's intrinsic prime
class interface, rather than a supported transfer. -/
theorem absolute_normalized_prime_witnesses
    {W W₀ : Over (Spec ↧ℂ)} [IsIntegral W.left] [IsIntegral W₀.left]
    [IsProjective W.hom] [IsProjective W₀.hom]
    (f : W ⟶ W₀) [IsProper f.left] (k : ℕ)
    (hW : TopologicalSpace.dim W.left = 2*k)
    (h₀ : TopologicalSpace.dim W₀.left = 2*k)
    (cW : Homology ℚ (a3b4_an W.hom) (2*(2*k)))
    (c₀ : Homology ℚ (a3b4_an W₀.hom) (2*(2*k)))
    (ξ : W.left) (hc : Order.coheight ξ = k) (hd : 0 < a1p_degree f.left ξ)
    (source : ∃! a : s2e_supportedClass W (properPrime ξ) k,
      a3b4_IsCycleClass W.hom (properPrime ξ) k a ∧
      ∀ u, properCyclePairing (a3b4_an W.hom) k cW
      (s2e_classToAbsolute W (properPrime ξ) k a) u =
      orientationIntegral (a3b4_an (intrinsicComponent W ξ).hom) (2*k)
        (retainedIntrinsicFundamentalClass W k hW ξ hc)
        (s2e_pullback ℚ (intrinsicComponentInclusion W ξ) (2*k) u))
    (target : ∃! b : s2e_supportedClass W₀ (properPrime (f.left ξ)) k,
      a3b4_IsCycleClass W₀.hom (properPrime (f.left ξ)) k b ∧
      ∀ u, properCyclePairing (a3b4_an W₀.hom) k c₀
      (s2e_classToAbsolute W₀ (properPrime (f.left ξ)) k b) u =
      orientationIntegral (a3b4_an (intrinsicComponent W₀ (f.left ξ)).hom) (2*k)
        (retainedIntrinsicFundamentalClass W₀ k h₀ (f.left ξ)
          ((retained_positive_degree_coheight f (2*k) hW h₀ ξ hd).trans hc))
        (s2e_pullback ℚ (intrinsicComponentInclusion W₀ (f.left ξ)) (2*k) u)) :
    ∃ a : s2e_supportedClass W (properPrime ξ) k,
      a3b4_IsCycleClass W.hom (properPrime ξ) k a ∧
      ∃ b : s2e_supportedClass W₀ (properPrime (f.left ξ)) k,
        a3b4_IsCycleClass W₀.hom (properPrime (f.left ξ)) k b ∧
        ∀ u, properCyclePairing (a3b4_an W₀.hom) k c₀
          ((a1p_degree f.left ξ : ℚ) •
            s2e_classToAbsolute W₀ (properPrime (f.left ξ)) k b) u =
          properCyclePairing (a3b4_an W.hom) k cW
            (s2e_classToAbsolute W (properPrime ξ) k a)
            (s2e_pullback ℚ f (2*k) u) := by
  obtain ⟨a, ⟨ha, hnW⟩, _⟩ := source
  obtain ⟨b, ⟨hb, hn₀⟩, _⟩ := target
  exact ⟨a, ha, b, hb, absolute_prime_pairing f k hW h₀ cW c₀ ξ hc hd a b hnW hn₀⟩

/-- A contracted prime has zero absolute pairing against every target pullback.
Source: Fulton, Intersection Theory, second edition, 1.4 and 19.1–19.2.
Proof plan: evaluate on the ambient component image, use homology naturality,
and substitute the zero residue degree. -/
theorem absolute_contracted_prime_pairing
    {W W₀ : Over (Spec ↧ℂ)} [IsIntegral W.left] [IsIntegral W₀.left]
    [IsProjective W.hom] [IsProjective W₀.hom]
    (f : W ⟶ W₀) [IsProper f.left] (k : ℕ)
    (hW : TopologicalSpace.dim W.left = 2*k)
    (h₀ : TopologicalSpace.dim W₀.left = 2*k)
    (cW : Homology ℚ (a3b4_an W.hom) (2*(2*k)))
    (ξ : W.left) (hc : Order.coheight ξ = k) (hd : a1p_degree f.left ξ = 0)
    (a : s2e_supportedClass W (properPrime ξ) k)
    (hnW : ∀ u, properCyclePairing (a3b4_an W.hom) k cW
      (s2e_classToAbsolute W (properPrime ξ) k a) u =
      orientationIntegral (a3b4_an (intrinsicComponent W ξ).hom) (2*k)
        (retainedIntrinsicFundamentalClass W k hW ξ hc)
        (s2e_pullback ℚ (intrinsicComponentInclusion W ξ) (2*k) u)) :
    ∀ u, properCyclePairing (a3b4_an W.hom) k cW
      (s2e_classToAbsolute W (properPrime ξ) k a) (s2e_pullback ℚ f (2*k) u) = 0 := by
  intro u
  rw [hnW, retained_intrinsic_integral_component_image W k hW ξ hc]
  change cohomologyEquivDualHomology ℚ (a3b4_an W.hom) (2*k)
    (cohomologyMap ℚ (2*k) (TopCat.ofHom (Point.continuousMap f)) u)
      (properCycle_intrinsic_component W k ξ) = 0
  rw [cohomologyEquivDualHomology_cohomologyMap,
    properCycle_intrinsic_component_degree_aux f k hW h₀ ξ hc, hd,
    Nat.cast_zero, zero_smul, map_zero]

end HodgeLean.Foundations.Program.G32Native
