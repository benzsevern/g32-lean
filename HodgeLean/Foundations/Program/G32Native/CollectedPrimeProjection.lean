import HodgeLean.Foundations.Program.G32Native.CollectedPrimeClasses
import HodgeLean.Foundations.Program.G32Native.AbsolutePrimePairing
import HodgeLean.Foundations.QuotientDuality.ProperCycleCollection

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
open HodgeLean.Foundations.QuotientDuality HodgeLean.Foundations.Analytic
open scoped BigOperators Classical
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program.G32Native

/-- Intrinsic normalization supplies both collected classes and their projection
pairing for the retained fundamental classes. Images may repeat.
Source: Fulton, Intersection Theory, second edition, 1.4 and 19.1–19.2;
Bredon, Sheaf Theory, second edition, V.9.
-/
theorem collected_prime_projection
    {W W₀ : Over (Spec ↧ℂ)} [IsIntegral W.left] [IsIntegral W₀.left]
    [IsProjective W.hom] [IsProjective W₀.hom]
    (φ : W ⟶ W₀) [IsProper φ.left] (k : ℕ)
    (hdim : TopologicalSpace.dim W.left = 2*k)
    (hdim₀ : TopologicalSpace.dim W₀.left = 2*k)
    (o : LocalRationalOrientation (a3b4_an W.hom) (2*(2*k)))
    (cW : Homology ℚ (a3b4_an W.hom) (2*(2*k)))
    (ho : ∀ x, localOrientation (a3b4_an W.hom) (2*(2*k)) cW x = o.generator x)
    (hchart : ∀ (E : OpenPartialHomeomorph (ComplexPoint W) (Fin (2*k) → ℂ)),
      (∀ j, (f4_analytification W).IsHolFun (fun u : E.source => E u j)) →
      ∀ x (hx : x ∈ E.source), localOrientation (a3b4_an W.hom) (2*(2*k)) cW x =
        localClassOfChart (2*k) E x hx)
    (hp : Function.Injective (properCyclePairing (a3b4_an W.hom) k cW))
    (o₀ : LocalRationalOrientation (a3b4_an W₀.hom) (2*(2*k)))
    (c₀ : Homology ℚ (a3b4_an W₀.hom) (2*(2*k)))
    (ho₀ : ∀ x, localOrientation (a3b4_an W₀.hom) (2*(2*k)) c₀ x = o₀.generator x)
    (hchart₀ : ∀ (E : OpenPartialHomeomorph (ComplexPoint W₀) (Fin (2*k) → ℂ)),
      (∀ j, (f4_analytification W₀).IsHolFun (fun u : E.source => E u j)) →
      ∀ x (hx : x ∈ E.source), localOrientation (a3b4_an W₀.hom) (2*(2*k)) c₀ x =
        localClassOfChart (2*k) E x hx)
    (hp₀ : Function.Injective (properCyclePairing (a3b4_an W₀.hom) k c₀))
    {I : Type} [Fintype I] (ξ : I → W.left)
    (hc : ∀ i, Order.coheight (ξ i) = k)
    (hd : ∀ i, 0 < a1p_degree φ.left (ξ i))
    : ∃ a : ∀ i, s2e_supportedClass W (properPrime (ξ i)) k,
      (∀ i, a3b4_IsCycleClass W.hom (properPrime (ξ i)) k (a i)) ∧
      ∀ q : I → ℚ,
        let Γ := ∑ i, (properPrime (ξ i)).mapRange (q i * ·) (mul_zero _)
        ∃ cr : s2e_supportedClass W Γ k,
          a3b4_IsCycleClass W.hom Γ k cr ∧
          s2e_classToAbsolute W Γ k cr =
            ∑ i, q i • s2e_classToAbsolute W (properPrime (ξ i)) k (a i) ∧
          ∃ c : s2e_supportedClass W₀ (a1p_pushforward φ.left Γ) k,
            a3b4_IsCycleClass W₀.hom (a1p_pushforward φ.left Γ) k c ∧
            ∀ u, properCyclePairing (a3b4_an W₀.hom) k c₀
              (s2e_classToAbsolute W₀ (a1p_pushforward φ.left Γ) k c) u =
              properCyclePairing (a3b4_an W.hom) k cW
                (s2e_classToAbsolute W Γ k cr) (s2e_pullback ℚ φ (2*k) u) := by
  have hline : ∀ x, Function.Bijective (orientationLine (a3b4_an W.hom) (2*(2*k)) cW x) := by
    intro x
    simpa only [orientationLine, ho] using o.generates x
  have hline₀ : ∀ x, Function.Bijective (orientationLine (a3b4_an W₀.hom) (2*(2*k)) c₀ x) := by
    intro x
    simpa only [orientationLine, ho₀] using o₀.generates x
  have hc₀ : ∀ i, Order.coheight (φ.left (ξ i)) = k := fun i =>
    (retained_positive_degree_coheight φ (2*k) hdim hdim₀ (ξ i) (hd i)).trans (hc i)
  obtain ⟨a, ha, hna, hsum⟩ := collected_prime_classes W k hdim cW hline
    (fun j hj x => o.vanishes x j hj) hchart hp ξ hc
  obtain ⟨b, hb, hnb, hsum₀⟩ := collected_prime_classes W₀ k hdim₀ c₀ hline₀
    (fun j hj x => o₀.vanishes x j hj) hchart₀ hp₀ (fun i => φ.left (ξ i)) hc₀
  refine ⟨a, ha, ?_⟩
  intro q
  obtain ⟨cr, hcr, hr⟩ := hsum q
  have hex := hsum₀ (fun i => q i * (a1p_degree φ.left (ξ i) : ℚ))
  have hpush : a1p_pushforward φ.left
      (∑ i, (properPrime (ξ i)).mapRange (q i * ·) (mul_zero _)) =
      ∑ i, (properPrime (φ.left (ξ i))).mapRange
        ((q i * (a1p_degree φ.left (ξ i) : ℚ)) * ·) (mul_zero _) := by
    rw [properCycle_pushforward_weighted_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [retained_prime_pushforward_formula]
    ext x
    simp only [Function.locallyFinsuppWithin.mapRange_apply, mul_assoc]
  rw [← hpush] at hex
  obtain ⟨c, hclass, ht⟩ := hex
  refine ⟨cr, hcr, hr, c, hclass, ?_⟩
  intro u
  rw [hr, ht]
  simpa only [mul_smul] using absolute_pairing_rational_family
    (properCyclePairing (a3b4_an W.hom) k cW)
    (properCyclePairing (a3b4_an W₀.hom) k c₀) (s2e_pullback ℚ φ (2*k))
    (fun i => s2e_classToAbsolute W (properPrime (ξ i)) k (a i))
    (fun i => (a1p_degree φ.left (ξ i) : ℚ) •
      s2e_classToAbsolute W₀ (properPrime (φ.left (ξ i))) k (b i))
    (fun i => absolute_prime_pairing φ k hdim hdim₀ cW c₀ (ξ i) (hc i) (hd i)
      (a i) (b i) (hna i) (hnb i)) q u

#print axioms collected_prime_projection
end HodgeLean.Foundations.Program.G32Native
