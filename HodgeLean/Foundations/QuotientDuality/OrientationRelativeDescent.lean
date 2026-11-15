import HodgeLean.Foundations.QuotientDuality.OrientationOrbitDescent

/-! Fixed relative lifts and detection for the actual quotient pair map. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

lemma orbit_relative_descent
    (G : Type) [Group G] [Fintype G] (X : TopCat.{0})
    [MulAction G X] [ContinuousConstSMul G X] [T2Space X] [PseudoMetrizableSpace X]
    [T2Space (orbitSpace G X)] [PseudoMetrizableSpace (orbitSpace G X)]
    (hX : ∀ (x : X) (U : Opens X), x ∈ U →
      ∃ V : Opens X, x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    (hY : ∀ (x : orbitSpace G X) (U : Opens (orbitSpace G X)), x ∈ U →
      ∃ V : Opens (orbitSpace G X), x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    (y : orbitSpace G X) (n : ℕ) :
    (∀ u : orientationGroup (orbitSpace G X) n y,
      ∃ c : RelativeHomology ℚ (orbitComplementPair G X y) n,
        relativeHomologyMap ℚ n (orbitComplementPairMap G X y) c = u ∧
        ∀ g, relativeHomologyMap ℚ n (orbitComplementDeckMap G X y g) c = c) ∧
    (∀ c : RelativeHomology ℚ (orbitComplementPair G X y) n,
      (∀ g, relativeHomologyMap ℚ n (orbitComplementDeckMap G X y g) c = c) →
      relativeHomologyMap ℚ n (orbitComplementPairMap G X y) c = 0 → c = 0) := by
  let P := orbitComplementPair G X y
  let ρ := pairRelativeChainAction G P (orbitComplementAction G X y)
  let R := complexHomologyRepresentation G (relativeChainShortComplex ℚ P).X₃ ρ n
  letI := orbit_relative_comparison_quasiIso G X hX hY y
  have hb : Function.Bijective (fun z : R.invariants =>
      relativeHomologyMap ℚ n (orbitComplementPairMap G X y) z.1) :=
    invariant_map_fixed_bijective G ρ ((relativeChainFunctor ℚ).map (orbitComplementPairMap G X y)) n
  have hfixed (z : R.invariants) (g : G) :
      relativeHomologyMap ℚ n (orbitComplementDeckMap G X y g) z.1 = z.1 := by
    have h := z.2 g⁻¹
    change relativeHomologyMap ℚ n (orbitComplementDeckMap G X y (g⁻¹)⁻¹) z.1 = z.1 at h
    simpa only [inv_inv] using h
  constructor
  · intro u
    obtain ⟨z, hz⟩ := hb.2 u
    exact ⟨z.1, hz, hfixed z⟩
  · intro c hc hz
    have hcinv : c ∈ R.invariants := by
      intro g
      change relativeHomologyMap ℚ n (orbitComplementDeckMap G X y g⁻¹) c = c
      exact hc g⁻¹
    have he : (⟨c, hcinv⟩ : R.invariants) = 0 := hb.1 (by
      change relativeHomologyMap ℚ n (orbitComplementPairMap G X y) c =
        relativeHomologyMap ℚ n (orbitComplementPairMap G X y) 0
      rw [map_zero]
      exact hz)
    exact congrArg Subtype.val he

end HodgeLean.Foundations.QuotientDuality
