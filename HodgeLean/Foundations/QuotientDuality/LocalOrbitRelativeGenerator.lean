import HodgeLean.Foundations.QuotientDuality.LocalTraceDefs
import HodgeLean.Foundations.QuotientDuality.OrientationRelativeDescent
import HodgeLean.Foundations.QuotientDuality.OrientationFiberLine

/-! Local generation by a specified invariant relative orientation class. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

theorem orbit_relative_class_generates
    (G : Type) [Group G] [Fintype G] (X : TopCat.{0})
    [MulAction G X] [ContinuousConstSMul G X] [T2Space X] [PseudoMetrizableSpace X]
    [T2Space (orbitSpace G X)] [PseudoMetrizableSpace (orbitSpace G X)]
    (hX : ∀ (x : X) (U : Opens X), x ∈ U →
      ∃ V : Opens X, x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    (hY : ∀ (x : orbitSpace G X) (U : Opens (orbitSpace G X)), x ∈ U →
      ∃ V : Opens (orbitSpace G X), x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    (n : ℕ) (o : LocalRationalOrientation X n)
    (y : orbitSpace G X)
    (c : RelativeHomology ℚ (orbitComplementPair G X y) n)
    (hc : ∀ (x : X) (hx : orbitMap G X x = y), relativeHomologyMap ℚ n
      (orbitPointRestriction G X y x hx) c = o.generator x)
    (hfixed : ∀ g, relativeHomologyMap ℚ n (orbitComplementDeckMap G X y g) c = c) :
    Function.Bijective (LinearMap.toSpanSingleton ℚ _
      (relativeHomologyMap ℚ n (orbitComplementPairMap G X y) c)) := by
  obtain ⟨hlift, hker⟩ := orbit_relative_descent G X hX hY y n
  let q := relativeHomologyMap ℚ n (orbitComplementPairMap G X y)
  obtain ⟨x₀, hx₀⟩ := Quotient.mk_surjective y
  refine ⟨?_, ?_⟩
  · intro r s hrs
    change r • q c = s • q c at hrs
    have hz : (r - s) • c = 0 := hker _
      (fun g => by rw [map_smul, hfixed g]) (by
        change q ((r - s) • c) = 0
        rw [map_smul, sub_smul, hrs, sub_self])
    have ht := congrArg
      (relativeHomologyMap ℚ n (orbitPointRestriction G X y x₀ hx₀)) hz
    rw [map_smul, hc, map_zero] at ht
    have he : LinearMap.toSpanSingleton ℚ _ (o.generator x₀) (r - s) =
        LinearMap.toSpanSingleton ℚ _ (o.generator x₀) (0 : ℚ) := by
      change (r - s) • o.generator x₀ = (0 : ℚ) • o.generator x₀
      rw [zero_smul]
      exact ht
    exact sub_eq_zero.mp ((o.generates x₀).1 he)
  · intro u
    obtain ⟨d, hd, hdfixed⟩ := hlift u
    obtain ⟨r, hr⟩ := (o.generates x₀).2
      (relativeHomologyMap ℚ n (orbitPointRestriction G X y x₀ hx₀) d)
    have hdr : d = r • c := sub_eq_zero.mp (by
      apply orbit_fixed_class_detected_at_one_point G X y x₀ hx₀ n
      · intro g
        rw [map_sub, map_smul, hdfixed g, hfixed g]
      · rw [map_sub, map_smul, hc]
        change relativeHomologyMap ℚ n (orbitPointRestriction G X y x₀ hx₀) d -
          r • o.generator x₀ = 0
        exact sub_eq_zero.mpr hr.symm)
    refine ⟨r, ?_⟩
    change r • q c = u
    rw [← map_smul, ← hdr]
    exact hd

#print axioms orbit_relative_class_generates
end HodgeLean.Foundations.QuotientDuality
