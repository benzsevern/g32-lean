import HodgeLean.Foundations.QuotientDuality.OrientationFiberLine

/-! Local generation from relative orbit descent. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

lemma quotient_pushforward_local_generators_of_relative_descent
    (G : Type) [Group G] [Finite G] (X : TopCat.{0})
    [MulAction G X] [ContinuousConstSMul G X] [T2Space X]
    (n : ℕ) (cX : Homology ℚ X n)
    (hlocal : ∀ x, Function.Bijective (orientationLine X n cX x))
    (hpreserve : ∀ g : G, homologyMap ℚ n (deckMap G X g) cX = cX)
    (y : orbitSpace G X)
    (hlift : ∀ u : orientationGroup (orbitSpace G X) n y,
      ∃ c : RelativeHomology ℚ (orbitComplementPair G X y) n,
        relativeHomologyMap ℚ n (orbitComplementPairMap G X y) c = u ∧
        ∀ g, relativeHomologyMap ℚ n (orbitComplementDeckMap G X y g) c = c)
    (hker : ∀ c : RelativeHomology ℚ (orbitComplementPair G X y) n,
      (∀ g, relativeHomologyMap ℚ n (orbitComplementDeckMap G X y g) c = c) →
      relativeHomologyMap ℚ n (orbitComplementPairMap G X y) c = 0 → c = 0) :
    Function.Bijective (orientationLine (orbitSpace G X) n
      (homologyMap ℚ n (orbitMap G X) cX) y) := by
  let C := (relativeHomologyProjection ℚ (orbitComplementPair G X y) n).hom cX
  let L := localOrientation (orbitSpace G X) n (homologyMap ℚ n (orbitMap G X) cX) y
  let q := relativeHomologyMap ℚ n (orbitComplementPairMap G X y)
  have hC : q C = L := orbit_local_projection G X y n cX
  have hfixedC : ∀ g, relativeHomologyMap ℚ n (orbitComplementDeckMap G X y g) C = C :=
    fun g => orbit_relative_projection_preserved G X y g n cX (hpreserve g)
  constructor
  · intro r s hrs
    change r • L = s • L at hrs
    have hzero : (r - s) • C = 0 := hker _
      (fun g => by rw [map_smul, hfixedC g]) (by
        change q ((r - s) • C) = 0
        rw [map_smul, hC, sub_smul, hrs, sub_self])
    obtain ⟨x₀, hx₀⟩ := Quotient.mk_surjective y
    have hRC : relativeHomologyMap ℚ n (orbitPointRestriction G X y x₀ hx₀) C =
        localOrientation X n cX x₀ := orbitPointRestriction_global G X y x₀ hx₀ n cX
    have hh := congrArg (relativeHomologyMap ℚ n (orbitPointRestriction G X y x₀ hx₀)) hzero
    rw [map_smul, hRC, map_zero] at hh
    have hr0 : orientationLine X n cX x₀ (r - s) = orientationLine X n cX x₀ (0 : ℚ) := by
      change (r - s) • localOrientation X n cX x₀ = (0 : ℚ) • localOrientation X n cX x₀
      rw [zero_smul]
      exact hh
    exact sub_eq_zero.mp ((hlocal x₀).1 hr0)
  · intro u
    obtain ⟨c, hc, hfixed⟩ := hlift u
    obtain ⟨r, hr⟩ := orbit_fixed_class_scalar G X n cX (fun x => (hlocal x).2)
      hpreserve y c hfixed
    refine ⟨r, ?_⟩
    change r • L = u
    calc
      _ = q (r • C) := by rw [map_smul, hC]
      _ = q c := congrArg q hr.symm
      _ = u := hc

end HodgeLean.Foundations.QuotientDuality
