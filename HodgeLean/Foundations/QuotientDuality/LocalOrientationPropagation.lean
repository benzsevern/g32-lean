import HodgeLean.Foundations.QuotientDuality.LocalOrientationCoefficients

/-! One local preservation equation propagates through a connected orientation section. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

theorem localOrientation_preserved_of_one_point
    (X : TopCat.{0}) [T2Space X] [PreconnectedSpace X]
    (n : ℕ) (o : LocalRationalOrientation X n) (c : Homology ℚ X n)
    (hc : ∀ x, localOrientation X n c x = o.generator x) (H : X ≃ₜ X)
    (x : X)
    (hx : relativeHomologyMap ℚ n (pointComplementHomeomorphPairMap H x)
      (o.generator x) = o.generator (H x)) :
    ∀ z, relativeHomologyMap ℚ n (pointComplementHomeomorphPairMap H z)
      (o.generator z) = o.generator (H z) := by
  let f := TopCat.ofHom ⟨H, H.continuous⟩
  obtain ⟨q, hq⟩ := local_values_constant X n o (homologyMap ℚ n f c)
  have hn (z : X) : relativeHomologyMap ℚ n (pointComplementHomeomorphPairMap H z)
      (o.generator z) = localOrientation X n (homologyMap ℚ n f c) (H z) := by
    exact (congrArg (relativeHomologyMap ℚ n (pointComplementHomeomorphPairMap H z))
      (hc z).symm).trans
        (localOrientation_map n z (H z) (pointComplementHomeomorphPairMap H z) c)
  have hq1 : q = 1 := (o.generates (H x)).1 (by
    change q • o.generator (H x) = (1 : ℚ) • o.generator (H x)
    exact (hq (H x)).symm.trans ((hn x).symm.trans (hx.trans (one_smul ℚ _).symm)))
  intro z
  exact (hn z).trans ((hq (H z)).trans (by rw [hq1, one_smul]))

theorem localOrientation_preserved_of_dense
    (X : TopCat.{0}) [T2Space X] (n : ℕ)
    (o : LocalRationalOrientation X n) (c : Homology ℚ X n)
    (hc : ∀ x, localOrientation X n c x = o.generator x) (H : X ≃ₜ X)
    (S : Set X) (hS : Dense S)
    (hpres : ∀ x ∈ S, relativeHomologyMap ℚ n (pointComplementHomeomorphPairMap H x)
      (o.generator x) = o.generator (H x)) :
    ∀ z, relativeHomologyMap ℚ n (pointComplementHomeomorphPairMap H z)
      (o.generator z) = o.generator (H z) := by
  let f := TopCat.ofHom ⟨H, H.continuous⟩
  obtain ⟨q, hqlc, hq⟩ := local_coefficients X n o (homologyMap ℚ n f c)
  have hn (z : X) : relativeHomologyMap ℚ n (pointComplementHomeomorphPairMap H z)
      (o.generator z) = localOrientation X n (homologyMap ℚ n f c) (H z) := by
    exact (congrArg (relativeHomologyMap ℚ n (pointComplementHomeomorphPairMap H z))
      (hc z).symm).trans
        (localOrientation_map n z (H z) (pointComplementHomeomorphPairMap H z) c)
  have hon : Set.EqOn (fun z => q (H z)) (fun _ => (1 : ℚ)) S := by
    intro x hx
    apply (o.generates (H x)).1
    change q (H x) • o.generator (H x) = (1 : ℚ) • o.generator (H x)
    exact (hq (H x)).symm.trans
      ((hn x).symm.trans ((hpres x hx).trans (one_smul ℚ _).symm))
  have hall := Continuous.ext_on hS (hqlc.continuous.comp H.continuous) continuous_const hon
  intro z
  have hz : q (H z) = 1 := congrFun hall z
  exact (hn z).trans ((hq (H z)).trans (by rw [hz, one_smul]))

#print axioms localOrientation_preserved_of_dense
#print axioms localOrientation_preserved_of_one_point
end HodgeLean.Foundations.QuotientDuality
