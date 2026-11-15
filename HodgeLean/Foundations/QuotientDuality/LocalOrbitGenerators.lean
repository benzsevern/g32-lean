import HodgeLean.Foundations.QuotientDuality.LocalTraceDefs
import HodgeLean.Foundations.QuotientDuality.LocalOrbitConcentration
import HodgeLean.Foundations.QuotientDuality.OrientationFiberLine

/-! Invariant relative classes realizing local generators along a finite orbit. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

theorem orbit_relative_orientation_class
    (G : Type) [Group G] [Finite G] (X : TopCat.{0})
    [MulAction G X] [ContinuousConstSMul G X] [T2Space X]
    (n : ℕ) (o : LocalRationalOrientation X n)
    (hp : ∀ (g : G) (x : X), relativeHomologyMap ℚ n
      (pointDeckMap G X g x) (o.generator x) = o.generator (g⁻¹ • x))
    (y : orbitSpace G X) :
    ∃ c : RelativeHomology ℚ (orbitComplementPair G X y) n,
      (∀ (x : X) (hx : orbitMap G X x = y), relativeHomologyMap ℚ n
        (orbitPointRestriction G X y x hx) c = o.generator x) ∧
      ∀ g, relativeHomologyMap ℚ n (orbitComplementDeckMap G X y g) c = c := by
  obtain ⟨c, hc⟩ := finite_support_class_exists X
    {x : X | orbitMap G X x = y} (orbit_fiber_finite G X y) n o.generator
  change RelativeHomology ℚ (orbitComplementPair G X y) n at c
  have hc' : ∀ (x : X) (hx : orbitMap G X x = y), relativeHomologyMap ℚ n
      (orbitPointRestriction G X y x hx) c = o.generator x := hc
  refine ⟨c, hc', fun g => sub_eq_zero.mp ?_⟩
  apply finite_support_detects_zero X {x : X | orbitMap G X x = y}
    (orbit_fiber_finite G X y) n
  intro x hx
  have hz : orbitMap G X (g • x) = y := by
    trans orbitMap G X x
    · apply Quotient.sound
      exact MulAction.mem_orbit_iff.mpr ⟨g, rfl⟩
    · exact hx
  have hzx : g⁻¹ • (g • x) = x := inv_smul_smul g x
  have hzi : orbitMap G X (g⁻¹ • (g • x)) = y := by rw [hzx]; exact hx
  have he := congrArg (fun f => relativeHomologyMap ℚ n f c)
    (orbitPointRestriction_deck G X y g (g • x) hz hzi)
  rw [relativeHomologyMap_comp, relativeHomologyMap_comp,
    LinearMap.comp_apply, LinearMap.comp_apply] at he
  have heo := (congrArg
    (relativeHomologyMap ℚ n (pointDeckMap G X g (g • x))) (hc' (g • x) hz)).symm.trans he
  have hen := (hp g (g • x)).symm.trans heo
  have he' : o.generator x = relativeHomologyMap ℚ n
      (orbitPointRestriction G X y x hx)
      (relativeHomologyMap ℚ n (orbitComplementDeckMap G X y g) c) := by
    have hzsub : (⟨g⁻¹ • (g • x), hzi⟩ : {z : X // orbitMap G X z = y}) =
        ⟨x, hx⟩ := Subtype.ext hzx
    exact (congrArg (fun z : {z : X // orbitMap G X z = y} =>
      o.generator z.val = relativeHomologyMap ℚ n
        (orbitPointRestriction G X y z.val z.property)
        (relativeHomologyMap ℚ n (orbitComplementDeckMap G X y g) c)) hzsub).mp hen
  change relativeHomologyMap ℚ n (orbitPointRestriction G X y x hx)
    (relativeHomologyMap ℚ n (orbitComplementDeckMap G X y g) c - c) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr (he'.symm.trans (hc' x hx).symm)

theorem orbit_local_generator
    (G : Type) [Group G] [Fintype G] (X : TopCat.{0})
    [MulAction G X] [ContinuousConstSMul G X] [T2Space X] [PseudoMetrizableSpace X]
    [T2Space (orbitSpace G X)] [PseudoMetrizableSpace (orbitSpace G X)]
    (hX : ∀ (x : X) (U : Opens X), x ∈ U →
      ∃ V : Opens X, x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    (hY : ∀ (x : orbitSpace G X) (U : Opens (orbitSpace G X)), x ∈ U →
      ∃ V : Opens (orbitSpace G X), x ∈ V ∧ ContractibleSpace V ∧ V ≤ U)
    (n : ℕ) (o : LocalRationalOrientation X n)
    (hp : ∀ (g : G) (x : X), relativeHomologyMap ℚ n
      (pointDeckMap G X g x) (o.generator x) = o.generator (g⁻¹ • x))
    (y : orbitSpace G X) :
    ∃ v : orientationGroup (orbitSpace G X) n y,
      Function.Bijective (LinearMap.toSpanSingleton ℚ _ v) := by
  obtain ⟨c, hc, hfixed⟩ := orbit_relative_orientation_class G X n o hp y
  obtain ⟨hlift, hker⟩ := orbit_relative_descent G X hX hY y n
  let q := relativeHomologyMap ℚ n (orbitComplementPairMap G X y)
  obtain ⟨x₀, hx₀⟩ := Quotient.mk_surjective y
  refine ⟨q c, ?_, ?_⟩
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

#print axioms orbit_local_generator
#print axioms orbit_relative_orientation_class
end HodgeLean.Foundations.QuotientDuality
