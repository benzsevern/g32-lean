import HodgeLean.Foundations.Program.SchoenCycleFiniteQuotientCohomology

/-! # From rational transfer identities to quotient comparison
The degree and norm equations imply injectivity and the invariant-image formula.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular
namespace HodgeLean.Foundations.Program

/-- The norm identity for a homology transfer gives descent of invariant cohomology.
Source: Bredon, Sheaf Theory, second edition, Chapter V, finite quotient
comparison; Hatcher, Algebraic Topology, §3.1, natural universal coefficients. -/
theorem s2e_quotient_pullback_range_of_homology_transfer
    {X Y : Over (Spec ↧ℂ)} (G : Type) [Group G] [Fintype G]
    (a : G → (X ⟶ X)) (q : X ⟶ Y)
    (hinv : ∀ u, a u ≫ q = q) (n : ℕ)
    (T : Homology ℚ (TopCat.of (ComplexPoint Y)) n →ₗ[ℚ]
      Homology ℚ (TopCat.of (ComplexPoint X)) n)
    (hnorm : T.comp (homologyMap ℚ n (TopCat.ofHom (Point.continuousMap q))) =
      ∑ g : G, homologyMap ℚ n (TopCat.ofHom (Point.continuousMap (a g))))
    (b : Cohomology ℚ (TopCat.of (ComplexPoint X)) n) :
    (∃ c, s2e_pullback ℚ q n c = b) ↔ ∀ g, s2e_pullback ℚ (a g) n b = b := by
  constructor
  · rintro ⟨c, rfl⟩ g
    exact s2e_quotient_pullback_invariant G a q hinv n c g
  · intro hb
    let eX := cohomologyEquivDualHomology ℚ (TopCat.of (ComplexPoint X)) n
    let eY := cohomologyEquivDualHomology ℚ (TopCat.of (ComplexPoint Y)) n
    let l := (Fintype.card G : ℚ)⁻¹ • (eX b).comp T
    refine ⟨eY.symm l, eX.injective ?_⟩
    ext z
    change eX (cohomologyMap ℚ n (TopCat.ofHom (Point.continuousMap q))
      (eY.symm l)) z = eX b z
    rw [cohomologyEquivDualHomology_cohomologyMap, LinearEquiv.apply_symm_apply]
    change (Fintype.card G : ℚ)⁻¹ •
      eX b (T (homologyMap ℚ n (TopCat.ofHom (Point.continuousMap q)) z)) = eX b z
    have hn := LinearMap.congr_fun hnorm z
    simp only [LinearMap.comp_apply, LinearMap.sum_apply] at hn
    rw [hn, map_sum]
    have hg (g : G) :
        eX b (homologyMap ℚ n (TopCat.ofHom (Point.continuousMap (a g))) z) = eX b z := by
      rw [← cohomologyEquivDualHomology_cohomologyMap]
      exact congrArg (fun c => eX c z) (hb g)
    simp_rw [hg]
    have hc : (Fintype.card G : ℚ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    simp only [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℚ,
      smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- The degree and norm equations give the full rational invariant comparison,
with the specified pullback formula.
Source: Bredon, Sheaf Theory, second edition, Chapter V, finite quotient
comparison; Hatcher, Algebraic Topology, §3.1, natural universal coefficients. -/
theorem s2e_quotient_comparison_of_homology_transfer
    {X Y : Over (Spec ↧ℂ)} (G : Type) [Group G] [Fintype G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) (hinv : ∀ u, a u ≫ q = q) (n : ℕ)
    (T : Homology ℚ (TopCat.of (ComplexPoint Y)) n →ₗ[ℚ]
      Homology ℚ (TopCat.of (ComplexPoint X)) n)
    (hdegree : (homologyMap ℚ n (TopCat.ofHom (Point.continuousMap q))).comp T =
      (Fintype.card G : ℚ) • LinearMap.id)
    (hnorm : T.comp (homologyMap ℚ n (TopCat.ofHom (Point.continuousMap q))) =
      ∑ g : G, homologyMap ℚ n (TopCat.ofHom (Point.continuousMap (a g)))) :
    ∃ e : Cohomology ℚ (TopCat.of (ComplexPoint Y)) n ≃ₗ[ℚ]
        (s2e_quotientCohomologyRepresentation X G a ha1 hamul n).invariants,
      ∀ c, (e c).val = s2e_pullback ℚ q n c := by
  let f := s2e_quotientPullbackToInvariants G a ha1 hamul q hinv n
  have hc : (Fintype.card G : ℚ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hq : Function.Injective (s2e_pullback ℚ q n) :=
    s2e_cohomology_injective_of_homology_transfer
      (TopCat.ofHom (Point.continuousMap q)) n (Fintype.card G : ℚ) hc T hdegree
  have hi : Function.Injective f := fun _ _ h => hq (congrArg Subtype.val h)
  have hs : Function.Surjective f := by
    intro b
    have hb (g : G) : s2e_pullback ℚ (a g) n b.val = b.val := by
      have h := b.property g⁻¹
      change s2e_pullback ℚ (a (g⁻¹)⁻¹) n b.val = b.val at h
      simpa only [inv_inv] using h
    obtain ⟨c, hc⟩ :=
      (s2e_quotient_pullback_range_of_homology_transfer G a q hinv n T hnorm b.val).mpr hb
    exact ⟨c, Subtype.ext hc⟩
  exact ⟨LinearEquiv.ofBijective f ⟨hi, hs⟩, fun _ => rfl⟩

end HodgeLean.Foundations.Program
