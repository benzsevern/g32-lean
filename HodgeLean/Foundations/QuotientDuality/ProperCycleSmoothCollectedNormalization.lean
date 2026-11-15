import HodgeLean.Foundations.QuotientDuality.ProperCycleSmoothSupportCollectedNormalization

/-! # Global original normalization of exactly descended classes in smooth ambient schemes -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Program
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

/-- In a smooth ambient scheme, an exact collected lift of independent normalized representatives retains every original complex chart normalization.
Source: Fulton, Intersection Theory, section 19.1; Bredon, Sheaf Theory, second edition, II.10 and V.9.
HC no distance; AV milestone no distance. -/
lemma properCycle_smooth_collected_lift_normalized
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom] [Smooth X.hom]
    (k : ℕ) (hk : 0 < k) (hdim : TopologicalSpace.dim X.left = 2 * k)
    (hvan : ∀ j : ℕ, j ≠ 2 * (2 * k) → ∀ x : a3b4_an X.hom,
      Subsingleton (orientationGroup (a3b4_an X.hom) j x))
    {I : Type} [Fintype I] (γ : I → AlgebraicCycle X.left ℚ) (q : I → ℚ)
    (hcodim : ∀ i ξ, ξ ∈ (γ i).support → Order.coheight ξ = k)
    (a : ∀ i, s2e_supportedClass X (γ i) k)
    (ha : ∀ i, a3b4_IsCycleClass X.hom (γ i) k (a i))
    (s : s2e_supportedClass X (∑ i, (γ i).mapRange (q i * ·) (mul_zero _)) k)
    (hs : enlargeSupport ℚ (a3b4_an X.hom) (properCycle_collected_support_subset X γ q) (2 * k) s =
      SupportedClasses.weightedSum (a3b4_an X.hom) (2 * k)
        (fun i => a3b4_cycleSupport X.hom (γ i))
        (⋃ i, ⋃ (_ : q i ≠ 0), a3b4_cycleSupport X.hom (γ i)) q
        (fun i hi y hy => Set.mem_iUnion₂.mpr ⟨i, hi, hy⟩) a) :
    a3b4_IsCycleClass X.hom (∑ i, (γ i).mapRange (q i * ·) (mul_zero _)) k s := by
  apply properCycle_collected_lift_normalized_on_smooth_support X k hk hdim hvan γ q hcodim a ha
    (s := s) (hs := hs)
  intro x _
  obtain ⟨U, hU, hxU, _⟩ := Smooth.exists_affine_isStandardSmooth X.hom x.underlying
  exact ⟨U, hU, hxU, inferInstanceAs (Smooth (U.ι ≫ X.hom))⟩

end HodgeLean.Foundations.QuotientDuality
