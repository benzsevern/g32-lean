import HodgeLean.Foundations.QuotientDuality.LocalSupportedGeneratorLocus
import HodgeLean.Foundations.QuotientDuality.LocalOrbitNeighborhood
import HodgeLean.Foundations.QuotientDuality.LocalOrbitGenerators
import HodgeLean.RealDefs.ComplexFundamentalClassParts.C_OpenLift

/-! Supported orientation classes on neighborhoods of whole quotient fibres. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular HodgeLean.RealDefs
namespace HodgeLean.Foundations.QuotientDuality

theorem orbit_orientation_neighborhood
    (G : Type) [Group G] [Finite G] (X : TopCat.{0})
    [MulAction G X] [ContinuousConstSMul G X] [T2Space X]
    (n : ℕ) (o : LocalRationalOrientation X n) (y : orbitSpace G X)
    (c : RelativeHomology ℚ (orbitComplementPair G X y) n)
    (hc : ∀ (x : X) (hx : orbitMap G X x = y), relativeHomologyMap ℚ n
      (orbitPointRestriction G X y x hx) c = o.generator x) :
    ∃ (V : Opens (orbitSpace G X)), y ∈ V ∧
      ∃ w : RelativeHomology ℚ (TopPair.ofSubset
        (X := X) (orbitMap G X ⁻¹' (V : Set (orbitSpace G X)))ᶜ) n,
        ∀ (x : X) (hx : orbitMap G X x ∈ V), relativeHomologyMap ℚ n
          (supportInclusionPairMap X (Set.singleton_subset_iff.mpr hx)) w = o.generator x := by
  let A : Set X := {x | orbitMap G X x = y}
  obtain ⟨W, hWo, hAW, hlift⟩ := C_exists_open_lift A n c
  obtain ⟨w, hw⟩ := hlift W hAW Set.Subset.rfl
  change RelativeHomology ℚ (TopPair.ofSubset (X := X) Wᶜ) n at w
  let U : Opens X := ⟨W, hWo⟩
  let L : Opens X := ⟨{x : X | ∃ hx : x ∈ U, relativeHomologyMap ℚ n
      (supportInclusionPairMap X (Set.singleton_subset_iff.mpr hx)) w = o.generator x},
    supported_generator_locus_isOpen X n o U w⟩
  have hAL (x : X) (hx : orbitMap G X x = y) : x ∈ L := by
    refine ⟨hAW hx, ?_⟩
    have ht := relativeHomologyMap_supportInclusion_trans
      (M := X) (Set.singleton_subset_iff.mpr hx) hAW n w
    exact ht.symm.trans ((congrArg
      (relativeHomologyMap ℚ n (orbitPointRestriction G X y x hx)) hw).trans (hc x hx))
  obtain ⟨V, hyV, hVL⟩ := orbit_saturated_neighborhood G X y L hAL
  have hVW : orbitMap G X ⁻¹' (V : Set (orbitSpace G X)) ⊆ W := by
    intro x hx
    exact (hVL x hx).choose
  let wV := relativeHomologyMap ℚ n (supportInclusionPairMap X hVW) w
  refine ⟨V, hyV, wV, fun x hx => ?_⟩
  have hxL := hVL x hx
  obtain ⟨hxU, he⟩ := hxL
  have ht := relativeHomologyMap_supportInclusion_trans
    (M := X) (Set.singleton_subset_iff.mpr hx) hVW n w
  exact ht.trans he

#print axioms orbit_orientation_neighborhood
end HodgeLean.Foundations.QuotientDuality
