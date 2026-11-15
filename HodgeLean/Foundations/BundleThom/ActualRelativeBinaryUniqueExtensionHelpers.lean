import HodgeLean.Foundations.BundleThom.ActualIntersectionCoclassDetectionHelpers

/-! # Unique extensions of compatible actual binary-domain coclasses -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- Compatible relative domain coclasses have a unique extension when the actual intersection homology in the preceding degree vanishes.
Source: Hatcher, Algebraic Topology, §2.2 and §3.1, relative Mayer–Vietoris. -/
theorem i1_actualRelativeBinaryCoclass_exists_unique (X : TopCat) (Z U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ)
    (hzero : IsZero (((relativeChainFunctor ℚ).obj (i1_subsetRelativePair X Z (U ∩ V))).homology n))
    (u : RelativeCohomology ℚ (i1_subsetRelativePair X Z U) (n + 1))
    (v : RelativeCohomology ℚ (i1_subsetRelativePair X Z V) (n + 1))
    (huv : relativeCohomologyMap ℚ (n + 1)
        (i1_subsetRelativePairMap X Z (Set.inter_subset_left : U ∩ V ⊆ U)) u =
      relativeCohomologyMap ℚ (n + 1)
        (i1_subsetRelativePairMap X Z (Set.inter_subset_right : U ∩ V ⊆ V)) v) :
    ∃! z : RelativeCohomology ℚ (TopPair.ofSubset (X := X) Z) (n + 1),
      relativeCohomologyMap ℚ (n + 1) (i1_subsetRelativePairInclusion X Z U) z = u ∧
      relativeCohomologyMap ℚ (n + 1) (i1_subsetRelativePairInclusion X Z V) z = v := by
  obtain ⟨z, hzU, hzV⟩ :=
    i1_actualRelativeBinaryCoclass_gluing X Z U V hU hV hcover (n + 1) u v huv
  refine ⟨z, ⟨hzU, hzV⟩, ?_⟩
  intro w hw
  exact i1_actualIntersectionBinaryCoclass_ext X Z U V hU hV hcover n hzero w z
    (hw.1.trans hzU.symm) (hw.2.trans hzV.symm)

end HodgeLean.Foundations.BundleThom
