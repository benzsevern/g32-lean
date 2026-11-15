import HodgeLean.Foundations.BundleThom.ProductFiniteCoverCoclassHelpers
import HodgeLean.Foundations.BundleThom.EmptyPairCoclassHelpers

/-! # Local detection of degree-two product coclasses over compact bases

Compactness is used only to extract finitely many actual open base restrictions.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

/-- On a compact base, locally equal product coclasses of degree two are equal in every positive complex rank.
Source: Hatcher, Algebraic Topology, §2.2 and §3.1, relative Mayer–Vietoris and finite open covers. -/
theorem i1_compactProductCoclass_ext_of_locally_eq {B : Type} [TopologicalSpace B]
    [CompactSpace B] (k : ℕ) (hk : 0 < k)
    (u v : RelativeCohomology ℚ (i1_productNormalPair B k) 2)
    (hlocal : ∀ b : B, ∃ U : Opens B, b ∈ U ∧
      relativeCohomologyMap ℚ 2
        (i1_productBaseMap k (Subtype.val : U → B) continuous_subtype_val) u =
      relativeCohomologyMap ℚ 2
        (i1_productBaseMap k (Subtype.val : U → B) continuous_subtype_val) v) : u = v := by
  classical
  cases isEmpty_or_nonempty B with
  | inl hB =>
    letI := hB
    letI : IsEmpty (i1_productNormalPair B k).fst := by
      change IsEmpty (B × (Fin k → ℂ))
      infer_instance
    letI := i1_relativeCohomology_subsingleton_of_isEmpty (i1_productNormalPair B k) 2
    exact Subsingleton.elim u v
  | inr hB =>
    letI := hB
    choose U hb heq using hlocal
    obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun b : B => (U b : Set B))
      (fun b => (U b).isOpen) (by
        intro b _
        exact Set.mem_iUnion.mpr ⟨b, hb b⟩)
    have hc (b : B) : ∃ i ∈ s, b ∈ U i := by
      obtain ⟨i, hi, hb⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ b))
      exact ⟨i, hi, hb⟩
    have hn : s.Nonempty := by
      obtain ⟨i, hi, _⟩ := hc (Classical.arbitrary B)
      exact ⟨i, hi⟩
    exact i1_productFiniteCoverCoclass_ext k hk s (fun b => (U b : Set B))
      (fun b _ => (U b).isOpen) hn hc u v (fun b _ => heq b)

end HodgeLean.Foundations.BundleThom
