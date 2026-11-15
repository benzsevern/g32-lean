import HodgeLean.Foundations.Program.SchoenTransferC1a5SigmaCollarHelpers

/-! Singular relative excision for arbitrary small families of collared cells.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Program

/-- A disjoint union of collared cell attachments gives the actual relative singular comparison.
The summand index is arbitrary and attaching maps may identify boundary points.
Source: Hatcher §2.1, Theorem 2.20, disjoint-union collars and neighborhood excision. -/
lemma c1a5_sigma_collar_singular_excision {I : Type} {A U C : I → TopCat.{0}}
    {B D : TopCat.{0}} (j : ∀ i, A i ⟶ U i) (k : ∀ i, U i ⟶ C i)
    (t : TopCat.of (Σ i, A i) ⟶ B) (r : B ⟶ D)
    (b : TopCat.of (Σ i, C i) ⟶ D)
    (sq : IsPushout t (c1a5_sigma_map j ≫ c1a5_sigma_map k) r b)
    (hk : ∀ i, Topology.IsOpenEmbedding (k i))
    (hl : ∀ i, Function.Injective (j i ≫ k i))
    (hc : ∀ i, IsClosed (Set.range (j i ≫ k i)))
    (q : ∀ i, U i ⟶ A i) (hq : ∀ i, j i ≫ q i = 𝟙 (A i))
    (H : ∀ i, TopCat.Homotopy (𝟙 (U i)) (q i ≫ j i))
    (hfixed : ∀ i (s : unitInterval) (a : A i), H i (s, j i a) = j i a) :
    QuasiIso (c1a5RelativeMap c1a5Chains
      (TopCat.toSSet.map (c1a5_sigma_map j ≫ c1a5_sigma_map k))
      (TopCat.toSSet.map r) (TopCat.toSSet.map t) (TopCat.toSSet.map b) (by
        rw [← TopCat.toSSet.map_comp, ← TopCat.toSSet.map_comp]
        exact congrArg TopCat.toSSet.map sq.w.symm)) := by
  have hinj : Function.Injective (c1a5_sigma_map j ≫ c1a5_sigma_map k) := by
    rw [c1a5_sigma_map_comp]
    exact c1a5_sigma_map_injective _ hl
  have hclosed : IsClosed (Set.range (c1a5_sigma_map j ≫ c1a5_sigma_map k)) := by
    rw [c1a5_sigma_map_comp]
    exact c1a5_sigma_map_range_isClosed _ hc
  exact c1a5_collar_attachment_singular_excision sq
    (c1a5_sigma_map_isOpenEmbedding k hk) hinj hclosed
    (c1a5_sigma_map q) (c1a5_sigma_retract j q hq)
    (c1a5_sigma_collar_homotopy j q H)
    (c1a5_sigma_collar_homotopy_fixed j q H hfixed)

end HodgeLean.Foundations.Program
