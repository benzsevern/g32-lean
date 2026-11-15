import HodgeLean.Foundations.QuotientDuality.ProperCycleSigmaOpenEmbedding

/-! # Detection by actual smooth pieces outside a small boundary neighborhood
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular Topology
namespace HodgeLean.Foundations.QuotientDuality

/-- Original ordinary top classes are detected on an actual disjoint family of charted open pieces whenever the original boundary-neighborhood projection is injective.
Source: properCycle_compact_manifold_support_point_detection; properCycle_sigma_chartedSpace; properCycle_sigma_open_embedding.
HC no distance; AV milestone no distance. -/
lemma properCycle_union_point_detection
    {ι : Type} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (X : TopCat.{0}) [T2Space X] [CompactSpace X]
    (Y : ι → TopCat.{0}) [∀ i, T2Space (Y i)] [∀ i, Nonempty (Y i)] [∀ i, ChartedSpace E (Y i)]
    (f : ∀ i, Y i ⟶ X) (hf : ∀ i, IsOpenEmbedding (f i))
    (hinj : Function.Injective (fun y : Σ i, Y i => f y.1 y.2))
    (N : Set X) (hN : IsOpen N)
    (hcover : ∀ x : X, x ∉ N → ∃ i, x ∈ Set.range (f i))
    (n : ℕ) (hn : Module.finrank ℝ E = n)
    (hproj : Function.Injective
      (relativeHomologyProjection ℚ (TopPair.ofSubset (X := X) N) n).hom)
    (c : Homology ℚ X n)
    (hc : ∀ i (y : Y i), f i y ∉ N → localOrientation X n c (f i y) = 0) : c = 0 := by
  let Z := TopCat.of (Σ i, Y i)
  letI : ChartedSpace E Z := properCycle_sigma_chartedSpace E (fun i => Y i)
  let g : Z ⟶ X := TopCat.ofHom
    ⟨fun y => f y.1 y.2, continuous_sigma (fun i => (f i).hom.continuous)⟩
  have hg : IsOpenEmbedding g := properCycle_sigma_open_embedding (fun i => Y i)
    (fun i => f i) hf hinj
  let K : Set X := Nᶜ
  let A : Set Z := g ⁻¹' K
  have hK : IsCompact K := hN.isClosed_compl.isCompact
  have hKG : K ⊆ Set.range g := by
    intro x hx
    obtain ⟨i, y, hy⟩ := hcover x hx
    exact ⟨⟨i, y⟩, hy⟩
  have hGA : g '' A = K := Set.image_preimage_eq_of_subset hKG
  have hA : IsCompact A := hg.isEmbedding.isCompact_iff.mpr (by rw [hGA]; exact hK)
  have hcomp : (g '' A)ᶜ = N := by rw [hGA]; exact compl_compl N
  have hp : Function.Injective
      (relativeHomologyProjection ℚ (TopPair.ofSubset (X := X) (g '' A)ᶜ) n).hom := by
    rw [hcomp]
    exact hproj
  apply properCycle_compact_manifold_support_point_detection (E := E) X Z g hg A hA n hn hp c
  intro y hy
  exact hc y.1 y.2 hy

end HodgeLean.Foundations.QuotientDuality
