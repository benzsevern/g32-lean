import HodgeLean.Foundations.QuotientDuality.ProperCycleTriadCapTransport
import HodgeLean.Foundations.QuotientDuality.ProperCycleProductSupport

/-! # Original triad caps under contraction of free tangential coordinates -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Projection of actual free real tangential coordinates is bijective on the original relative homology for every actual normal subspace.
Source: Hatcher, Algebraic Topology, section 2.1, relative homotopy invariance; the original product-support contraction.
HC no distance; AV milestone no distance. -/
lemma properCycle_product_relative_projection_bijective
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y : TopCat.{0}) (A : Set Y) (n : ℕ) :
    Function.Bijective (relativeHomologyMap ℚ n
      (TopPair.ofSubsetHom (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩ : TopCat.of (E × Y) ⟶ Y)
        (show Set.MapsTo (fun z : E × Y => z.2) (Prod.snd ⁻¹' A) A from fun _ h => h))) := by
  obtain ⟨S, rfl⟩ : ∃ S : Set Y, Sᶜ = A := ⟨Aᶜ, compl_compl A⟩
  exact (properCycle_product_support_homology_iso E Y S n).toLinearEquiv.bijective

/-- Projection of actual free tangential coordinates is bijective on the original triad homology groups for open normal subspaces.
Source: Hatcher, Algebraic Topology, sections 2.1 and 2.2, product contraction and triad excision.
HC no distance; AV milestone no distance. -/
lemma properCycle_product_triad_projection_bijective
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y : TopCat.{0}) (A B : Set Y) (hAo : IsOpen A) (hBo : IsOpen B) (n : ℕ) :
    let f : TopCat.of (E × Y) ⟶ Y := TopCat.ofHom ⟨Prod.snd, continuous_snd⟩
    Function.Bijective (HomologicalComplex.homologyMap
      (properCycle_triad_relative_chain_map f (Prod.snd ⁻¹' A) (Prod.snd ⁻¹' B) A B
        (fun _ h => h) (fun _ h => h)) n).hom := by
  dsimp only
  apply properCycle_triad_homology_bijective_of_union
    (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩ : TopCat.of (E × Y) ⟶ Y)
    (Prod.snd ⁻¹' A) (Prod.snd ⁻¹' B) A B (fun _ h => h) (fun _ h => h)
    (hAo.preimage continuous_snd) (hBo.preimage continuous_snd) hAo hBo n
  exact properCycle_product_relative_projection_bijective E Y (A ∪ B) n

/-- Original triad cap bijectivity is retained after adding actual free real tangential coordinates, with the original class pulled back by projection.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.3, product contraction and cap naturality.
HC no distance; AV milestone no distance. -/
lemma properCycle_product_triad_cap_bijective
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y : TopCat.{0}) (A B : Set Y) (hAo : IsOpen A) (hBo : IsOpen B) (p q : ℕ)
    (a : RelativeCohomology ℚ (TopPair.ofSubset (X := Y) A) p)
    (hc : Function.Bijective (triadCapCohomologyLinear ℚ Y A B p q a)) :
    let f : TopCat.of (E × Y) ⟶ Y := TopCat.ofHom ⟨Prod.snd, continuous_snd⟩
    Function.Bijective (triadCapCohomologyLinear ℚ (TopCat.of (E × Y))
      (Prod.snd ⁻¹' A) (Prod.snd ⁻¹' B) p q
      (relativeCohomologyMap ℚ p (TopPair.ofSubsetHom f (show Set.MapsTo f (Prod.snd ⁻¹' A) A from fun _ h => h)) a)) := by
  dsimp only
  apply properCycle_triad_cap_bijective_of_map
    (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩ : TopCat.of (E × Y) ⟶ Y)
    (Prod.snd ⁻¹' A) (Prod.snd ⁻¹' B) A B (fun _ h => h) (fun _ h => h) p q a
  · exact properCycle_product_triad_projection_bijective E Y A B hAo hBo (p + q)
  · exact properCycle_product_relative_projection_bijective E Y B q
  · exact hc

end HodgeLean.Foundations.QuotientDuality
