import HodgeLean.Foundations.QuotientDuality.ProperCycleComplexLocalCapLinearity
import HodgeLean.Foundations.QuotientDuality.ProperCycleCofinalProductChart

/-! # Actual product projections for the small normal factors of chart neighborhoods -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- Replacing a contractible normal vector factor by an actual homeomorphic chart factor leaves the literal relative homology projection bijective.
Source: Hatcher, Algebraic Topology, sections 2.1 and 2.2, relative homotopy invariance in product neighborhoods.
HC no distance; AV milestone no distance. -/
lemma properCycle_homeomorphic_product_relative_projection_bijective
    (E : TopCat.{0}) (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃ₜ F) (Y : TopCat.{0}) (A : Set Y) (n : ℕ) :
    Function.Bijective (relativeHomologyMap ℚ n
      (TopPair.ofSubsetHom (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩ : TopCat.of (E × Y) ⟶ Y)
        (show Set.MapsTo (fun z : E × Y => z.2) (Prod.snd ⁻¹' A) A from fun _ h => h))) := by
  let eP : TopPair.ofSubset (X := TopCat.of (E × Y)) (Prod.snd ⁻¹' A) ≅
      TopPair.ofSubset (X := TopCat.of (F × Y)) (Prod.snd ⁻¹' A) :=
    TopPair.isoOfSubset (e.prodCongr (Homeomorph.refl Y)) (fun _ => Iff.rfl)
  let pF := TopPair.ofSubsetHom
    (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩ : TopCat.of (F × Y) ⟶ Y)
    (show Set.MapsTo (fun z : F × Y => z.2) (Prod.snd ⁻¹' A) A from fun _ h => h)
  have hF := properCycle_product_relative_projection_bijective F Y A n
  letI : IsIso eP.hom := eP.isIso_hom
  have hE : Function.Bijective (relativeHomologyMap ℚ n eP.hom) := by
    exact ConcreteCategory.bijective_of_isIso
      (HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map eP.hom) n)
  have h := hF.comp hE
  have hp : eP.hom ≫ pF = TopPair.ofSubsetHom
      (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩ : TopCat.of (E × Y) ⟶ Y)
      (show Set.MapsTo (fun z : E × Y => z.2) (Prod.snd ⁻¹' A) A from fun _ h => h) := by
    ext z : 2 <;> rfl
  change Function.Bijective ((relativeHomologyMap ℚ n pF).comp (relativeHomologyMap ℚ n eP.hom)) at h
  rw [← relativeHomologyMap_comp, hp] at h
  exact h

/-- The literal projection with an actual positive-radius normal ball factor is bijective on the original relative homology, with arbitrary tangential space and subspace.
Source: Hatcher, Algebraic Topology, sections 2.1 and 2.2, product neighborhoods and relative homotopy invariance.
HC no distance; AV milestone no distance. -/
lemma properCycle_ball_product_relative_projection_bijective
    (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : F) (r : ℝ) (hr : 0 < r) (Y : TopCat.{0}) (A : Set Y) (n : ℕ) :
    Function.Bijective (relativeHomologyMap ℚ n
      (TopPair.ofSubsetHom
        (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩ : TopCat.of ((Metric.ball c r) × Y) ⟶ Y)
        (show Set.MapsTo (fun z : (Metric.ball c r) × Y => z.2) (Prod.snd ⁻¹' A) A from fun _ h => h))) :=
  properCycle_homeomorphic_product_relative_projection_bijective (TopCat.of (Metric.ball c r)) F
    (properCycle_ball_coordinates F c r hr).symm Y A n

/-- A literal product map with contractible actual normal factors induces bijective relative homology whenever its tangential pair map does, without a supplied product-homology premise.
Source: Hatcher, Algebraic Topology, section 2.1, naturality of product contraction in relative homology.
HC no distance; AV milestone no distance. -/
lemma properCycle_homeomorphic_product_pair_map_bijective
    (E : TopCat.{0}) (F G : Type)
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (e : E ≃ₜ F) (Y Z : TopCat.{0}) (A : Set Y) (B : Set Z)
    (f : Y ⟶ Z) (hA : Set.MapsTo f A B) (g : E ⟶ TopCat.of G) (n : ℕ)
    (hf : Function.Bijective (relativeHomologyMap ℚ n (TopPair.ofSubsetHom f hA))) :
    Function.Bijective (relativeHomologyMap ℚ n
      (TopPair.ofSubsetHom
        (TopCat.ofHom ⟨fun z => (g z.1, f z.2),
          (g.hom.continuous.comp continuous_fst).prodMk (f.hom.continuous.comp continuous_snd)⟩ :
          TopCat.of (E × Y) ⟶ TopCat.of (G × Z))
        (show Set.MapsTo (fun z : E × Y => (g z.1, f z.2))
          (Prod.snd ⁻¹' A) (Prod.snd ⁻¹' B) from fun _ h => hA h))) := by
  let pE := TopPair.ofSubsetHom
    (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩ : TopCat.of (E × Y) ⟶ Y)
    (show Set.MapsTo (fun z : E × Y => z.2) (Prod.snd ⁻¹' A) A from fun _ h => h)
  let pG := TopPair.ofSubsetHom
    (TopCat.ofHom ⟨Prod.snd, continuous_snd⟩ : TopCat.of (G × Z) ⟶ Z)
    (show Set.MapsTo (fun z : G × Z => z.2) (Prod.snd ⁻¹' B) B from fun _ h => h)
  let P := TopPair.ofSubsetHom
    (TopCat.ofHom ⟨fun z => (g z.1, f z.2),
      (g.hom.continuous.comp continuous_fst).prodMk (f.hom.continuous.comp continuous_snd)⟩ :
      TopCat.of (E × Y) ⟶ TopCat.of (G × Z))
    (show Set.MapsTo (fun z : E × Y => (g z.1, f z.2))
      (Prod.snd ⁻¹' A) (Prod.snd ⁻¹' B) from fun _ h => hA h)
  have hs := properCycle_homeomorphic_product_relative_projection_bijective E F e Y A n
  have ht := properCycle_product_relative_projection_bijective G Z B n
  have hp : P ≫ pG = pE ≫ TopPair.ofSubsetHom f hA := by ext z : 2 <;> rfl
  have hlin := congrArg (relativeHomologyMap ℚ n) hp
  rw [relativeHomologyMap_comp, relativeHomologyMap_comp] at hlin
  have h := hf.comp hs
  change Function.Bijective ((relativeHomologyMap ℚ n (TopPair.ofSubsetHom f hA)).comp
    (relativeHomologyMap ℚ n pE)) at h
  rw [← hlin] at h
  exact (Function.Bijective.of_comp_iff' ht _).mp h

end HodgeLean.Foundations.QuotientDuality
