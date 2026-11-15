import HodgeLean.Foundations.QuotientDuality.ProperCycleChartProductProjection

/-! # The actual local homology map of an open embedding -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- An actual open embedding induces a bijective original point-complement relative homology map.
Source: Hatcher, Algebraic Topology, section 2.2, point excision and homeomorphisms onto open images.
HC no distance; AV milestone no distance. -/
lemma properCycle_open_embedding_local_homology_bijective
    {X Y : TopCat.{0}} [T1Space Y] (f : X ⟶ Y) (hf : Topology.IsOpenEmbedding f) (x : X) (n : ℕ) :
    Function.Bijective (relativeHomologyMap ℚ n
      (TopPair.ofSubsetHom f (show Set.MapsTo f ({x} : Set X)ᶜ ({f x} : Set Y)ᶜ from
        fun z hz h => hz (hf.injective h)))) := by
  let U : Set Y := Set.range f
  have hU : IsOpen U := by
    simpa only [Set.image_univ] using hf.isOpenMap Set.univ isOpen_univ
  let e : X ≃ₜ U := (Homeomorph.Set.univ X).symm.trans
    ((hf.isEmbedding.homeomorphImage (Set.univ : Set X)).trans
      (Homeomorph.setCongr (Set.image_univ)))
  let eP : TopPair.ofSubset (X := X) ({x} : Set X)ᶜ ≅ neighborhoodPointComplementPair U (f x) :=
    TopPair.isoOfSubset e (by
      intro z
      change (f z ≠ f x) ↔ z ≠ x
      exact not_congr hf.injective.eq_iff)
  let i := neighborhoodPointComplementPairMap U (f x)
  letI : QuasiIso ((relativeChainFunctor ℚ).map i) :=
    neighborhoodPointComplement_relativeChainMap_quasiIso U (f x) hU ⟨x, rfl⟩
  letI : IsIso eP.hom := eP.isIso_hom
  have he : Function.Bijective (relativeHomologyMap ℚ n eP.hom) :=
    ConcreteCategory.bijective_of_isIso (HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map eP.hom) n)
  have hi : Function.Bijective (relativeHomologyMap ℚ n i) :=
    ConcreteCategory.bijective_of_isIso (HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map i) n)
  have hp : eP.hom ≫ i = TopPair.ofSubsetHom f
      (show Set.MapsTo f ({x} : Set X)ᶜ ({f x} : Set Y)ᶜ from fun z hz h => hz (hf.injective h)) := by
    ext z : 2 <;> rfl
  have h := hi.comp he
  change Function.Bijective ((relativeHomologyMap ℚ n i).comp (relativeHomologyMap ℚ n eP.hom)) at h
  rw [← relativeHomologyMap_comp, hp] at h
  exact h

/-- A literal chart map with a positive-radius normal ball and an actual open tangential embedding is bijective on the original local-fiber relative homology target.
Source: Hatcher, Algebraic Topology, sections 2.1 and 2.2, product contraction and point excision.
HC no distance; AV milestone no distance. -/
lemma properCycle_chart_normal_ball_pair_map_bijective
    (F G : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (c : F) (r : ℝ) (hr : 0 < r)
    {Y Z : TopCat.{0}} [T1Space Z] (f : Y ⟶ Z) (hf : Topology.IsOpenEmbedding f)
    (y : Y) (g : TopCat.of (Metric.ball c r) ⟶ TopCat.of G) (n : ℕ) :
    Function.Bijective (relativeHomologyMap ℚ n
      (TopPair.ofSubsetHom
        (TopCat.ofHom ⟨fun z => (g z.1, f z.2),
          (g.hom.continuous.comp continuous_fst).prodMk (f.hom.continuous.comp continuous_snd)⟩ :
          TopCat.of ((Metric.ball c r) × Y) ⟶ TopCat.of (G × Z))
        (show Set.MapsTo (fun z : (Metric.ball c r) × Y => (g z.1, f z.2))
          (Prod.snd ⁻¹' ({y} : Set Y)ᶜ) (Prod.snd ⁻¹' ({f y} : Set Z)ᶜ) from
            fun z hz h => hz (hf.injective h)))) :=
  properCycle_homeomorphic_product_pair_map_bijective (TopCat.of (Metric.ball c r)) F G
    (properCycle_ball_coordinates F c r hr).symm Y Z ({y} : Set Y)ᶜ ({f y} : Set Z)ᶜ
    f (fun z hz h => hz (hf.injective h)) g n
    (properCycle_open_embedding_local_homology_bijective f hf y n)

/-- The original triad map of an actual open embedding is bijective on homology when both specified open unions are the corresponding punctured spaces.
Source: Hatcher, Algebraic Topology, section 2.2, naturality of point excision and open-triad subdivision.
HC no distance; AV milestone no distance. -/
lemma properCycle_open_embedding_triad_local_homology_bijective
    {X Y : TopCat.{0}} [T1Space Y] (f : X ⟶ Y) (hf : Topology.IsOpenEmbedding f)
    (A B : Set X) (C D : Set Y) (hA : Set.MapsTo f A C) (hB : Set.MapsTo f B D)
    (hAo : IsOpen A) (hBo : IsOpen B) (hCo : IsOpen C) (hDo : IsOpen D)
    (x : X) (hUX : A ∪ B = ({x} : Set X)ᶜ) (hUY : C ∪ D = ({f x} : Set Y)ᶜ) (n : ℕ) :
    Function.Bijective (HomologicalComplex.homologyMap
      (properCycle_triad_relative_chain_map f A B C D hA hB) n).hom := by
  apply properCycle_triad_homology_bijective_of_union f A B C D hA hB hAo hBo hCo hDo n
  let fU := TopPair.ofSubsetHom f (show Set.MapsTo f (A ∪ B) (C ∪ D) from
    fun _ h => h.elim (fun h => Or.inl (hA h)) (fun h => Or.inr (hB h)))
  let fP := TopPair.ofSubsetHom f (show Set.MapsTo f ({x} : Set X)ᶜ ({f x} : Set Y)ᶜ from
    fun z hz h => hz (hf.injective h))
  let eS : TopPair.ofSubset (X := X) (A ∪ B) ≅ TopPair.ofSubset (X := X) ({x} : Set X)ᶜ :=
    TopPair.isoOfSubset (Homeomorph.refl X) (fun z => (Set.ext_iff.mp hUX z).symm)
  let eT : TopPair.ofSubset (X := Y) (C ∪ D) ≅ TopPair.ofSubset (X := Y) ({f x} : Set Y)ᶜ :=
    TopPair.isoOfSubset (Homeomorph.refl Y) (fun z => (Set.ext_iff.mp hUY z).symm)
  letI : IsIso eS.hom := eS.isIso_hom
  letI : IsIso eT.hom := eT.isIso_hom
  have hS : Function.Bijective (relativeHomologyMap ℚ n eS.hom) :=
    ConcreteCategory.bijective_of_isIso (HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map eS.hom) n)
  have hT : Function.Bijective (relativeHomologyMap ℚ n eT.hom) :=
    ConcreteCategory.bijective_of_isIso (HomologicalComplex.homologyMap ((relativeChainFunctor ℚ).map eT.hom) n)
  have hp : fU ≫ eT.hom = eS.hom ≫ fP := by ext z : 2 <;> rfl
  have hlin := congrArg (relativeHomologyMap ℚ n) hp
  rw [relativeHomologyMap_comp, relativeHomologyMap_comp] at hlin
  have h := (properCycle_open_embedding_local_homology_bijective f hf x n).comp hS
  change Function.Bijective ((relativeHomologyMap ℚ n fP).comp (relativeHomologyMap ℚ n eS.hom)) at h
  rw [← hlin] at h
  exact (Function.Bijective.of_comp_iff' hT _).mp h

end HodgeLean.Foundations.QuotientDuality
