import HodgeLean.Foundations.QuotientDuality.ProperCycleNeighborhoodPointMap
import HodgeLean.Foundations.QuotientDuality.ProperCycleNeighborhoodCapNaturality

/-! # Actual local point values of original homology images
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace Topology
namespace HodgeLean.Foundations.QuotientDuality

/-- A nonzero original local value remains nonzero under an actual embedding whose image is a neighborhood at that point.
Source: Hatcher, Algebraic Topology, sections 2.1 and 2.2, relative naturality and point excision.
HC no distance; AV milestone no distance. -/
lemma properCycle_local_orientation_image_ne_zero
    {X Y : TopCat.{0}} [T1Space X] [T1Space Y] (f : X ⟶ Y) (hf : IsEmbedding f)
    (x : X) (hnb : Set.range f ∈ 𝓝 (f x)) (n : ℕ) (c : Homology ℚ X n)
    (hc : localOrientation X n c x ≠ 0) :
    localOrientation Y n (homologyMap ℚ n f c) (f x) ≠ 0 := by
  let p := imagePointPairMap f hf.injective x
  have hp := properCycle_neighborhood_point_map_bijective f hf x hnb n
  have hn := properCycle_relative_homology_projection_naturality p n c
  change relativeHomologyMap ℚ n p (localOrientation X n c x) =
    localOrientation Y n (homologyMap ℚ n f c) (f x) at hn
  intro hz
  apply hc
  apply hp.1
  change relativeHomologyMap ℚ n p (localOrientation X n c x) = relativeHomologyMap ℚ n p 0
  rw [map_zero, hn, hz]

/-- A homology image has zero original point value outside the actual range of its continuous map.
Source: Hatcher, Algebraic Topology, section 2.1, the subspace-to-relative chain composite.
HC no distance; AV milestone no distance. -/
lemma properCycle_local_orientation_image_outside_range
    {X Y : TopCat.{0}} (f : X ⟶ Y) (y : Y) (hy : y ∉ Set.range f)
    (n : ℕ) (c : Homology ℚ X n) :
    localOrientation Y n (homologyMap ℚ n f c) y = 0 := by
  let P := pointComplementPair y
  have hf (x : X) : f x ∈ ({y} : Set Y)ᶜ := fun h => hy ⟨x, h⟩
  let fA : X ⟶ P.snd := TopCat.ofHom
    ⟨fun x => ⟨f x, hf x⟩, f.hom.continuous.subtype_mk hf⟩
  have hfactor : fA ≫ P.map = f := by ext x; rfl
  let H := HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n
  have hz := congrArg H.map (subspaceChainMap_relativeChainProjection ℚ P)
  simp only [Functor.map_comp, Functor.map_zero] at hz
  have hz' := ConcreteCategory.congr_hom hz (homologyMap ℚ n fA c)
  change (relativeHomologyProjection ℚ P n).hom
    (homologyMap ℚ n P.map (homologyMap ℚ n fA c)) = 0 at hz'
  change (relativeHomologyProjection ℚ P n).hom (homologyMap ℚ n f c) = 0
  rw [← hfactor, homologyMap_comp, LinearMap.comp_apply]
  exact hz'

end HodgeLean.Foundations.QuotientDuality
