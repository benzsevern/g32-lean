import HodgeLean.Foundations.QuotientDuality.ProperCycleNeighborhoodCapNaturality

/-! # Ordinary-to-relative projections under actual homeomorphisms
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- An actual homeomorphism transports bijectivity of the original ordinary-to-relative homology projection to the literal image subset.
Source: properCycle_relative_homology_projection_naturality; functoriality of relative singular homology.
HC no distance; AV milestone no distance. -/
lemma properCycle_homeomorph_relative_projection_bijective
    (X Y : TopCat.{0}) (e : X ≃ₜ Y) (A : Set X) (n : ℕ)
    (hA : Function.Bijective (relativeHomologyProjection ℚ
      (TopPair.ofSubset (X := X) A) n).hom) :
    Function.Bijective (relativeHomologyProjection ℚ
      (TopPair.ofSubset (X := Y) (e '' A)) n).hom := by
  let f : TopPair.ofSubset (X := X) A ⟶ TopPair.ofSubset (X := Y) (e '' A) :=
    TopPair.ofSubsetHom (TopCat.ofHom ⟨e, e.continuous⟩) (fun x hx => ⟨x, hx, rfl⟩)
  let g : TopPair.ofSubset (X := Y) (e '' A) ⟶ TopPair.ofSubset (X := X) A :=
    TopPair.ofSubsetHom (TopCat.ofHom ⟨e.symm, e.symm.continuous⟩) (by
      rintro y ⟨x, hx, rfl⟩
      change e.symm (e x) ∈ A
      rw [e.symm_apply_apply]
      exact hx)
  have hfg : f ≫ g = 𝟙 _ := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext x : 1
      apply Subtype.ext
      exact e.symm_apply_apply x.val
    · ext x : 1
      exact e.symm_apply_apply x
  have hgf : g ≫ f = 𝟙 _ := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext x : 1
      apply Subtype.ext
      exact e.apply_symm_apply x.val
    · ext x : 1
      exact e.apply_symm_apply x
  have hr : Function.Bijective (relativeHomologyMap ℚ n f) := by
    constructor
    · intro a b he
      have hh := congrArg (relativeHomologyMap ℚ n g) he
      simpa only [← LinearMap.comp_apply, ← relativeHomologyMap_comp, hfg,
        relativeHomologyMap_id, LinearMap.id_apply] using hh
    · intro b
      refine ⟨relativeHomologyMap ℚ n g b, ?_⟩
      rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp, hgf,
        relativeHomologyMap_id, LinearMap.id_apply]
  let H : Homology ℚ X n ≃ₗ[ℚ] Homology ℚ Y n :=
    (((singularHomologyFunctor.{0} (ModuleCat.{0} ℚ) n).obj (ModuleCat.of ℚ ℚ)).mapIso
    (TopCat.isoOfHomeo e)).toLinearEquiv
  have he (c : Homology ℚ X n) :
      relativeHomologyMap ℚ n f
        ((relativeHomologyProjection ℚ (TopPair.ofSubset (X := X) A) n).hom c) =
      (relativeHomologyProjection ℚ (TopPair.ofSubset (X := Y) (e '' A)) n).hom (H c) :=
    properCycle_relative_homology_projection_naturality f n c
  constructor
  · intro a b hab
    obtain ⟨a', rfl⟩ := H.surjective a
    obtain ⟨b', rfl⟩ := H.surjective b
    apply congrArg H
    apply hA.injective
    apply hr.injective
    rw [he, he]
    exact hab
  · intro b
    obtain ⟨b', hb'⟩ := hr.surjective b
    obtain ⟨c, hc⟩ := hA.surjective b'
    exact ⟨H c, (he c).symm.trans (by rw [hc, hb'])⟩

end HodgeLean.Foundations.QuotientDuality
