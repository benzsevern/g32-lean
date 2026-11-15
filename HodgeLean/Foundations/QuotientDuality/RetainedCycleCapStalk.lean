import HodgeLean.Foundations.QuotientDuality.RetainedCycleAmbientCapSheaf

noncomputable section
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular TopologicalSpace Opposite
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- The presheaf stalk comparison intertwines actual ambient cap with cap on point-complement chains. -/
theorem retained_chain_presheaf_stalk_cap (X : TopCat.{0}) [T2Space X]
    (x : X) (p q : ℕ) (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (retainedChainPresheafAmbientCap X p q φ) ≫
      (singularChainPresheafStalkIso ℚ X x q).hom =
    (singularChainPresheafStalkIso ℚ X x (p + q)).hom ≫
      (forget₂ (ModuleCat ℚ) AddCommGrpCat).map
        (retainedRelativeAmbientCapHom (TopPair.ofSubset ({x} : Set X)ᶜ) p q φ) := by
  apply (singularChainPresheaf ℚ X (p + q)).stalk_hom_ext
  intro U hx
  rw [← Category.assoc, TopCat.Presheaf.stalkFunctor_map_germ,
    Category.assoc, singularChainPresheafStalkIso_germ,
    ← Category.assoc, singularChainPresheafStalkIso_germ]
  exact congrArg ((forget₂ (ModuleCat ℚ) AddCommGrpCat).map)
    (retained_relative_ambient_cap_support_inclusion X p q φ
      (Set.singleton_subset_iff.mpr hx)).symm

/-- Sheafification followed by the actual chain-stalk comparison retains the presheaf local restriction. -/
theorem retained_sheafification_stalk_chain_comparison (X : TopCat.{0}) [T2Space X]
    (x : X) (n : ℕ) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (toSheafify (Opens.grothendieckTopology X) (singularChainPresheaf ℚ X n)) ≫
      (singularChainSheafStalkIso ℚ X x).hom.f n =
      (singularChainPresheafStalkIso ℚ X x n).hom := by
  let e := singularChainSheafificationStalkIso ℚ X x
  have he := congrArg (fun f => f.f n) e.hom_inv_id
  change e.hom.f n ≫ e.inv.f n = 𝟙 _ at he
  change e.hom.f n ≫ (e.inv.f n ≫
    (singularChainPresheafStalkIso ℚ X x n).hom) = _
  rw [← Category.assoc, he, Category.id_comp]

/-- The sheaf stalk comparison intertwines actual ambient cap with cap on point-complement chains. -/
theorem retained_chain_sheaf_stalk_cap (X : TopCat.{0}) [T2Space X]
    (x : X) (p q : ℕ) (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
      (retainedChainSheafAmbientCap X p q φ).hom ≫
      (singularChainSheafStalkIso ℚ X x).hom.f q =
    (singularChainSheafStalkIso ℚ X x).hom.f (p + q) ≫
      (forget₂ (ModuleCat ℚ) AddCommGrpCat).map
        (retainedRelativeAmbientCapHom (TopPair.ofSubset ({x} : Set X)ᶜ) p q φ) := by
  let e := singularChainSheafificationStalkIso ℚ X x
  let G := TopCat.Presheaf.stalkFunctor AddCommGrpCat x
  have hu := congrArg G.map (retained_chain_sheaf_ambient_cap_unit X p q φ)
  simp only [Functor.map_comp] at hu
  apply (cancel_epi (e.hom.f (p + q))).mp
  change G.map (toSheafify (Opens.grothendieckTopology X)
      (singularChainPresheaf ℚ X (p + q))) ≫ _ =
    G.map (toSheafify (Opens.grothendieckTopology X)
      (singularChainPresheaf ℚ X (p + q))) ≫ _
  rw [← Category.assoc, hu, Category.assoc,
    retained_sheafification_stalk_chain_comparison,
    ← Category.assoc, retained_sheafification_stalk_chain_comparison]
  exact retained_chain_presheaf_stalk_cap X x p q φ

end HodgeLean.Foundations.QuotientDuality
