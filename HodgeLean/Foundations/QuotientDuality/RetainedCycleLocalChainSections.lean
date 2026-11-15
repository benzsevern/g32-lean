import HodgeLean.Foundations.QuotientDuality.RetainedCycleChainSectionInjection

noncomputable section
open CategoryTheory Limits TopologicalSpace Opposite AlgebraicTopology AlgebraicTopology.Singular
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- Every actual chain-sheaf section germ is represented by an actual absolute singular chain. -/
theorem retained_chain_section_germ_representative (X : TopCat.{0}) [T2Space X]
    (U : Opens X) (n : ℕ) (s : (singularChainSheaf ℚ X n).presheaf.obj (op U))
    (x : X) (hx : x ∈ U) :
    ∃ c : Simplicial.ChainGroup ℚ (TopCat.toSSet.obj X) n,
      (singularChainSheaf ℚ X n).presheaf.germ U x hx ((retainedChainSheafSectionMap X U).f n c) =
        (singularChainSheaf ℚ X n).presheaf.germ U x hx s := by
  let e := (singularChainSheafStalkIso ℚ X x).hom.f n
  let π := (relativeChainProjection ℚ (pointComplementPair x)).f n
  letI : Epi π := Cofork.IsColimit.epi
    (relativeChainProjectionComponentIsCokernelForCap ℚ (pointComplementPair x) n)
  obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective π).mp inferInstance
    (e ((singularChainSheaf ℚ X n).presheaf.germ U x hx s))
  refine ⟨c, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso e).1
  have hg := ConcreteCategory.congr_hom (retained_chain_sheaf_section_germ X U x hx n) c
  change e ((singularChainSheaf ℚ X n).presheaf.germ U x hx
    ((retainedChainSheafSectionMap X U).f n c)) = π.hom c at hg
  exact hg.trans hc

/-- One actual absolute chain represents a section on all germs in a suitable open neighbourhood. -/
theorem retained_chain_section_local_representative (X : TopCat.{0}) [T2Space X]
    (U : Opens X) (n : ℕ) (s : (singularChainSheaf ℚ X n).presheaf.obj (op U))
    (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (hVU : V ≤ U) (_hxV : x ∈ V)
      (c : Simplicial.ChainGroup ℚ (TopCat.toSSet.obj X) n),
      ∀ y (hy : y ∈ V),
        (singularChainSheaf ℚ X n).presheaf.germ U y (hVU hy)
            ((retainedChainSheafSectionMap X U).f n c) =
          (singularChainSheaf ℚ X n).presheaf.germ U y (hVU hy) s := by
  obtain ⟨c, hc⟩ := retained_chain_section_germ_representative X U n s x hx
  obtain ⟨V, hxV, i₁, i₂, he⟩ := (singularChainSheaf ℚ X n).presheaf.germ_eq x hx hx
    ((retainedChainSheafSectionMap X U).f n c) s hc
  have hi : i₁ = i₂ := Subsingleton.elim _ _
  subst i₂
  refine ⟨V, leOfHom i₁, hxV, c, ?_⟩
  intro y hy
  exact (singularChainSheaf ℚ X n).presheaf.germ_ext V hy i₁ i₁ he

end HodgeLean.Foundations.QuotientDuality
