import HodgeLean.Foundations.QuotientDuality.RetainedCycleCompactSectionCoordinates

noncomputable section
open CategoryTheory Limits TopologicalSpace Opposite AlgebraicTopology AlgebraicTopology.Singular
open scoped Simplicial
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- Reconstruction of an actual finite chain from a global section on a compact space. -/
def retainedChainFromGlobalSection (X : TopCat.{0}) [T2Space X] [CompactSpace X]
    (n : ℕ) (s : (singularChainSheaf ℚ X n).presheaf.obj (op ⊤)) :
    Simplicial.ChainGroup ℚ (TopCat.toSSet.obj X) n :=
  retainedChainFromCoordinates (TopCat.toSSet.obj X) n
    (Finsupp.ofSupportFinite (retainedGlobalSectionCoefficient X n s)
      (retained_compact_section_coefficient_support_finite X n s))

/-- The reconstructed chain has exactly the section's actual constant simplex coefficients. -/
theorem retained_chain_from_global_section_coordinate (X : TopCat.{0}) [T2Space X]
    [CompactSpace X] (n : ℕ) (s : (singularChainSheaf ℚ X n).presheaf.obj (op ⊤))
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    retainedSimplexCoordinate (TopCat.toSSet.obj X) n σ
      (retainedChainFromGlobalSection X n s) = retainedGlobalSectionCoefficient X n s σ := by
  have h := LinearMap.congr_fun
    (retained_chain_coordinates_comp_from_coordinates (TopCat.toSSet.obj X) n)
    (Finsupp.ofSupportFinite (retainedGlobalSectionCoefficient X n s)
      (retained_compact_section_coefficient_support_finite X n s))
  exact congrArg (fun f => f σ) h

/-- A simplex absent from the point complement passes through that point. -/
theorem retained_simplex_hits_point_of_not_from_complement (X : TopCat.{0}) (n : ℕ)
    (x : X) (σ : (TopCat.toSSet.obj X) _⦋n⦌)
    (hσ : ∀ τ : (TopCat.toSSet.obj (pointComplementPair x).snd) _⦋n⦌,
      (TopCat.toSSet.map (pointComplementPair x).map).app (op ⦋n⦌) τ ≠ σ) :
    ∃ t : SimplexCategory.toTop.{0}.obj ⦋n⦌, retainedSimplexAt X n σ t = x := by
  classical
  by_contra h
  have ht : ∀ t, retainedSimplexAt X n σ t ≠ x := by simpa only [not_exists] using h
  let f : C(SimplexCategory.toTop.{0}.obj ⦋n⦌, X) :=
    TopCat.Hom.hom (show SimplexCategory.toTop.{0}.obj ⦋n⦌ ⟶ X from σ.down)
  let g : C(SimplexCategory.toTop.{0}.obj ⦋n⦌, (pointComplementPair x).snd) :=
    ⟨fun t => ⟨f t, ht t⟩, f.continuous.subtype_mk _⟩
  let τ : (TopCat.toSSet.obj (pointComplementPair x).snd) _⦋n⦌ :=
    ⟨TopCat.ofHom g⟩
  apply hσ τ
  apply ULift.ext
  apply TopCat.hom_ext
  ext t
  rfl

end HodgeLean.Foundations.QuotientDuality
