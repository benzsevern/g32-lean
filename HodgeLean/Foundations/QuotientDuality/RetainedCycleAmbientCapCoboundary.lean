import HodgeLean.Foundations.QuotientDuality.RetainedCycleRelativeCapHomology

noncomputable section
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- Cap by an ambient coboundary has the actual relative-chain homotopy formula. -/
theorem retained_relative_ambient_cap_coboundary_apply (P : TopPair.{0}) (p q : ℕ)
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj P.fst) p)
    (c : RelativeChainGroup ℚ P (p + q + 1)) :
    (retainedRelativeAmbientCapHom P (p + 1) q (Simplicial.coboundary ℚ p φ)).hom
        (relativeReassocChain ℚ P p q c) =
      (retainedRelativeAmbientCapHom P p q φ).hom (relativeBoundary ℚ P (p + q) c) -
        (-1 : ℚ) ^ p • relativeBoundary ℚ P q
          ((retainedRelativeAmbientCapHom P p (q + 1) φ).hom c) := by
  let π := (relativeChainProjection ℚ P).f (p + q + 1)
  letI : Epi π := Cofork.IsColimit.epi
    (relativeChainProjectionComponentIsCokernelForCap ℚ P (p + q + 1))
  obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective π).mp inferInstance c
  dsimp only [π]
  have hp (a b : ℕ) (ψ : Simplicial.Cochain ℚ (TopCat.toSSet.obj P.fst) a)
      (v : Simplicial.ChainGroup ℚ (TopCat.toSSet.obj P.fst) (a + b)) :=
    ConcreteCategory.congr_hom (retained_relative_projection_ambient_cap P a b ψ) v
  change ∀ a b ψ v, (retainedRelativeAmbientCapHom P a b ψ).hom
      (((relativeChainProjection ℚ P).f (a + b)).hom v) =
      ((relativeChainProjection ℚ P).f b).hom (Simplicial.cap ℚ a b ψ v) at hp
  erw [relativeChainProjection_reassoc_apply, hp, relativeBoundary_projection,
    hp, hp, relativeBoundary_projection]
  have h := LinearMap.congr_fun (Simplicial.cap_coboundary_eq ℚ p q φ) b
  have h' := congrArg ((relativeChainProjection ℚ P).f q).hom h
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    map_sub, map_smul] at h'
  exact h'

/-- The actual coboundary cap short-complex map with its source-degree reassociation. -/
def retainedRelativeCapCoboundaryShortComplex (P : TopPair.{0}) (p q : ℕ)
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj P.fst) p) :
    ((relativeChainFunctor ℚ).obj P).sc (p + q + 1) ⟶ ((relativeChainFunctor ℚ).obj P).sc q :=
  (relativeReassocShortComplexIso ℚ P p q).hom ≫
    retainedRelativeCapShortComplex P (p + 1) q (Simplicial.coboundary ℚ p φ)
      (Simplicial.coboundary_coboundary ℚ p φ)

/-- The actual middle map of coboundary cap is the difference of the two chain-homotopy terms. -/
theorem retained_relative_cap_coboundary_middle (P : TopPair.{0}) (p q : ℕ)
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj P.fst) p) :
    (retainedRelativeCapCoboundaryShortComplex P p q φ).τ₂ =
      ModuleCat.ofHom (relativeBoundary ℚ P (p + q)) ≫ retainedRelativeAmbientCapHom P p q φ -
        (-1 : ℤ) ^ p •
          (retainedRelativeAmbientCapHom P p (q + 1) φ ≫ ModuleCat.ofHom (relativeBoundary ℚ P q)) := by
  rw [retainedRelativeCapCoboundaryShortComplex, ShortComplex.comp_τ₂,
    relativeReassocShortComplexIso_hom_τ₂, retained_relative_cap_short_complex_middle]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change (retainedRelativeAmbientCapHom P (p + 1) q (Simplicial.coboundary ℚ p φ)).hom
      (relativeReassocChain ℚ P p q c) =
    (retainedRelativeAmbientCapHom P p q φ).hom (relativeBoundary ℚ P (p + q) c) -
      (-1 : ℤ) ^ p • relativeBoundary ℚ P q
        ((retainedRelativeAmbientCapHom P p (q + 1) φ).hom c)
  rw [← Int.cast_smul_eq_zsmul ℚ, Int.cast_pow, Int.cast_neg, Int.cast_one]
  exact retained_relative_ambient_cap_coboundary_apply P p q φ c

/-- Actual cap by an ambient coboundary induces zero on relative homology after degree reassociation. -/
theorem retained_relative_cap_coboundary_homology_zero (P : TopPair.{0}) (p q : ℕ)
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj P.fst) p) :
    ShortComplex.homologyMap (retainedRelativeCapCoboundaryShortComplex P p q φ) = 0 := by
  let K := (relativeChainFunctor ℚ).obj P
  rw [← cancel_epi (K.sc (p + q + 1)).homologyπ,
    ← cancel_mono (K.sc q).homologyι]
  simp only [Category.assoc, zero_comp, comp_zero]
  rw [ShortComplex.π_homologyMap_ι, retained_relative_cap_coboundary_middle]
  have hs : (K.sc (p + q + 1)).iCycles ≫ ModuleCat.ofHom (relativeBoundary ℚ P (p + q)) = 0 :=
    K.iCycles_d (p + q + 1) (p + q)
  have ht : ModuleCat.ofHom (relativeBoundary ℚ P q) ≫ (K.sc q).pOpcycles = 0 :=
    K.d_pOpcycles (q + 1) q
  rw [Preadditive.sub_comp, Preadditive.comp_sub, Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  simp only [← Category.assoc, hs, zero_comp]
  simp only [Category.assoc]
  erw [ht]
  simp only [comp_zero, smul_zero, sub_zero]

/-- The unreassociated actual cap short-complex map of a coboundary also induces zero. -/
theorem retained_relative_cap_coboundary_homology_zero_unreassociated
    (P : TopPair.{0}) (p q : ℕ) (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj P.fst) p) :
    ShortComplex.homologyMap
      (retainedRelativeCapShortComplex P (p + 1) q (Simplicial.coboundary ℚ p φ)
        (Simplicial.coboundary_coboundary ℚ p φ)) = 0 := by
  rw [← cancel_epi (ShortComplex.homologyMap (relativeReassocShortComplexIso ℚ P p q).hom)]
  rw [← ShortComplex.homologyMap_comp, comp_zero]
  exact retained_relative_cap_coboundary_homology_zero P p q φ

/-- Cap by an ambient coboundary is the zero linear map on actual relative homology. -/
theorem retained_relative_cap_homology_coboundary_zero
    (P : TopPair.{0}) (p q : ℕ) (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj P.fst) p) :
    retainedRelativeCapHomology P (p + 1) q (Simplicial.coboundary ℚ p φ)
      (Simplicial.coboundary_coboundary ℚ p φ) = 0 := by
  exact congrArg ModuleCat.Hom.hom
    (retained_relative_cap_coboundary_homology_zero_unreassociated P p q φ)

end HodgeLean.Foundations.QuotientDuality
