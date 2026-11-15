import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.Cap.Relative
import HodgeLean.RealDefs.Port.AlgebraicTopology.Singular.Sheaf.ChainStalk

noncomputable section
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular TopologicalSpace Opposite
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- Cap by an ambient cochain followed by the actual relative-chain projection. -/
def retainedAmbientCapRelativeLift (P : TopPair.{0}) (p q : ℕ)
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj P.fst) p) :
    Simplicial.ChainGroup ℚ (TopCat.toSSet.obj P.fst) (p + q) ⟶
      RelativeChainGroup ℚ P q :=
  Simplicial.capHom ℚ p q φ ≫ (relativeChainProjection ℚ P).f q

/-- Cap by an ambient cochain kills subspace chains after relative projection. -/
theorem retained_subspace_chain_ambient_cap_relative_lift (P : TopPair.{0}) (p q : ℕ)
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj P.fst) p) :
    ((chainPairFunctor ℚ).obj P).hom.f (p + q) ≫
      retainedAmbientCapRelativeLift P p q φ = 0 := by
  have hc : ((chainPairFunctor ℚ).obj P).hom.f (p + q) ≫ Simplicial.capHom ℚ p q φ =
      Simplicial.capHom ℚ p q
        (Simplicial.cochainMap ℚ (TopCat.toSSet.map P.map) p φ) ≫
          ((chainPairFunctor ℚ).obj P).hom.f q := by
    apply ModuleCat.hom_ext
    ext c
    exact (Simplicial.cap_naturality ℚ (TopCat.toSSet.map P.map) p q φ c).symm
  have hz := congrArg (fun f => f.f q) (subspaceChainMap_relativeChainProjection ℚ P)
  change ((chainPairFunctor ℚ).obj P).hom.f q ≫ (relativeChainProjection ℚ P).f q = 0 at hz
  rw [retainedAmbientCapRelativeLift, ← Category.assoc, hc, Category.assoc, hz, comp_zero]

/-- Ambient cochains act on the actual quotient relative-chain groups. -/
def retainedRelativeAmbientCapHom (P : TopPair.{0}) (p q : ℕ)
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj P.fst) p) :
    RelativeChainGroup ℚ P (p + q) ⟶ RelativeChainGroup ℚ P q :=
  (relativeChainProjectionComponentIsCokernelForCap ℚ P (p + q)).desc
    (CokernelCofork.ofπ (retainedAmbientCapRelativeLift P p q φ)
      (retained_subspace_chain_ambient_cap_relative_lift P p q φ))

/-- The quotient cap map retains the actual absolute-chain formula. -/
@[reassoc]
theorem retained_relative_projection_ambient_cap (P : TopPair.{0}) (p q : ℕ)
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj P.fst) p) :
    (relativeChainProjection ℚ P).f (p + q) ≫ retainedRelativeAmbientCapHom P p q φ =
      Simplicial.capHom ℚ p q φ ≫ (relativeChainProjection ℚ P).f q :=
  (Cofork.IsColimit.π_desc (relativeChainProjectionComponentIsCokernelForCap ℚ P (p + q))
    (t := CokernelCofork.ofπ (retainedAmbientCapRelativeLift P p q φ)
      (retained_subspace_chain_ambient_cap_relative_lift P p q φ))).trans
        (CokernelCofork.π_ofπ _ _ _)

/-- The actual relative ambient cap operation commutes with restricting the closed support. -/
theorem retained_relative_ambient_cap_support_inclusion
    (X : TopCat.{0}) (p q : ℕ) (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p)
    {S T : Set X} (h : S ⊆ T) :
    ((relativeChainFunctor ℚ).map (supportInclusionPairMap X h)).f (p + q) ≫
      retainedRelativeAmbientCapHom (TopPair.ofSubset Sᶜ) p q φ =
    retainedRelativeAmbientCapHom (TopPair.ofSubset Tᶜ) p q φ ≫
      ((relativeChainFunctor ℚ).map (supportInclusionPairMap X h)).f q := by
  apply Cofork.IsColimit.hom_ext
    (relativeChainProjectionComponentIsCokernelForCap ℚ (TopPair.ofSubset Tᶜ) (p + q))
  change (relativeChainProjection ℚ (TopPair.ofSubset Tᶜ)).f (p + q) ≫ _ =
    (relativeChainProjection ℚ (TopPair.ofSubset Tᶜ)).f (p + q) ≫ _
  have hn (j : ℕ) := congrArg (fun f => f.f j)
    (relativeChainProjection_supportInclusion ℚ X h)
  change ∀ j, (relativeChainProjection ℚ (TopPair.ofSubset Tᶜ)).f j ≫
    ((relativeChainFunctor ℚ).map (supportInclusionPairMap X h)).f j =
    (relativeChainProjection ℚ (TopPair.ofSubset Sᶜ)).f j at hn
  rw [← Category.assoc, hn, retained_relative_projection_ambient_cap,
    retained_relative_projection_ambient_cap_assoc, hn]

/-- The actual relative cap operation satisfies the signed boundary formula on every chain class. -/
theorem retained_relative_ambient_cap_boundary_apply
    (P : TopPair.{0}) (p q : ℕ)
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj P.fst) p)
    (hφ : Simplicial.coboundary ℚ p φ = 0)
    (c : RelativeChainGroup ℚ P (p + q + 1)) :
    relativeBoundary ℚ P q ((retainedRelativeAmbientCapHom P p (q + 1) φ).hom c) =
      (-1 : ℚ) ^ p • (retainedRelativeAmbientCapHom P p q φ).hom
        (relativeBoundary ℚ P (p + q) c) := by
  let π := (relativeChainProjection ℚ P).f (p + q + 1)
  letI : Epi π := Cofork.IsColimit.epi
    (relativeChainProjectionComponentIsCokernelForCap ℚ P (p + q + 1))
  obtain ⟨b, rfl⟩ := (ModuleCat.epi_iff_surjective π).mp inferInstance c
  dsimp only [π]
  have hproj (j : ℕ) (a : Simplicial.ChainGroup ℚ (TopCat.toSSet.obj P.fst) (p + j)) :=
    ConcreteCategory.congr_hom (retained_relative_projection_ambient_cap P p j φ) a
  change ∀ j a,
    (retainedRelativeAmbientCapHom P p j φ).hom
      (((relativeChainProjection ℚ P).f (p + j)).hom a) =
      ((relativeChainProjection ℚ P).f j).hom (Simplicial.cap ℚ p j φ a) at hproj
  erw [hproj, relativeBoundary_projection, relativeBoundary_projection, hproj,
    Simplicial.boundary_cap_eq_of_cocycle ℚ p q φ hφ, map_smul]

/-- The signed relative cap boundary identity as an equality of actual chain-group morphisms. -/
theorem retained_relative_ambient_cap_boundary (P : TopPair.{0}) (p q : ℕ)
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj P.fst) p)
    (hφ : Simplicial.coboundary ℚ p φ = 0) :
    retainedRelativeAmbientCapHom P p (q + 1) φ ≫ ((relativeChainFunctor ℚ).obj P).d (q + 1) q =
      (-1 : ℤ) ^ p •
        (((relativeChainFunctor ℚ).obj P).d (p + q + 1) (p + q) ≫
          retainedRelativeAmbientCapHom P p q φ) := by
  apply ModuleCat.hom_ext
  ext c
  change relativeBoundary ℚ P q ((retainedRelativeAmbientCapHom P p (q + 1) φ).hom c) =
    (-1 : ℤ) ^ p • (retainedRelativeAmbientCapHom P p q φ).hom
      (relativeBoundary ℚ P (p + q) c)
  rw [← Int.cast_smul_eq_zsmul ℚ, Int.cast_pow, Int.cast_neg, Int.cast_one]
  exact retained_relative_ambient_cap_boundary_apply P p q φ hφ c

end HodgeLean.Foundations.QuotientDuality
