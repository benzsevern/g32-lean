import HodgeLean.Foundations.QuotientDuality.ProperCycleTriadCapNaturality
import HodgeLean.Foundations.QuotientDuality.ProperCycleRelativePullbackCochain

/-! # Original cap naturality on actual triad homology groups -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original triad cap on homology is natural for actual maps of both subspaces and the literal relative cocycle pullback.
Source: Hatcher, Algebraic Topology, section 3.3, naturality of relative cap products on homology.
HC no distance; AV milestone no distance. -/
lemma properCycle_triad_cap_cocycle_naturality
    {X Y : TopCat.{0}} (f : X ⟶ Y) (A B : Set X) (C D : Set Y)
    (hA : Set.MapsTo f A C) (hB : Set.MapsTo f B D) (p q : ℕ)
    (φ : RelativeCochain ℚ (TopPair.ofSubset (X := Y) C) p)
    (hφ : relativeCoboundary ℚ (TopPair.ofSubset (X := Y) C) p φ = 0) :
    let ψ : RelativeCocycle ℚ (TopPair.ofSubset (X := X) A) p :=
      ⟨(((relativeChainFunctor ℚ).map (TopPair.ofSubsetHom f hA)).f p).hom.dualMap φ, by
        change relativeCoboundary ℚ _ p _ = 0
        rw [properCycle_relative_coboundary_naturality, hφ, map_zero]⟩
    ∀ c : TriadRelativeHomology ℚ X A B (p + q),
      relativeHomologyMap ℚ q (TopPair.ofSubsetHom f hB)
          (triadCapHomologyMap ℚ X A B p q ψ.1 ψ.2 c) =
        triadCapHomologyMap ℚ Y C D p q φ hφ
          ((HomologicalComplex.homologyMap (properCycle_triad_relative_chain_map f A B C D hA hB) (p + q)).hom c) := by
  let ψ : RelativeCocycle ℚ (TopPair.ofSubset (X := X) A) p :=
    ⟨(((relativeChainFunctor ℚ).map (TopPair.ofSubsetHom f hA)).f p).hom.dualMap φ, by
      change relativeCoboundary ℚ _ p _ = 0
      rw [properCycle_relative_coboundary_naturality, hφ, map_zero]⟩
  dsimp only
  intro c
  let F := (HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) (p + q)).map
    (properCycle_triad_relative_chain_map f A B C D hA hB)
  let G := (HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) q).map
    ((relativeChainFunctor ℚ).map (TopPair.ofSubsetHom f hB))
  let CX := triadCapShortComplexHom ℚ X A B p q ψ.1 ψ.2
  let CY := triadCapShortComplexHom ℚ Y C D p q φ hφ
  have h : ShortComplex.homologyMap (CX ≫ G) = ShortComplex.homologyMap (F ≫ CY) := by
    apply AlgebraicTopology.Simplicial.homologyMap_eq_of_τ₂_eq
    change CX.τ₂ ≫ G.τ₂ = F.τ₂ ≫ CY.τ₂
    rw [triadCapShortComplexHom_τ₂, triadCapShortComplexHom_τ₂]
    exact properCycle_triad_cap_chain_naturality f A B C D hA hB p q φ
  rw [ShortComplex.homologyMap_comp, ShortComplex.homologyMap_comp] at h
  exact ConcreteCategory.congr_hom h c

/-- The original triad cap on actual relative cohomology and homology is natural for the literal induced maps of both subspaces.
Source: Hatcher, Algebraic Topology, section 3.3, naturality of relative cap products.
HC no distance; AV milestone no distance. -/
lemma properCycle_triad_cap_naturality
    {X Y : TopCat.{0}} (f : X ⟶ Y) (A B : Set X) (C D : Set Y)
    (hA : Set.MapsTo f A C) (hB : Set.MapsTo f B D) (p q : ℕ)
    (a : RelativeCohomology ℚ (TopPair.ofSubset (X := Y) C) p)
    (c : TriadRelativeHomology ℚ X A B (p + q)) :
    relativeHomologyMap ℚ q (TopPair.ofSubsetHom f hB)
        (triadCapCohomologyLinear ℚ X A B p q
          (relativeCohomologyMap ℚ p (TopPair.ofSubsetHom f hA) a) c) =
      triadCapCohomologyLinear ℚ Y C D p q a
        ((HomologicalComplex.homologyMap (properCycle_triad_relative_chain_map f A B C D hA hB) (p + q)).hom c) := by
  let fA := TopPair.ofSubsetHom f hA
  let fB := TopPair.ofSubsetHom f hB
  let SQ := ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := Y) C)).sc p
  let SP := ((relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := X) A)).sc p
  obtain ⟨u, rfl⟩ := (relativeCochainCohomologyEquiv ℚ (TopPair.ofSubset (X := Y) C) p).surjective a
  obtain ⟨φ, rfl⟩ := SQ.linearDual.moduleCatHomologyClass_surjective u
  let F := (HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) p).map
    ((relativeChainFunctor ℚ).map fA)
  let τ := ShortComplex.moduleCatCycleMap (ShortComplex.linearDualMap F) φ
  have ha : relativeCohomologyMap ℚ p fA
      (relativeCochainCohomologyEquiv ℚ (TopPair.ofSubset (X := Y) C) p (SQ.linearDual.moduleCatHomologyClass φ)) =
    relativeCochainCohomologyEquiv ℚ (TopPair.ofSubset (X := X) A) p (SP.linearDual.moduleCatHomologyClass τ) := by
    have h := congrArg (relativeCochainCohomologyEquiv ℚ (TopPair.ofSubset (X := X) A) p)
      (properCycle_relative_pullback_cochain_comparison fA p (SQ.linearDual.moduleCatHomologyClass φ))
    rw [LinearEquiv.apply_symm_apply, ShortComplex.moduleCatHomologyClass_naturality] at h
    exact h
  refine (congrArg (fun z : RelativeCohomology ℚ (TopPair.ofSubset (X := X) A) p =>
    relativeHomologyMap ℚ q fB (triadCapCohomologyLinear ℚ X A B p q z c)) ha).trans ?_
  have hx : triadCapCohomologyLinear ℚ X A B p q
      (relativeCochainCohomologyEquiv ℚ (TopPair.ofSubset (X := X) A) p (SP.linearDual.moduleCatHomologyClass τ)) =
      triadRelativeCohomologyCycleCapLinear ℚ X A B p q τ := triadCapCohomologyLinear_on_cycle ℚ X A B p q τ
  have hy : triadCapCohomologyLinear ℚ Y C D p q
      (relativeCochainCohomologyEquiv ℚ (TopPair.ofSubset (X := Y) C) p (SQ.linearDual.moduleCatHomologyClass φ)) =
      triadRelativeCohomologyCycleCapLinear ℚ Y C D p q φ := triadCapCohomologyLinear_on_cycle ℚ Y C D p q φ
  refine (congrArg (relativeHomologyMap ℚ q fB) (LinearMap.congr_fun hx c)).trans ?_
  refine Eq.trans ?_ (LinearMap.congr_fun hy
    ((HomologicalComplex.homologyMap (properCycle_triad_relative_chain_map f A B C D hA hB) (p + q)).hom c)).symm
  exact properCycle_triad_cap_cocycle_naturality f A B C D hA hB p q
    (relativeCohomologyCycleToCocycle ℚ (TopPair.ofSubset (X := Y) C) p φ).1
    (relativeCohomologyCycleToCocycle ℚ (TopPair.ofSubset (X := Y) C) p φ).2 c

end HodgeLean.Foundations.QuotientDuality
