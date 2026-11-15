import HodgeLean.Foundations.BundleThom.DegreeZeroCoverHelpers

/-! # Relative degree-zero detection on pairs with empty subspace

For such pairs the chain projection is an isomorphism, and actual covering maps detect coclasses.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.RealDefs
namespace HodgeLean.Foundations.BundleThom

/-- The canonical relative-to-absolute comparison commutes with every actual pair map.
Source: Hatcher, Algebraic Topology, §3.1, naturality of relative cohomology. -/
theorem i1_relativeToAbsolute_naturality {P Q : TopPair} (f : P ⟶ Q)
    (n : ℕ) (u : RelativeCohomology ℚ Q n) :
    relativeCohomologyToAbsolute ℚ P n (relativeCohomologyMap ℚ n f u) =
      cohomologyMap ℚ n (TopPair.Hom.fst f) (relativeCohomologyToAbsolute ℚ Q n u) := by
  have hdual := congrArg HomologicalComplex.linearDualMap
    (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) f)
  rw [HomologicalComplex.linearDualMap_comp, HomologicalComplex.linearDualMap_comp] at hdual
  have hhom := congrArg (fun a => HomologicalComplex.homologyMap a n) hdual
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hhom
  exact ConcreteCategory.congr_hom hhom u

/-- For a pair with empty subspace, forgetting the relative condition is injective in every degree.
Source: Hatcher, Algebraic Topology, §3.1, pairs with empty subspace and universal coefficients. -/
theorem i1_relativeToAbsolute_injective (P : TopPair) (hP : IsEmpty P.snd) (n : ℕ) :
    Function.Injective (relativeCohomologyToAbsolute ℚ P n) := by
  letI : IsIso (relativeChainProjection ℚ P) := isIso_relativeChainProjection P hP
  intro u v huv
  apply (relativeCohomologyEquivDualHomology ℚ P n).injective
  ext z
  let e := HomologicalComplex.homologyMapIso (asIso (relativeChainProjection ℚ P)) n
  obtain ⟨w, hw⟩ := (e.toLinearEquiv).surjective z
  have hw' : (relativeHomologyProjection ℚ P n).hom w = z := hw
  have h := congrArg (fun c => cohomologyEquivDualHomology ℚ P.fst n c w) huv
  simpa only [cohomologyEquivDualHomology_relativeCohomologyToAbsolute, hw'] using h

/-- Actual jointly surjective maps of pairs detect degree-zero relative classes on an empty-subspace pair.
Source: Hatcher, Algebraic Topology, §3.1, degree-zero cohomology and relative naturality. -/
theorem i1_relativeCohomologyZero_ext_of_cover {P : TopPair} (hP : IsEmpty P.snd)
    {ι : Type} (Q : ι → TopPair) (p : ∀ i, Q i ⟶ P)
    (hcover : ∀ x : P.fst, ∃ i y, TopPair.Hom.fst (p i) y = x)
    (u v : RelativeCohomology ℚ P 0)
    (h : ∀ i, relativeCohomologyMap ℚ 0 (p i) u = relativeCohomologyMap ℚ 0 (p i) v) :
    u = v := by
  apply i1_relativeToAbsolute_injective P hP 0
  apply i1_cohomologyZero_ext_of_cover (fun i => (Q i).fst)
    (fun i => TopPair.Hom.fst (p i)) hcover
  intro i
  rw [← i1_relativeToAbsolute_naturality, ← i1_relativeToAbsolute_naturality, h i]

end HodgeLean.Foundations.BundleThom
