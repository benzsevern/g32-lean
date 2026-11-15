import HodgeLean.Foundations.BundleThom.RelativeBinaryHomologyVanishingHelpers

/-! # Actual relative chains and coclasses on empty ambient spaces

The singular generators vanish because no simplex maps into an empty space.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicTopology.Singular Simplicial
namespace HodgeLean.Foundations.BundleThom

/-- An empty topological space has zero actual rational singular chain complex.
Source: Hatcher, Algebraic Topology, §2.1, singular chain generators. -/
theorem i1_singularChainComplex_isZero_of_isEmpty (X : TopCat) [IsEmpty X] :
    IsZero (SingularChainComplex ℚ X) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply HomologicalComplex.Hom.ext
  funext n
  apply (TopCat.toSSet.obj X).chainComplex_hom_ext
  intro σ
  exact isEmptyElim ((X.toSSetObjEquiv _ σ) (Classical.arbitrary _))

/-- A pair with empty ambient space has zero actual rational relative chain complex.
Source: Hatcher, Algebraic Topology, §2.1, relative chain quotients. -/
theorem i1_relativeChainComplex_isZero_of_isEmpty (P : TopPair) [IsEmpty P.fst] :
    IsZero ((relativeChainFunctor ℚ).obj P) := by
  let π : SingularChainComplex ℚ P.fst ⟶ (relativeChainFunctor ℚ).obj P :=
    relativeChainProjection ℚ P
  haveI : Epi π := by
    dsimp [π, relativeChainProjection]
    infer_instance
  have hπ : π = 0 := (i1_singularChainComplex_isZero_of_isEmpty P.fst).eq_zero_of_src _
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (cancel_epi π).mp
  rw [Category.comp_id, hπ, comp_zero]

/-- Every rational relative coclass space is a subsingleton when its actual ambient space is empty.
Source: Hatcher, Algebraic Topology, §3.1, rational universal coefficients. -/
theorem i1_relativeCohomology_subsingleton_of_isEmpty (P : TopPair) [IsEmpty P.fst]
    (n : ℕ) : Subsingleton (RelativeCohomology ℚ P n) := by
  apply (i1_relativeHomology_isZero_iff_cohomology_subsingleton P n).mp
  exact (HomologicalComplex.homologyFunctor (ModuleCat ℚ) (ComplexShape.down ℕ) n).map_isZero
    (i1_relativeChainComplex_isZero_of_isEmpty P)

end HodgeLean.Foundations.BundleThom
