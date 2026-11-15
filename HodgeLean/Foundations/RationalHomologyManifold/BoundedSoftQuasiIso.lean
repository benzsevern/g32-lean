import HodgeLean.Foundations.RationalHomologyManifold.BoundedSoftGlobalExactness
import HodgeLean.Foundations.RationalHomologyManifold.SoftBiproduct
import HodgeLean.Foundations.RationalHomologyManifold.ConeCriterion
import Mathlib.Algebra.Homology.HomotopyCategory.Plus

/-! Global sections on actual bounded-below soft sheaf complexes.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Every term of the actual cone of a map between soft complexes is soft.
Source: Bredon, Sheaf Theory, second edition, II.9; the binary soft direct sum in each cone degree.
HC no distance; AV milestone no distance.
-/
theorem soft_mappingCone_terms (X : TopCat.{0})
    {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℤ} (f : K ⟶ L)
    (hK : ∀ i, IsSoft (K.X i)) (hL : ∀ i, IsSoft (L.X i)) (i : ℤ) :
    IsSoft ((CochainComplex.mappingCone f).X i) := by
  let e := HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1) rfl
  exact isSoft_of_sheaf_iso e.symm (isSoft_biprod _ _ (hK _) (hL _))

#print axioms soft_mappingCone_terms
/-- Global sections preserve quasi-isomorphisms between bounded-below complexes of soft sheaves.
Source: Bredon, Sheaf Theory, second edition, II.9 and IV.2; the exact soft mapping-cone argument.
HC no distance; AV milestone no distance.
-/
theorem bounded_soft_global_quasiIso (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    {K L : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℤ} (f : K ⟶ L)
    (a b : ℤ) [K.IsStrictlyGE a] [L.IsStrictlyGE b] (hf : QuasiIso f)
    (hK : ∀ i, IsSoft (K.X i)) (hL : ∀ i, IsSoft (L.X i)) :
    QuasiIso (((subdivisionGlobalSectionsFunctor X).mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  let E := subdivisionGlobalSectionsFunctor X
  let c : ℤ := min a b - 1
  letI : (CochainComplex.mappingCone f).IsStrictlyGE c :=
    CochainComplex.isStrictlyGE_mappingCone f a b c (by dsimp [c]; omega)
      (by dsimp [c]; omega)
  have hc := (quasiIso_iff_mappingCone_acyclic f).mp hf
  have hg := bounded_soft_global_acyclic X (CochainComplex.mappingCone f) c hc
    (soft_mappingCone_terms X f hK hL)
  apply (quasiIso_iff_mappingCone_acyclic _).mpr
  intro i
  exact (hg i).of_iso (CochainComplex.mappingCone.mapHomologicalComplexIso f E)

#print axioms bounded_soft_global_quasiIso
end HodgeLean.Foundations.RationalHomologyManifold
