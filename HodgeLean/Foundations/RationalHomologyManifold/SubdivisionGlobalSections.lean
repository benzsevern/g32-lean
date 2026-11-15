import HodgeLean.Foundations.RationalHomologyManifold.SubdivisionBoundaryGlobalLifting

/-! Global sections on the actual subdivision-limit sheaf model.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
open HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Evaluation of actual abelian sheaves on the whole space.
Source: Bredon, Sheaf Theory, second edition, II.1; the global section functor.
HC no distance; AV milestone no distance.
-/
def subdivisionGlobalSectionsFunctor (X : TopCat.{0}) :
    TopCat.Sheaf AddCommGrpCat.{0} X ⥤ AddCommGrpCat.{0} :=
  sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat ⋙
    (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (Opposite.op ⊤)

/-- Evaluation of abelian sheaves respects addition of morphisms.
Source: Mathlib, CategoryTheory.Preadditive; pointwise addition of sheaf morphisms.
HC no distance; AV milestone no distance.
-/
instance subdivisionGlobalSectionsFunctor_additive (X : TopCat.{0}) :
    (subdivisionGlobalSectionsFunctor X).Additive where
  map_add := rfl

/-- Global sections preserve finite limits of actual abelian sheaves.
Source: Mathlib, CategoryTheory.Sites.Limits; limits of sheaves and pointwise evaluation.
HC no distance; AV milestone no distance.
-/
instance subdivisionGlobalSectionsFunctor_preservesFiniteLimits (X : TopCat.{0}) :
    PreservesFiniteLimits (subdivisionGlobalSectionsFunctor X) := by
  letI : PreservesFiniteLimits (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) :=
    inferInstance
  letI : PreservesFiniteLimits ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{0}).obj (Opposite.op ⊤)) :=
    inferInstance
  exact comp_preservesFiniteLimits _ _

#print axioms subdivisionGlobalSectionsFunctor
#print axioms subdivisionGlobalSectionsFunctor_additive
#print axioms subdivisionGlobalSectionsFunctor_preservesFiniteLimits
/-- Global sections preserve right homology of the actual positive-degree boundary short complex at and above the orientation dimension.
Source: Bredon, Sheaf Theory, second edition, VI.12; preservation of boundary cokernels and kernels under global sections.
HC no distance; AV milestone no distance.
-/
theorem subdivision_global_preservesRightHomology (X : TopCat.{0})
    [CompactSpace X] [T2Space X] (t : FiniteTriangulation X) (N n : ℕ)
    (o : LocalRationalOrientation X N) (hN : N ≤ n + 1) :
    (subdivisionGlobalSectionsFunctor X).PreservesRightHomologyOf
      ((subdivisionLimitSheafComplex X).sc' (n + 2) (n + 1) n) := by
  refine ⟨fun h => ?_⟩
  exact {
    f := subdivision_boundary_global_preservesCokernel X t N n o hN
    g' := inferInstance }

#print axioms subdivision_global_preservesRightHomology

/-- The actual global subdivision-limit chain complex is exact in every positive degree above the orientation dimension.
Source: Bredon, Sheaf Theory, second edition, VI.12; local concentration and soft boundary-image lifting.
HC no distance; AV milestone no distance.
-/
theorem subdivision_global_exactAt_above_orientation (X : TopCat.{0})
    [CompactSpace X] [T2Space X] (t : FiniteTriangulation X) (N n : ℕ)
    (o : LocalRationalOrientation X N) (hN : N < n + 1) :
    (((subdivisionGlobalSectionsFunctor X).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (subdivisionLimitSheafComplex X)).ExactAt (n + 1) := by
  let C := subdivisionLimitSheafComplex X
  let E := subdivisionGlobalSectionsFunctor X
  letI := subdivision_global_preservesRightHomology X t N n o (by omega)
  have hS : (C.sc' (n + 2) (n + 1) n).Exact :=
    (C.exactAt_iff' (n + 2) (n + 1) n (ChainComplex.prev ℕ (n + 1))
      (ChainComplex.next_nat_succ n)).mp
      (subdivisionLimitSheaf_exactAt X N o (n + 1) (by omega))
  apply (((E.mapHomologicalComplex (ComplexShape.down ℕ)).obj C).exactAt_iff'
    (n + 2) (n + 1) n (ChainComplex.prev ℕ (n + 1)) (ChainComplex.next_nat_succ n)).mpr
  exact hS.map_of_preservesRightHomologyOf E

#print axioms subdivision_global_exactAt_above_orientation

/-- Global sections preserve the actual regraded right homology at and below the orientation cutoff.
Source: Bredon, Sheaf Theory, second edition, VI.12; regrading the canonical boundary cokernel comparison.
HC no distance; AV milestone no distance.
-/
theorem subdivision_global_preservesCochainRightHomology (X : TopCat.{0})
    [CompactSpace X] [T2Space X] (t : FiniteTriangulation X) (N n : ℕ)
    (o : LocalRationalOrientation X N) (hN : N ≤ n + 1) :
    (subdivisionGlobalSectionsFunctor X).PreservesRightHomologyOf
      ((subdivisionLimitSheafCochainComplex X).sc (-((n + 1 : ℕ) : ℤ))) := by
  let C := subdivisionLimitSheafComplex X
  let K := subdivisionLimitSheafCochainComplex X
  let E := subdivisionGlobalSectionsFunctor X
  let i : ℤ := -((n + 1 : ℕ) : ℤ)
  have ha : ComplexShape.embeddingDownNat.f (n + 2) = (ComplexShape.up ℤ).prev i := by
    rw [CochainComplex.prev]
    change -((n + 2 : ℕ) : ℤ) = i - 1
    dsimp [i]
    omega
  have hb : ComplexShape.embeddingDownNat.f (n + 1) = i := rfl
  let a := C.extendXIso ComplexShape.embeddingDownNat ha
  let b := C.extendXIso ComplexShape.embeddingDownNat hb
  have hf : (K.sc i).f ≫ b.hom = a.hom ≫ C.d (n + 2) (n + 1) := by
    change (C.extend ComplexShape.embeddingDownNat).d ((ComplexShape.up ℤ).prev i) i ≫ b.hom = _
    rw [C.extend_d_eq ComplexShape.embeddingDownNat ha hb]
    simp only [a, b, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  let e : parallelPair (K.sc i).f 0 ≅ parallelPair (C.d (n + 2) (n + 1)) 0 :=
    parallelPair.ext a b hf (by simp)
  letI : PreservesColimit (parallelPair (C.d (n + 2) (n + 1)) 0) E :=
    subdivision_boundary_global_preservesCokernel X t N n o hN
  have hp : PreservesColimit (parallelPair (K.sc i).f 0) E :=
    preservesColimit_of_iso_diagram E e.symm
  refine ⟨fun h => ?_⟩
  exact { f := hp, g' := inferInstance }

#print axioms subdivision_global_preservesCochainRightHomology

end HodgeLean.Foundations.RationalHomologyManifold
