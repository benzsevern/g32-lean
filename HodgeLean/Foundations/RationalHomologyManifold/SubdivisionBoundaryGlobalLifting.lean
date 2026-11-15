import HodgeLean.Foundations.RationalHomologyManifold.SubdivisionTruncationSoftness
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Sites.Limits

/-! Global lifting through actual subdivision boundary images.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
open HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The actual subdivision-limit chain sheaf is exact away from its orientation degree.
Source: Bredon, Sheaf Theory, second edition, VI.12; local homology concentration under subdivision.
HC no distance; AV milestone no distance.
-/
theorem subdivisionLimitSheaf_exactAt (X : TopCat.{0}) [T2Space X]
    (N : ℕ) (o : LocalRationalOrientation X N) (i : ℕ) (hi : i ≠ N) :
    (subdivisionLimitSheafComplex X).ExactAt i := by
  let C := subdivisionLimitSheafComplex X
  apply (C.extend_exactAt_iff ComplexShape.embeddingDownNat (show -(i : ℤ) = -(i : ℤ) from rfl)).mp
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact subdivisionLimitSheafCochainHomology_concentrated X N o (-(i : ℤ)) (by omega)

#print axioms subdivisionLimitSheaf_exactAt
/-- Above the orientation degree, the kernel of the actual next boundary is soft.
Source: Bredon, Sheaf Theory, second edition, VI.12; exactness identifies this kernel with the next soft boundary image.
HC no distance; AV milestone no distance.
-/
theorem subdivision_boundary_kernel_isSoft (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    (t : FiniteTriangulation X) (N n : ℕ) (o : LocalRationalOrientation X N)
    (hN : N ≤ n + 1) :
    IsSoft (kernel ((subdivisionLimitSheafComplex X).d (n + 2) (n + 1))) := by
  let C := subdivisionLimitSheafComplex X
  let S := C.sc' (n + 3) (n + 2) (n + 1)
  have hS : S.Exact := (C.exactAt_iff' (n + 3) (n + 2) (n + 1)
    (ChainComplex.prev ℕ (n + 2)) (ChainComplex.next_nat_succ (n + 1))).mp
      (subdivisionLimitSheaf_exactAt X N o (n + 2) (by omega))
  let e : image S.f ≅ kernel S.g :=
    hS.isLimitImage'.conePointUniqueUpToIso (limit.isLimit _)
  exact isSoft_of_sheaf_iso e (subdivision_boundary_image_isSoft_of_le X t N (n + 1) o (by omega))

#print axioms subdivision_boundary_kernel_isSoft

/-- Every global section of the actual boundary image lifts to a global chain-sheaf section at or above the orientation degree.
Source: Bredon, Sheaf Theory, second edition, Theorem II.9.9 and VI.12; global exactness with a soft kernel.
HC no distance; AV milestone no distance.
-/
theorem subdivision_boundary_global_lift_surjective (X : TopCat.{0})
    [CompactSpace X] [T2Space X] (t : FiniteTriangulation X) (N n : ℕ)
    (o : LocalRationalOrientation X N) (hN : N ≤ n + 1) :
    Function.Surjective ((factorThruImage
      ((subdivisionLimitSheafComplex X).d (n + 2) (n + 1))).hom.app (Opposite.op ⊤)) := by
  let f := (subdivisionLimitSheafComplex X).d (n + 2) (n + 1)
  let g := factorThruImage f
  let S := ShortComplex.mk (kernel.ι g) g (kernel.condition g)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel g }
  have hk : IsSoft (kernel g) := isSoft_of_sheaf_iso (kernelFactorThruImage f).symm
    (subdivision_boundary_kernel_isSoft X t N n o hN)
  exact spec_surjective_globalSections_of_isSoft hS hk

#print axioms subdivision_boundary_global_lift_surjective

/-- Global sections lift through the actual orientation truncation cokernel.
Source: Bredon, Sheaf Theory, second edition, Theorem II.9.9 and VI.12; the soft boundary-image kernel.
HC no distance; AV milestone no distance.
-/
theorem subdivision_boundary_cokernel_global_surjective (X : TopCat.{0})
    [CompactSpace X] [T2Space X] (t : FiniteTriangulation X) (N n : ℕ)
    (o : LocalRationalOrientation X N) (hN : N ≤ n + 1) :
    Function.Surjective ((cokernel.π
      ((subdivisionLimitSheafComplex X).d (n + 2) (n + 1))).hom.app (Opposite.op ⊤)) := by
  let f := (subdivisionLimitSheafComplex X).d (n + 2) (n + 1)
  let S := ShortComplex.mk (image.ι f) (cokernel.π f)
    (image_ι_comp_eq_zero (cokernel.condition f))
  have hS : S.ShortExact := {
    exact := ShortComplex.exact_of_f_is_kernel S
      (ShortComplex.exact_cokernel f).isLimitImage' }
  exact spec_surjective_globalSections_of_isSoft hS
    (subdivision_boundary_image_isSoft_of_le X t N n o hN)

#print axioms subdivision_boundary_cokernel_global_surjective

/-- Global sections preserve the actual boundary cokernel at or above the orientation degree.
Source: Bredon, Sheaf Theory, second edition, Theorem II.9.9 and VI.12; soft image and kernel lifting.
HC no distance; AV milestone no distance.
-/
theorem subdivision_boundary_global_preservesCokernel (X : TopCat.{0})
    [CompactSpace X] [T2Space X] (t : FiniteTriangulation X) (N n : ℕ)
    (o : LocalRationalOrientation X N) (hN : N ≤ n + 1) :
    PreservesColimit (parallelPair
      ((subdivisionLimitSheafComplex X).d (n + 2) (n + 1)) 0)
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat ⋙
        (evaluation (TopologicalSpace.Opens X)ᵒᵖ AddCommGrpCat).obj (Opposite.op ⊤)) := by
  let E : TopCat.Sheaf AddCommGrpCat.{0} X ⥤ AddCommGrpCat.{0} := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat ⋙
    (evaluation (TopologicalSpace.Opens X)ᵒᵖ AddCommGrpCat).obj (Opposite.op ⊤)
  letI : E.Additive := { map_add := rfl }
  letI : PreservesFiniteLimits (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := by
    infer_instance
  letI : PreservesFiniteLimits ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{0}).obj (Opposite.op ⊤)) := by
    infer_instance
  letI : PreservesFiniteLimits E := by
    dsimp [E]
    exact comp_preservesFiniteLimits _ _
  let f := (subdivisionLimitSheafComplex X).d (n + 2) (n + 1)
  let S := ShortComplex.mk (image.ι f) (cokernel.π f)
    (image_ι_comp_eq_zero (cokernel.condition f))
  have hS : S.ShortExact := {
    exact := ShortComplex.exact_of_f_is_kernel S
      (ShortComplex.exact_cokernel f).isLimitImage' }
  letI : Epi (E.map (cokernel.π f)) := (AddCommGrpCat.epi_iff_surjective _).mpr
    (subdivision_boundary_cokernel_global_surjective X t N n o hN)
  letI := hS.mono_f
  letI : Mono (S.map E).f := by
    change Mono (E.map S.f)
    infer_instance
  letI : Epi (S.map E).g := inferInstanceAs (Epi (E.map (cokernel.π f)))
  have hES : (S.map E).ShortExact := {
    exact := ShortComplex.exact_of_f_is_kernel _ (KernelFork.mapIsLimit _ hS.fIsKernel E) }
  letI : Epi (E.map (factorThruImage f)) := (AddCommGrpCat.epi_iff_surjective _).mpr
    (subdivision_boundary_global_lift_surjective X t N n o hN)
  apply preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f)
  refine (CokernelCofork.isColimitMapCoconeEquiv _ E).symm ?_
  exact isCokernelEpiComp hES.gIsCokernel (E.map (factorThruImage f))
    (by change E.map f = E.map (factorThruImage f) ≫ E.map (image.ι f)
        rw [← E.map_comp, image.fac])

#print axioms subdivision_boundary_global_preservesCokernel

end HodgeLean.Foundations.RationalHomologyManifold
