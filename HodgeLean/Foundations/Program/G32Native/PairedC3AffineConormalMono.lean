import HodgeLean.Foundations.Program.G32Native.PairedC3ConormalIdealMono
import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineFirstRawArrow
import HodgeLean.Foundations.Program.G32Native.UnionConormalTildeMono
import HodgeLean.Foundations.Program.SchoenCycleC2ScalarExtensionTensorHelpers

/-! # Injectivity of the natural affine conormal flag map -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

variable {K A B C : Type} [CommRing K] [CommRing A] [CommRing B] [CommRing C]
    [Algebra K A] [Algebra K B] [Algebra K C]
    [Algebra A B] [Algebra A C] [Algebra B C]
    [IsScalarTower K A B] [IsScalarTower K A C] [IsScalarTower K B C]
    [IsScalarTower A B C]

/-- The natural affine first map is monic for a smooth ambient algebra
and intermediate quotient. The coordinates use the original ideal map.
Source: Hartshorne, Algebraic Geometry, II.8.12 and II.8.17. -/
theorem paired_c3_affine_conormal_first_mono
    [Algebra.FormallySmooth K A] [Algebra.FormallySmooth K B]
    (hAB : Function.Surjective (algebraMap A B))
    (hAC : Function.Surjective (algebraMap A C))
    (h : Spec.map (CommRingCat.ofHom (algebraMap B C)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A B)) =
      Spec.map (CommRingCat.ofHom (algebraMap A C))) :
    Mono (unionConormalFirst (Spec.map (CommRingCat.ofHom (algebraMap A B)))
      (Spec.map (CommRingCat.ofHom (algebraMap A C)))
      (Spec.map (CommRingCat.ofHom (algebraMap B C))) h) := by
  let p : CommRingCat.of A ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap A B)
  let q : CommRingCat.of A ⟶ CommRingCat.of C := CommRingCat.ofHom (algebraMap A C)
  let k : CommRingCat.of B ⟶ CommRingCat.of C := CommRingCat.ofHom (algebraMap B C)
  have hABC := IsScalarTower.algebraMap_eq A B C
  have hKAC := IsScalarTower.algebraMap_eq K A C
  letI : Algebra A C := q.hom.toAlgebra
  haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' hABC
  haveI : IsScalarTower K A C := IsScalarTower.of_algebraMap_eq' hKAC
  have hAC' : Function.Surjective (algebraMap A C) := hAC
  let I := RingHom.ker p.hom
  let J := RingHom.ker q.hom
  have hk : I ≤ J := by
    intro t ht
    change algebraMap A C t = 0
    have ht' : algebraMap A B t = 0 := RingHom.mem_ker.mp ht
    rw [IsScalarTower.algebraMap_apply A B C, ht', map_zero]
  let b : ModuleCat.of A (A ⊗[A] I) ⟶ ModuleCat.of A J :=
    ModuleCat.ofHom ((Submodule.inclusion hk).comp (TensorProduct.lid A I).toLinearMap)
  let eI := s2e_extendScalars_algebraMap_iso (A := A) (S := A) (ModuleCat.of A I)
  let E : (ModuleCat.extendScalars (algebraMap A A)).obj (ModuleCat.of A I) ⟶
      ModuleCat.of A J := eI.hom ≫ b
  have hE (t : I) : (E.hom ((1 : A) ⊗ₜ[A] t)).val = t.val := by
    change (1 : A) * t.val = t.val
    exact one_mul _
  haveI : Mono ((ModuleCat.extendScalars q.hom).map b) := by
    apply (ModuleCat.mono_iff_injective _).mpr
    change Function.Injective
      (((Submodule.inclusion hk).comp (TensorProduct.lid A I).toLinearMap).baseChange C)
    rw [LinearMap.baseChange_comp]
    exact (paired_c3_ideal_conormal_inclusion_injective (K := K) hAB hAC').comp
      ((TensorProduct.lid A I).baseChange A C _ _).injective
  haveI : Mono ((ModuleCat.extendScalars q.hom).map E) := by
    dsimp only [E]
    rw [Functor.map_comp]
    infer_instance
  let T := (tilde.functor (CommRingCat.of C)).map ((ModuleCat.extendScalars q.hom).map E)
  haveI : Mono T := union_tilde_map_mono ((ModuleCat.extendScalars q.hom).map E)
  let ea := unionConormalAffineFirstRawArrowIso A (CommRingCat.of B) (CommRingCat.of C)
    p q k h E hE
  exact ((MorphismProperty.monomorphisms (Spec (CommRingCat.of C)).Modules).arrow_mk_iso_iff ea).mpr
    (show Mono T from inferInstance)

#print axioms paired_c3_affine_conormal_first_mono
end HodgeLean.Foundations.Program.G32Native
