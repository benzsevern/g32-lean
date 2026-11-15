import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineComparisonEpi

/-! # Kernel generation and affine conormal epimorphisms -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program AlgebraicGeometry.Conormal

/-- The extended ambient kernel maps onto the specified target kernel. -/
def unionConormalGeneratedKernelMap
    {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (A B : CommRingCat.{0}) (p : CommRingCat.of R ⟶ A) (q : CommRingCat.of S ⟶ B)
    (hker : (RingHom.ker p.hom).map (algebraMap R S) = RingHom.ker q.hom) :
    (ModuleCat.extendScalars (algebraMap R S)).obj
      (ModuleCat.of R (RingHom.ker p.hom)) ⟶ ModuleCat.of S (RingHom.ker q.hom) :=
  (s2e_extendScalars_algebraMap_iso (ModuleCat.of R (RingHom.ker p.hom))).hom ≫
    ModuleCat.ofHom (idealExtensionMap (S := S) (RingHom.ker p.hom)) ≫
      (LinearEquiv.ofEq _ _ hker).toModuleIso.hom

/-- The generated kernel arrow is epic without a flatness requirement. -/
lemma unionConormalGeneratedKernelMap_epi
    {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (A B : CommRingCat.{0}) (p : CommRingCat.of R ⟶ A) (q : CommRingCat.of S ⟶ B)
    (hker : (RingHom.ker p.hom).map (algebraMap R S) = RingHom.ker q.hom) :
    Epi (unionConormalGeneratedKernelMap A B p q hker) := by
  haveI : Epi (ModuleCat.ofHom (idealExtensionMap (S := S) (RingHom.ker p.hom))) :=
    (ModuleCat.epi_iff_surjective _).mpr (idealExtensionMap_surjective _)
  unfold unionConormalGeneratedKernelMap
  infer_instance

/-- The generated kernel arrow retains the ambient ring map on unit tensors. -/
lemma unionConormalGeneratedKernelMap_one_tmul
    {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (A B : CommRingCat.{0}) (p : CommRingCat.of R ⟶ A) (q : CommRingCat.of S ⟶ B)
    (hker : (RingHom.ker p.hom).map (algebraMap R S) = RingHom.ker q.hom)
    (x : RingHom.ker p.hom) :
    ((unionConormalGeneratedKernelMap A B p q hker).hom ((1 : S) ⊗ₜ[R] x)).val =
      algebraMap R S x.val := by
  change (1 : S) • algebraMap R S x.val = algebraMap R S x.val
  rw [one_smul]

/-- Kernel generation suffices for epimorphy of natural affine conormal comparison. -/
lemma unionConormal_affineComparison_epi_of_kernel_eq
    {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (A B : CommRingCat.{0}) (p : CommRingCat.of R ⟶ A) (q : CommRingCat.of S ⟶ B)
    (k : A ⟶ B)
    (h : Spec.map k ≫ Spec.map p = Spec.map q ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (hker : (RingHom.ker p.hom).map (algebraMap R S) = RingHom.ker q.hom) :
    Epi (comparisonMap (Spec.map p) (Spec.map q)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) (Spec.map k) h) := by
  haveI := unionConormalGeneratedKernelMap_epi A B p q hker
  exact unionConormal_affineComparison_epi A B p q k h
    (unionConormalGeneratedKernelMap A B p q hker)
    (unionConormalGeneratedKernelMap_one_tmul A B p q hker)

#print axioms unionConormalGeneratedKernelMap_epi
#print axioms unionConormalGeneratedKernelMap_one_tmul
#print axioms unionConormal_affineComparison_epi_of_kernel_eq
end HodgeLean.Foundations.Program.G32Native
