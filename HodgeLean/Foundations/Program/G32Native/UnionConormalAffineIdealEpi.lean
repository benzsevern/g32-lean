import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineKernelEpi

/-! # Epimorphy of the natural affine ideal comparison -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open AlgebraicGeometry.Conormal

/-- Generation of the target kernel makes the actual affine ideal comparison epic. -/
lemma unionConormal_affineIdeal_epi_of_kernel_eq
    {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (A B : CommRingCat.{0}) (p : CommRingCat.of R ⟶ A) (q : CommRingCat.of S ⟶ B)
    (k : A ⟶ B)
    (h : Spec.map k ≫ Spec.map p = Spec.map q ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (hker : (RingHom.ker p.hom).map (algebraMap R S) = RingHom.ker q.hom) :
    Epi (idealPullbackMap (Spec.map p) (Spec.map q)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) (Spec.map k) h) := by
  haveI := unionConormalGeneratedKernelMap_epi A B p q hker
  letI : (tilde.functor (CommRingCat.of S)).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (tilde.adjunction (R := CommRingCat.of S))
  haveI : Epi ((tilde.functor (CommRingCat.of S)).map
      (unionConormalGeneratedKernelMap A B p q hker)) := inferInstance
  rw [unionConormal_affineIdealPullbackMap_transported A B p q k h
    (unionConormalGeneratedKernelMap A B p q hker)
    (unionConormalGeneratedKernelMap_one_tmul A B p q hker)]
  infer_instance

end HodgeLean.Foundations.Program.G32Native
