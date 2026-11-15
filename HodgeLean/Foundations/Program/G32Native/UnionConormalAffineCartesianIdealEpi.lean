import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineIdealEpi

/-! # Ideal comparison in cartesian affine diagrams -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open AlgebraicGeometry.Conormal

/-- A cartesian affine square over a surjective ring map gives an epic
natural ideal comparison without a flatness assumption. -/
lemma unionConormal_affineCartesianIdeal_epi
    {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (A B : CommRingCat.{0}) (p : CommRingCat.of R ⟶ A) (q : CommRingCat.of S ⟶ B)
    (k : A ⟶ B)
    (sq : IsPullback (Spec.map k) (Spec.map q) (Spec.map p)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (hp : Function.Surjective p.hom) :
    Epi (idealPullbackMap (Spec.map p) (Spec.map q)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) (Spec.map k) sq.w) := by
  have hs : IsPullback k.op q.op p.op (CommRingCat.ofHom (algebraMap R S)).op :=
    IsPullback.of_map_of_faithful Scheme.Spec sq
  have hker : (RingHom.ker p.hom).map (algebraMap R S) = RingHom.ker q.hom :=
    pushout_kernel_eq p (CommRingCat.ofHom (algebraMap R S)) k q hs.unop.flip hp
  exact unionConormal_affineIdeal_epi_of_kernel_eq A B p q k sq.w hker

end HodgeLean.Foundations.Program.G32Native
