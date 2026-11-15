import HodgeLean.Foundations.AlgebraicGeometry.ConormalAffineFlatIdeal
import HodgeLean.Foundations.AlgebraicGeometry.ConormalBaseChangeTransport
import HodgeLean.Foundations.AlgebraicGeometry.ConormalPushoutKernel
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Conormal comparison for affine ring pushout squares
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Conormal

/-- Flat conormal comparison on an affine cartesian square given by its ring pushout. -/
def affineFlatPushoutConormalIso
    {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (A B : CommRingCat.{0}) (p : CommRingCat.of R ⟶ A) (k : A ⟶ B)
    (q : CommRingCat.of S ⟶ B)
    (sq : IsPushout p (CommRingCat.ofHom (algebraMap R S)) k q)
    (hp : Function.Surjective p.hom) :
    (Scheme.Modules.pullback (Spec.map k)).obj (sheaf (Spec.map p)) ≅
      sheaf (Spec.map q) := by
  have h : Spec.map k ≫ Spec.map p =
      Spec.map q ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, sq.w]
  have hker : (RingHom.ker p.hom).map (algebraMap R S) = RingHom.ker q.hom :=
    pushout_kernel_eq p (CommRingCat.ofHom (algebraMap R S)) k q sq hp
  let e := affineFlatKernelIdealIso (R := R) (S := S) A B p q hker
  exact sheafIsoOfIdealIso (Spec.map p) (Spec.map q)
    (Spec.map (CommRingCat.ofHom (algebraMap R S))) (Spec.map k) h e

/-- A cartesian square of affine presentations supplies the ring pushout comparison. -/
def affineFlatCartesianConormalIso
    {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
    (A B : CommRingCat.{0}) (p : CommRingCat.of R ⟶ A) (k : A ⟶ B)
    (q : CommRingCat.of S ⟶ B)
    (sq : IsPullback (Spec.map k) (Spec.map q) (Spec.map p)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))))
    (hp : Function.Surjective p.hom) :
    (Scheme.Modules.pullback (Spec.map k)).obj (sheaf (Spec.map p)) ≅
      sheaf (Spec.map q) := by
  have hs : IsPullback k.op q.op p.op (CommRingCat.ofHom (algebraMap R S)).op :=
    IsPullback.of_map_of_faithful Scheme.Spec sq
  exact affineFlatPushoutConormalIso (R := R) (S := S) A B p k q hs.unop.flip hp

/-- The affine presentation case with the geometric immersion and flatness hypotheses. -/
def affineFlatBaseChangeIso
    {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (A B : CommRingCat.{0}) (p : CommRingCat.of R ⟶ A) (k : A ⟶ B)
    (q : CommRingCat.of S ⟶ B)
    [IsClosedImmersion (Spec.map p)]
    [Flat (Spec.map (CommRingCat.ofHom (algebraMap R S)))]
    (sq : IsPullback (Spec.map k) (Spec.map q) (Spec.map p)
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))) :
    (Scheme.Modules.pullback (Spec.map k)).obj (sheaf (Spec.map p)) ≅
      sheaf (Spec.map q) := by
  have hf : (algebraMap R S).Flat :=
    (Flat.SpecMap_iff (f := CommRingCat.ofHom (algebraMap R S))).mp inferInstance
  have : Module.Flat R S := RingHom.flat_algebraMap_iff.mp hf
  have hp : Function.Surjective p.hom := by
    have hsurj := (Spec.map p).app_surjective ⊤ (isAffineOpen_top _)
    have heq : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Spec.map p).appTop ≫
        (Scheme.ΓSpecIso A).hom = p := by
      rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    rw [← heq]
    exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso A).hom).surjective.comp
      (hsurj.comp (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv).surjective)
  exact affineFlatCartesianConormalIso (R := R) (S := S) A B p k q sq hp

end AlgebraicGeometry.Conormal
