import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineIdealMap

/-! # Affine presentations of the natural conormal comparison -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program AlgebraicGeometry.Conormal

/-- Evaluation of pullback transport along an equality is the corresponding
object transport map. -/
lemma unionConormal_pullbackCongr_hom_app {X Y : Scheme.{0}}
    {f g : X ⟶ Y} (h : f = g) (M : Y.Modules) :
    ((Scheme.Modules.pullbackCongr h).app M).hom =
      eqToHom (congrArg (fun t : X ⟶ Y => (Scheme.Modules.pullback t).obj M) h) := by
  cases h
  rfl

/-- The intrinsic pullback prefix of a conormal comparison. -/
def unionConormalComparisonPrefixIso
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    (f : W' ⟶ W) (g : Q' ⟶ Q) (h : g ≫ i = i' ≫ f) :
    (Scheme.Modules.pullback g).obj (s2c_conormal i) ≅
      (Scheme.Modules.pullback i').obj ((Scheme.Modules.pullback f).obj (idealModule i)) :=
  (Scheme.Modules.pullbackComp g i).app (idealModule i) ≪≫
    eqToIso (congrArg (fun t : Q' ⟶ W =>
      (Scheme.Modules.pullback t).obj (idealModule i)) h) ≪≫
    (Scheme.Modules.pullbackComp i' f).symm.app (idealModule i)

/-- The natural conormal map consists of its intrinsic prefix and the ideal map. -/
lemma unionConormal_comparisonMap_eq_prefix
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    (f : W' ⟶ W) (g : Q' ⟶ Q) (h : g ≫ i = i' ≫ f) :
    comparisonMap i i' f g h = (unionConormalComparisonPrefixIso i i' f g h).hom ≫
      (Scheme.Modules.pullback i').map (idealPullbackMap i i' f g h) := by
  unfold comparisonMap unionConormalComparisonPrefixIso
  dsimp only [eqToIso]
  simp only [Iso.trans_hom]
  simp only [Iso.app_hom, Iso.app_inv, Iso.symm_hom, Category.assoc]

/-- The source of an affine conormal comparison is an iterated scalar extension
of the original kernel ideal. -/
def unionConormalAffineComparisonSourceIso
    {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (A B : CommRingCat.{0}) (p : CommRingCat.of R ⟶ A) (q : CommRingCat.of S ⟶ B)
    (k : A ⟶ B)
    (h : Spec.map k ≫ Spec.map p = Spec.map q ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S))) :
    (Scheme.Modules.pullback (Spec.map k)).obj (s2c_conormal (Spec.map p)) ≅
      tilde ((ModuleCat.extendScalars q.hom).obj
        ((ModuleCat.extendScalars (algebraMap R S)).obj
          (ModuleCat.of R (RingHom.ker p.hom)))) :=
  unionConormalComparisonPrefixIso (Spec.map p) (Spec.map q)
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) (Spec.map k) h ≪≫
    (Scheme.Modules.pullback (Spec.map q)).mapIso
      (unionConormalAffineIdealSourceIso (S := S) A p) ≪≫
    (s2e_affine_pullback_tilde_iso _ _ q).app
      ((ModuleCat.extendScalars (algebraMap R S)).obj
        (ModuleCat.of R (RingHom.ker p.hom)))

/-- The target of an affine conormal comparison is scalar extension of its kernel ideal. -/
def unionConormalAffineComparisonTargetIso (S B : CommRingCat.{0}) (q : S ⟶ B) :
    s2c_conormal (Spec.map q) ≅
      tilde ((ModuleCat.extendScalars q.hom).obj (ModuleCat.of S (RingHom.ker q.hom))) :=
  (Scheme.Modules.pullback (Spec.map q)).mapIso (affineIdealIso _ _ q) ≪≫
    (s2e_affine_pullback_tilde_iso _ _ q).app (ModuleCat.of S (RingHom.ker q.hom))

/-- The affine source presentation has the displayed composite as its map. -/
lemma unionConormalAffineComparisonSourceIso_hom
    {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (A B : CommRingCat.{0}) (p : CommRingCat.of R ⟶ A) (q : CommRingCat.of S ⟶ B)
    (k : A ⟶ B)
    (h : Spec.map k ≫ Spec.map p = Spec.map q ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S))) :
    (unionConormalAffineComparisonSourceIso A B p q k h).hom =
      ((unionConormalComparisonPrefixIso (Spec.map p) (Spec.map q)
          (Spec.map (CommRingCat.ofHom (algebraMap R S))) (Spec.map k) h).hom ≫
        (Scheme.Modules.pullback (Spec.map q)).map
          (unionConormalAffineIdealSourceIso (S := S) A p).hom) ≫
        (s2e_affine_pullback_tilde_iso _ _ q).hom.app
          ((ModuleCat.extendScalars (algebraMap R S)).obj
            (ModuleCat.of R (RingHom.ker p.hom))) := rfl

/-- The affine target presentation has the displayed composite as its map. -/
lemma unionConormalAffineComparisonTargetIso_hom (S B : CommRingCat.{0}) (q : S ⟶ B) :
    (unionConormalAffineComparisonTargetIso S B q).hom =
      (Scheme.Modules.pullback (Spec.map q)).map (affineIdealIso _ _ q).hom ≫
        (s2e_affine_pullback_tilde_iso _ _ q).hom.app (ModuleCat.of S (RingHom.ker q.hom)) := rfl

end HodgeLean.Foundations.Program.G32Native
