import HodgeLean.Adapters.CycleClassFlatComparisonCore
import Mathlib.RingTheory.Flat.IsBaseChange
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Smooth.Local
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.Data.Fintype.Lattice
import Mathlib.Topology.Sheaves.MayerVietoris
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import HodgeConjecture.Lemmas.AlgebraicTopology.Sheaf.OpenSheafification
import HodgeLean.Adapters.CycleClassSmoothChartsDefs
import HodgeConjecture.Lemmas.AlgebraicGeometry.ClosedImmersion.AnalyticLeftInverse

/-! # Smooth complex charts and finite component support obligations

The geometric inputs are algebraic smoothness and étaleness. The local section
is anchored at the specified complex point. HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxRecDepth 2048
set_option maxHeartbeats 200000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open CategoryTheory.Limits
open Filter Topology

open HodgeLean.RealDefs AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Adapters

attribute [local instance] overSpecAlgebra

private theorem ccm5_smooth_relative_etale_coordinates
    {X Z : Scheme} (f : X ⟶ Z) [Smooth f] (y : X) :
    ∃ (U : Z.Opens) (V : X.Opens) (_ : IsAffineOpen U) (_ : IsAffineOpen V)
      (hVU : V ≤ f ⁻¹ᵁ U), y ∈ V ∧
      ∃ (n : ℕ) (g : MvPolynomial (Fin n) Γ(Z, U) →+* Γ(X, V)),
        g.comp MvPolynomial.C = (f.appLE U V hVU).hom ∧ g.Etale := by
  obtain ⟨U, hU, V, hV, hy, hVU, hf⟩ := Smooth.exists_isStandardSmooth f y
  obtain ⟨n, g, hg, hEtale⟩ := hf.exists_etale_mvPolynomial
  exact ⟨U, V, hU, hV, hVU, hy, n, g, hg, hEtale⟩

attribute [-simp] Scheme.Opens.topIso_inv

private theorem ccm5_smooth_etale_local_section_construct
    (X Z : Over (Spec ↧ℂ)) (f : X ⟶ Z) (e : ℕ)
    [SmoothOfRelativeDimension e Z.hom] [Smooth f.left] (z : ComplexPoint X) :
    ∃ (W : Over (Spec ↧ℂ)) (s : W ⟶ X) (t : W ⟶ Z)
      (_ : SmoothOfRelativeDimension e W.hom) (w : ComplexPoint W),
      Etale t.left ∧ s ≫ f = t ∧ Point.map s w = z := by
  obtain ⟨U, V, hU, hV, hVU, hzV, n, g, hg, hEtale⟩ :=
    ccm5_smooth_relative_etale_coordinates f.left z.underlying
  letI : IsAffine U.toScheme := hU
  letI : IsAffine V.toScheme := hV
  letI : IsIso U.toSpecΓ := inferInstanceAs (IsIso hU.isoSpec.hom)
  letI : IsIso V.toSpecΓ := inferInstanceAs (IsIso hV.isoSpec.hom)
  let zV : ComplexPoint (ComplexPoint.openScheme X V) :=
    ComplexPoint.asOpenPoint X V z hzV
  have hzU : (Point.map f z).underlying ∈ U := hVU hzV
  let zU : ComplexPoint (ComplexPoint.openScheme Z U) :=
    ComplexPoint.asOpenPoint Z U (Point.map f z) hzU
  let A := MvPolynomial (Fin n) Γ(Z.left, U)
  let p : V.toScheme ⟶ Spec ↧A :=
    V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom g)
  let value (i : Fin n) : ℂ :=
    (Scheme.ΓSpecIso ↧ℂ).hom (zV.left.appTop (V.topIso.inv (g (.X i))))
  let constants : Fin n → Γ(Z.left, U) := fun i ↦
    U.topIso.hom ((ComplexPoint.openScheme Z U).hom.appTop
      ((Scheme.ΓSpecIso ↧ℂ).inv (value i)))
  let qRing : A →+* Γ(Z.left, U) :=
    MvPolynomial.eval₂Hom (RingHom.id _) constants
  let q : U.toScheme ⟶ Spec ↧A :=
    U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom qRing)
  let r : Spec ↧A ⟶ Spec ↧Γ(Z.left, U) :=
    Spec.map (CommRingCat.ofHom MvPolynomial.C)
  have hpbase : p ≫ r = f.left.resLE U V hVU ≫ U.toSpecΓ := by
    dsimp only [p, r]
    rw [Category.assoc, ← Spec.map_comp]
    rw [show CommRingCat.ofHom MvPolynomial.C ≫ CommRingCat.ofHom g =
      f.left.appLE U V hVU from CommRingCat.hom_ext hg]
    exact Scheme.Opens.toSpecΓ_SpecMap_appLE f.left U V hVU
  have hqbase : q ≫ r = U.toSpecΓ := by
    dsimp only [q, r]
    rw [Category.assoc, ← Spec.map_comp]
    rw [show CommRingCat.ofHom MvPolynomial.C ≫ CommRingCat.ofHom qRing = 𝟙 _ by
      ext a
      simp [qRing], Spec.map_id]
    exact Category.comp_id _
  let W0 : Scheme := pullback p q
  let W : Over (Spec ↧ℂ) := Over.mk (pullback.snd p q ≫ U.ι ≫ Z.hom)
  have hres : pullback.fst p q ≫ f.left.resLE U V hVU = pullback.snd p q := by
    have hh : (pullback.fst p q ≫ f.left.resLE U V hVU) ≫ U.toSpecΓ =
        pullback.snd p q ≫ U.toSpecΓ := by
      rw [Category.assoc]
      rw [← hpbase, ← hqbase]
      exact congrArg (fun k ↦ k ≫ r) (pullback.condition :
        pullback.fst p q ≫ p = pullback.snd p q ≫ q)
    exact (cancel_mono U.toSpecΓ).mp hh
  have hbase : (pullback.fst p q ≫ V.ι) ≫ f.left =
      pullback.snd p q ≫ U.ι := by
    calc
      (pullback.fst p q ≫ V.ι) ≫ f.left =
          pullback.fst p q ≫ (V.ι ≫ f.left) := Category.assoc _ _ _
      _ = pullback.fst p q ≫ (f.left.resLE U V hVU ≫ U.ι) := by
        rw [f.left.resLE_comp_ι]
      _ = (pullback.fst p q ≫ f.left.resLE U V hVU) ≫ U.ι :=
        (Category.assoc _ _ _).symm
      _ = pullback.snd p q ≫ U.ι := by rw [hres]
  let s : W ⟶ X := Over.homMk (pullback.fst p q ≫ V.ι) (by
    change (pullback.fst p q ≫ V.ι) ≫ X.hom =
      pullback.snd p q ≫ U.ι ≫ Z.hom
    rw [← f.w]
    simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ Z.hom) hbase)
  let t : W ⟶ Z := Over.homMk (pullback.snd p q ≫ U.ι) rfl
  have hp : Etale p := by
    letI : Etale (Spec.map (CommRingCat.ofHom g)) :=
      HasRingHomProperty.Spec_iff.mpr hEtale
    dsimp only [p]
    infer_instance
  letI : Etale (pullback.snd p q) := inferInstance
  have ht : Etale t.left := by
    change Etale (pullback.snd p q ≫ U.ι)
    infer_instance
  have hW : SmoothOfRelativeDimension e W.hom := by
    change SmoothOfRelativeDimension e ((pullback.snd p q ≫ U.ι) ≫ Z.hom)
    haveI : SmoothOfRelativeDimension 0 (pullback.snd p q ≫ U.ι) := inferInstance
    simpa using (inferInstance :
      SmoothOfRelativeDimension (0 + e) ((pullback.snd p q ≫ U.ι) ≫ Z.hom))
  have hzres : zV.left ≫ f.left.resLE U V hVU = zU.left := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, f.left.resLE_comp_ι]
    simp [zV, zU, ComplexPoint.asOpenPoint, Point.map]
  have hpzqz : zV.left ≫ p = zU.left ≫ q := by
    apply (ΓSpec.adjunction.homEquiv (Spec ↧ℂ)
      (Opposite.op (CommRingCat.of A))).symm.injective
    apply Quiver.Hom.unop_inj
    change (Scheme.ΓSpecIso ↧A).inv ≫ (zV.left ≫ p).appTop =
      (Scheme.ΓSpecIso ↧A).inv ≫ (zU.left ≫ q).appTop
    simp only [Scheme.Hom.comp_appTop]
    simp only [p, q, Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    simp
    ext i
    · have hzapp := congrArg Scheme.Hom.appTop hzres
      rw [Scheme.Hom.comp_appTop] at hzapp
      have hconvert :
          (f.left.resLE U V hVU).appTop.hom (U.topIso.inv.hom i) =
          V.topIso.inv.hom ((f.left.appLE U V hVU).hom i) := by
        have hsquare := (arrowResLEAppIso f.left U V hVU).hom.w
        have hi := congrArg (fun k : Γ(U.toScheme, ⊤) ⟶ Γ(X.left, V) ↦
          k.hom (U.topIso.inv.hom i)) hsquare
        dsimp [arrowResLEAppIso] at hi
        have hi0 : (f.left.appLE U V hVU).hom i =
            V.topIso.hom.hom ((f.left.resLE U V hVU).appTop.hom
              (U.topIso.inv.hom i)) := by
          simpa only [Arrow.isoMk_hom_left, Arrow.isoMk_hom_right,
            CommRingCat.comp_apply, Iso.inv_hom_id_apply] using hi
        rw [hi0]
        exact (ConcreteCategory.congr_hom V.topIso.hom_inv_id _).symm
      have hi := congrArg (fun k : Γ(U.toScheme, ⊤) ⟶ Γ(Spec ↧ℂ, ⊤) ↦
        k.hom (U.topIso.inv i)) hzapp
      rw [RingHom.comp_apply, RingHom.comp_apply,
        ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
        ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
      rw [show (CommRingCat.ofHom g).hom (MvPolynomial.C i) =
        (f.left.appLE U V hVU).hom i from DFunLike.congr_fun hg i]
      rw [show (CommRingCat.ofHom qRing).hom (MvPolynomial.C i) = i by
        change (MvPolynomial.eval₂Hom (RingHom.id _) constants) (MvPolynomial.C i) = i
        exact (MvPolynomial.eval₂Hom_C _ _ i).trans (RingHom.id_apply i)]
      rw [← hconvert]
      exact hi
    · have hw := congrArg Scheme.Hom.appTop (Over.w zU)
      rw [Scheme.Hom.comp_appTop] at hw
      have hi := congrArg (fun k : Γ(Spec ↧ℂ, ⊤) ⟶ Γ(Spec ↧ℂ, ⊤) ↦
        k.hom ((Scheme.ΓSpecIso ↧ℂ).inv (value i))) hw
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
        ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
      rw [show (CommRingCat.ofHom qRing).hom (MvPolynomial.X i) = constants i by
        change (MvPolynomial.eval₂Hom (RingHom.id _) constants) (MvPolynomial.X i) = constants i
        exact MvPolynomial.eval₂_X (RingHom.id Γ(Z.left, U)) constants i]
      rw [show U.topIso.inv.hom (constants i) =
          (ComplexPoint.openScheme Z U).hom.appTop.hom
            ((Scheme.ΓSpecIso ↧ℂ).inv.hom (value i)) by
        change U.topIso.inv.hom (U.topIso.hom.hom _) = _
        exact ConcreteCategory.congr_hom U.topIso.hom_inv_id _]
      have hleft :
          (Over.mk (𝟙 (Spec ↧ℂ))).hom.appTop.hom
              ((Scheme.ΓSpecIso ↧ℂ).inv.hom (value i)) =
            zV.left.appTop.hom (V.topIso.inv.hom (g (MvPolynomial.X i))) := by
        change (Scheme.Hom.appTop (𝟙 (Spec ↧ℂ))).hom
            ((Scheme.ΓSpecIso ↧ℂ).inv.hom (value i)) = _
        rw [Scheme.Hom.id_appTop, CommRingCat.id_apply]
        exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso ↧ℂ).hom_inv_id _).trans (by rfl)
      exact hleft.symm.trans hi.symm
  let w0 : Spec ↧ℂ ⟶ W0 := pullback.lift zV.left zU.left hpzqz
  let w : ComplexPoint W := Over.homMk w0 (by
    change w0 ≫ (pullback.snd p q ≫ U.ι ≫ Z.hom) = 𝟙 _
    change (w0 ≫ pullback.snd p q) ≫ U.ι ≫ Z.hom = _
    rw [show w0 ≫ pullback.snd p q = zU.left from pullback.lift_snd _ _ _]
    exact Over.w zU)
  refine ⟨W, s, t, hW, w, ht, ?_, ?_⟩
  · apply Over.OverMorphism.ext
    change (pullback.fst p q ≫ V.ι) ≫ f.left = pullback.snd p q ≫ U.ι
    exact hbase
  · apply Over.OverMorphism.ext
    change w0 ≫ (pullback.fst p q ≫ V.ι) = z.left
    rw [← Category.assoc, show w0 ≫ pullback.fst p q = zV.left from pullback.lift_fst _ _ _]
    exact ComplexPoint.liftToOpen_fac X V z hzV

attribute [simp] Scheme.Opens.topIso_inv

private theorem ccm5_smooth_absolute_dimension_eq
    (X : Over (Spec ↧ℂ)) (d e : ℕ)
    [SmoothOfRelativeDimension d X.hom]
    [SmoothOfRelativeDimension e X.hom] (z : ComplexPoint X) : d = e := by
  letI : Smooth X.hom := SmoothOfRelativeDimension.smooth (n := d) X.hom
  have hzclosed : IsClosed {z.underlying} :=
    ((pointEquivClosedPoint X.hom) ⟨z.left, Over.w z⟩).2
  have hdim : ∀ n : ℕ, SmoothOfRelativeDimension n X.hom →
      (n : ℕ∞) = Order.coheight z.underlying := by
    intro n hn
    letI : SmoothOfRelativeDimension n X.hom := hn
    obtain ⟨U, hU, hzU, hsmooth⟩ :=
      SmoothOfRelativeDimension.exists_affine_isStandardSmoothOfRelativeDimension
        (d := n) X.hom z.underlying
    let zu : U.toScheme := ⟨z.underlying, hzU⟩
    let P : Ideal Γ(X.left, U) := (hU.primeIdealOf zu).asIdeal
    letI : P.IsMaximal := hU.primeIdealOf_isMaximal_of_isClosed zu hzclosed
    have hP : P.height = n :=
      (algebraMap_isStandardSmoothOfRelativeDimension
        (d := n) X hsmooth).height_eq_of_isMaximal P
    calc
      (n : ℕ∞) = P.height := by exact_mod_cast hP.symm
      _ = Order.coheight zu := hU.primeIdealOf_height_eq_coheight zu
      _ = Order.coheight z.underlying :=
        (coheight_eq_of_isOpenImmersion (x := zu) U.ι).symm
  exact_mod_cast (hdim d inferInstance).trans (hdim e inferInstance).symm

private theorem ccm5_etale_pullback_coordinates
    (X Z : Over (Spec ↧ℂ)) (f : X ⟶ Z) (e : ℕ)
    [SmoothOfRelativeDimension e X.hom]
    [SmoothOfRelativeDimension e Z.hom] [Etale f.left]
    (z : ComplexPoint X) :
    ∃ (D : LocalEtaleCoordinates X e z.underlying)
      (hV : D.neighborhood ≤ f.left ⁻¹ᵁ
        (localEtaleCoordinates Z e (Point.map f z).underlying).neighborhood),
      D.coordinateAlgHom.toRingHom =
        (f.left.appLE _ _ hV).hom.comp
          (localEtaleCoordinates Z e (Point.map f z).underlying).coordinateAlgHom.toRingHom := by
  let E := localEtaleCoordinates Z e (Point.map f z).underlying
  have hzpre : z.underlying ∈ f.left ⁻¹ᵁ E.neighborhood := by
    change (Point.map f z).underlying ∈ E.neighborhood
    exact E.mem
  obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hVU : V ≤ _⟩ :=
    X.left.isBasis_affineOpens.exists_subset_of_mem_open hzpre
      (f.left ⁻¹ᵁ E.neighborhood).isOpen
  let g : MvPolynomial (Fin e) ℂ →+* Γ(X.left, V) :=
    (f.left.appLE E.neighborhood V hVU).hom.comp E.coordinateAlgHom.toRingHom
  have hgC : g.comp MvPolynomial.C = algebraMap ℂ Γ(X.left, V) := by
    have hmaps :
        Z.hom.appLE ⊤ E.neighborhood (by simp) ≫
            f.left.appLE E.neighborhood V hVU =
          X.hom.appLE ⊤ V (by simp) := by
      rw [Scheme.Hom.appLE_comp_appLE]
      rw [f.w]
    ext c
    simp only [g, RingHom.comp_apply]
    have hEc : E.coordinateAlgHom.toRingHom (MvPolynomial.C c) =
        algebraMap ℂ Γ(Z.left, E.neighborhood) c := by
      change E.coordinateAlgHom (algebraMap ℂ (MvPolynomial (Fin e) ℂ) c) = _
      exact E.coordinateAlgHom.commutes c
    rw [hEc]
    simp only [overSpecAlgebra, RingHom.algebraMap_toAlgebra, RingHom.comp_apply]
    have hc := congrArg (fun k ↦ k.hom ((Scheme.ΓSpecIso ↧ℂ).inv.hom c)) hmaps
    simpa only [CommRingCat.comp_apply] using hc
  let g' : MvPolynomial (Fin e) ℂ →ₐ[ℂ] Γ(X.left, V) :=
    { toRingHom := g
      commutes' := fun c ↦ DFunLike.congr_fun hgC c }
  have hgetale : g'.toRingHom.Etale := by
    exact RingHom.Etale.stableUnderComposition _ _
      E.etale (f.left.etale_appLE E.isAffine hV hVU)
  let D : LocalEtaleCoordinates X e z.underlying := ⟨V, hV, hzV, g', hgetale⟩
  exact ⟨D, hVU, rfl⟩

private theorem ccm5_pullback_coordinateRingHomOnOpen
    (X Z : Over (Spec ↧ℂ)) (f : X ⟶ Z) (e : ℕ)
    [SmoothOfRelativeDimension e X.hom]
    [SmoothOfRelativeDimension e Z.hom]
    (z : ComplexPoint X)
    (D : LocalEtaleCoordinates X e z.underlying)
    (hV : D.neighborhood ≤ f.left ⁻¹ᵁ
      (localEtaleCoordinates Z e (Point.map f z).underlying).neighborhood)
    (hcoord : D.coordinateAlgHom.toRingHom =
      (f.left.appLE _ _ hV).hom.comp
        (localEtaleCoordinates Z e (Point.map f z).underlying).coordinateAlgHom.toRingHom) :
    D.coordinateRingHomOnOpen =
      (f.left.resLE _ _ hV).appTop.hom.comp
        (localEtaleCoordinates Z e
          (Point.map f z).underlying).coordinateRingHomOnOpen := by
  let E := localEtaleCoordinates Z e (Point.map f z).underlying
  have hconvert (s : Γ(Z.left, E.neighborhood)) :
      (f.left.resLE E.neighborhood D.neighborhood hV).appTop.hom
          (E.neighborhood.topIso.inv.hom s) =
        D.neighborhood.topIso.inv.hom
          ((f.left.appLE E.neighborhood D.neighborhood hV).hom s) := by
    have hsquare :=
      (arrowResLEAppIso f.left E.neighborhood D.neighborhood hV).hom.w
    have hr := congrArg
      (fun k : Γ(E.neighborhood.toScheme, ⊤) ⟶ Γ(X.left, D.neighborhood) ↦
        k.hom (E.neighborhood.topIso.inv.hom s)) hsquare
    dsimp [arrowResLEAppIso] at hr
    have hr0 : (f.left.appLE E.neighborhood D.neighborhood hV).hom s =
        D.neighborhood.topIso.hom.hom
          ((f.left.resLE E.neighborhood D.neighborhood hV).appTop.hom
            (E.neighborhood.topIso.inv.hom s)) := by
      simpa only [Arrow.isoMk_hom_left, Arrow.isoMk_hom_right,
        CommRingCat.comp_apply, Iso.inv_hom_id_apply] using hr
    rw [hr0]
    exact (ConcreteCategory.congr_hom D.neighborhood.topIso.hom_inv_id _).symm
  apply DFunLike.ext _ _
  intro r
  simp only [LocalEtaleCoordinates.coordinateRingHomOnOpen, RingHom.comp_apply]
  rw [DFunLike.congr_fun hcoord r]
  exact (hconvert _).symm

private theorem ccm5_pullback_coordinates_apply
    (X Z : Over (Spec ↧ℂ)) (f : X ⟶ Z) (e : ℕ)
    [SmoothOfRelativeDimension e X.hom]
    [SmoothOfRelativeDimension e Z.hom]
    (z x : ComplexPoint X)
    (D : LocalEtaleCoordinates X e z.underlying)
    (hV : D.neighborhood ≤ f.left ⁻¹ᵁ
      (localEtaleCoordinates Z e (Point.map f z).underlying).neighborhood)
    (hcoord : D.coordinateAlgHom.toRingHom =
      (f.left.appLE _ _ hV).hom.comp
        (localEtaleCoordinates Z e (Point.map f z).underlying).coordinateAlgHom.toRingHom)
    (hx : x.underlying ∈ D.neighborhood) :
    D.analyticCoordinates (ComplexPoint.asOpenPoint X D.neighborhood x hx) =
      (localEtaleCoordinates Z e (Point.map f z).underlying).analyticCoordinates
        (ComplexPoint.asOpenPoint Z _ (Point.map f x) (hV hx)) := by
  let E := localEtaleCoordinates Z e (Point.map f z).underlying
  let xD := ComplexPoint.asOpenPoint X D.neighborhood x hx
  let xE := ComplexPoint.asOpenPoint Z E.neighborhood (Point.map f x) (hV hx)
  have hbase : (f.left.resLE E.neighborhood D.neighborhood hV ≫ E.neighborhood.ι) ≫
      Z.hom = D.neighborhood.ι ≫ X.hom := by
    rw [f.left.resLE_comp_ι, Category.assoc, f.w]
  let fr : ComplexPoint.openScheme X D.neighborhood ⟶
      ComplexPoint.openScheme Z E.neighborhood :=
    Over.homMk (f.left.resLE E.neighborhood D.neighborhood hV) hbase
  have hpoint : Point.map fr xD = xE := by
    apply Over.OverMorphism.ext
    apply (cancel_mono E.neighborhood.ι).mp
    change (xD.left ≫ f.left.resLE E.neighborhood D.neighborhood hV) ≫
      E.neighborhood.ι = xE.left ≫ E.neighborhood.ι
    rw [Category.assoc, f.left.resLE_comp_ι]
    simp [xD, xE, ComplexPoint.asOpenPoint, Point.map]
  have hring := ccm5_pullback_coordinateRingHomOnOpen X Z f e z D hV hcoord
  funext i
  rw [D.analyticCoordinates_apply_eq_evaluate,
    E.analyticCoordinates_apply_eq_evaluate]
  change Point.evaluate ⊤ (D.coordinateRingHomOnOpen (MvPolynomial.X i)) xD =
    Point.evaluate ⊤ (E.coordinateRingHomOnOpen (MvPolynomial.X i)) xE
  rw [← hpoint, Point.evaluate_map]
  exact congrArg (fun r ↦ Point.evaluate ⊤ r xD)
    (DFunLike.congr_fun hring (MvPolynomial.X i))

/-- Étale maps have invertible derivatives in the existing complex charts.
Source: complex inverse function theorem applied to an étale presentation;
`AlgebraicGeometry.LocalEtaleCoordinates`. -/
theorem ccm5_etale_chart_derivative_bijective_aux
    (X Z : Over (Spec ↧ℂ)) (f : X ⟶ Z) (d e : ℕ)
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension e Z.hom]
    [Etale f.left] (z : ComplexPoint X) :
    Function.Bijective (fderiv ℂ (inclusionInComplexCharts Z X f d e z)
      (localChart X d z z)) := by
  have hXe : SmoothOfRelativeDimension e X.hom := by
    rw [← f.w]
    simpa using (inferInstance :
      SmoothOfRelativeDimension (0 + e) (f.left ≫ Z.hom))
  letI : SmoothOfRelativeDimension e X.hom := hXe
  have hde : d = e := ccm5_smooth_absolute_dimension_eq X d e z
  subst d
  obtain ⟨D, hV, hcoord⟩ := ccm5_etale_pullback_coordinates X Z f e z
  let p : {x : ComplexPoint X // x ∈ Point.overOpen D.neighborhood} :=
    ⟨z, D.mem⟩
  let C := D.ambientProjectionChart p
  let A := localEtaleCoordinates X e z.underlying
  let a := localChart X e z z
  let b := localChart Z e (Point.map f z) (Point.map f z)
  have hpC : p ∈ C.source := D.mem_ambientProjectionChart_source p
  have hCp : C.symm (C p) = p := C.left_inv hpC
  have hcenter : C p = b := by
    rw [D.ambientProjectionChart_apply_of_mem p p hpC]
    change D.analyticCoordinates
        (ComplexPoint.asOpenPoint X D.neighborhood z D.mem) = b
    rw [ccm5_pullback_coordinates_apply X Z f e z z D hV hcoord D.mem]
    convert (localChart_apply_of_mem Z e (Point.map f z) (Point.map f z)
      (mem_localChart_source Z e (Point.map f z))).symm using 1 <;> rfl
  let L : (Fin e → ℂ) → (Fin e → ℂ) := fun v i ↦
    Point.evaluate A.ambientCoordinateOpen (A.ambientCoordinateSection i) (C.symm v).1
  have hL : AnalyticAt ℂ L b := by
    rw [← hcenter]
    exact AnalyticAt.pi fun i ↦
      D.analyticAt_ambientProjectionChart_symm_evaluate p (C.map_source hpC)
        A.ambientCoordinateOpen (A.ambientCoordinateSection i) (by
          rw [hCp]
          change z.underlying ∈ A.ambientCoordinateOpen
          simpa only [LocalEtaleCoordinates.ambientCoordinateOpen,
            Scheme.Opens.ι_image_top, Set.mem_ofPred_eq] using A.mem)
  have hleft :
      (L ∘ inclusionInComplexCharts Z X f e e z) =ᶠ[𝓝 a] id := by
    have hcontX : ContinuousAt (localChart X e z).symm a :=
      (localChart X e z).continuousAt_symm
        ((localChart X e z).map_source (mem_localChart_source X e z))
    let S : Set (ComplexPoint X) := Subtype.val '' C.source
    have hSopen : IsOpen S :=
      (Point.isOpen_overOpen D.neighborhood).isOpenEmbedding_subtypeVal.isOpenMap
        C.source C.open_source
    have haS : (localChart X e z).symm a ∈ S := by
      rw [(localChart X e z).left_inv (mem_localChart_source X e z)]
      exact ⟨p, hpC, rfl⟩
    have heS := hcontX (hSopen.mem_nhds haS)
    have heTarget := (localChart X e z).open_target.mem_nhds
      ((localChart X e z).map_source (mem_localChart_source X e z))
    have hcontMap : ContinuousAt
        (fun v => Point.map f ((localChart X e z).symm v)) a :=
      (Point.continuous_map f).continuousAt.comp hcontX
    have hmapCenter : Point.map f ((localChart X e z).symm a) ∈
        (localChart Z e (Point.map f z)).source := by
      rw [(localChart X e z).left_inv (mem_localChart_source X e z)]
      exact mem_localChart_source Z e (Point.map f z)
    have heMap := hcontMap
      ((localChart Z e (Point.map f z)).open_source.mem_nhds hmapCenter)
    filter_upwards [heS, heTarget, heMap] with v hvS hvTarget hvMap
    rcases hvS with ⟨xD, hxDC, hxD⟩
    have hxSource := (localChart X e z).map_target hvTarget
    have hxNeighborhood : (localChart X e z).symm v ∈
        Point.overOpen D.neighborhood := by
      rw [← hxD]
      exact xD.property
    have hxDsub : xD =
        ⟨(localChart X e z).symm v, hxNeighborhood⟩ :=
      Subtype.ext hxD
    have hchart : inclusionInComplexCharts Z X f e e z v = C xD := by
      dsimp only [inclusionInComplexCharts]
      rw [localChart_apply_of_mem Z e (Point.map f z)
        (Point.map f ((localChart X e z).symm v)) hvMap,
        D.ambientProjectionChart_apply_of_mem p xD hxDC]
      rw [hxDsub]
      exact (ccm5_pullback_coordinates_apply X Z f e z
        ((localChart X e z).symm v) D hV hcoord hxNeighborhood).symm
    apply funext
    intro i
    change Point.evaluate A.ambientCoordinateOpen
        (A.ambientCoordinateSection i)
        (C.symm (inclusionInComplexCharts Z X f e e z v)).1 = v i
    rw [hchart, C.left_inv hxDC]
    rw [hxD]
    calc
      Point.evaluate A.ambientCoordinateOpen (A.ambientCoordinateSection i)
          ((localChart X e z).symm v) =
          localChart X e z ((localChart X e z).symm v) i :=
        (localChart_apply_component_eq_evaluate X e z
          ((localChart X e z).symm v) hxSource i).symm
      _ = v i := congrFun ((localChart X e z).right_inv hvTarget) i
  have hφ := analyticAt_inclusionInComplexCharts Z X f e e z
  have hφcenter : inclusionInComplexCharts Z X f e e z a = b := by
    exact inclusionInComplexCharts_at_center Z X f e e z
  have hL' : AnalyticAt ℂ L
      (inclusionInComplexCharts Z X f e e z a) := by
    rw [hφcenter]
    exact hL
  have hc := hL'.differentiableAt.hasFDerivAt.comp a hφ.differentiableAt.hasFDerivAt
  have hinv :
      (fderiv ℂ L b).comp
          (fderiv ℂ (inclusionInComplexCharts Z X f e e z) a) =
        ContinuousLinearMap.id ℂ (Fin e → ℂ) :=
    by
      rw [← hφcenter]
      exact (hc.congr_of_eventuallyEq hleft.symm).unique (hasFDerivAt_id a)
  have hleftlin : Function.LeftInverse (fderiv ℂ L b)
      (fderiv ℂ (inclusionInComplexCharts Z X f e e z) a) := fun v ↦ by
    change ((fderiv ℂ L b).comp
      (fderiv ℂ (inclusionInComplexCharts Z X f e e z) a)) v = v
    rw [hinv]
    rfl
  have hinj := hleftlin.injective
  have hsurj : Function.Surjective
      (fderiv ℂ (inclusionInComplexCharts Z X f e e z) a) :=
    LinearMap.surjective_of_injective hinj
  exact ⟨hinj, hsurj⟩

/-- A smooth morphism has an étale-local section through each given complex point.
Source: Stacks Project, Lemma 37.38.5 (Slicing smooth morphisms),
https://stacks.math.columbia.edu/tag/055S. -/
theorem ccm5_smooth_etale_local_section_aux
    (X Z : Over (Spec ↧ℂ)) (f : X ⟶ Z) (e : ℕ)
    [SmoothOfRelativeDimension e Z.hom] [Smooth f.left] (z : ComplexPoint X) :
    ∃ (W : Over (Spec ↧ℂ)) (s : W ⟶ X) (t : W ⟶ Z)
      (_ : SmoothOfRelativeDimension e W.hom) (w : ComplexPoint W),
      Etale t.left ∧ s ≫ f = t ∧ Point.map s w = z := by
  exact ccm5_smooth_etale_local_section_construct X Z f e z

private theorem ccm5_chart_composition_eventually
    (X Y Z : Over (Spec ↧ℂ)) (f : X ⟶ Y) (g : Y ⟶ Z)
    (d e k : ℕ) [SmoothOfRelativeDimension d X.hom]
    [SmoothOfRelativeDimension e Y.hom] [SmoothOfRelativeDimension k Z.hom]
    (z : ComplexPoint X) :
    (inclusionInComplexCharts Z Y g e k (Point.map f z) ∘
      inclusionInComplexCharts Y X f d e z) =ᶠ[𝓝 (localChart X d z z)]
        inclusionInComplexCharts Z X (f ≫ g) d k z := by
  let a := localChart X d z z
  have hcont : ContinuousAt
      (fun v => Point.map f ((localChart X d z).symm v)) a :=
    (Point.continuous_map f).continuousAt.comp
      ((localChart X d z).continuousAt_symm
        ((localChart X d z).map_source (mem_localChart_source X d z)))
  have hm : Point.map f ((localChart X d z).symm a) ∈
      (localChart Y e (Point.map f z)).source := by
    rw [(localChart X d z).left_inv (mem_localChart_source X d z)]
    exact mem_localChart_source Y e (Point.map f z)
  have he := hcont ((localChart Y e (Point.map f z)).open_source.mem_nhds hm)
  filter_upwards [he] with v hv
  dsimp only [Function.comp_def, inclusionInComplexCharts]
  rw [(localChart Y e (Point.map f z)).left_inv hv]
  simp only [Point.map_comp_apply]

/-- Chain rule in the existing absolute charts.
Source: `HasFDerivAt.comp` and the chart inverse identities. -/
theorem ccm5_chart_derivative_comp_aux
    (X Y Z : Over (Spec ↧ℂ)) (f : X ⟶ Y) (g : Y ⟶ Z)
    (d e k : ℕ) [SmoothOfRelativeDimension d X.hom]
    [SmoothOfRelativeDimension e Y.hom] [SmoothOfRelativeDimension k Z.hom]
    (z : ComplexPoint X) :
    (fderiv ℂ (inclusionInComplexCharts Z Y g e k (Point.map f z))
      (localChart Y e (Point.map f z) (Point.map f z))).comp
      (fderiv ℂ (inclusionInComplexCharts Y X f d e z) (localChart X d z z)) =
    fderiv ℂ (inclusionInComplexCharts Z X (f ≫ g) d k z) (localChart X d z z) := by
  have hf := (analyticAt_inclusionInComplexCharts Y X f d e z).differentiableAt.hasFDerivAt
  have hg := (analyticAt_inclusionInComplexCharts Z Y g e k (Point.map f z)).differentiableAt.hasFDerivAt
  rw [← inclusionInComplexCharts_at_center Y X f d e z] at hg
  simpa only [inclusionInComplexCharts_at_center] using ((hg.comp _ hf).congr_of_eventuallyEq
    (ccm5_chart_composition_eventually X Y Z f g d e k z).symm).fderiv.symm

/-- Algebraic smoothness implies surjectivity of the analytic chart derivative.
Source: the étale-local section, the étale inverse function theorem, and the chain rule. -/
theorem ccm5_smooth_chart_derivative_surjective_aux
    (X Z : Over (Spec ↧ℂ)) (f : X ⟶ Z) (d e : ℕ)
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension e Z.hom]
    [Smooth f.left] (z : ComplexPoint X) :
    Function.Surjective (fderiv ℂ (inclusionInComplexCharts Z X f d e z)
      (localChart X d z z)) := by
  obtain ⟨W, s, t, hW, w, ht, hst, hw⟩ :=
    ccm5_smooth_etale_local_section_aux X Z f e z
  let := hW
  let := ht
  have hcomp := ccm5_chart_derivative_comp_aux W X Z s f e d e w
  rw [hst, hw] at hcomp
  intro v
  obtain ⟨u, hu⟩ := (ccm5_etale_chart_derivative_bijective_aux W Z t e e w).2 v
  refine ⟨(fderiv ℂ (inclusionInComplexCharts X W s e d w)
    (localChart W e w w)) u, ?_⟩
  exact (DFunLike.congr_fun hcomp u).trans hu

private lemma ccm5_isPushout_biprod_cokernel_square
    {C : Type*} [Category C] [Preadditive C] [Limits.HasBinaryBiproducts C]
    {A B D E : C} {u : A ⟶ B} {v : A ⟶ D} {p : B ⟶ E} {q : D ⟶ E}
    (h : IsPushout u v p q) :
    IsPushout (biprod.lift u v) (u ≫ p)
      (biprod.map p q) (biprod.lift (𝟙 E) (𝟙 E)) := by
  apply IsPushout.mk'
  · ext <;> simp [h.w]
  · intro T a b ha hb
    have hlift (X Y Z : C) (f : X ⟶ Y) (g : X ⟶ Z) :
        biprod.lift f g = f ≫ biprod.inl + g ≫ biprod.inr := by
      ext <;> simp
    have hp₁ : p ≫ biprod.inl ≫ a = p ≫ biprod.inl ≫ b := by
      simpa [Category.assoc] using congrArg (fun z => biprod.inl ≫ z) ha
    have hq₂ : q ≫ biprod.inr ≫ a = q ≫ biprod.inr ≫ b := by
      simpa [Category.assoc] using congrArg (fun z => biprod.inr ≫ z) ha
    have hs : biprod.inl ≫ a + biprod.inr ≫ a =
        biprod.inl ≫ b + biprod.inr ≫ b := by
      rw [hlift E E E (𝟙 E) (𝟙 E)] at hb
      simpa only [Preadditive.add_comp, Category.id_comp] using hb
    have hq₁ : q ≫ biprod.inl ≫ a = q ≫ biprod.inl ≫ b := by
      rw [← Category.assoc, ← Category.assoc]
      have ht := congrArg (fun z => q ≫ z) hs
      simp only [Preadditive.comp_add, Category.assoc] at ht
      rw [hq₂] at ht
      simpa only [Category.assoc] using add_right_cancel ht
    have hp₂ : p ≫ biprod.inr ≫ a = p ≫ biprod.inr ≫ b := by
      rw [← Category.assoc, ← Category.assoc]
      have ht := congrArg (fun z => p ≫ z) hs
      simp only [Preadditive.comp_add, Category.assoc] at ht
      rw [hp₁] at ht
      simpa only [Category.assoc] using add_left_cancel ht
    apply biprod.hom_ext'
    · exact h.hom_ext hp₁ hq₁
    · exact h.hom_ext hp₂ hq₂
  · intro T a b hab
    have hlift (X Y Z : C) (f : X ⟶ Y) (g : X ⟶ Z) :
        biprod.lift f g = f ≫ biprod.inl + g ≫ biprod.inr := by
      ext <;> simp
    rw [hlift, Preadditive.add_comp] at hab
    let z₁ := h.desc (biprod.inl ≫ a) (q ≫ b - biprod.inr ≫ a) (by
      simp only [Category.assoc, Preadditive.comp_sub]
      have ht := hab
      simp only [Category.assoc] at ht
      rw [← h.w_assoc, eq_sub_iff_add_eq]
      exact ht)
    let z₂ := h.desc (p ≫ b - biprod.inl ≫ a) (biprod.inr ≫ a) (by
      simp only [Category.assoc, Preadditive.comp_sub]
      have ht := hab
      simp only [Category.assoc] at ht
      rw [sub_eq_iff_eq_add]
      simpa only [add_comm] using ht.symm)
    refine ⟨biprod.desc z₁ z₂, ?_, ?_⟩
    · apply biprod.hom_ext' <;> simp [z₁, z₂]
    · apply h.hom_ext <;> simp [z₁, z₂, Category.assoc]

private lemma ccm5_isPushout_freeAbelianSheaf_compl
    (T : TopCat.{0}) (A B : TopologicalSpace.Closeds T) (hAB : Disjoint A B) :
    IsPushout
      ((CategoryTheory.Sheaf.freeAbelianSheaf (Opens.grothendieckTopology T)).map
        (homOfLE (show (A ⊔ B).compl ≤ A.compl from
          fun _ hx hA => hx (Or.inl hA))))
      ((CategoryTheory.Sheaf.freeAbelianSheaf (Opens.grothendieckTopology T)).map
        (homOfLE (show (A ⊔ B).compl ≤ B.compl from
          fun _ hx hB => hx (Or.inr hB))))
      ((CategoryTheory.Sheaf.freeAbelianSheaf (Opens.grothendieckTopology T)).map
        (homOfLE (show A.compl ≤ ⊤ from le_top)))
      ((CategoryTheory.Sheaf.freeAbelianSheaf (Opens.grothendieckTopology T)).map
        (homOfLE (show B.compl ≤ ⊤ from le_top))) := by
  let sq : Square (Opens T) := Square.mk
    (homOfLE (show (A ⊔ B).compl ≤ A.compl from
      fun _ hx hA => hx (Or.inl hA)))
    (homOfLE (show (A ⊔ B).compl ≤ B.compl from
      fun _ hx hB => hx (Or.inr hB)))
    (homOfLE (show A.compl ≤ ⊤ from le_top))
    (homOfLE (show B.compl ≤ ⊤ from le_top)) (Subsingleton.elim _ _)
  have hp : sq.IsPullback := by
    refine Square.IsPullback.mk sq (PullbackCone.IsLimit.mk sq.fac
      (fun s => homOfLE (fun x hx hab => hab.elim (s.fst.le hx) (s.snd.le hx)))
      (fun s => Subsingleton.elim _ _) (fun s => Subsingleton.elim _ _)
      (fun s m hm₁ hm₂ => Subsingleton.elim _ _))
  have hc : Sieve.ofTwoArrows sq.f₂₄ sq.f₃₄ ∈
      Opens.grothendieckTopology T sq.X₄ := by
    rw [Opens.mem_grothendieckTopology]
    intro x hx
    by_cases ha : x ∈ A.compl
    · refine ⟨A.compl, sq.f₂₄, ?_, ha⟩
      exact Sieve.ofArrows_mk _ _ WalkingPair.left
    · have hxA : x ∈ A := Classical.byContradiction ha
      have hb : x ∈ B.compl := fun hxB => False.elim (hAB.le_bot ⟨hxA, hxB⟩)
      refine ⟨B.compl, sq.f₃₄, ?_, hb⟩
      exact Sieve.ofArrows_mk _ _ WalkingPair.right
  exact GrothendieckTopology.MayerVietorisSquare.isPushoutAddCommGrpFreeSheaf
    (GrothendieckTopology.MayerVietorisSquare.mk_of_isPullback sq hp hc)

private lemma ccm5_isIso_cokernel_biprod_map
    {C : Type*} [Category C] [Preadditive C] [Limits.HasBinaryBiproducts C]
    {A B D E : C} (p : A ⟶ B) (q : D ⟶ E)
    [HasCokernel p] [HasCokernel q] [HasCokernel (biprod.map p q)] :
    IsIso (cokernel.desc (biprod.map p q)
      (biprod.map (cokernel.π p) (cokernel.π q)) (by ext <;> simp)) := by
  let d := cokernel.desc (biprod.map p q)
    (biprod.map (cokernel.π p) (cokernel.π q)) (by ext <;> simp)
  let e₁ := cokernel.desc p (biprod.inl ≫ cokernel.π (biprod.map p q)) (by
    rw [← Category.assoc, ← biprod.inl_map, Category.assoc, cokernel.condition, comp_zero])
  let e₂ := cokernel.desc q (biprod.inr ≫ cokernel.π (biprod.map p q)) (by
    rw [← Category.assoc, ← biprod.inr_map, Category.assoc, cokernel.condition, comp_zero])
  refine ⟨⟨biprod.desc e₁ e₂, ?_, ?_⟩⟩
  · apply (cancel_epi (cokernel.π (biprod.map p q))).1
    apply biprod.hom_ext' <;> simp [d, e₁, e₂]
  · apply biprod.hom_ext' <;> apply (cancel_epi (cokernel.π _)).1 <;>
      simp [d, e₁, e₂]

private lemma ccm5_isIso_cokernel_split
    {C : Type*} [Category C] [Abelian C]
    {A B D E : C} {u : A ⟶ B} {v : A ⟶ D} {p : B ⟶ E} {q : D ⟶ E}
    (h : IsPushout u v p q) :
    IsIso (biprod.lift
      (cokernel.map (u ≫ p) p u (𝟙 E) (by simp))
      (cokernel.map (u ≫ p) q v (𝟙 E) (by simpa using h.w))) := by
  let sq := (ccm5_isPushout_biprod_cokernel_square h).flip
  let d := cokernel.desc (biprod.map p q)
    (biprod.map (cokernel.π p) (cokernel.π q)) (by ext <;> simp)
  haveI : IsIso d := ccm5_isIso_cokernel_biprod_map p q
  haveI := isIso_cokernel_map_of_isPushout sq
  have he : biprod.lift
      (cokernel.map (u ≫ p) p u (𝟙 E) (by simp))
      (cokernel.map (u ≫ p) q v (𝟙 E) (by simpa using h.w)) =
      cokernel.map _ _ _ _ sq.w ≫ d := by
    apply (cancel_epi (cokernel.π (u ≫ p))).1
    ext <;> simp [d, sq, cokernel.map]
  rw [he]
  infer_instance

section SupportSplitting

attribute [local implicit_reducible] TopCat.Sheaf TopCat.instCategorySheaf._aux_1
  TopCat.instCategorySheaf._aux_3 TopCat.instCategorySheaf._aux_5

private lemma ccm5_isIso_cokernel_split_of_eq
    {C : Type*} [Category C] [Abelian C]
    {A B D E : C} {u : A ⟶ B} {v : A ⟶ D} {p : B ⟶ E} {q : D ⟶ E}
    (h : IsPushout u v p q) {f : A ⟶ E} (hf : u ≫ p = f) :
    IsIso (biprod.lift
      (cokernel.map f p u (𝟙 E) (by simp [← hf]))
      (cokernel.map f q v (𝟙 E) (by simpa [← hf] using h.w))) := by
  subst f
  exact ccm5_isIso_cokernel_split h

private abbrev ccm5_pair (T : TopCat.{0}) (S : Closeds T) :=
  CategoryTheory.Sheaf.pairSheaf (J := Opens.grothendieckTopology T)
    (homOfLE (show S.compl ≤ ⊤ from le_top))

private abbrev ccm5_pairMap {T : TopCat.{0}} {S R : Closeds T} (h : S ≤ R) :
    ccm5_pair T R ⟶ ccm5_pair T S :=
  CategoryTheory.Sheaf.pairSheafMap
    (homOfLE (show S.compl ≤ ⊤ from le_top))
    (homOfLE (show R.compl ≤ ⊤ from le_top))
    (homOfLE (show R.compl ≤ S.compl from fun _ hx hs => hx (h hs)))
    (𝟙 _) (Subsingleton.elim _ _)

private lemma ccm5_pairMap_comp {T : TopCat.{0}} {S R Q : Closeds T}
    (h : S ≤ R) (k : R ≤ Q) :
    ccm5_pairMap k ≫ ccm5_pairMap h = ccm5_pairMap (h.trans k) := by
  rw [← CategoryTheory.Sheaf.pairSheafMap_comp]
  rfl

private lemma ccm5_pair_split (T : TopCat.{0}) (A B : Closeds T)
    (h : Disjoint A B) :
    IsIso (biprod.lift (ccm5_pairMap (show A ≤ A ⊔ B from le_sup_left))
      (ccm5_pairMap (show B ≤ A ⊔ B from le_sup_right))) := by
  let G := CategoryTheory.Sheaf.freeAbelianSheaf (Opens.grothendieckTopology T)
  let u := G.map (homOfLE (show (A ⊔ B).compl ≤ A.compl from
    fun _ hx ha => hx (Or.inl ha)))
  let v := G.map (homOfLE (show (A ⊔ B).compl ≤ B.compl from
    fun _ hx hb => hx (Or.inr hb)))
  let p := G.map (homOfLE (show A.compl ≤ ⊤ from le_top))
  let q := G.map (homOfLE (show B.compl ≤ ⊤ from le_top))
  have hp : u ≫ p = G.map (homOfLE (show (A ⊔ B).compl ≤ ⊤ from le_top)) := by
    rw [← G.map_comp]
    rfl
  have hh := ccm5_isIso_cokernel_split_of_eq
    (ccm5_isPushout_freeAbelianSheaf_compl T A B h) hp
  convert hh using 2 <;>
    dsimp only [ccm5_pairMap, CategoryTheory.Sheaf.pairSheafMap] <;>
    congr 1 <;>
    exact G.map_id _

/-- The additive structure inherited from the supported Ext group.
Source: `CategoryTheory.Abelian.Ext.instAddCommGroup`. -/
local instance ccm5_supportedGroup (T : TopCat.{0}) (F : TopCat.Sheaf AddCommGrpCat T)
    (S : Closeds T) (n : ℕ) : AddCommGroup (TopCat.Sheaf.supportH T S F n) :=
  Abelian.Ext.instAddCommGroup

private abbrev ccm5_enlarge {T : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat T)
    {S R : Closeds T} (h : S ≤ R) (n : ℕ) :
    TopCat.Sheaf.supportH T S F n →+ TopCat.Sheaf.supportH T R F n :=
  (Abelian.Ext.mk₀ (ccm5_pairMap h)).precomp F (zero_add n)

private lemma ccm5_enlarge_comp {T : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat T)
    {S R Q : Closeds T} (h : S ≤ R) (k : R ≤ Q) (n : ℕ)
    (x : TopCat.Sheaf.supportH T S F n) :
    ccm5_enlarge F k n (ccm5_enlarge F h n x) =
      ccm5_enlarge F (h.trans k) n x := by
  change (Abelian.Ext.mk₀ _).comp ((Abelian.Ext.mk₀ _).comp x (zero_add n)) (zero_add n) = _
  rw [Abelian.Ext.mk₀_comp_mk₀_assoc, ccm5_pairMap_comp]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
private lemma ccm5_binary_enlarge_bijective
    (T : TopCat.{0}) (F : TopCat.Sheaf AddCommGrpCat T)
    (A B : Closeds T) (h : Disjoint A B) (n : ℕ) :
    Function.Bijective (fun x :
      TopCat.Sheaf.supportH T A F n × TopCat.Sheaf.supportH T B F n =>
      ccm5_enlarge F (show A ≤ A ⊔ B from le_sup_left) n x.1 +
      ccm5_enlarge F (show B ≤ A ⊔ B from le_sup_right) n x.2) := by
  let d := biprod.lift (ccm5_pairMap (show A ≤ A ⊔ B from le_sup_left))
    (ccm5_pairMap (show B ≤ A ⊔ B from le_sup_right))
  haveI : IsIso d := ccm5_pair_split T A B h
  let e : (Abelian.Ext (ccm5_pair T A) F n × Abelian.Ext (ccm5_pair T B) F n) ≃+
      Abelian.Ext (ccm5_pair T (A ⊔ B)) F n :=
    Abelian.Ext.biprodAddEquiv.symm.trans
    (Abelian.Ext.precompAddEquiv (asIso d) F n)
  have he : (fun x :
      TopCat.Sheaf.supportH T A F n × TopCat.Sheaf.supportH T B F n =>
      ccm5_enlarge F (show A ≤ A ⊔ B from le_sup_left) n x.1 +
      ccm5_enlarge F (show B ≤ A ⊔ B from le_sup_right) n x.2) = e := by
    funext x
    change _ = (Abelian.Ext.mk₀ d).comp
      ((Abelian.Ext.mk₀ (biprod.fst (X := ccm5_pair T A) (Y := ccm5_pair T B))).comp x.1 (zero_add n) +
       (Abelian.Ext.mk₀ (biprod.snd (X := ccm5_pair T A) (Y := ccm5_pair T B))).comp x.2 (zero_add n)) (zero_add n)
    rw [Abelian.Ext.comp_add, Abelian.Ext.mk₀_comp_mk₀_assoc,
      Abelian.Ext.mk₀_comp_mk₀_assoc]
    simp only [d, biprod.lift_fst, biprod.lift_snd]
    rfl
  rw [he]
  exact e.bijective

private lemma ccm5_empty_support_subsingleton
    (T : TopCat.{0}) (F : TopCat.Sheaf AddCommGrpCat T) (n : ℕ) :
    Subsingleton (TopCat.Sheaf.supportH T ⊥ F n) := by
  have hz : IsZero (ccm5_pair T ⊥) := by
    let f : (⊥ : Closeds T).compl ⟶ (⊤ : Opens T) := homOfLE le_top
    have hc : (⊥ : Closeds T).compl = ⊤ := by
      ext x
      simp [Closeds.compl]
    haveI : IsIso f := ⟨⟨homOfLE (by rw [hc]), Subsingleton.elim _ _,
      Subsingleton.elim _ _⟩⟩
    exact isZero_cokernel_of_epi
      ((CategoryTheory.Sheaf.freeAbelianSheaf (Opens.grothendieckTopology T)).map f)
  refine ⟨fun x y => ?_⟩
  have he (z : TopCat.Sheaf.supportH T ⊥ F n) : z = 0 := by
    rw [← Abelian.Ext.mk₀_id_comp z, hz.eq_of_src (𝟙 _) 0,
      Abelian.Ext.mk₀_zero, Abelian.Ext.zero_comp]
  exact (he x).trans (he y).symm

private lemma ccm5_finite_enlarge_bijective
    (T : TopCat.{0}) (F : TopCat.Sheaf AddCommGrpCat T) (n r : ℕ)
    (S : Fin r → Closeds T) (hS : Pairwise (fun i j => Disjoint (S i) (S j)))
    (Z : Closeds T) (h : ∀ i, S i ≤ Z) (hZ : (⨆ i, S i) = Z) :
    Function.Bijective (fun x : ∀ i, TopCat.Sheaf.supportH T (S i) F n =>
      ∑ i, ccm5_enlarge F (h i) n (x i)) := by
  classical
  induction r generalizing Z with
  | zero =>
    have hz : Z = ⊥ := by simpa only [iSup_of_empty] using hZ.symm
    clear hZ
    subst Z
    haveI := ccm5_empty_support_subsingleton T F n
    constructor
    · intro x y _
      funext i
      exact Fin.elim0 i
    · intro y
      exact ⟨fun i => Fin.elim0 i, Subsingleton.elim _ _⟩
  | succ r ih =>
    have hz : S 0 ⊔ (⨆ i : Fin r, S i.succ) = Z := by
      rw [← hZ]
      apply le_antisymm
      · exact sup_le (le_iSup S 0) (iSup_le fun i => le_iSup S i.succ)
      · apply iSup_le
        intro i
        exact Fin.cases le_sup_left
          (fun j => le_sup_of_le_right (le_iSup (fun k : Fin r => S k.succ) j)) i
    clear hZ
    subst Z
    have hd : Disjoint (S 0) (⨆ i : Fin r, S i.succ) := by
      rw [← Finset.sup_univ_eq_iSup, Finset.disjoint_sup_right]
      intro i _
      exact hS (Fin.succ_ne_zero i).symm
    have hb := ccm5_binary_enlarge_bijective T F (S 0) (⨆ i : Fin r, S i.succ) hd n
    have ht := ih (fun i => S i.succ)
      (fun i j hij => hS (fun he => hij (Fin.succ_injective _ he)))
      (⨆ i : Fin r, S i.succ) (fun i => le_iSup (fun j : Fin r => S j.succ) i) rfl
    have he (x : ∀ i, TopCat.Sheaf.supportH T (S i) F n) :
        (∑ i, ccm5_enlarge F (h i) n (x i)) =
        ccm5_enlarge F (show S 0 ≤ S 0 ⊔ (⨆ i : Fin r, S i.succ) from le_sup_left) n (x 0) +
        ccm5_enlarge F (show (⨆ i : Fin r, S i.succ) ≤
          S 0 ⊔ (⨆ i : Fin r, S i.succ) from le_sup_right) n
          (∑ i : Fin r, ccm5_enlarge F (le_iSup (fun j : Fin r => S j.succ) i) n
            (x i.succ)) := by
      rw [Fin.sum_univ_succ, map_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact (ccm5_enlarge_comp F _ _ n (x i.succ)).symm
    constructor
    · intro x y hxy
      dsimp only at hxy
      rw [he x, he y] at hxy
      have hp : (x 0, ∑ i : Fin r,
          ccm5_enlarge F (le_iSup (fun j : Fin r => S j.succ) i) n (x i.succ)) =
          (y 0, ∑ i : Fin r,
          ccm5_enlarge F (le_iSup (fun j : Fin r => S j.succ) i) n (y i.succ)) :=
        hb.1 hxy
      have htxy : (fun i : Fin r => x i.succ) = (fun i : Fin r => y i.succ) :=
        ht.1 (congrArg Prod.snd hp)
      funext i
      refine Fin.cases (congrArg Prod.fst hp) (fun j => congrFun htxy j) i
    · intro y
      obtain ⟨⟨a, b⟩, hab⟩ := hb.2 y
      obtain ⟨x, hx⟩ := ht.2 b
      refine ⟨Fin.cons a x, ?_⟩
      dsimp only
      rw [he]
      dsimp only at hx hab
      simpa only [Fin.cons_zero, Fin.cons_succ, hx] using hab

/-- Finite disjoint closed supports split supported cohomology in every degree
under the canonical sum of enlargement maps.
Source: Bredon, *Sheaf Theory*, second edition, Chapter II, cohomology with supports. -/
theorem ccm5_disjoint_supportSum_bijective_aux
    (T : TopCat.{0}) (F : TopCat.Sheaf AddCommGrpCat T)
    (r : ℕ) (S : Fin r → TopologicalSpace.Closeds T)
    (hS : Pairwise (fun i j => Disjoint (S i) (S j))) (n : ℕ) :
    Function.Bijective (ccm5_supportSum T F r S n) := by
  classical
  have he : (fun x => ccm5_supportSum T F r S n x) =
      (fun x : ∀ i, TopCat.Sheaf.supportH T (S i) F n =>
        ∑ i, ccm5_enlarge F (le_iSup S i) n (x i)) := by
    funext x
    simp only [ccm5_supportSum, AddMonoidHom.finsetSum_apply, AddMonoidHom.comp_apply]
    rfl
  change Function.Bijective (fun x => ccm5_supportSum T F r S n x)
  rw [he]
  exact ccm5_finite_enlarge_bijective T F n r S hS (⨆ i, S i)
    (fun i => le_iSup S i) rfl

end SupportSplitting

/-- Excision for the relative pair sheaves of two opens.
Source: `Opens.mayerVietorisSquare` and `isIso_cokernel_map_of_isPushout`. -/
theorem ccm5_pairSheaf_excision_isIso
    (T : TopCat.{0}) (U V : Opens T) :
    IsIso (CategoryTheory.Sheaf.pairSheafMap
      (J := Opens.grothendieckTopology T)
      (homOfLE (show V ≤ U ⊔ V from le_sup_right))
      (homOfLE (show U ⊓ V ≤ U from inf_le_left))
      (homOfLE inf_le_right) (homOfLE le_sup_left) (Subsingleton.elim _ _)) := by
  exact CategoryTheory.Limits.isIso_cokernel_map_of_isPushout
    (Opens.mayerVietorisSquare U V).isPushoutAddCommGrpFreeSheaf

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Vanishing of both outer terms in the nested-pair sequence kills the middle term.
Source: `CategoryTheory.Abelian.Ext.contravariant_sequence_exact₂'`. -/
theorem ccm5_relH_nested_middle_subsingleton
    (T : TopCat.{0}) (F : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})
    {W U V : Opens T} (f : W ⟶ U) (g : U ⟶ V) (n : ℕ)
    (hsmall : Subsingleton (CategoryTheory.Sheaf.relH F n g))
    (hlayer : Subsingleton (CategoryTheory.Sheaf.relH F n f)) :
    Subsingleton (CategoryTheory.Sheaf.relH F n (f ≫ g)) := by
  let := hsmall
  let := hlayer
  let hS := CategoryTheory.Sheaf.pairNestedShortComplex_shortExact
    (J := Opens.grothendieckTopology T) f g
  exact AddCommGrpCat.subsingleton_of_isZero
    ((Abelian.Ext.contravariant_sequence_exact₂' hS F n).isZero_X₂
      ((@AddCommGrpCat.isZero_of_subsingleton (AddCommGrpCat.of
        (CategoryTheory.Sheaf.relH F n g)) hsmall).eq_zero_of_src _)
      ((@AddCommGrpCat.isZero_of_subsingleton (AddCommGrpCat.of
        (CategoryTheory.Sheaf.relH F n f)) hlayer).eq_zero_of_tgt _))

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The pair layer vanishes when the ambient supported group and next boundary group do.
Source: `CategoryTheory.Abelian.Ext.contravariant_sequence_exact₁'`. -/
theorem ccm5_relH_nested_layer_subsingleton
    (T : TopCat.{0}) (F : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})
    {W U V : Opens T} (f : W ⟶ U) (g : U ⟶ V) (n : ℕ)
    (hbig : Subsingleton (CategoryTheory.Sheaf.relH F n (f ≫ g)))
    (hnext : Subsingleton (CategoryTheory.Sheaf.relH F (n + 1) g)) :
    Subsingleton (CategoryTheory.Sheaf.relH F n f) := by
  let := hbig
  let := hnext
  let hS := CategoryTheory.Sheaf.pairNestedShortComplex_shortExact
    (J := Opens.grothendieckTopology T) f g
  exact AddCommGrpCat.subsingleton_of_isZero
    ((Abelian.Ext.contravariant_sequence_exact₁' hS F n (n + 1) (by omega)).isZero_X₂
      ((@AddCommGrpCat.isZero_of_subsingleton (AddCommGrpCat.of
        (CategoryTheory.Sheaf.relH F n (f ≫ g))) hbig).eq_zero_of_src _)
      ((@AddCommGrpCat.isZero_of_subsingleton (AddCommGrpCat.of
        (CategoryTheory.Sheaf.relH F (n + 1) g)) hnext).eq_zero_of_tgt _))
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Supported cohomology of a union vanishes if both supports and the next
intersection group vanish.
Source: relative-pair excision and the nested-pair long exact sequence. -/
theorem ccm5_supportH_union_subsingleton
    (T : TopCat.{0}) (F : CategoryTheory.Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0})
    (A B : Closeds T) (n : ℕ)
    (hA : Subsingleton (TopCat.Sheaf.supportH T A F n))
    (hB : Subsingleton (TopCat.Sheaf.supportH T B F n))
    (hAB : Subsingleton (TopCat.Sheaf.supportH T (A ⊓ B) F (n + 1))) :
    Subsingleton (TopCat.Sheaf.supportH T (A ⊔ B) F n) := by
  let U := A.compl
  let V := B.compl
  have hnext : Subsingleton (CategoryTheory.Sheaf.relH F (n + 1)
      (homOfLE (show U ⊔ V ≤ ⊤ from le_top))) := by
    have he : (A ⊓ B).compl = U ⊔ V := by
      ext z
      change ¬ (z ∈ A ∧ z ∈ B) ↔ (z ∉ A ∨ z ∉ B)
      exact not_and_or
    exact (congrArg (fun O : Opens T => Subsingleton (CategoryTheory.Sheaf.relH F
      (n + 1) (homOfLE (show O ≤ ⊤ from le_top)))) he).mp hAB
  have hlayer := ccm5_relH_nested_layer_subsingleton T F
    (homOfLE (show V ≤ U ⊔ V from le_sup_right))
    (homOfLE (show U ⊔ V ≤ ⊤ from le_top)) n hB hnext
  let e := CategoryTheory.Sheaf.pairSheafMap
    (J := Opens.grothendieckTopology T)
    (homOfLE (show V ≤ U ⊔ V from le_sup_right))
    (homOfLE (show U ⊓ V ≤ U from inf_le_left))
    (homOfLE inf_le_right) (homOfLE le_sup_left) (Subsingleton.elim _ _)
  let : IsIso e := ccm5_pairSheaf_excision_isIso T U V
  let := hlayer
  have hsmallLayer : Subsingleton (CategoryTheory.Sheaf.relH F n
      (homOfLE (show U ⊓ V ≤ U from inf_le_left))) := by
    let ee : CategoryTheory.Sheaf.relH F n
        (homOfLE (show U ⊓ V ≤ U from inf_le_left)) ≃+
        CategoryTheory.Sheaf.relH F n
        (homOfLE (show V ≤ U ⊔ V from le_sup_right)) :=
      Abelian.Ext.precompAddEquiv (asIso e).symm F n
    exact ee.injective.subsingleton
  have h := ccm5_relH_nested_middle_subsingleton T F
    (homOfLE (show U ⊓ V ≤ U from inf_le_left))
    (homOfLE (show U ≤ ⊤ from le_top)) n hA hsmallLayer
  have he : (A ⊔ B).compl = U ⊓ V := by
    ext z
    simp [U, V]
  exact (congrArg (fun O : Opens T => Subsingleton (CategoryTheory.Sheaf.relH F
    n (homOfLE (show O ≤ ⊤ from le_top)))) he).mpr h

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The smooth part of a component has no section cohomology below its codimension degree.
Source: `cycleComponentSmoothSupport_exists_supportedInjectiveSection_vanishing` and
`TopCat.Sheaf.sectionCohomology_isZero_of_cofinal_lower_vanishing`. -/
theorem ccm5_component_smoothLayer_homology_isZero
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (x : X.left) (p : ℕ) (hx : Order.coheight x = p)
    (n : ℤ) (hn : n < 2 * (p : ℤ)) :
    CategoryTheory.Limits.IsZero ((((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X))
      (cycleComponentSmoothSupportAmbientOpen X x)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (complexSupportInjectiveComplex X
          (cycleComponentAnalyticClosedSupport X x))).homology n) := by
  apply TopCat.Sheaf.sectionCohomology_isZero_of_cofinal_lower_vanishing
    (TopCat.of (ComplexPoint X)) _ _ 0 n
  · exact fun j => TopCat.Sheaf.sheafSectionsSupportedOutside_isFlasque
      (TopCat.of (ComplexPoint X)) (cycleComponentAnalyticClosedSupport X x).compl
      ((ambientRationalInjectiveComplex X).X j)
  · exact fun j hj y hy V hyV =>
      cycleComponentSmoothSupport_exists_supportedInjectiveSection_vanishing
        X x hx j (ne_of_lt (hj.trans_lt hn)) y hy V hyV


set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A single prime support has no cohomology below twice its coheight.
Source: smooth local support purity, singular-boundary vanishing, and localization. -/
theorem ccm5_component_supportH_subsingleton_of_lt
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (x : X.left) (p : ℕ) (hx : Order.coheight x = p)
    (n : ℕ) (hn : n < 2 * p) :
    Subsingleton (TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X))
      (cycleComponentAnalyticClosedSupport X x)
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
        (AddCommGrpCat.of ℚ)) n) := by
  let T := TopCat.of (ComplexPoint X)
  let Z := cycleComponentSingularAnalyticClosedFiltration X x 0
  let F := (TopCat.Sheaf.constantFunctor T).obj (AddCommGrpCat.of ℚ)
  let K := ambientRationalInjectiveComplex X
  have hs : Subsingleton (TopCat.Sheaf.supportH T Z F n) :=
    AddCommGrpCat.subsingleton_of_isZero
      (cycleComponentSingularBoundaryRelH_isZero_of_lt X x hx n (by omega))
  let := hs
  let e := rationalSupportAddEquivSupportedInjectiveHomology X Z n
  have hsmall : CategoryTheory.Limits.IsZero ((((TopCat.Sheaf.supportEvaluation T ⊤).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (complexSupportInjectiveComplex X Z)).homology (n : ℤ)) := by
    let := e.symm.injective.subsingleton
    exact AddCommGrpCat.isZero_of_subsingleton _
  have hvan := TopCat.Sheaf.nestedSupportRestriction_middle_homology_isZero T
    (cycleComponentSupportComplement_le_smoothAmbientOpen X x) K
    (fun j => TopCat.Sheaf.injective_isFlasque _ _) (n : ℤ) hsmall
    (ccm5_component_smoothLayer_homology_isZero X x p hx n (by omega))
  let : Subsingleton ((((TopCat.Sheaf.supportEvaluation T ⊤).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (complexSupportInjectiveComplex X
        (cycleComponentAnalyticClosedSupport X x))).homology (n : ℤ)) :=
    AddCommGrpCat.subsingleton_of_isZero hvan
  exact (rationalSupportAddEquivSupportedInjectiveHomology X
    (cycleComponentAnalyticClosedSupport X x) n).injective.subsingleton

/-- A nonempty closed set can be split into one generic component and a smaller remainder.
Source: `NoetherianSpace.exists_finset_irreducible`, finite maximality, and sobriety. -/
theorem ccm5_closed_generic_split (X : Scheme) [NoetherianSpace X]
    (S : Closeds X) (hne : S ≠ ⊥) :
    ∃ (x : X) (B : Closeds X),
      S = (⟨closure ({x} : Set X), isClosed_closure⟩ : Closeds X) ⊔ B ∧
      B < S ∧ x ∉ B := by
  classical
  obtain ⟨s, hs, hS⟩ := NoetherianSpace.exists_finset_irreducible S
  have hsne : s.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h] at hS
    exact hne (by simpa using hS)
  obtain ⟨A, hA⟩ := s.exists_maximal hsne
  have hi := hs ⟨A, hA.1⟩
  let x := hi.genericPoint
  let B := (s.erase A).sup id
  have hx : closure ({x} : Set X) = (A : Set X) :=
    hi.closure_genericPoint A.isClosed
  have hxA : x ∈ A := by
    change x ∈ (A : Set X)
    rw [← hx]
    exact subset_closure (Set.mem_singleton x)
  have hxB : x ∉ B := by
    intro hm
    change x ∈ (↑((s.erase A).sup id) : Set X) at hm
    rw [Closeds.coe_finset_sup, Finset.sup_eq_iSup] at hm
    obtain ⟨C, hC, hxC⟩ := Set.mem_iUnion₂.mp hm
    have hAC : A ≤ C := by
      change (A : Set X) ⊆ (C : Set X)
      rw [← hx]
      exact closure_minimal (Set.singleton_subset_iff.mpr hxC) C.isClosed
    have he : C = A := le_antisymm (hA.2 (Finset.mem_of_mem_erase hC) hAC) hAC
    exact (Finset.ne_of_mem_erase hC) he
  have hsup : A ⊔ B = S := by
    rw [hS, ← Finset.insert_erase hA.1, Finset.sup_insert]
    rfl
  have hBS : B < S := lt_of_le_of_ne (hsup ▸ le_sup_right) (by
    intro he
    apply hxB
    rw [he, ← hsup]
    exact Or.inl hxA)
  refine ⟨x, B, ?_, hBS, hxB⟩
  have hAx : (⟨closure ({x} : Set X), isClosed_closure⟩ : Closeds X) = A :=
    SetLike.coe_injective hx
  rw [hAx]
  exact hsup.symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Empty support has zero rational supported cohomology.
Source: `TopCat.Sheaf.supportedSections_top_homology_isZero`. -/
theorem ccm5_supportH_bot_subsingleton
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (n : ℕ) :
    Subsingleton (TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X)) ⊥
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
        (AddCommGrpCat.of ℚ)) n) := by
  let T := TopCat.of (ComplexPoint X)
  let : Subsingleton ((((TopCat.Sheaf.supportEvaluation T ⊤).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (complexSupportInjectiveComplex X ⊥)).homology (n : ℤ)) :=
    AddCommGrpCat.subsingleton_of_isZero (by
      have he : (⊥ : Closeds (ComplexPoint X)).compl = ⊤ := by ext; simp
      simpa only [complexSupportInjectiveComplex, he] using
        TopCat.Sheaf.supportedSections_top_homology_isZero T ⊤
          (ambientRationalInjectiveComplex X) n)
  exact (rationalSupportAddEquivSupportedInjectiveHomology X ⊥ n).injective.subsingleton


set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Closed algebraic supports of coheight at least `p` have no rational supported
cohomology below `2p`.
Source: Noetherian induction, component purity, and supported union localization. -/
theorem ccm5_closed_supportH_subsingleton_of_coheight
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S : Closeds X.left) (p n : ℕ)
    (hc : ∀ z ∈ S, (p : ℕ∞) ≤ Order.coheight z) (hn : n < 2 * p) :
    Subsingleton (TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X))
      (S.preimage (continuous_underlying_to_zariski X))
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
        (AddCommGrpCat.of ℚ)) n) := by
  classical
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : IsNoetherian X.left := { }
  revert p n
  induction S using (wellFounded_lt (α := Closeds X.left)).induction with
  | h S ih =>
    intro p n hc hn
    by_cases hSbot : S = ⊥
    · subst S
      exact ccm5_supportH_bot_subsingleton X n
    obtain ⟨x, B, hS, hBS, hxB⟩ := ccm5_closed_generic_split X.left S hSbot
    let C : Closeds X.left := ⟨closure ({x} : Set X.left), isClosed_closure⟩
    have hxC : x ∈ C := subset_closure (Set.mem_singleton x)
    have hxS : x ∈ S := by rw [hS]; exact Or.inl hxC
    have hfin : Order.coheight x ≠ ⊤ := ne_of_lt
      (lt_of_le_of_lt (SmoothOfRelativeDimension.coheight_le_complex
        (f := X.hom) (d := dim X.left) x) (WithTop.coe_lt_top _))
    let m := (Order.coheight x).toNat
    have hm : Order.coheight x = m := (ENat.natCast_toNat hfin).symm
    have hpm : p ≤ m := by
      have hh := hc x hxS
      rw [hm] at hh
      exact_mod_cast hh
    have hA : Subsingleton (TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X))
        (C.preimage (continuous_underlying_to_zariski X))
        ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
          (AddCommGrpCat.of ℚ)) n) :=
      ccm5_component_supportH_subsingleton_of_lt X x m hm n (by omega)
    have hB := ih B hBS p n (fun z hz => hc z (hBS.le hz)) hn
    have hI := ih (C ⊓ B) (lt_of_le_of_lt inf_le_right hBS) (p + 1) (n + 1)
      (by
        intro z hz
        have hzx : z ≤ x := Scheme.le_iff_specializes.mpr
          (specializes_iff_mem_closure.mpr hz.1)
        have hlt : z < x := lt_iff_le_not_ge.mpr ⟨hzx, fun hxz => by
          have he : z = x := ((Scheme.le_iff_specializes.mp hxz).antisymm
            (Scheme.le_iff_specializes.mp hzx)).eq
          exact hxB (he ▸ hz.2)⟩
        calc
          ((p + 1 : ℕ) : ℕ∞) ≤ Order.coheight x + 1 := by
            rw [hm]
            exact_mod_cast Nat.add_le_add_right hpm 1
          _ ≤ Order.coheight z := Order.coheight_add_one_le hlt)
      (by omega)
    have he : S.preimage (continuous_underlying_to_zariski X) =
        C.preimage (continuous_underlying_to_zariski X) ⊔
          B.preimage (continuous_underlying_to_zariski X) := by
      rw [hS]
      rfl
    rw [he]
    exact ccm5_supportH_union_subsingleton _ _ _ _ n hA hB hI


/-- Intersections of distinct equal-coheight component closures have higher coheight.
Source: `Order.coheight_strictAnti` and `Order.coheight_add_one_le`. -/
theorem ccm5_intersection_coheight_lower_bound
    (X : Scheme) (q : ℕ) (x y z : X) (hxy : x ≠ y)
    (hx : Order.coheight x = q) (hy : Order.coheight y = q)
    (hzx : z ∈ closure ({x} : Set X)) (hzy : z ∈ closure ({y} : Set X)) :
    (q + 1 : ℕ∞) ≤ Order.coheight z := by
  have hzx' : z ≤ x := Scheme.le_iff_specializes.mpr
    (specializes_iff_mem_closure.mpr hzx)
  have hzy' : z ≤ y := Scheme.le_iff_specializes.mpr
    (specializes_iff_mem_closure.mpr hzy)
  have hzx_ne : z ≠ x := by
    intro heq
    subst z
    have hlt : x < y := lt_iff_le_not_ge.mpr ⟨hzy', fun hyx =>
      hxy (((Scheme.le_iff_specializes.mp hyx).antisymm
        (Scheme.le_iff_specializes.mp hzy')).eq)⟩
    have h := Order.coheight_strictAnti hlt (by rw [hy]; exact WithTop.coe_lt_top q)
    rw [hx, hy] at h
    exact (lt_irrefl _ h)
  simpa only [hx] using Order.coheight_add_one_le (lt_iff_le_not_ge.mpr ⟨hzx', fun hxz =>
    hzx_ne (((Scheme.le_iff_specializes.mp hxz).antisymm
      (Scheme.le_iff_specializes.mp hzx')).eq)⟩)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A prime component's generic point avoids its singular boundary.
Source: generic smoothness over a perfect field and uniqueness of generic points. -/
theorem ccm5_generic_not_mem_singularBoundary
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (x : X.left) : x ∉ cycleComponentSingularAmbientClosedFiltration X x 0 := by
  let Y := cycleComponent X.left x
  let i := cycleComponentι X.left x
  have hg : i (genericPoint Y) = x := by
    have hr : Set.range (fun y : Y => i y) = closure ({x} : Set X.left) :=
      range_cycleComponentι X.left x
    have hh : IsGenericPoint (i (genericPoint Y))
        (closure (Set.range (fun y : Y => i y))) := by
      simpa only [Set.image_univ] using (genericPoint_spec Y).image i.continuous
    rw [hr, closure_closure] at hh
    exact hh.eq isGenericPoint_closure
  rintro ⟨y, hy, he⟩
  have hey : y = genericPoint Y := i.isClosedEmbedding.injective (he.trans hg.symm)
  subst y
  exact hy (i ≫ X.hom).genericPoint_mem_smoothLocus_of_perfectField

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Every point of the singular boundary has coheight strictly above the component.
Source: generic smoothness and `Order.coheight_add_one_le`. -/
theorem ccm5_singularBoundary_coheight_lower_bound
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (q : ℕ) (x z : X.left) (hx : Order.coheight x = q)
    (hz : z ∈ cycleComponentSingularAmbientClosedFiltration X x 0) :
    ((q + 1 : ℕ) : ℕ∞) ≤ Order.coheight z := by
  have hzx : z ≤ x := by
    apply Scheme.le_iff_specializes.mpr
    apply specializes_iff_mem_closure.mpr
    rw [← range_cycleComponentι X.left x]
    obtain ⟨y, _, hy⟩ := hz
    exact ⟨y, hy⟩
  have hlt : z < x := lt_iff_le_not_ge.mpr ⟨hzx, fun hxz => by
    have he : z = x := ((Scheme.le_iff_specializes.mp hxz).antisymm
      (Scheme.le_iff_specializes.mp hzx)).eq
    exact ccm5_generic_not_mem_singularBoundary X x (he ▸ hz)⟩
  simpa only [hx, Nat.cast_add, Nat.cast_one] using Order.coheight_add_one_le hlt


/-- Membership in a finite supremum of closed sets is membership in one summand.
Source: `Closeds.coe_finset_sup`. -/
theorem ccm5_mem_finite_iSup {T : Type*} [TopologicalSpace T]
    {ι : Type*} [Fintype ι] (S : ι → Closeds T) (z : T) :
    z ∈ (⨆ i, S i) ↔ ∃ i, z ∈ S i := by
  classical
  rw [← Finset.sup_univ_eq_iSup]
  change z ∈ (↑(Finset.univ.sup S) : Set T) ↔ _
  rw [Closeds.coe_finset_sup, Finset.sup_eq_iSup]
  simp only [Set.iSup_eq_iUnion, Set.mem_iUnion, Finset.mem_univ, exists_true_left, Function.comp_apply]
  rfl


/-- The removed boundary has no supported cohomology below degree `2(q+1)`.
Source: stratified local support vanishing, extending
`cycleComponentSingularBoundaryRelH_isZero_of_lt` to the finite boundary union. -/
theorem ccm5_componentBoundary_vanishing_aux
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (r q : ℕ) (x : Fin r → X.left) (hx : Function.Injective x)
    (hc : ∀ i, Order.coheight (x i) = q) (n : ℕ) (hn : n < 2 * (q + 1)) :
    Subsingleton (TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X))
      (ccm5_componentBoundary X r x)
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
        (AddCommGrpCat.of ℚ)) n) := by
  classical
  let C (i : Fin r) : Closeds X.left := ⟨closure ({x i} : Set X.left), isClosed_closure⟩
  let S : Closeds X.left :=
    (⨆ i, cycleComponentSingularAmbientClosedFiltration X (x i) 0) ⊔
      ⨆ i, ⨆ j, if i = j then ⊥ else C i ⊓ C j
  have hcodim : ∀ z ∈ S, ((q + 1 : ℕ) : ℕ∞) ≤ Order.coheight z := by
    intro z hz
    change (z ∈ (⨆ i, cycleComponentSingularAmbientClosedFiltration X (x i) 0) ∨
      z ∈ (⨆ i, ⨆ j, if i = j then ⊥ else C i ⊓ C j)) at hz
    rcases hz with hz | hz
    · obtain ⟨i, hi⟩ := (ccm5_mem_finite_iSup _ z).mp hz
      exact ccm5_singularBoundary_coheight_lower_bound X q (x i) z (hc i) hi
    · obtain ⟨i, hi⟩ := (ccm5_mem_finite_iSup _ z).mp hz
      obtain ⟨j, hj⟩ := (ccm5_mem_finite_iSup _ z).mp hi
      by_cases hij : i = j
      · rw [ite_eq_left hij] at hj
        exact False.elim hj
      · rw [ite_eq_right hij] at hj
        simpa only [Nat.cast_add, Nat.cast_one] using
          ccm5_intersection_coheight_lower_bound X.left q (x i) (x j) z
            (fun he => hij (hx he)) (hc i) (hc j) hj.1 hj.2
  have he : S.preimage (continuous_underlying_to_zariski X) =
      ccm5_componentBoundary X r x := by
    ext z
    change (z.underlying ∈ (⨆ i, cycleComponentSingularAmbientClosedFiltration X (x i) 0) ∨
      z.underlying ∈ (⨆ i, ⨆ j, if i = j then ⊥ else C i ⊓ C j)) ↔
      (z ∈ (⨆ i, cycleComponentSingularAnalyticClosedFiltration X (x i) 0) ∨
      z ∈ (⨆ i, ⨆ j, if i = j then ⊥ else
        cycleComponentAnalyticClosedSupport X (x i) ⊓ cycleComponentAnalyticClosedSupport X (x j)))
    simp only [ccm5_mem_finite_iSup]
    apply or_congr
    · rfl
    · apply exists_congr
      intro i
      apply exists_congr
      intro j
      split_ifs <;> rfl
  rw [← he]
  exact ccm5_closed_supportH_subsingleton_of_coheight X S (q + 1) n hcodim hn

/-- Removing the boundary preserves the degree `2q` supported group of the union.
Source: the localization sequence and boundary vanishing in degrees `2q` and `2q+1`. -/
theorem ccm5_componentRestriction_bijective_aux
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (r q : ℕ) (x : Fin r → X.left) (hx : Function.Injective x)
    (hc : ∀ i, Order.coheight (x i) = q) :
    Function.Bijective (ccm5_componentRestriction X r x (2 * q)) := by
  let S : Closeds (ComplexPoint X) :=
    ⨆ i, cycleComponentAnalyticClosedSupport X (x i)
  let B : Closeds (ComplexPoint X) := ccm5_componentBoundary X r x
  have hB : B ≤ S := by
    dsimp only [B, S, ccm5_componentBoundary]
    apply sup_le
    · apply iSup_le
      intro i y hy
      apply le_iSup (fun j => cycleComponentAnalyticClosedSupport X (x j)) i
      obtain ⟨z, _, hz⟩ := hy
      change y.underlying ∈ closure ({x i} : Set X.left)
      rw [← range_cycleComponentι X.left (x i)]
      exact ⟨z, hz⟩
    · apply iSup_le
      intro i
      apply iSup_le
      intro j
      split_ifs
      · exact bot_le
      · exact (inf_le_left.trans (le_iSup
          (fun k => cycleComponentAnalyticClosedSupport X (x k)) i))
  have hSB : S.compl ≤ B.compl := fun _ hyS hyB => hyS (hB hyB)
  have hinter : S.compl ⊓ B.compl = S.compl := inf_eq_left.mpr hSB
  let F := (TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
    (AddCommGrpCat.of ℚ)
  let f : S.compl ⟶ B.compl := homOfLE hSB
  let g : B.compl ⟶ ⊤ := homOfLE le_top
  have h₀ : Limits.IsZero (AddCommGrpCat.of (TopCat.Sheaf.supportH
      (TopCat.of (ComplexPoint X)) B F (2 * q))) := by
    letI := ccm5_componentBoundary_vanishing_aux X r q x hx hc (2 * q) (by omega)
    exact AddCommGrpCat.isZero_of_subsingleton _
  have h₁ : Limits.IsZero (AddCommGrpCat.of (TopCat.Sheaf.supportH
      (TopCat.of (ComplexPoint X)) B F (2 * q + 1))) := by
    letI := ccm5_componentBoundary_vanishing_aux X r q x hx hc (2 * q + 1) (by omega)
    exact AddCommGrpCat.isZero_of_subsingleton _
  haveI := CategoryTheory.Sheaf.relH.isIso_restrict_of_isZero F f g (2 * q) h₀ h₁
  have hbij := ConcreteCategory.bijective_of_isIso
    (AddCommGrpCat.ofHom (CategoryTheory.Sheaf.relH.restrict F (f ≫ g) f (𝟙 _) g
      (Subsingleton.elim _ _) (2 * q)))
  have aux (U : Opens (ComplexPoint X)) (hU : U = S.compl)
      (p : S.compl ⟶ ⊤) (hp : p = f ≫ g)
      (f' : U ⟶ B.compl) (a : U ⟶ S.compl) (w : f' ≫ g = a ≫ p) :
      Function.Bijective
        (CategoryTheory.Sheaf.relH.restrict F p f' a g w (2 * q)) := by
    subst U
    subst p
    have ef' : f' = f := Subsingleton.elim _ _
    have ea : a = 𝟙 _ := Subsingleton.elim _ _
    subst f'
    subst a
    exact hbij
  exact aux (S.compl ⊓ B.compl) hinter
    (homOfLE le_top) (Subsingleton.elim _ _)
    (homOfLE inf_le_right) (homOfLE inf_le_left) (Subsingleton.elim _ _)

/-- The component sum on the good open is bijective in every degree.
Source: finite disjoint-support additivity after removing the defined boundary. -/
theorem ccm5_separated_supportSum_bijective_aux
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (r : ℕ) (x : Fin r → X.left) (n : ℕ) :
    Function.Bijective (ccm5_supportSum
      (TopCat.of (ccm5_componentBoundary X r x).compl)
      ((TopCat.Sheaf.constantFunctor
        (TopCat.of (ccm5_componentBoundary X r x).compl)).obj (AddCommGrpCat.of ℚ))
      r (ccm5_separatedComponentSupport X r x) n) := by
  classical
  apply ccm5_disjoint_supportSum_bijective_aux
  intro i j hij
  rw [disjoint_iff]
  apply le_antisymm
  · intro z hz
    have hb : cycleComponentAnalyticClosedSupport X (x i) ⊓
        cycleComponentAnalyticClosedSupport X (x j) ≤ ccm5_componentBoundary X r x := by
      unfold ccm5_componentBoundary
      apply le_sup_of_le_right
      apply le_iSup_of_le i
      apply le_iSup_of_le j
      simp only [ite_eq_right hij, le_refl]
    exact (z.property (hb hz)).elim
  · exact bot_le

/-- The complete inverse support is the union over every nonzero coefficient.
Source: inverse-image ideal support and generic points of irreducible components. -/
theorem ccm5_inverseAnalyticSupport_eq_component_union_aux
    {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) (x : Z.left) :
    (ccm4_inverseAnalyticSupport f (cycleComponentAnalyticClosedSupport Z x) :
        Set (ComplexPoint X)) =
      ⋃ z : {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0},
        (cycleComponentAnalyticClosedSupport X z.1 : Set (ComplexPoint X)) := by
  let I := ccm3_inverseIdeal f.left x
  have hrange : Set.range I.subschemeι = f.left ⁻¹' closure ({x} : Set Z.left) := by
    rw [I.range_subschemeι]
    simp only [I, ccm3_inverseIdeal, Scheme.IdealSheafData.support_comap,
      ccm3_primeIdeal]
    rfl
  ext a
  change f.left a.underlying ∈ closure ({x} : Set Z.left) ↔ _
  constructor
  · intro ha
    have har : a.underlying ∈ Set.range I.subschemeι := by
      rw [hrange]
      exact ha
    obtain ⟨b, hb⟩ := har
    let C := irreducibleComponent b
    have hC : C ∈ irreducibleComponents I.subscheme :=
      irreducibleComponent_mem_irreducibleComponents b
    let y := hC.1.genericPoint
    have hy : closure ({y} : Set I.subscheme) = C :=
      hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
    have hz : ccm3_flatPullbackPrime f.left x (I.subschemeι y) ≠ 0 :=
      (ccm3_flatPullbackPrime_support f x _).mpr ⟨y, rfl, hy ▸ hC⟩
    apply Set.mem_iUnion.mpr
    refine ⟨⟨I.subschemeι y, hz⟩, ?_⟩
    change a.underlying ∈ closure ({I.subschemeι y} : Set X.left)
    rw [← hb]
    have hbc : b ∈ closure ({y} : Set I.subscheme) := hy.symm ▸ mem_irreducibleComponent
    have him := image_closure_subset_closure_image I.subschemeι.continuous
      (s := ({y} : Set I.subscheme))
    simpa only [Set.image_singleton] using him ⟨b, hbc, rfl⟩
  · intro ha
    obtain ⟨z, hz⟩ := Set.mem_iUnion.mp ha
    obtain ⟨y, heq, hy⟩ := (ccm3_flatPullbackPrime_support f x z.1).mp z.2
    change a.underlying ∈ closure ({z.1} : Set X.left) at hz
    have hclosed : IsClosed (f.left ⁻¹' closure ({x} : Set Z.left)) :=
      isClosed_closure.preimage f.left.continuous
    apply (hclosed.closure_subset_iff.mpr ?_) hz
    rw [Set.singleton_subset_iff, ← heq, ← hrange]
    exact ⟨y, rfl⟩




/-- The finite enumeration covers the entire inverse analytic support.
Source: generic-component support union and `ccm5_primeEnumeration`. -/
theorem ccm5_inverseAnalyticSupport_eq_enumerated_union_aux
    {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) (x : Z.left) :
    (ccm4_inverseAnalyticSupport f (cycleComponentAnalyticClosedSupport Z x) :
        Set (ComplexPoint X)) =
      ⋃ i, (cycleComponentAnalyticClosedSupport X
        (ccm5_primeEnumeration f x i).1 : Set (ComplexPoint X)) := by
  rw [ccm5_inverseAnalyticSupport_eq_component_union_aux]
  ext a
  constructor
  · intro ha
    obtain ⟨z, hz⟩ := Set.mem_iUnion.mp ha
    exact Set.mem_iUnion.mpr ⟨(ccm5_primeEnumeration f x).symm z, by
      simpa only [Equiv.apply_symm_apply] using hz⟩
  · intro ha
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ha
    exact Set.mem_iUnion.mpr ⟨ccm5_primeEnumeration f x i, hi⟩

local instance ccm5_relHGroup (T : TopCat.{0}) (F : TopCat.Sheaf AddCommGrpCat T)
    (U V : Opens T) (f : U ⟶ V) (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.relH F n f) :=
  CategoryTheory.Abelian.Ext.instAddCommGroup

/-- Restriction of supported cohomology to an ambient open.
Source: `CategoryTheory.Sheaf.relH.restrict`. -/
def ccm5_supportOpenRestriction (T : TopCat.{0})
    (F : TopCat.Sheaf AddCommGrpCat T) (S : Closeds T) (U : Opens T) (n : ℕ) :=
  CategoryTheory.Sheaf.relH.restrict F
    (homOfLE (show S.compl ≤ ⊤ from le_top))
    (homOfLE (show S.compl ⊓ U ≤ U from inf_le_right))
    (homOfLE inf_le_left) (homOfLE le_top) (Subsingleton.elim _ _) n

example (T : TopCat.{0}) (F : TopCat.Sheaf AddCommGrpCat T)
    (S : Closeds T) (U : Opens T) (n : ℕ) :
    ccm5_supportOpenRestriction T F S U n 0 = 0 := map_zero _

/-- The component restriction is the ambient-open restriction of its support union. -/
theorem ccm5_componentRestriction_eq_openRestriction
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (r : ℕ) (x : Fin r → X.left) (n : ℕ) :
    HEq (ccm5_componentRestriction X r x n)
      (ccm5_supportOpenRestriction (TopCat.of (ComplexPoint X))
        ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
          (AddCommGrpCat.of ℚ))
        (⨆ i, cycleComponentAnalyticClosedSupport X (x i))
        (ccm5_componentBoundary X r x).compl n) := by
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Restricting an ambient open commutes with enlarging its closed support. -/
theorem ccm5_supportOpenRestriction_enlarge (T : TopCat.{0})
    (F : TopCat.Sheaf AddCommGrpCat T) {S S' : Closeds T} (h : S ≤ S')
    (U : Opens T) (n : ℕ) (z : TopCat.Sheaf.supportH T S F n) :
    ccm5_supportOpenRestriction T F S' U n
      (CategoryTheory.Sheaf.relH.restrict F
        (homOfLE (show S.compl ≤ ⊤ from le_top))
        (homOfLE (show S'.compl ≤ ⊤ from le_top))
        (homOfLE (show S'.compl ≤ S.compl from fun _ hz hs => hz (h hs)))
        (𝟙 _) (Subsingleton.elim _ _) n z) =
      CategoryTheory.Sheaf.relH.restrict F
        (homOfLE (show S.compl ⊓ U ≤ U from inf_le_right))
        (homOfLE (show S'.compl ⊓ U ≤ U from inf_le_right))
        (homOfLE (inf_le_inf_right U
          (show S'.compl ≤ S.compl from fun _ hz hs => hz (h hs))))
        (𝟙 _) (Subsingleton.elim _ _) n
        (ccm5_supportOpenRestriction T F S U n z) := by
  unfold ccm5_supportOpenRestriction CategoryTheory.Sheaf.relH.restrict
  change (CategoryTheory.Abelian.Ext.mk₀ _).comp
      ((CategoryTheory.Abelian.Ext.mk₀ _).comp z (zero_add n)) (zero_add n) =
    (CategoryTheory.Abelian.Ext.mk₀ _).comp
      ((CategoryTheory.Abelian.Ext.mk₀ _).comp z (zero_add n)) (zero_add n)
  rw [CategoryTheory.Abelian.Ext.mk₀_comp_mk₀_assoc,
    CategoryTheory.Abelian.Ext.mk₀_comp_mk₀_assoc,
    ← CategoryTheory.Sheaf.pairSheafMap_comp,
    ← CategoryTheory.Sheaf.pairSheafMap_comp]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The supported injective-to-singular comparison respects restriction of the ambient open. -/
theorem ccm5_injectiveSectionEquiv_restrict
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S : Closeds (ComplexPoint X)) {U V : Opens (ComplexPoint X)}
    (h : U ≤ V) (n : ℕ)
    (z : (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) V).mapHomologicalComplex
      ℤᵘᵖ).obj (complexSupportInjectiveComplex X S)).homology (n : ℤ)) :
    complexSupportInjectiveSectionCohomologyEquiv X S U n
      (HomologicalComplex.homologyMap
        (TopCat.Sheaf.sectionComplexRestriction (TopCat.of (ComplexPoint X)) ℤᵘᵖ
          (complexSupportInjectiveComplex X S) (homOfLE h)) (n : ℤ) z) =
      relativeCohomologyMap ℚ n (neighborhoodSupportInclusionPairMap h (S : Set _))
        (complexSupportInjectiveSectionCohomologyEquiv X S V n z) := by
  let : ∀ W : Opens (ComplexPoint X), ParacompactSpace W := openParacompactSpace X
  let eU := complexSupportedSingularInjectiveHomologyIso X S.compl U (n : ℤ)
  let eV := complexSupportedSingularInjectiveHomologyIso X S.compl V (n : ℤ)
  have hn : HomologicalComplex.homologyMap
        (TopCat.Sheaf.sectionComplexRestriction (TopCat.of (ComplexPoint X)) ℤᵘᵖ
          (supportedRationalSingularCochainComplex (TopCat.of (ComplexPoint X)) S.compl)
          (homOfLE h)) (n : ℤ) ≫ eU.hom =
      eV.hom ≫ HomologicalComplex.homologyMap
        (TopCat.Sheaf.sectionComplexRestriction (TopCat.of (ComplexPoint X)) ℤᵘᵖ
          (complexSupportInjectiveComplex X S) (homOfLE h)) (n : ℤ) := by
    change HomologicalComplex.homologyMap _ _ ≫ HomologicalComplex.homologyMap _ _ =
      HomologicalComplex.homologyMap _ _ ≫ HomologicalComplex.homologyMap _ _
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp]
    congr 1
    exact (((TopCat.Sheaf.supportEvaluationRestriction (TopCat.of (ComplexPoint X))
      (homOfLE h)).mapHomologicalComplex ℤᵘᵖ).naturality
      (complexSupportedSingularToAmbientInjective X S.compl)).symm
  have hi : (HomologicalComplex.homologyMap
        (TopCat.Sheaf.sectionComplexRestriction (TopCat.of (ComplexPoint X)) ℤᵘᵖ
          (complexSupportInjectiveComplex X S) (homOfLE h)) (n : ℤ)) ≫ eU.inv =
      eV.inv ≫ HomologicalComplex.homologyMap
        (TopCat.Sheaf.sectionComplexRestriction (TopCat.of (ComplexPoint X)) ℤᵘᵖ
          (supportedRationalSingularCochainComplex (TopCat.of (ComplexPoint X)) S.compl)
          (homOfLE h)) (n : ℤ) := by
    apply (cancel_mono eU.hom).1
    simp only [Category.assoc, eU.inv_hom_id, hn,
      Iso.inv_hom_id_assoc]
    exact Category.comp_id _
  change supportedRationalSingularSectionCohomologyEquivSupportComplement
      (TopCat.of (ComplexPoint X)) S S.isClosed U n (eU.inv _) = _
  have hi' := ConcreteCategory.congr_hom hi z
  change eU.inv (HomologicalComplex.homologyMap
      (TopCat.Sheaf.sectionComplexRestriction (TopCat.of (ComplexPoint X)) ℤᵘᵖ
        (complexSupportInjectiveComplex X S) (homOfLE h)) (n : ℤ) z) =
    HomologicalComplex.homologyMap
      (TopCat.Sheaf.sectionComplexRestriction (TopCat.of (ComplexPoint X)) ℤᵘᵖ
        (supportedRationalSingularCochainComplex (TopCat.of (ComplexPoint X)) S.compl)
        (homOfLE h)) (n : ℤ) (eV.inv z) at hi'
  rw [hi']
  exact supportedRationalSingularSectionCohomologyEquivSupportComplement_naturality
    (TopCat.of (ComplexPoint X)) S S.isClosed (homOfLE h) n _

/-- Relative Ext on an ambient open, compared with relative singular cohomology.
Source: `relHAddEquivSupportedSectionsHomology` and
`complexSupportInjectiveSectionCohomologyEquiv`. -/
def ccm5_supportedSingularClassOnOpen
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S : Closeds (ComplexPoint X)) (U : Opens (ComplexPoint X)) (n : ℕ) :=
  (@TopCat.Sheaf.relHAddEquivSupportedSectionsHomology
    (TopCat.of (ComplexPoint X)) S.compl U (S.compl ⊓ U) (inf_comm _ _) inferInstance
    ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ))
    (ambientRationalInjectiveComplex X) (ambientRationalInjectiveComplex_isKInjective X)
    (ambientRationalInjectiveSingleAugmentation X)
    (ambientRationalInjectiveSingleAugmentation_quasiIso X) n).trans
      (complexSupportInjectiveSectionCohomologyEquiv X S U n)

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S : Closeds (ComplexPoint X)) (U : Opens (ComplexPoint X)) (n : ℕ) :
    Function.Bijective (ccm5_supportedSingularClassOnOpen X S U n) :=
  (ccm5_supportedSingularClassOnOpen X S U n).bijective

set_option maxHeartbeats 400000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Restricting a supported class agrees with restricting its relative singular class. -/
theorem ccm5_supportedSingularClassOnOpen_restrict
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S : Closeds (ComplexPoint X)) (U : Opens (ComplexPoint X)) (n : ℕ)
    (z : TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X)) S
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
        (AddCommGrpCat.of ℚ)) n) :
    ccm5_supportedSingularClassOnOpen X S U n
      (ccm5_supportOpenRestriction (TopCat.of (ComplexPoint X))
        ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
          (AddCommGrpCat.of ℚ)) S U n z) =
      relativeCohomologyMap ℚ n
        (neighborhoodSupportInclusionPairMap (show U ≤ ⊤ from le_top) (S : Set _))
        (supportedSingularClass X S n z) := by
  have := ambientRationalInjectiveComplex_isKInjective X
  have := ambientRationalInjectiveSingleAugmentation_quasiIso X
  have h := TopCat.Sheaf.relHAddEquivSupportedSectionsHomology_restrict
    (TopCat.of (ComplexPoint X)) (top_inf_eq S.compl) (inf_comm U S.compl)
    (le_refl S.compl) (show U ≤ ⊤ from le_top) (inf_le_left : S.compl ⊓ U ≤ S.compl)
    ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj (AddCommGrpCat.of ℚ))
    (ambientRationalInjectiveComplex X) (ambientRationalInjectiveSingleAugmentation X) n z
  rw [TopCat.Sheaf.supportedSectionsRestriction_refl] at h
  dsimp only [ccm5_supportedSingularClassOnOpen, AddEquiv.trans_apply,
    supportedSingularClass, rationalSupportAddEquivSupportedInjectiveHomology]
  exact (congrArg (complexSupportInjectiveSectionCohomologyEquiv X S U n) h).trans
    (ccm5_injectiveSectionEquiv_restrict X S (U := U) (V := ⊤) le_top n
      (rationalSupportAddEquivSupportedInjectiveHomology X S n z))

/-- The ambient germ factors through the relative Ext restriction on any containing open. -/
theorem ccm5_supportGerm_via_openRestriction
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S : Closeds (ComplexPoint X)) (U : Opens (ComplexPoint X)) (n : ℕ)
    (a : ComplexPoint X) (ha : a ∈ U)
    (z : TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X)) S
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
        (AddCommGrpCat.of ℚ)) n) :
    supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X)) (S : Set _) n U a ha
      (ccm5_supportedSingularClassOnOpen X S U n
        (ccm5_supportOpenRestriction (TopCat.of (ComplexPoint X))
          ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
            (AddCommGrpCat.of ℚ)) S U n z)) = ccm5_supportGerm X S n a z := by
  rw [ccm5_supportedSingularClassOnOpen_restrict]
  exact supportRelativeCohomologyGerm_restrict (TopCat.of (ComplexPoint X))
    (S : Set _) n (U := U) (V := ⊤) le_top a ha (supportedSingularClass X S n z)

open CategoryTheory.Limits Opposite TopCat.Sheaf in
/-- Lower cohomology-sheaf vanishing makes the section cohomology presheaf a sheaf. -/
theorem ccm5_sectionCohomology_isSheaf_lowest (T : TopCat.{0})
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat T) ℤ)
    (N n : ℤ) [K.IsStrictlyGE N]
    (hK : ∀ j, j < n → IsZero (K.homology j))
    (hflasque : ∀ j, (K.X j).IsFlasque) :
    CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology T)
      (sectionCohomologyPresheaf T K n) := by
  have hi (V : (Opens T)ᵒᵖ) :
      IsIso ((sectionCohomologyPresheafToSheaf T K n).app V) := by
    let := sectionCohomologyToSheafSection_isIso_lowest T K N n hK hflasque V.unop
    change IsIso ((sectionCohomologyPresheafOnOpenIso T K n V.unop).hom ≫
      (sectionCohomologyPresheafToSheaf T K n).app V) at this
    exact IsIso.of_isIso_comp_left (sectionCohomologyPresheafOnOpenIso T K n V.unop).hom _
  let := NatIso.isIso_of_isIso_app (sectionCohomologyPresheafToSheaf T K n)
  exact (CategoryTheory.Presheaf.isSheaf_of_iso_iff
    (asIso (sectionCohomologyPresheafToSheaf T K n))).mpr (K.homology n).property

open CategoryTheory.Limits Opposite TopCat.Sheaf in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Lower vanishing on an open makes its restricted section cohomology presheaf a sheaf. -/
theorem ccm5_restrictedSectionCohomology_isSheaf_lowest (T : TopCat.{0})
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat T) ℤ)
    (U : Opens T) (N n : ℤ) [K.IsStrictlyGE N]
    (hK : ∀ j, j < n → IsZero
      ((((U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapHomologicalComplex
        ℤᵘᵖ).obj K).homology j))
    (hflasque : ∀ j, (K.X j).IsFlasque) :
    CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology (TopCat.of U))
      (U.isOpenEmbedding.functor.op ⋙ sectionCohomologyPresheaf T K n) := by
  let L := ((U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapHomologicalComplex ℤᵘᵖ).obj K
  have hL : ∀ j, (L.X j).IsFlasque := fun j => by
    let := hflasque j
    exact openSheafRestriction_isFlasque T U (K.X j)
  let P := ((TopCat.Sheaf.forget AddCommGrpCat T).mapHomologicalComplex ℤᵘᵖ).obj K
  let W := (Functor.whiskeringLeft (Opens (TopCat.of U))ᵒᵖ (Opens T)ᵒᵖ AddCommGrpCat).obj
    U.isOpenEmbedding.functor.op
  let : W.PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  let : PreservesFiniteLimits W := by dsimp [W]; infer_instance
  let : PreservesFiniteColimits W := by dsimp [W]; infer_instance
  let : W.PreservesHomology := inferInstance
  let e : U.isOpenEmbedding.functor.op ⋙ sectionCohomologyPresheaf T K n ≅
      sectionCohomologyPresheaf (TopCat.of U) L n :=
    ((P.sc n).mapHomologyIso W).symm
  exact (CategoryTheory.Presheaf.isSheaf_of_iso_iff e).mpr
    (ccm5_sectionCohomology_isSheaf_lowest (TopCat.of U) L N n hK hL)

open CategoryTheory.Limits Opposite TopCat.Sheaf in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A presheaf already satisfying the sheaf condition on an open has an invertible unit there. -/
theorem ccm5_toSheafify_app_isIso_onOpen (T : TopCat.{0})
    (P : TopCat.Presheaf AddCommGrpCat T) (U : Opens T)
    (hP : CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology (TopCat.of U))
      (U.isOpenEmbedding.functor.op ⋙ P)) :
    IsIso ((toSheafify (Opens.grothendieckTopology T) P).app (op U)) := by
  let := isIso_toSheafify (Opens.grothendieckTopology (TopCat.of U)) hP
  have h := congr_app (toSheafify_openRestrictionSheafificationIso T U P) (op ⊤)
  have hi : IsIso ((toSheafify (Opens.grothendieckTopology T) P).app
      (op (U.isOpenEmbedding.functor.obj ⊤))) := by
    change IsIso ((Functor.whiskerLeft U.isOpenEmbedding.functor.op
      (toSheafify (Opens.grothendieckTopology T) P)).app (op ⊤))
    rw [← h]
    change IsIso ((toSheafify (Opens.grothendieckTopology (TopCat.of U))
      (U.isOpenEmbedding.functor.op ⋙ P)).app (op ⊤) ≫
      (openRestrictionSheafificationIso T U P).hom.hom.app (op ⊤))
    infer_instance
  rwa [Opens.isOpenEmbedding_obj_top] at hi

open CategoryTheory.Limits Opposite TopCat.Sheaf in
set_option maxHeartbeats 400000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Lower local supported cohomology vanishing makes the relative class map invertible on an open. -/
theorem ccm5_relativeToSheaf_isIso_of_lowerVanishing
    (T : TopCat.{0}) [T2Space T] [∀ V : Opens T, ParacompactSpace V]
    (S : Closeds T) (U : Opens T) (n : ℕ)
    (hH : ∀ j : ℕ, j < n → IsZero
      ((U.isOpenEmbedding.sheafPullback AddCommGrpCat).obj
        (supportRelativeCohomologySheaf T S j))) :
    IsIso (C := AddCommGrpCat) ((toSheafify (Opens.grothendieckTopology T)
      (supportRelativeCohomologyPresheaf T S n)).app (op U)) := by
  let K := supportedRationalSingularCochainComplex T S.compl
  let : K.IsStrictlyGE 0 := by
    dsimp only [K, supportedRationalSingularCochainComplex]
    infer_instance
  have hK : ∀ j : ℤ, j < (n : ℤ) → IsZero
      ((((U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapHomologicalComplex
        ℤᵘᵖ).obj K).homology j) :=
    openRestrictedLowestSectionCohomologyIsoOfNat_isZero T U K
      (fun j => supportRelativeCohomologySheaf T S j)
      (fun j => supportedSingularCohomologySheafIsoRelative T S S.isClosed j) n hH
  have hflasque (j : ℤ) : (K.X j).IsFlasque :=
    sheafSectionsSupportedOutside_isFlasque T S.compl ((rationalSingularCochainComplex T).X j)
  have hP := ccm5_restrictedSectionCohomology_isSheaf_lowest T K U 0 n hK hflasque
  have hR : CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology (TopCat.of U))
      (U.isOpenEmbedding.functor.op ⋙ supportRelativeCohomologyPresheaf T S n) :=
    (CategoryTheory.Presheaf.isSheaf_of_iso_iff
      (Functor.isoWhiskerLeft U.isOpenEmbedding.functor.op
        (supportedSingularCohomologyPresheafIsoRelative T S S.isClosed n))).mp hP
  exact ccm5_toSheafify_app_isIso_onOpen T (supportRelativeCohomologyPresheaf T S n) U hR

open CategoryTheory.Limits Opposite in
/-- In the lowest local degree, relative singular classes on an open are determined by germs. -/
theorem ccm5_relativeGerms_injective_of_lowerVanishing
    (T : TopCat.{0}) [T2Space T] [∀ V : Opens T, ParacompactSpace V]
    (S : Closeds T) (U : Opens T) (n : ℕ)
    (hH : ∀ j : ℕ, j < n → IsZero
      ((U.isOpenEmbedding.sheafPullback AddCommGrpCat).obj
        (supportRelativeCohomologySheaf T S j))) :
    Function.Injective (fun z => fun a : U =>
      supportRelativeCohomologyGerm T S n U a.1 a.2 z) := by
  let := ccm5_relativeToSheaf_isIso_of_lowerVanishing T S U n hH
  intro z z' h
  apply (ConcreteCategory.bijective_of_isIso
    ((toSheafify (Opens.grothendieckTopology T)
      (supportRelativeCohomologyPresheaf T S n)).app (op U))).1
  apply TopCat.Presheaf.section_ext
  intro a ha
  exact congrFun h ⟨a, ha⟩

/-- Membership in a finite supremum of closed sets is membership in one of them. -/
theorem ccm5_mem_finiteClosedSup {T : Type} [TopologicalSpace T]
    {ι : Type} [Finite ι] (S : ι → Closeds T) (a : T) :
    a ∈ (⨆ i, S i) ↔ ∃ i, a ∈ S i := by
  have hclosed : IsClosed (⋃ i, (S i : Set T)) := isClosed_iUnion_of_finite fun i => (S i).isClosed
  constructor
  · intro ha
    have hle : (⨆ i, S i) ≤ (⟨⋃ i, (S i : Set T), hclosed⟩ : Closeds T) := by
      apply iSup_le
      intro i b hb
      exact Set.mem_iUnion.mpr ⟨i, hb⟩
    exact Set.mem_iUnion.mp (hle ha)
  · rintro ⟨i, hi⟩
    exact (le_iSup S i) hi

/-- Near a point lying on only one of finitely many closed supports, the union equals that support. -/
theorem ccm5_finiteSupport_local_eq {T : Type} [TopologicalSpace T]
    {ι : Type} [Finite ι] (S : ι → Closeds T) (i : ι) (a : T)
    (ha : ∀ j, j ≠ i → a ∉ S j) (V : Opens T) (haV : a ∈ V) :
    ∃ W : Opens T, W ≤ V ∧ a ∈ W ∧
      ∀ b ∈ W, (b ∈ (⨆ j, S j) ↔ b ∈ S i) := by
  let C : Closeds T := ⨆ j : {j : ι // j ≠ i}, S j.1
  refine ⟨V ⊓ C.compl, inf_le_left, ⟨haV, ?_⟩, ?_⟩
  · intro h
    obtain ⟨j, hj⟩ := (ccm5_mem_finiteClosedSup _ a).mp h
    exact ha j.1 j.2 hj
  · intro b hb
    constructor
    · intro h
      obtain ⟨j, hj⟩ := (ccm5_mem_finiteClosedSup S b).mp h
      by_cases hji : j = i
      · exact hji ▸ hj
      · exact (hb.2 ((le_iSup (fun j : {j : ι // j ≠ i} => S j.1) ⟨j, hji⟩) hj)).elim
    · intro h
      exact (le_iSup S i) h

/-- Below degree `2q`, the separated component union has vanishing relative classes locally. -/
theorem ccm5_componentUnion_exists_relativeVanishing
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (r q : ℕ) (x : Fin r → X.left) (hc : ∀ i, Order.coheight (x i) = q)
    (n : ℕ) (hn : n < 2 * q)
    (a : ComplexPoint X) (ha : a ∈ (ccm5_componentBoundary X r x).compl)
    (V : Opens (ComplexPoint X)) (haV : a ∈ V) :
    ∃ W : Opens (ComplexPoint X), W ≤ V ∧ a ∈ W ∧
      Subsingleton (RelativeCohomology ℚ
        (neighborhoodSupportComplementPair (W : Set (ComplexPoint X))
          ((⨆ i, cycleComponentAnalyticClosedSupport X (x i) : Closeds (ComplexPoint X)) : Set (ComplexPoint X))) n) := by
  classical
  let S : Fin r → Closeds (ComplexPoint X) := fun i => cycleComponentAnalyticClosedSupport X (x i)
  by_cases haS : a ∈ (⨆ i, S i)
  · obtain ⟨i, hai⟩ := (ccm5_mem_finiteClosedSup S a).mp haS
    have hother : ∀ j, j ≠ i → a ∉ S j := by
      intro j hji haj
      apply ha
      have hle : S i ⊓ S j ≤ ccm5_componentBoundary X r x := by
        unfold ccm5_componentBoundary
        apply le_sup_of_le_right
        apply le_iSup_of_le i
        apply le_iSup_of_le j
        simp only [ite_eq_right (Ne.symm hji), S, le_refl]
      exact hle ⟨hai, haj⟩
    obtain ⟨W, hWV, haW, hW⟩ := ccm5_finiteSupport_local_eq S i a hother V haV
    have hasmooth : a ∈ cycleComponentSmoothSupportAmbientOpen X (x i) := by
      intro hs
      apply ha
      exact (le_sup_of_le_left (le_iSup
        (fun i => cycleComponentSingularAnalyticClosedFiltration X (x i) 0) i)) hs
    obtain ⟨W', hW'W, haW', hvan⟩ :=
      cycleComponentSmoothSupport_exists_relativeCohomology_vanishing X (x i) (hc i)
        a hai hasmooth W haW
    refine ⟨W', hW'W.trans hWV, haW', ?_⟩
    have hp : neighborhoodSupportComplementPair (W' : Set (ComplexPoint X))
        ((⨆ i, S i : Closeds (ComplexPoint X)) : Set (ComplexPoint X)) =
      neighborhoodSupportComplementPair (W' : Set (ComplexPoint X))
        (S i : Set (ComplexPoint X)) := by
      apply congrArg (fun A : Set (W' : Set (ComplexPoint X)) =>
        TopPair.ofSubset (X := TopCat.of (W' : Set (ComplexPoint X))) A)
      ext b
      exact not_congr (hW b.1 (hW'W b.2))
    change Subsingleton (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (W' : Set (ComplexPoint X))
        ((⨆ i, S i : Closeds (ComplexPoint X)) : Set (ComplexPoint X))) n)
    rw [hp]
    exact ModuleCat.subsingleton_of_isZero (hvan n (ne_of_lt hn))
  · let W : Opens (ComplexPoint X) := V ⊓ (⨆ i, S i).compl
    refine ⟨W, inf_le_left, ⟨haV, haS⟩, ?_⟩
    exact neighborhoodSupportRelativeCohomology_subsingleton (TopCat.of (ComplexPoint X))
      ((⨆ i, S i : Closeds (ComplexPoint X)) : Set (ComplexPoint X)) n W (fun _ hb => hb.2)

open CategoryTheory.Limits in
/-- Local purity kills the lower supported cohomology sheaves of the union on the good open. -/
theorem ccm5_componentUnion_lowerSheaf_vanishing
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (r q : ℕ) (x : Fin r → X.left) (hc : ∀ i, Order.coheight (x i) = q)
    (n : ℕ) (hn : n < 2 * q) :
    IsZero ((((ccm5_componentBoundary X r x).compl).isOpenEmbedding.sheafPullback
      AddCommGrpCat).obj
      (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
        ((⨆ i, cycleComponentAnalyticClosedSupport X (x i) : Closeds (ComplexPoint X)) : Set (ComplexPoint X)) n)) := by
  let S : Closeds (ComplexPoint X) := ⨆ i, cycleComponentAnalyticClosedSupport X (x i)
  let U := (ccm5_componentBoundary X r x).compl
  have hI : IsZero ((((U.isOpenEmbedding.sheafPullback AddCommGrpCat).mapHomologicalComplex
      ℤᵘᵖ).obj (complexSupportInjectiveComplex X S)).homology (n : ℤ)) := by
    apply TopCat.Sheaf.openRestriction_homology_isZero_of_cofinal_sections
    intro a ha V haV
    obtain ⟨W, hWV, haW, hW⟩ :=
      ccm5_componentUnion_exists_relativeVanishing X r q x hc n hn a ha V haV
    refine ⟨W, hWV, haW, ?_⟩
    let := hW
    let e := complexSupportInjectiveSectionCohomologyEquiv X S W n
    let := e.injective.subsingleton
    exact AddCommGrpCat.isZero_of_subsingleton _
  exact IsZero.of_iso hI
    (complexSupportInjectiveCohomologySheafIsoRelative_restrict X S U n).symm

/-- Lowest-degree supported classes are detected off the component boundary.
Source: boundary localization, disjoint-support additivity and local purity. -/
theorem ccm5_primeGoodOpen_germs_injective_aux
    {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) [Smooth f.left] (q : ℕ) (x : Z.left)
    (hx : Order.coheight x = q) :
    Function.Injective (fun u => fun a : ccm5_primeGoodOpen f x =>
      ccm5_supportGerm X
        (ccm4_inverseAnalyticSupport f (cycleComponentAnalyticClosedSupport Z x))
        (2 * q) a.1 u) := by
  classical
  let : ∀ V : Opens (ComplexPoint X), ParacompactSpace V := openParacompactSpace X
  let r := Fintype.card {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0}
  let y : Fin r → X.left := fun i => (ccm5_primeEnumeration f x i).1
  let S : Closeds (ComplexPoint X) := ⨆ i, cycleComponentAnalyticClosedSupport X (y i)
  let U := (ccm5_componentBoundary X r y).compl
  have hy : Function.Injective y := by
    intro i j h
    exact (ccm5_primeEnumeration f x).injective (Subtype.ext h)
  have hc : ∀ i, Order.coheight (y i) = q := fun i =>
    ccm3_flatPullbackPrime_codimension f q x hx (y i) (ccm5_primeEnumeration f x i).2
  have hS : ccm4_inverseAnalyticSupport f (cycleComponentAnalyticClosedSupport Z x) = S := by
    apply SetLike.coe_injective
    rw [ccm5_inverseAnalyticSupport_eq_enumerated_union_aux]
    ext a
    exact (Set.mem_iUnion.trans (ccm5_mem_finiteClosedSup
      (fun i => cycleComponentAnalyticClosedSupport X (y i)) a).symm)
  change Function.Injective (fun u => fun a : U =>
    ccm5_supportGerm X
      (ccm4_inverseAnalyticSupport f (cycleComponentAnalyticClosedSupport Z x))
      (2 * q) a.1 u)
  rw [hS]
  intro z z' h
  apply (ccm5_componentRestriction_bijective_aux X r q y hy hc).1
  change ccm5_supportOpenRestriction (TopCat.of (ComplexPoint X))
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
        (AddCommGrpCat.of ℚ)) S U (2 * q) z =
    ccm5_supportOpenRestriction (TopCat.of (ComplexPoint X))
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
        (AddCommGrpCat.of ℚ)) S U (2 * q) z'
  apply (ccm5_supportedSingularClassOnOpen X S U (2 * q)).injective
  apply ccm5_relativeGerms_injective_of_lowerVanishing (TopCat.of (ComplexPoint X)) S U (2 * q)
    (fun j hj => ccm5_componentUnion_lowerSheaf_vanishing X r q y hc j hj)
  funext a
  exact (ccm5_supportGerm_via_openRestriction X S U (2 * q) a.1 a.2 z).trans
    ((congrFun h a).trans
      (ccm5_supportGerm_via_openRestriction X S U (2 * q) a.1 a.2 z').symm)

/-- Restriction preserves the germ at a point of the remaining open.
Source: `supportRelativeCohomologyGerm_restrict`. -/
theorem ccm5_supportGerm_restriction_aux
    (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S : Closeds (ComplexPoint X)) (U : Opens (ComplexPoint X))
    (n : ℕ) (a : ComplexPoint X) (ha : a ∈ U)
    (u : TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X)) S
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
        (AddCommGrpCat.of ℚ)) n) :
    supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
      (S : Set (ComplexPoint X)) n U a ha
      (relativeCohomologyMap ℚ n
        (neighborhoodSupportInclusionPairMap (show (U : Set (ComplexPoint X)) ⊆
          (⊤ : Opens (ComplexPoint X)) from le_top) (S : Set (ComplexPoint X)))
        (supportedSingularClass X S n u)) = ccm5_supportGerm X S n a u := by
  exact supportRelativeCohomologyGerm_restrict (TopCat.of (ComplexPoint X))
    (S : Set (ComplexPoint X)) n (U := U) (V := ⊤) le_top a ha
    (supportedSingularClass X S n u)

/-- Support enlargement commutes with passage to the local relative class.
Source: `supportedSingularClass_restrict`. -/
theorem ccm5_supportGerm_enlarge_aux
    (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {S T : Closeds (ComplexPoint X)} (h : S ≤ T) (n : ℕ) (a : ComplexPoint X)
    (u : TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X)) S
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
        (AddCommGrpCat.of ℚ)) n) :
    ccm5_supportGerm X T n a (supportEnlarge X h n u) =
      supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
        (T : Set (ComplexPoint X)) n ⊤ a (by trivial)
        (relativeCohomologyMap ℚ n
          (neighborhoodSupportEnlargePairMap _ (SetLike.coe_subset_coe.mpr h))
          (supportedSingularClass X S n u)) := by
  change supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
    (T : Set (ComplexPoint X)) n ⊤ a (by trivial)
    (supportedSingularClass X T n (supportEnlarge X h n u)) = _
  rw [supportedSingularClass_restrict]

/-- The extended component class has its normalized smooth coclass germ.
Source: component normalization and naturality of the supported singular comparison. -/
theorem ccm5_componentClass_normalized_germ_aux
    (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (q : ℕ) (x : X.left) (hx : Order.coheight x = q)
    (a : ComplexPoint X) (ha : a ∈ cycleComponentSmoothSupportAmbientOpen X x) :
    ccm5_supportGerm X (cycleComponentAnalyticClosedSupport X x) (2 * q) a
      (cycleComponentSupportedInjectiveClass X x hx) =
      (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
        (cycleComponentSupport X x) (2 * q)).presheaf.germ
        (cycleComponentSmoothSupportAmbientOpen X x) a ha
        (cycleComponentSmoothSupportCoclassSection X x hx) := by
  change (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
      (cycleComponentSupport X x) (2 * q)).presheaf.germ ⊤ a (by trivial)
      ((supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X))
        (cycleComponentSupport X x) (2 * q)).app (Opposite.op ⊤)
        (complexSupportInjectiveSectionCohomologyEquiv X
          (cycleComponentAnalyticClosedSupport X x) ⊤ (2 * q)
          (rationalSupportAddEquivSupportedInjectiveHomology X
            (cycleComponentAnalyticClosedSupport X x) (2 * q)
            (cycleComponentSupportedInjectiveClass X x hx)))) = _
  rw [← cycleComponentSupportedInjectiveClass_normalization]
  change _ = (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
    (cycleComponentSupport X x) (2 * q)).presheaf.germ
      (cycleComponentSmoothSupportAmbientOpen X x) a ha
      (cycleComponentSupportedClassNormalizationIso X x hx
        (cycleComponentSupportedInjectiveClass X x hx))
  rw [cycleComponentSupportedClassNormalizationIso_eq_restrict]
  have h := TopCat.Presheaf.germ_res
    (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
      (cycleComponentSupport X x) (2 * q)).presheaf
    (homOfLE (show cycleComponentSmoothSupportAmbientOpen X x ≤ ⊤ from le_top)) a ha
  exact ConcreteCategory.congr_hom h.symm _

open scoped TensorProduct in
private theorem ccm5_flat_unramified_reduced_domain
    (R A : Type*) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] [Module.Flat R A] [Algebra.FormallyUnramified R A] :
    _root_.IsReduced A := by
  let K := FractionRing R
  have : _root_.IsReduced (K ⊗[R] A) := Algebra.FormallyUnramified.isReduced_of_field K _
  exact isReduced_of_injective (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A)
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective R K))

private theorem ccm5_smooth_reduced_domain
    (R A : Type*) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]
    [Algebra.Smooth R A] : _root_.IsReduced A := by
  constructor
  intro u hu
  apply eq_zero_of_localization u
  intro p hp
  letI := hp
  obtain ⟨g, hg, n, hAlg, hTower, hEtale⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R) (p := p)
  letI := hAlg
  letI := hTower
  letI := hEtale
  have : _root_.IsReduced (Localization.Away g) :=
    ccm5_flat_unramified_reduced_domain (MvPolynomial (Fin n) R) _
  have hz := (hu.map (algebraMap A (Localization.Away g))).eq_zero
  obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers g)
    (Localization.Away g) u).mp hz
  obtain ⟨k, hk⟩ := m.property
  apply (IsLocalization.map_eq_zero_iff p.primeCompl (Localization.AtPrime p) u).mpr
  refine ⟨⟨m, ?_⟩, hm⟩
  change (m : A) ∉ p
  rw [← hk]
  exact p.primeCompl.pow_mem hg k

private theorem ccm5_smooth_reduced_integral {X Y : Scheme} (f : X ⟶ Y)
    [IsIntegral Y] [Smooth f] : AlgebraicGeometry.IsReduced X := by
  apply +allowSynthFailures isReduced_of_isReduced_stalk
  intro x
  obtain ⟨U, hU, V, hV, hxV, e, _⟩ := Smooth.exists_isStandardSmooth f x
  have : Nonempty U := ⟨⟨f x, e hxV⟩⟩
  algebraize [(f.appLE U V e).hom]
  have : Algebra.Smooth Γ(Y, U) Γ(X, V) := by
    rw [← RingHom.smooth_algebraMap]
    exact f.smooth_appLE hU hV e
  have : _root_.IsReduced Γ(X, V) := ccm5_smooth_reduced_domain Γ(Y, U) Γ(X, V)
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxV⟩ : V)
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  exact isReduced_localizationPreserves (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl
    (X.presheaf.stalk x) inferInstance

private theorem ccm5_inverseIdeal_isReduced {X Z : Scheme}
    (f : X ⟶ Z) [Smooth f] (x : Z) :
    IsReduced (ccm3_inverseIdeal f x).subscheme := by
  have : IsIntegral (ccm3_primeIdeal Z x).subscheme :=
    inferInstanceAs (IsIntegral (cycleComponent Z x))
  have : IsReduced (CategoryTheory.Limits.pullback f
      (ccm3_primeIdeal Z x).subschemeι) :=
    ccm5_smooth_reduced_integral (CategoryTheory.Limits.pullback.snd _ _)
  exact ObjectProperty.prop_of_iso (fun Y : Scheme => IsReduced Y)
    ((ccm3_primeIdeal Z x).comapIso f).symm inferInstance

private theorem ccm5_genericLength_eq_one_of_isReduced {X Z : Scheme}
    (f : X ⟶ Z) (x : Z) [IsReduced (ccm3_inverseIdeal f x).subscheme]
    (y : (ccm3_inverseIdeal f x).subscheme)
    (hy : closure ({y} : Set (ccm3_inverseIdeal f x).subscheme) ∈
      irreducibleComponents (ccm3_inverseIdeal f x).subscheme) :
    ccm3_genericLength f x y = 1 := by
  have hfield := isField_stalk_of_closure_mem_irreducibleComponents
    (ccm3_inverseIdeal f x).subscheme y hy
  letI := hfield.toField
  exact Module.length_eq_one _ _

private theorem ccm5_flatPullbackPrime_coeff_eq_one_of_isReduced
    {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Z) (x : Z.left) [IsReduced (ccm3_inverseIdeal f.left x).subscheme]
    (z : X.left) (hz : ccm3_flatPullbackPrime f.left x z ≠ 0) :
    ccm3_flatPullbackPrime f.left x z = 1 := by
  obtain ⟨y, rfl, hy⟩ := (ccm3_flatPullbackPrime_support f x z).mp hz
  rw [ccm3_flatPullbackPrime_coeff f x y hy,
    ccm5_genericLength_eq_one_of_isReduced f.left x y hy]
  rfl

private theorem ccm5_flatPullbackPrime_coeff_eq_one_of_smooth
    {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom]
    (f : X ⟶ Z) [Smooth f.left] (x : Z.left)
    (z : X.left) (hz : ccm3_flatPullbackPrime f.left x z ≠ 0) :
    ccm3_flatPullbackPrime f.left x z = 1 := by
  have := ccm5_inverseIdeal_isReduced f.left x
  exact ccm5_flatPullbackPrime_coeff_eq_one_of_isReduced f x z hz

private theorem ccm5_chartNormalProjectionCoclass_pullback
    {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
    (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (c : ℕ)
    (e : OpenPartialHomeomorph M (E × (Fin c → ℂ)))
    (d : OpenPartialHomeomorph N (F × (Fin c → ℂ)))
    (S : Set M) (T : Set N)
    (hS : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (hT : ∀ y ∈ d.source, y ∈ T ↔ (d y).2 = 0)
    (V : Set M) (W : Set N) (hV : V ⊆ e.source) (hW : W ⊆ d.source)
    (φ : neighborhoodSupportComplementPair V S ⟶ neighborhoodSupportComplementPair W T)
    (hφ : ∀ y : V, (d (TopPair.Hom.fst φ y).1).2 = (e y.1).2) :
    relativeCohomologyMap ℚ (2 * c) φ
      (chartNormalProjectionCoclass F c d T hT W hW) =
        chartNormalProjectionCoclass E c e S hS V hV := by
  have hcomp : φ ≫ chartNormalProjectionPair F c d T hT W hW =
      chartNormalProjectionPair E c e S hS V hV := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext y
      apply Subtype.ext
      change (d (TopPair.Hom.snd φ y).1.1).2 = (e y.1.1).2
      have hw : (TopPair.Hom.snd φ y).1 = TopPair.Hom.fst φ y.1 :=
        TopPair.Hom.w_apply φ y
      rw [hw]
      exact hφ y.1
    · ext y
      exact hφ y
  unfold chartNormalProjectionCoclass
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp, hcomp]

private theorem ccm5_splitSubmersion_support_chart
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    {g : E → F} {A : E →L[ℂ] F} {a : E}
    (hg : HasStrictFDerivAt g A a) (B : F →L[ℂ] E)
    (hAB : A.comp B = ContinuousLinearMap.id ℂ F) :
    ∃ e : OpenPartialHomeomorph E (F × A.ker),
      a ∈ e.source ∧ (∀ y : E, (e y).1 = g y) ∧
      ∀ S : Set F, e '' (e.source ∩ g ⁻¹' S) =
        e.target ∩ S ×ˢ (Set.univ : Set A.ker) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℂ E
  let L := (B.splitKernelEquiv A hAB).symm
  let K : E →L[ℂ] A.ker :=
    (ContinuousLinearMap.snd ℂ F A.ker).comp L.toContinuousLinearMap
  have hd : HasStrictFDerivAt (fun y => (g y, K y)) L.toContinuousLinearMap a := by
    convert hg.prodMk K.hasStrictFDerivAt using 1
    ext y <;> rfl
  let e := hd.toOpenPartialHomeomorph _
  have ha : a ∈ e.source := hd.mem_toOpenPartialHomeomorph_source
  have he : ∀ y : E, (e y).1 = g y := fun _ => rfl
  refine ⟨e, ha, he, fun S => ?_⟩
  ext w
  constructor
  · rintro ⟨y, ⟨hy, hS⟩, rfl⟩
    exact ⟨e.map_source hy, (he y).symm ▸ hS, Set.mem_univ _⟩
  · rintro ⟨hw, hS, _⟩
    refine ⟨e.symm w, ⟨e.map_target hw, ?_⟩, e.right_inv hw⟩
    change g (e.symm w) ∈ S
    rw [← he, e.right_inv hw]
    exact hS

private theorem ccm5_primeGoodOpen_mem_smoothSupport
    {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) (x : Z.left) (a : ccm5_primeGoodOpen f x)
    (i : Fin (Fintype.card {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0})) :
    a.1 ∈ cycleComponentSmoothSupportAmbientOpen X (ccm5_primeEnumeration f x i).1 := by
  intro ha
  apply a.2
  unfold ccm5_primeGoodOpen ccm5_componentBoundary
  exact (le_sup_of_le_left (le_iSup (fun i =>
    cycleComponentSingularAnalyticClosedFiltration X
      (ccm5_primeEnumeration f x i).1 0) i)) ha

private theorem ccm5_primeGoodOpen_component_disjoint
    {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) (x : Z.left) (a : ccm5_primeGoodOpen f x)
    (i j : Fin (Fintype.card {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0}))
    (hij : i ≠ j) :
    a.1 ∈ cycleComponentAnalyticClosedSupport X (ccm5_primeEnumeration f x i).1 →
      a.1 ∉ cycleComponentAnalyticClosedSupport X (ccm5_primeEnumeration f x j).1 := by
  intro hi hj
  apply a.2
  unfold ccm5_primeGoodOpen ccm5_componentBoundary
  have hle : cycleComponentAnalyticClosedSupport X (ccm5_primeEnumeration f x i).1 ⊓
      cycleComponentAnalyticClosedSupport X (ccm5_primeEnumeration f x j).1 ≤
      (⨆ i, ⨆ j, if i = j then ⊥ else
        cycleComponentAnalyticClosedSupport X (ccm5_primeEnumeration f x i).1 ⊓
          cycleComponentAnalyticClosedSupport X (ccm5_primeEnumeration f x j).1) := by
    apply le_iSup_of_le i
    apply le_iSup_of_le j
    rw [if_neg hij]
  exact (le_sup_of_le_right hle) ⟨hi, hj⟩

private theorem ccm5_primeGoodOpen_unique_component
    {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) (x : Z.left) (a : ccm5_primeGoodOpen f x)
    (ha : a.1 ∈ ccm4_inverseAnalyticSupport f (cycleComponentAnalyticClosedSupport Z x)) :
    ∃! z : {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0},
      a.1 ∈ cycleComponentAnalyticClosedSupport X z.1 := by
  change a.1 ∈ (ccm4_inverseAnalyticSupport f
    (cycleComponentAnalyticClosedSupport Z x) : Set (ComplexPoint X)) at ha
  rw [ccm5_inverseAnalyticSupport_eq_component_union_aux] at ha
  obtain ⟨z, hz⟩ := Set.mem_iUnion.mp ha
  refine ⟨z, hz, fun w hw => ?_⟩
  by_contra hne
  have hij : (ccm5_primeEnumeration f x).symm z ≠
      (ccm5_primeEnumeration f x).symm w := by
    intro h
    exact hne ((ccm5_primeEnumeration f x).symm.injective h).symm
  have h := ccm5_primeGoodOpen_component_disjoint f x a _ _ hij
  simp only [Equiv.apply_symm_apply] at h
  exact h hz hw

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem ccm5_supportGerm_enlarge_eq_zero_of_not_mem
    (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {S T : Closeds (ComplexPoint X)} (h : S ≤ T) (n : ℕ)
    (a : ComplexPoint X) (ha : a ∉ S)
    (u : TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X)) S
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
        (AddCommGrpCat.of ℚ)) n) :
    ccm5_supportGerm X T n a (supportEnlarge X h n u) = 0 := by
  rw [ccm5_supportGerm_enlarge_aux]
  let W : Opens (ComplexPoint X) := S.compl
  have haW : a ∈ W := ha
  have hW : W ≤ ⊤ := le_top
  rw [← supportRelativeCohomologyGerm_restrict (TopCat.of (ComplexPoint X))
    (T : Set (ComplexPoint X)) n hW a haW]
  have hcomp :
      neighborhoodSupportInclusionPairMap (show (W : Set (ComplexPoint X)) ⊆
        (⊤ : Opens (ComplexPoint X)) from hW) (T : Set (ComplexPoint X)) ≫
        neighborhoodSupportEnlargePairMap _ (SetLike.coe_subset_coe.mpr h) =
      neighborhoodSupportEnlargePairMap (W : Set (ComplexPoint X))
        (SetLike.coe_subset_coe.mpr h) ≫
        neighborhoodSupportInclusionPairMap (show (W : Set (ComplexPoint X)) ⊆
          (⊤ : Opens (ComplexPoint X)) from hW) (S : Set (ComplexPoint X)) := by
    apply MorphismProperty.Arrow.Hom.ext <;> rfl
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp, hcomp,
    relativeCohomologyMap_comp, LinearMap.comp_apply]
  let := neighborhoodSupportRelativeCohomology_subsingleton
    (TopCat.of (ComplexPoint X)) (S : Set (ComplexPoint X)) n W (fun _ hy => hy)
  have hz : relativeCohomologyMap ℚ n
      (neighborhoodSupportInclusionPairMap (show (W : Set (ComplexPoint X)) ⊆
        (⊤ : Opens (ComplexPoint X)) from hW) (S : Set (ComplexPoint X)))
      (supportedSingularClass X S n u) = 0 := Subsingleton.elim _ _
  rw [hz, map_zero]
  simp only [supportRelativeCohomologyGerm, map_zero]

private theorem ccm5_analytic_splitSubmersion_support_chart
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F]
    {g : E → F} {a : E} (hg : AnalyticAt ℂ g a)
    (B : F →L[ℂ] E)
    (hAB : (fderiv ℂ g a).comp B = ContinuousLinearMap.id ℂ F) :
    ∃ e : OpenPartialHomeomorph E (F × (fderiv ℂ g a).ker),
      a ∈ e.source ∧ (∀ y : E, (e y).1 = g y) ∧
      AnalyticAt ℂ e a ∧ AnalyticAt ℂ e.symm (e a) ∧
      ∀ S : Set F, e '' (e.source ∩ g ⁻¹' S) =
        e.target ∩ S ×ˢ (Set.univ : Set (fderiv ℂ g a).ker) := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  let A := fderiv ℂ g a
  let L := (B.splitKernelEquiv A hAB).symm
  let K : E →L[ℂ] A.ker :=
    (ContinuousLinearMap.snd ℂ F A.ker).comp L.toContinuousLinearMap
  have hd : HasStrictFDerivAt (fun y => (g y, K y)) L.toContinuousLinearMap a := by
    convert hg.hasStrictFDerivAt.prodMk K.hasStrictFDerivAt using 1
    ext y <;> rfl
  let e := hd.toOpenPartialHomeomorph _
  have ha : a ∈ e.source := hd.mem_toOpenPartialHomeomorph_source
  have he : ∀ y : E, (e y).1 = g y := fun _ => rfl
  have heA : AnalyticAt ℂ e a := hg.prod (K.analyticAt a)
  have heI : AnalyticAt ℂ e.symm (e a) :=
    e.analyticAt_symm' ha heA hd.hasFDerivAt.fderiv
  refine ⟨e, ha, he, heA, heI, fun S => ?_⟩
  ext w
  constructor
  · rintro ⟨y, ⟨hy, hS⟩, rfl⟩
    exact ⟨e.map_source hy, (he y).symm ▸ hS, Set.mem_univ _⟩
  · rintro ⟨hw, hS, _⟩
    refine ⟨e.symm w, ⟨e.map_target hw, ?_⟩, e.right_inv hw⟩
    change g (e.symm w) ∈ S
    rw [← he, e.right_inv hw]
    exact hS

private theorem ccm5_smooth_chart_local_product
    (X Z : Over (Spec ↧ℂ)) (f : X ⟶ Z) (d e : ℕ)
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension e Z.hom]
    [Smooth f.left] (z : ComplexPoint X) :
    let g := inclusionInComplexCharts Z X f d e z
    let A := fderiv ℂ g (localChart X d z z)
    ∃ φ : OpenPartialHomeomorph (Fin d → ℂ) ((Fin e → ℂ) × A.ker),
      localChart X d z z ∈ φ.source ∧ (∀ y, (φ y).1 = g y) ∧
      AnalyticAt ℂ φ (localChart X d z z) ∧
      AnalyticAt ℂ φ.symm (φ (localChart X d z z)) ∧
      ∀ S : Set (Fin e → ℂ), φ '' (φ.source ∩ g ⁻¹' S) =
        φ.target ∩ S ×ˢ (Set.univ : Set A.ker) := by
  dsimp only
  let A := fderiv ℂ (inclusionInComplexCharts Z X f d e z) (localChart X d z z)
  have hsurj := ccm5_smooth_chart_derivative_surjective_aux X Z f d e z
  obtain ⟨B, hB⟩ := A.toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hsurj)
  let B' : (Fin e → ℂ) →L[ℂ] (Fin d → ℂ) := B.toContinuousLinearMap
  have hAB : A.comp B' = ContinuousLinearMap.id ℂ (Fin e → ℂ) := by
    apply ContinuousLinearMap.ext
    intro y
    exact DFunLike.congr_fun hB y
  exact ccm5_analytic_splitSubmersion_support_chart
    (analyticAt_inclusionInComplexCharts Z X f d e z) B' hAB

private theorem ccm5_primeGoodOpen_sum_eq_component
    {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) [Smooth f.left] (q : ℕ) (x : Z.left)
    (hx : Order.coheight x = q) (a : ccm5_primeGoodOpen f x)
    (z : {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0})
    (hz : a.1 ∈ cycleComponentAnalyticClosedSupport X z.1) :
    (∑ᶠ w : {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0},
      ccm5_supportGerm X
        (ccm4_inverseAnalyticSupport f (cycleComponentAnalyticClosedSupport Z x))
        (2 * q) a.1
        (ccm3_flatPullbackPrime f.left x w.1 •
          supportEnlarge X (ccm4_flatPullbackPrime_support_le_aux f x w.1 w.2) (2 * q)
            (cycleComponentSupportedInjectiveClass X w.1
              (ccm3_flatPullbackPrime_codimension f q x hx w.1 w.2)))) =
      ccm5_supportGerm X
        (ccm4_inverseAnalyticSupport f (cycleComponentAnalyticClosedSupport Z x))
        (2 * q) a.1
        (supportEnlarge X (ccm4_flatPullbackPrime_support_le_aux f x z.1 z.2) (2 * q)
          (cycleComponentSupportedInjectiveClass X z.1
            (ccm3_flatPullbackPrime_codimension f q x hx z.1 z.2))) := by
  classical
  rw [finsum_eq_single _ z]
  · rw [ccm5_flatPullbackPrime_coeff_eq_one_of_smooth f x z.1 z.2, one_smul]
  · intro w hw
    rw [ccm5_flatPullbackPrime_coeff_eq_one_of_smooth f x w.1 w.2, one_smul]
    apply ccm5_supportGerm_enlarge_eq_zero_of_not_mem
    have hij : (ccm5_primeEnumeration f x).symm z ≠
        (ccm5_primeEnumeration f x).symm w := by
      intro h
      exact hw ((ccm5_primeEnumeration f x).symm.injective h).symm
    have h := ccm5_primeGoodOpen_component_disjoint f x a _ _ hij
    simpa only [Equiv.apply_symm_apply] using h (by
      simpa only [Equiv.apply_symm_apply] using hz)

private theorem ccm5_primeGoodOpen_component_neighborhood
    {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) (x : Z.left) (a : ccm5_primeGoodOpen f x)
    (z : {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0})
    (hz : a.1 ∈ cycleComponentAnalyticClosedSupport X z.1) :
    ∃ U : Opens (ComplexPoint X), a.1 ∈ U ∧ U ≤ ccm5_primeGoodOpen f x ∧
      ∀ b ∈ U, b ∈ ccm4_inverseAnalyticSupport f
        (cycleComponentAnalyticClosedSupport Z x) ↔
        b ∈ cycleComponentAnalyticClosedSupport X z.1 := by
  classical
  have hothers : ∀ᶠ b in 𝓝 a.1,
      ∀ w : {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0},
        w ≠ z → b ∉ cycleComponentAnalyticClosedSupport X w.1 := by
    rw [Filter.eventually_all]
    intro w
    by_cases hw : w = z
    · exact Filter.Eventually.of_forall (fun _ h => (h hw).elim)
    · have hij : (ccm5_primeEnumeration f x).symm z ≠
          (ccm5_primeEnumeration f x).symm w := by
        intro h
        exact hw ((ccm5_primeEnumeration f x).symm.injective h).symm
      have hn := ccm5_primeGoodOpen_component_disjoint f x a _ _ hij
      simp only [Equiv.apply_symm_apply] at hn
      have hn' : ∀ᶠ b in 𝓝 a.1, b ∉ cycleComponentAnalyticClosedSupport X w.1 :=
        (cycleComponentAnalyticClosedSupport X w.1).isClosed.isOpen_compl.mem_nhds (hn hz)
      exact hn'.mono (fun _ hb _ => hb)
  have hgood : ∀ᶠ b in 𝓝 a.1, b ∈ ccm5_primeGoodOpen f x :=
    (ccm5_primeGoodOpen f x).isOpen.mem_nhds a.2
  obtain ⟨U, hU, hopen, haU⟩ := mem_nhds_iff.mp (hgood.and hothers)
  refine ⟨⟨U, hopen⟩, haU, fun b hb => (hU hb).1, fun b hb => ?_⟩
  constructor
  · intro h
    change b ∈ (ccm4_inverseAnalyticSupport f
      (cycleComponentAnalyticClosedSupport Z x) : Set (ComplexPoint X)) at h
    rw [ccm5_inverseAnalyticSupport_eq_component_union_aux] at h
    obtain ⟨w, hw⟩ := Set.mem_iUnion.mp h
    by_cases he : w = z
    · subst w
      exact hw
    · exact ((hU hb).2 w he hw).elim
  · intro hz'
    change b ∈ (ccm4_inverseAnalyticSupport f
      (cycleComponentAnalyticClosedSupport Z x) : Set (ComplexPoint X))
    rw [ccm5_inverseAnalyticSupport_eq_component_union_aux]
    exact Set.mem_iUnion.mpr ⟨z, hz'⟩

set_option backward.isDefEq.respectTransparency false in
private theorem ccm5_smoothClosedSupportCoclass_germ_eq_normalChart
    (X Y : Over (Spec ↧ℂ)) (i : Y ⟶ X) (m d : ℕ)
    [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
    [IsClosedImmersion i.left] (z : ComplexPoint Y)
    (e : OpenPartialHomeomorph (ComplexPoint X) ((Fin m → ℂ) × (Fin (d - m) → ℂ)))
    (hS : ∀ y ∈ e.source, y ∈ Set.range (Point.map i) ↔ (e y).2 = 0)
    (he : Point.map i z ∈ e.source)
    (ht : AnalyticAt ℂ
      ((closedImmersionHolomorphicFlatteningChart X Y i m d z).symm.trans e)
      (closedImmersionHolomorphicFlatteningChart X Y i m d z (Point.map i z)))
    (hti : AnalyticAt ℂ
      ((closedImmersionHolomorphicFlatteningChart X Y i m d z).symm.trans e).symm
      (((closedImmersionHolomorphicFlatteningChart X Y i m d z).symm.trans e)
        (closedImmersionHolomorphicFlatteningChart X Y i m d z (Point.map i z)))) :
    (smoothClosedSupportCoclassSheaf X Y i m d).presheaf.Γgerm (Point.map i z)
      (smoothClosedSupportCoclassSection X Y i m d) =
    supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
      (Set.range (Point.map i)) (2 * (d - m)) ⟨e.source, e.open_source⟩
      (Point.map i z) he
      (chartNormalProjectionCoclass (Fin m → ℂ) (d - m) e
        (Set.range (Point.map i)) hS e.source (le_refl _)) := by
  rw [smoothClosedSupportCoclassSection_germ,
    smoothClosedSupportCoclassStalk_eq_chartGerm X Y i m d z _
      (mem_smoothClosedSupportChartOpen X Y i m d z)]
  obtain ⟨W, hW, hW', hxW, hclasses⟩ :=
    exists_open_chartNormalProjectionCoclass_eq (d - m)
      (closedImmersionHolomorphicFlatteningChart X Y i m d z) e
      (Set.range (Point.map i))
      (closedImmersionHolomorphicFlatteningChart_mem_range_iff X Y i m d z)
      hS (Point.map i z) (mem_smoothClosedSupportChartOpen X Y i m d z)
      ((closedImmersionHolomorphicFlatteningChart_mem_range_iff X Y i m d z _
        (mem_smoothClosedSupportChartOpen X Y i m d z)).mp ⟨z, rfl⟩) he ht hti
  apply supportRelativeCohomologyGerm_eq_of_restrict_eq
    (TopCat.of (ComplexPoint X)) (Set.range (Point.map i)) (2 * (d - m))
    hW hW' (Point.map i z) hxW
  exact (chartNormalProjectionCoclass_restrict (Fin m → ℂ) (d - m)
    (closedImmersionHolomorphicFlatteningChart X Y i m d z)
    (Set.range (Point.map i))
    (closedImmersionHolomorphicFlatteningChart_mem_range_iff X Y i m d z)
    hW (le_refl _)).trans (hclasses.trans
      (chartNormalProjectionCoclass_restrict (Fin m → ℂ) (d - m)
        e (Set.range (Point.map i)) hS hW' (le_refl _)).symm)


set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem ccm5_supportOpenIso_toSheaf
    {X Y : TopCat.{0}} (f : Y ⟶ X) (hf : IsOpenEmbedding f)
    (S : Set X) (B : Set Y) (hB : f ⁻¹' S = B) (n : ℕ) :
    supportRelativeCohomologyToSheaf Y B n ≫
      (supportRelativeCohomologySheafOpenIso f hf S B hB n).hom.hom =
    (supportRelativeCohomologyPresheafOpenIso f hf S B hB n).inv ≫
      Functor.whiskerLeft hf.functor.op (supportRelativeCohomologyToSheaf X S n) := by
  let := hf.functor_isContinuous
  let := hf.functor_isCocontinuous
  change toSheafify (Opens.grothendieckTopology Y) _ ≫
    ((presheafToSheaf (Opens.grothendieckTopology Y) AddCommGrpCat).map
      (supportRelativeCohomologyPresheafOpenIso f hf S B hB n).inv).hom ≫
    (supportOpenEmbeddingSheafificationIso f hf _).hom.hom = _
  rw [← Category.assoc, ← toSheafify_naturality, Category.assoc]
  congr 1
  exact hf.functor.toSheafify_pullbackSheafificationCompatibility
    AddCommGrpCat (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
    (supportRelativeCohomologyPresheaf X S n)

set_option backward.isDefEq.respectTransparency false in
private theorem ccm5_smoothClosedSupportCoclass_restrict_chart
    (X Y : Over (Spec ↧ℂ)) (i : Y ⟶ X) (m d : ℕ)
    [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
    [IsClosedImmersion i.left] (z : ComplexPoint Y) :
    (smoothClosedSupportCoclassSheaf X Y i m d).presheaf.map
      (homOfLE (show smoothClosedSupportChartOpen X Y i m d z ≤ ⊤ from le_top)).op
      (smoothClosedSupportCoclassSection X Y i m d) =
    smoothClosedSupportChartSheafSection X Y i m d z := by
  apply TopCat.Presheaf.section_ext
  intro a ha
  rw [TopCat.Presheaf.germ_res_apply]
  exact (smoothClosedSupportCoclassSection_germ X Y i m d a).trans
    (smoothClosedSupportCoclassStalk_eq_chartGerm X Y i m d z a ha)

set_option backward.isDefEq.respectTransparency false in
private theorem ccm5_smoothClosedSupportCoclass_openImage_chart
    (X Y : Over (Spec ↧ℂ)) (i : Y ⟶ X) (m d : ℕ)
    [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
    [IsClosedImmersion i.left] (z : ComplexPoint Y)
    {M : TopCat.{0}} (f : TopCat.of (ComplexPoint X) ⟶ M)
    (hf : IsOpenEmbedding f) (S : Set M)
    (hS : f ⁻¹' S = Set.range (Point.map i)) :
    (supportRelativeCohomologySheaf M S (2 * (d - m))).presheaf.map
      (hf.functor.map (homOfLE
        (show smoothClosedSupportChartOpen X Y i m d z ≤ ⊤ from le_top))).op
      (supportRelativeCohomologySectionOpenImage f hf S (Set.range (Point.map i)) hS
        (2 * (d - m)) (smoothClosedSupportCoclassSection X Y i m d)) =
    (supportRelativeCohomologyToSheaf M S (2 * (d - m))).app
      (Opposite.op (hf.functor.obj (smoothClosedSupportChartOpen X Y i m d z)))
      ((supportRelativeCohomologyPresheafOpenIso f hf S (Set.range (Point.map i)) hS
        (2 * (d - m))).inv.app (Opposite.op (smoothClosedSupportChartOpen X Y i m d z))
        (smoothClosedSupportChartCoclass X Y i m d z
          (smoothClosedSupportChartOpen X Y i m d z) (le_refl _))) := by
  have hn := ConcreteCategory.congr_hom
    ((supportRelativeCohomologySheafOpenIso f hf S (Set.range (Point.map i)) hS
      (2 * (d - m))).hom.hom.naturality
      (homOfLE (show smoothClosedSupportChartOpen X Y i m d z ≤ ⊤ from le_top)).op)
    (smoothClosedSupportCoclassSection X Y i m d)
  have hu := ConcreteCategory.congr_hom
    (NatTrans.congr_app (ccm5_supportOpenIso_toSheaf f hf S
      (Set.range (Point.map i)) hS (2 * (d - m)))
      (Opposite.op (smoothClosedSupportChartOpen X Y i m d z)))
    (smoothClosedSupportChartCoclass X Y i m d z
      (smoothClosedSupportChartOpen X Y i m d z) (le_refl _))
  change _ = _ at hn
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    ccm5_smoothClosedSupportCoclass_restrict_chart] at hn
  exact hn.symm.trans hu


set_option backward.isDefEq.respectTransparency false in
private theorem ccm5_smoothClosedSupportCoclass_transported_germ
    (X Y : Over (Spec ↧ℂ)) (i : Y ⟶ X) (m d : ℕ)
    [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
    [IsClosedImmersion i.left] (z : ComplexPoint Y)
    {M : TopCat.{0}} (f : TopCat.of (ComplexPoint X) ⟶ M)
    (hf : IsOpenEmbedding f) (S : Set M)
    (hS : f ⁻¹' S = Set.range (Point.map i))
    (U : Opens M) (hU : hf.functor.obj ⊤ = U) :
    (supportRelativeCohomologySheaf M S (2 * (d - m))).presheaf.germ U
      (f (Point.map i z)) (hU ▸ ⟨Point.map i z, Set.mem_univ _, rfl⟩)
      (supportRelativeCohomologySectionOnOpen f hf S (Set.range (Point.map i)) hS
        (2 * (d - m)) U hU (smoothClosedSupportCoclassSection X Y i m d)) =
    supportRelativeCohomologyGerm M S (2 * (d - m))
      (hf.functor.obj (smoothClosedSupportChartOpen X Y i m d z)) (f (Point.map i z))
      ⟨Point.map i z, mem_smoothClosedSupportChartOpen X Y i m d z, rfl⟩
      ((supportRelativeCohomologyPresheafOpenIso f hf S (Set.range (Point.map i)) hS
        (2 * (d - m))).inv.app (Opposite.op (smoothClosedSupportChartOpen X Y i m d z))
        (smoothClosedSupportChartCoclass X Y i m d z
          (smoothClosedSupportChartOpen X Y i m d z) (le_refl _))) := by
  subst U
  change (supportRelativeCohomologySheaf M S (2 * (d - m))).presheaf.germ _ _ _
    ((supportRelativeCohomologySheaf M S (2 * (d - m))).presheaf.map (𝟙 _)
      (supportRelativeCohomologySectionOpenImage f hf S (Set.range (Point.map i)) hS
        (2 * (d - m)) (smoothClosedSupportCoclassSection X Y i m d))) = _
  rw [CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
  have h := (supportRelativeCohomologySheaf M S (2 * (d - m))).presheaf.germ_res_apply
    (hf.functor.map (homOfLE
      (show smoothClosedSupportChartOpen X Y i m d z ≤ ⊤ from le_top)))
    (f (Point.map i z))
    ⟨Point.map i z, mem_smoothClosedSupportChartOpen X Y i m d z, rfl⟩
    (supportRelativeCohomologySectionOpenImage f hf S (Set.range (Point.map i)) hS
      (2 * (d - m)) (smoothClosedSupportCoclassSection X Y i m d))
  rw [ccm5_smoothClosedSupportCoclass_openImage_chart] at h
  exact h.symm


set_option backward.isDefEq.respectTransparency false in
private theorem ccm5_chartNormalProjectionCoclass_openImage
    {M N E : Type} [TopologicalSpace M] [TopologicalSpace N]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℕ)
    (f : M → N) (hf : IsOpenEmbedding f)
    (e : OpenPartialHomeomorph M (E × (Fin c → ℂ)))
    (B : Set M) (S : Set N) (hB : f ⁻¹' S = B)
    (he : ∀ y ∈ e.source, y ∈ B ↔ (e y).2 = 0)
    (he' : ∀ y ∈ (e.lift_openEmbedding hf).source,
      y ∈ S ↔ (e.lift_openEmbedding hf y).2 = 0)
    (W : Set M) (hW : W ⊆ e.source) :
    (neighborhoodSupportPairImageCohomologyEquiv f hf.isEmbedding W B S
      (fun y _ => by rw [← hB]; rfl) (2 * c)).symm
      (chartNormalProjectionCoclass E c e B he W hW) =
    chartNormalProjectionCoclass E c (e.lift_openEmbedding hf) S he'
      (f '' W) (Set.image_mono hW) := by
  apply (neighborhoodSupportPairImageCohomologyEquiv f hf.isEmbedding W B S
    (fun y _ => by rw [← hB]; rfl) (2 * c)).injective
  rw [LinearEquiv.apply_symm_apply]
  change _ = relativeCohomologyMap ℚ (2 * c)
    (neighborhoodSupportPairImageIso f hf.isEmbedding W B S
      (fun y _ => by rw [← hB]; rfl)).hom _
  symm
  apply ccm5_chartNormalProjectionCoclass_pullback
  intro y
  change (e.lift_openEmbedding hf (f y.1)).2 = (e y.1).2
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]


private theorem ccm5_product_normal_chart
    {E F G K : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (c : ℕ) (g : E → F) (φ : OpenPartialHomeomorph E (F × K))
    (hφg : ∀ y, (φ y).1 = g y)
    (d : OpenPartialHomeomorph F (G × (Fin c → ℂ)))
    (S : Set F) (hS : ∀ y ∈ d.source, y ∈ S ↔ (d y).2 = 0)
    (a : E) (ha : a ∈ φ.source) (hga : g a ∈ d.source)
    (hφ : AnalyticAt ℂ φ a) (hφi : AnalyticAt ℂ φ.symm (φ a))
    (hd : AnalyticAt ℂ d (g a)) (hdi : AnalyticAt ℂ d.symm (d (g a))) :
    ∃ e : OpenPartialHomeomorph E ((G × K) × (Fin c → ℂ)),
      a ∈ e.source ∧ (∀ y, (e y).2 = (d (g y)).2) ∧
      (∀ y ∈ e.source, y ∈ g ⁻¹' S ↔ (e y).2 = 0) ∧
      AnalyticAt ℂ e a ∧ AnalyticAt ℂ e.symm (e a) := by
  let p := d.prod (OpenPartialHomeomorph.refl K)
  let r : ((G × (Fin c → ℂ)) × K) ≃L[ℂ] ((G × K) × (Fin c → ℂ)) :=
    (ContinuousLinearEquiv.prodAssoc ℂ G (Fin c → ℂ) K).trans
      (((ContinuousLinearEquiv.refl ℂ G).prodCongr
        (ContinuousLinearEquiv.prodComm ℂ (Fin c → ℂ) K)).trans
          (ContinuousLinearEquiv.prodAssoc ℂ G K (Fin c → ℂ)).symm)
  let e := (φ.trans p).trans r.toHomeomorph.toOpenPartialHomeomorph
  have hpa : φ a ∈ p.source := ⟨(hφg a).symm ▸ hga, Set.mem_univ _⟩
  have hea : a ∈ e.source := ⟨⟨ha, hpa⟩, Set.mem_univ _⟩
  have hen : ∀ y, (e y).2 = (d (g y)).2 := by
    intro y
    change (d (φ y).1).2 = _
    rw [hφg]
  have hp : AnalyticAt ℂ p (φ a) :=
    (show AnalyticAt ℂ d (φ a).1 from (hφg a).symm ▸ hd).comp analyticAt_fst |>.prod
      analyticAt_snd
  have hdi' : AnalyticAt ℂ d.symm (p (φ a)).1 := by
    change AnalyticAt ℂ d.symm (d (φ a).1)
    rw [hφg]
    exact hdi
  have hpi : AnalyticAt ℂ p.symm (p (φ a)) :=
    (hdi'.comp (f := Prod.fst) (x := p (φ a)) analyticAt_fst).prod analyticAt_snd
  refine ⟨e, hea, hen, ?_, ?_, ?_⟩
  · intro y hy
    rw [hen]
    exact hS (g y) ((hφg y) ▸ hy.1.2.1)
  · exact (r.toContinuousLinearMap.analyticAt _).comp (hp.comp hφ)
  · have hpir : AnalyticAt ℂ p.symm (r.symm (r (p (φ a)))) := by
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using hpi
    have hφir : AnalyticAt ℂ φ.symm (p.symm (r.symm (r (p (φ a))))) := by
      simpa only [ContinuousLinearEquiv.symm_apply_apply, p.left_inv hpa] using hφi
    exact hφir.comp (f := fun w => p.symm (r.symm w)) (x := r (p (φ a)))
      (hpir.comp (f := r.symm) (x := r (p (φ a)))
        (r.symm.toContinuousLinearMap.analyticAt _))


set_option backward.isDefEq.respectTransparency false in
private theorem ccm5_smoothClosedSupportCoclass_ambient_chart
    (X Y : Over (Spec ↧ℂ)) (i : Y ⟶ X) (m d : ℕ)
    [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
    [IsClosedImmersion i.left] (z : ComplexPoint Y)
    {M : TopCat.{0}} (f : TopCat.of (ComplexPoint X) ⟶ M)
    (hf : IsOpenEmbedding f) (S : Set M)
    (hS : f ⁻¹' S = Set.range (Point.map i))
    (U : Opens M) (hU : hf.functor.obj ⊤ = U) :
    ∃ (e : OpenPartialHomeomorph M ((Fin m → ℂ) × (Fin (d - m) → ℂ))),
      e = (closedImmersionHolomorphicFlatteningChart X Y i m d z).lift_openEmbedding hf ∧
      ∃ (he : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
      (ha : f (Point.map i z) ∈ e.source),
      (supportRelativeCohomologySheaf M S (2 * (d - m))).presheaf.germ U
        (f (Point.map i z)) (hU ▸ ⟨Point.map i z, Set.mem_univ _, rfl⟩)
        (supportRelativeCohomologySectionOnOpen f hf S (Set.range (Point.map i)) hS
          (2 * (d - m)) U hU (smoothClosedSupportCoclassSection X Y i m d)) =
      supportRelativeCohomologyGerm M S (2 * (d - m)) ⟨e.source, e.open_source⟩
        (f (Point.map i z)) ha
        (chartNormalProjectionCoclass (Fin m → ℂ) (d - m) e S he e.source (le_refl _)) := by
  let e₀ := closedImmersionHolomorphicFlatteningChart X Y i m d z
  let e := e₀.lift_openEmbedding hf
  have he : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0 := by
    rintro _ ⟨y, hy, rfl⟩
    change f y ∈ S ↔ (e₀.lift_openEmbedding hf (f y)).2 = 0
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
    change y ∈ f ⁻¹' S ↔ _
    rw [hS]
    exact closedImmersionHolomorphicFlatteningChart_mem_range_iff X Y i m d z y hy
  refine ⟨e, rfl, he, ⟨Point.map i z, mem_smoothClosedSupportChartOpen X Y i m d z, rfl⟩, ?_⟩
  have h := ccm5_smoothClosedSupportCoclass_transported_germ X Y i m d z f hf S hS U hU
  convert h using 1
  congr 1
  exact (ccm5_chartNormalProjectionCoclass_openImage (d - m) f hf e₀
    (Set.range (Point.map i)) S hS
    (closedImmersionHolomorphicFlatteningChart_mem_range_iff X Y i m d z) he
    e₀.source (le_refl _)).symm
private theorem ccm5_component_smoothLift_point
    (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (x : X.left) (a : ComplexPoint X)
    (ha : a ∈ cycleComponentSmoothSupportAmbientOpen X x)
    (haS : a ∈ cycleComponentSupport X x) :
    ∃ z : ComplexPoint (cycleComponentSmoothLocusOver X x),
      cycleComponentSmoothClosedLiftAmbientMap X x
        (Point.map (cycleComponentSmoothLocusClosedLiftOver X x) z) = a := by
  have hrange : a ∈ Set.range (cycleComponentSmoothClosedLiftAmbientMap X x) := by
    rw [← Set.image_univ]
    change a ∈ (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x).functor.obj ⊤
    rw [cycleComponentSmoothClosedLiftAmbientMap_imageOpen]
    exact ha
  obtain ⟨b, rfl⟩ := hrange
  have hb : b ∈ Set.range (Point.map (cycleComponentSmoothLocusClosedLiftOver X x)) := by
    rw [← cycleComponentSmoothClosedLiftAmbientMap_support]
    exact haS
  obtain ⟨z, rfl⟩ := hb
  exact ⟨z, rfl⟩
private theorem ccm5_openEmbedding_chart_analytic
    (X Y : Over (Spec ↧ℂ)) (i : Y ⟶ X) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] [SmoothOfRelativeDimension d Y.hom]
    [Etale i.left] (hi : IsOpenEmbedding (Point.map i)) (b : ComplexPoint Y) :
    let e := (localChart X d (Point.map i b)).symm.trans
      ((localChart Y d b).lift_openEmbedding hi)
    AnalyticAt ℂ e (localChart X d (Point.map i b) (Point.map i b)) ∧
    AnalyticAt ℂ e.symm (e (localChart X d (Point.map i b) (Point.map i b))) := by
  let C := localChart X d (Point.map i b)
  let D := localChart Y d b
  let e := C.symm.trans (D.lift_openEmbedding hi)
  have hb : D b ∈ e.symm.source := by
    refine ⟨D.map_source (mem_localChart_source Y d b), ?_⟩
    change Point.map i (D.symm (D b)) ∈ C.source
    rw [D.left_inv (mem_localChart_source Y d b)]
    exact mem_localChart_source X d (Point.map i b)
  have he : e.symm (D b) = C (Point.map i b) := by
    change C (Point.map i (D.symm (D b))) = _
    rw [D.left_inv (mem_localChart_source Y d b)]
  have he' : e (C (Point.map i b)) = D b := by
    rw [← he]
    exact e.symm.left_inv hb
  have ha : AnalyticAt ℂ e.symm (D b) :=
    analyticAt_inclusionInComplexCharts X Y i d d b
  have hd := ccm5_etale_chart_derivative_bijective_aux Y X i d d b
  let L := ContinuousLinearEquiv.ofBijective
    (fderiv ℂ (inclusionInComplexCharts X Y i d d b) (D b)) (LinearMap.ker_eq_bot.mpr hd.1) (LinearMap.range_eq_top.mpr hd.2)
  have hinv := e.symm.analyticAt_symm' (i := L) hb ha rfl
  change AnalyticAt ℂ e (C (Point.map i b)) ∧ AnalyticAt ℂ e.symm (e (C (Point.map i b)))
  refine ⟨?_, ?_⟩
  · simpa only [OpenPartialHomeomorph.symm_symm, he] using hinv
  · rwa [he']
private theorem ccm5_lifted_flatteningChart_analytic
    (X Y O : Over (Spec ↧ℂ)) (i : Y ⟶ X) (j : X ⟶ O) (m d : ℕ)
    [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
    [SmoothOfRelativeDimension d O.hom] [IsClosedImmersion i.left]
    [Etale j.left] (hj : IsOpenEmbedding (Point.map j)) (z : ComplexPoint Y) :
    let e := (closedImmersionHolomorphicFlatteningChart X Y i m d z).lift_openEmbedding hj
    let C := localChart O d (Point.map j (Point.map i z))
    AnalyticAt ℂ (C.symm.trans e) (C (Point.map j (Point.map i z))) ∧
    AnalyticAt ℂ (C.symm.trans e).symm (e (Point.map j (Point.map i z))) := by
  let b := Point.map i z
  let C := localChart O d (Point.map j b)
  let D := localChart X d b
  let A := closedImmersionNormalCoordinateChange X Y i m d z
  let e₀ := closedImmersionHolomorphicFlatteningChart X Y i m d z
  let e := e₀.lift_openEmbedding hj
  let t := C.symm.trans (D.lift_openEmbedding hj)
  have hb : b ∈ e₀.source := mem_smoothClosedSupportChartOpen X Y i m d z
  have hA : AnalyticAt ℂ A (D b) ∧ AnalyticAt ℂ A.symm (e₀ b) :=
    ((OpenPartialHomeomorph.biAnalyticRestrict_mem_source_iff _ _).mp hb.1.2).2
  have ht := ccm5_openEmbedding_chart_analytic O X j d hj b
  have htval : t (C (Point.map j b)) = D b := by
    change (D.lift_openEmbedding hj) (C.symm (C (Point.map j b))) = _
    rw [C.left_inv (mem_localChart_source O d (Point.map j b)),
      OpenPartialHomeomorph.lift_openEmbedding_apply]
  have hcenter : C (Point.map j b) ∈ t.source := by
    refine ⟨C.map_source (mem_localChart_source O d (Point.map j b)), ?_⟩
    change C.symm (C (Point.map j b)) ∈ (D.lift_openEmbedding hj).source
    rw [C.left_inv (mem_localChart_source O d (Point.map j b))]
    exact ⟨b, mem_localChart_source X d b, rfl⟩
  have heval : e (Point.map j b) = e₀ b := OpenPartialHomeomorph.lift_openEmbedding_apply _ _
  have hAval : A.symm (e₀ b) = D b := A.left_inv hb.1.2.1
  change AnalyticAt ℂ (C.symm.trans e) (C (Point.map j b)) ∧
    AnalyticAt ℂ (C.symm.trans e).symm (e (Point.map j b))
  constructor
  · have hcomp : AnalyticAt ℂ (A ∘ t) (C (Point.map j b)) :=
      (htval.symm ▸ hA.1).comp ht.1
    apply hcomp.congr
    filter_upwards [t.open_source.mem_nhds hcenter] with v hv
    obtain ⟨y, hy, heq⟩ := hv.2
    change Point.map j y = C.symm v at heq
    change A ((D.lift_openEmbedding hj) (C.symm v)) = e (C.symm v)
    rw [← heq, OpenPartialHomeomorph.lift_openEmbedding_apply,
      OpenPartialHomeomorph.lift_openEmbedding_apply]
    rfl
  · rw [heval]
    have hti : AnalyticAt ℂ t.symm (A.symm (e₀ b)) := by
      rw [hAval, ← htval]
      exact ht.2
    exact hti.comp hA.2

set_option backward.isDefEq.respectTransparency false in
private theorem ccm5_componentClass_germ_exists_normalChart
    (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (q : ℕ) (x : X.left) (hx : Order.coheight x = q)
    (a : ComplexPoint X) (ha : a ∈ cycleComponentSmoothSupportAmbientOpen X x)
    (haS : a ∈ cycleComponentSupport X x) :
    ∃ (e : OpenPartialHomeomorph (ComplexPoint X)
        ((Fin (dim X.left - q) → ℂ) × (Fin q → ℂ)))
      (he : ∀ y ∈ e.source, y ∈ cycleComponentSupport X x ↔ (e y).2 = 0)
      (hae : a ∈ e.source),
      ccm5_supportGerm X (cycleComponentAnalyticClosedSupport X x) (2 * q) a
        (cycleComponentSupportedInjectiveClass X x hx) =
      supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
        (cycleComponentSupport X x) (2 * q) ⟨e.source, e.open_source⟩ a hae
        (chartNormalProjectionCoclass (Fin (dim X.left - q) → ℂ) q e
          (cycleComponentSupport X x) he e.source (le_refl _)) ∧
      AnalyticAt ℂ ((localChart X (dim X.left) a).symm.trans e)
        (localChart X (dim X.left) a a) ∧
      AnalyticAt ℂ ((localChart X (dim X.left) a).symm.trans e).symm (e a) := by
  obtain ⟨z, rfl⟩ := ccm5_component_smoothLift_point X x a ha haS
  have := cycleComponentSmoothLocusOver_hom_smoothOfRelativeDimension X x hx
  have h := ccm5_smoothClosedSupportCoclass_ambient_chart
    (cycleComponentSmoothLocusAmbientOpenOver X x) (cycleComponentSmoothLocusOver X x)
    (cycleComponentSmoothLocusClosedLiftOver X x) (dim X.left - q) (dim X.left) z
    (cycleComponentSmoothClosedLiftAmbientMap X x)
    (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x)
    (cycleComponentSupport X x) (cycleComponentSmoothClosedLiftAmbientMap_support X x)
    (cycleComponentSmoothSupportAmbientOpen X x)
    (cycleComponentSmoothClosedLiftAmbientMap_imageOpen X x)
  obtain ⟨e, heq, he, hae, hg⟩ := h
  have : Etale (openInclusion X (cycleComponentSmoothLocusAmbientOpen X x)).left := by
    change Etale (cycleComponentSmoothLocusAmbientOpen X x).ι
    infer_instance
  have hA := ccm5_lifted_flatteningChart_analytic
    (cycleComponentSmoothLocusAmbientOpenOver X x) (cycleComponentSmoothLocusOver X x) X
    (cycleComponentSmoothLocusClosedLiftOver X x)
    (openInclusion X (cycleComponentSmoothLocusAmbientOpen X x))
    (dim X.left - q) (dim X.left)
    (cycleComponentSmoothClosedLiftAmbientMap_isOpenEmbedding X x) z
  rw [← heq] at hA
  rw [ccm5_componentClass_normalized_germ_aux X q x hx _ ha]
  unfold cycleComponentSmoothSupportCoclassSection cycleComponentSmoothClosedLiftCoclassSection
  have hcod := cycleComponentSmoothClosedLift_codimension X x hx
  generalize_proofs at *
  generalize hm : dim X.left - q = m at *
  cases hcod
  exact ⟨e, he, hae, hg, hA⟩

set_option backward.isDefEq.respectTransparency false in
private theorem ccm5_supportGerm_exists_restrict_eq
    (X : TopCat.{0}) (S : Set X) (n : ℕ) {U V : Opens X}
    (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
    (a : RelativeCohomology ℚ (neighborhoodSupportComplementPair (U : Set X) S) n)
    (b : RelativeCohomology ℚ (neighborhoodSupportComplementPair (V : Set X) S) n)
    (h : supportRelativeCohomologyGerm X S n U x hxU a =
      supportRelativeCohomologyGerm X S n V x hxV b) :
    ∃ (W : Opens X) (_hxW : x ∈ W) (hWU : W ≤ U) (hWV : W ≤ V),
      relativeCohomologyMap ℚ n (neighborhoodSupportInclusionPairMap hWU S) a =
      relativeCohomologyMap ℚ n (neighborhoodSupportInclusionPairMap hWV S) b := by
  let P := supportRelativeCohomologyPresheaf X S n
  let η := supportRelativeCohomologyToSheaf X S n
  have : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map η) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat P
  have h' : P.germ U x hxU a = P.germ V x hxV b := by
    apply (ConcreteCategory.bijective_of_isIso
      ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map η)).1
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
      TopCat.Presheaf.stalkFunctor_map_germ_apply]
    exact h
  obtain ⟨W, hxW, iU, iV, he⟩ := P.germ_eq x hxU hxV a b h'
  exact ⟨W, hxW, leOfHom iU, leOfHom iV, he⟩
set_option backward.isDefEq.respectTransparency false in
private theorem ccm5_componentClass_restrict_normalChart
    (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (q : ℕ) (x : X.left) (hx : Order.coheight x = q)
    (a : ComplexPoint X) (ha : a ∈ cycleComponentSmoothSupportAmbientOpen X x)
    (haS : a ∈ cycleComponentSupport X x) :
    ∃ (e : OpenPartialHomeomorph (ComplexPoint X)
        ((Fin (dim X.left - q) → ℂ) × (Fin q → ℂ)))
      (he : ∀ y ∈ e.source, y ∈ cycleComponentSupport X x ↔ (e y).2 = 0),
      a ∈ e.source ∧
      AnalyticAt ℂ ((localChart X (dim X.left) a).symm.trans e)
        (localChart X (dim X.left) a a) ∧
      AnalyticAt ℂ ((localChart X (dim X.left) a).symm.trans e).symm (e a) ∧
      ∃ (W : Opens (ComplexPoint X)) (_haW : a ∈ W) (hWe : (W : Set (ComplexPoint X)) ⊆ e.source),
        relativeCohomologyMap ℚ (2 * q)
          (neighborhoodSupportInclusionPairMap (show (W : Set (ComplexPoint X)) ⊆ Set.univ from Set.subset_univ _)
            (cycleComponentSupport X x))
          (supportedSingularClass X (cycleComponentAnalyticClosedSupport X x) (2 * q)
            (cycleComponentSupportedInjectiveClass X x hx)) =
        chartNormalProjectionCoclass (Fin (dim X.left - q) → ℂ) q e
          (cycleComponentSupport X x) he W hWe := by
  obtain ⟨e, he, hae, hg, heA, heI⟩ := ccm5_componentClass_germ_exists_normalChart X q x hx a ha haS
  obtain ⟨W, haW, hWU, hWV, hW⟩ :=
    ccm5_supportGerm_exists_restrict_eq (TopCat.of (ComplexPoint X))
      (cycleComponentSupport X x) (2 * q) a (show a ∈ (⊤ : Opens (ComplexPoint X)) from trivial)
      hae _ _ hg
  refine ⟨e, he, hae, heA, heI, W, haW, hWV, ?_⟩
  exact hW.trans (chartNormalProjectionCoclass_restrict (Fin (dim X.left - q) → ℂ)
    q e (cycleComponentSupport X x) he hWV (le_refl _))

private theorem ccm5_formallySmooth_of_retract
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.FormallySmooth R B]
    (i : A →ₐ[R] B) (r : B →ₐ[R] A) (h : r.comp i = AlgHom.id R A) :
    Algebra.FormallySmooth R A := by
  apply Algebra.FormallySmooth.of_split r ((Ideal.Quotient.mkₐ R _).comp i)
  ext a
  exact AlgHom.congr_fun h a

private theorem ccm5_formallySmooth_ringHom_of_retract
    {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    (a : R →+* A) (i : A →+* B) (r : B →+* A)
    (h : r.comp i = RingHom.id A) (hi : (i.comp a).FormallySmooth) :
    a.FormallySmooth := by
  algebraize [a, i.comp a]
  let i' : A →ₐ[R] B := { i with commutes' := fun _ => rfl }
  let r' : B →ₐ[R] A :=
    { r with commutes' := fun x => RingHom.congr_fun h (a x) }
  exact ccm5_formallySmooth_of_retract i' r' (AlgHom.ext (RingHom.congr_fun h))

set_option backward.isDefEq.respectTransparency false in
private theorem ccm5_smoothLocus_of_section
    {X Y S : Scheme} (f : X ⟶ Y) (g : Y ⟶ S) (s : Y ⟶ X)
    [LocallyOfFinitePresentation g] [LocallyOfFinitePresentation (f ≫ g)]
    (hs : s ≫ f = 𝟙 Y) (y : Y) (hy : s y ∈ (f ≫ g).smoothLocus) :
    y ∈ g.smoothLocus := by
  have he : f (s y) = y := by
    exact congrArg (fun k : Y ⟶ Y => k y) hs
  let e := Y.presheaf.stalkCongr (Inseparable.of_eq he)
  let eS := S.presheaf.stalkCongr (Inseparable.of_eq (congrArg g he))
  let i := e.inv ≫ f.stalkMap (s y)
  have hir : i ≫ s.stalkMap y = 𝟙 _ := by
    dsimp only [i]
    rw [Category.assoc, ← Scheme.Hom.stalkMap_comp,
      Scheme.Hom.stalkMap_congr_hom _ _ hs, Scheme.Hom.stalkMap_id]
    change e.inv ≫ e.hom ≫ 𝟙 _ = 𝟙 _
    simp only [Category.comp_id, e.inv_hom_id]
  have hc : g.stalkMap y ≫ i = eS.inv ≫ (f ≫ g).stalkMap (s y) := by
    have h := g.stalkMap_congr_point (f (s y)) y he
    change g.stalkMap (f (s y)) ≫ e.hom = eS.hom ≫ g.stalkMap y at h
    calc
      g.stalkMap y ≫ i =
          eS.inv ≫ (eS.hom ≫ g.stalkMap y) ≫ e.inv ≫ f.stalkMap (s y) := by
            simp only [i, ← Category.assoc, eS.inv_hom_id, Category.id_comp]
      _ = eS.inv ≫ (g.stalkMap (f (s y)) ≫ e.hom) ≫ e.inv ≫
          f.stalkMap (s y) := by rw [h]
      _ = eS.inv ≫ (f ≫ g).stalkMap (s y) := by
        simp only [Scheme.Hom.stalkMap_comp, Category.assoc, e.hom_inv_id_assoc]
  apply ccm5_formallySmooth_ringHom_of_retract (g.stalkMap y).hom i.hom
    (s.stalkMap y).hom
  · exact congrArg CommRingCat.Hom.hom hir
  · change (g.stalkMap y ≫ i).hom.FormallySmooth
    rw [hc, CommRingCat.hom_comp]
    exact (RingHom.FormallySmooth.of_bijective
      ((ConcreteCategory.bijective_of_isIso eS.inv))).comp hy

private theorem ccm5_inverseSupport_eq_component_union
    {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) (x : Z.left) :
    ((ccm3_inverseIdeal f.left x).support : Set X.left) =
      ⋃ z : {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0},
        closure ({z.1} : Set X.left) := by
  let I := ccm3_inverseIdeal f.left x
  have hrange : Set.range I.subschemeι = f.left ⁻¹' closure ({x} : Set Z.left) := by
    rw [I.range_subschemeι]
    simp only [I, ccm3_inverseIdeal, Scheme.IdealSheafData.support_comap,
      ccm3_primeIdeal]
    rfl
  ext a
  rw [ccm3_inverseIdeal, Scheme.IdealSheafData.support_comap]
  change f.left a ∈ closure ({x} : Set Z.left) ↔ _
  constructor
  · intro ha
    have har : a ∈ Set.range I.subschemeι := by
      rw [hrange]
      exact ha
    obtain ⟨b, hb⟩ := har
    let C := irreducibleComponent b
    have hC : C ∈ irreducibleComponents I.subscheme :=
      irreducibleComponent_mem_irreducibleComponents b
    let y := hC.1.genericPoint
    have hy : closure ({y} : Set I.subscheme) = C :=
      hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
    have hz : ccm3_flatPullbackPrime f.left x (I.subschemeι y) ≠ 0 :=
      (ccm3_flatPullbackPrime_support f x _).mpr ⟨y, rfl, hy ▸ hC⟩
    apply Set.mem_iUnion.mpr
    refine ⟨⟨I.subschemeι y, hz⟩, ?_⟩
    change a ∈ closure ({I.subschemeι y} : Set X.left)
    rw [← hb]
    have hbc : b ∈ closure ({y} : Set I.subscheme) := hy.symm ▸ mem_irreducibleComponent
    have him := image_closure_subset_closure_image I.subschemeι.continuous
      (s := ({y} : Set I.subscheme))
    simpa only [Set.image_singleton] using him ⟨b, hbc, rfl⟩
  · intro ha
    obtain ⟨z, hz⟩ := Set.mem_iUnion.mp ha
    obtain ⟨y, heq, hy⟩ := (ccm3_flatPullbackPrime_support f x z.1).mp z.2
    change a ∈ closure ({z.1} : Set X.left) at hz
    have hclosed : IsClosed (f.left ⁻¹' closure ({x} : Set Z.left)) :=
      isClosed_closure.preimage f.left.continuous
    apply (hclosed.closure_subset_iff.mpr ?_) hz
    rw [Set.singleton_subset_iff, ← heq, ← hrange]
    exact ⟨y, rfl⟩

private theorem ccm5_primeGoodOpen_component_zariski_neighborhood
    {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) (x : Z.left) (a : ccm5_primeGoodOpen f x)
    (z : {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0})
    (hz : a.1 ∈ cycleComponentAnalyticClosedSupport X z.1) :
    ∃ U : X.left.Opens, a.1.underlying ∈ U ∧
      U ≤ cycleComponentSmoothLocusAmbientOpen X z.1 ∧
      ∀ b ∈ U, b ∈ (ccm3_inverseIdeal f.left x).support ↔
        b ∈ closure ({z.1} : Set X.left) := by
  classical
  have hothers : ∀ᶠ b in 𝓝 a.1.underlying,
      ∀ w : {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0},
        w ≠ z → b ∉ closure ({w.1} : Set X.left) := by
    rw [Filter.eventually_all]
    intro w
    by_cases hw : w = z
    · exact Filter.Eventually.of_forall (fun _ h => (h hw).elim)
    · have hij : (ccm5_primeEnumeration f x).symm z ≠
          (ccm5_primeEnumeration f x).symm w := by
        intro h
        exact hw ((ccm5_primeEnumeration f x).symm.injective h).symm
      have hn := ccm5_primeGoodOpen_component_disjoint f x a _ _ hij
      simp only [Equiv.apply_symm_apply] at hn
      have hn' : ∀ᶠ b in 𝓝 a.1.underlying, b ∉ closure ({w.1} : Set X.left) :=
        isClosed_closure.isOpen_compl.mem_nhds (hn hz)
      exact hn'.mono (fun _ hb _ => hb)
  have hs := ccm5_primeGoodOpen_mem_smoothSupport f x a ((ccm5_primeEnumeration f x).symm z)
  simp only [Equiv.apply_symm_apply] at hs
  have hs' : a.1.underlying ∈ cycleComponentSmoothLocusAmbientOpen X z.1 := hs
  have hgood : ∀ᶠ b in 𝓝 a.1.underlying,
      b ∈ cycleComponentSmoothLocusAmbientOpen X z.1 :=
    (cycleComponentSmoothLocusAmbientOpen X z.1).isOpen.mem_nhds hs'
  obtain ⟨U, hU, hopen, haU⟩ := mem_nhds_iff.mp (hgood.and hothers)
  refine ⟨⟨U, hopen⟩, haU, fun b hb => (hU hb).1, fun b hb => ?_⟩
  change b ∈ ((ccm3_inverseIdeal f.left x).support : Set X.left) ↔ _
  rw [ccm5_inverseSupport_eq_component_union]
  constructor
  · intro h
    obtain ⟨w, hw⟩ := Set.mem_iUnion.mp h
    by_cases he : w = z
    · subst w
      exact hw
    · exact ((hU hb).2 w he hw).elim
  · intro hz'
    exact Set.mem_iUnion.mpr ⟨z, hz'⟩

private theorem ccm5_reduced_ker_eq_vanishingIdeal
    {X Y : Scheme} [IsReduced X] (f : X ⟶ Y) :
    f.ker = Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure (Set.range f)) := by
  rw [← Scheme.IdealSheafData.map_bot,
    ← X.nilradical_eq_bot, ← Scheme.IdealSheafData.vanishingIdeal_top,
    Scheme.IdealSheafData.map_vanishingIdeal]
  congr 2
  exact Set.image_univ

private theorem ccm5_reducedIdeal_eq_of_support_eq
    {X : Scheme} (I J : X.IdealSheafData)
    [IsReduced I.subscheme] [IsReduced J.subscheme]
    (h : I.support = J.support) : I = J := by
  rw [← I.ker_subschemeι, ← J.ker_subschemeι,
    ccm5_reduced_ker_eq_vanishingIdeal, ccm5_reduced_ker_eq_vanishingIdeal,
    I.range_subschemeι, J.range_subschemeι, h]

private theorem ccm5_reducedIdeal_comap_open
    {X : Scheme} (I : X.IdealSheafData) [IsReduced I.subscheme] (U : X.Opens) :
    IsReduced (I.comap U.ι).subscheme := by
  let P := CategoryTheory.Limits.pullback U.ι I.subschemeι
  have : IsReduced P :=
    isReduced_of_isOpenImmersion (CategoryTheory.Limits.pullback.snd U.ι I.subschemeι)
  exact ObjectProperty.prop_of_iso (fun Y : Scheme => IsReduced Y)
    (I.comapIso U.ι).symm inferInstance

private theorem ccm5_reducedIdeal_comap_eq_of_support_eq
    {X : Scheme} (I J : X.IdealSheafData)
    [IsReduced I.subscheme] [IsReduced J.subscheme]
    (U : X.Opens) (h : ∀ b ∈ U, b ∈ I.support ↔ b ∈ J.support) :
    I.comap U.ι = J.comap U.ι := by
  letI := ccm5_reducedIdeal_comap_open I U
  letI := ccm5_reducedIdeal_comap_open J U
  apply ccm5_reducedIdeal_eq_of_support_eq
  ext b
  simp only [Scheme.IdealSheafData.support_comap]
  exact h b.1 b.2

private theorem ccm5_primeGoodOpen_component_ideal_eq
    {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) [Smooth f.left] (x : Z.left) (a : ccm5_primeGoodOpen f x)
    (z : {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0})
    (hz : a.1 ∈ cycleComponentAnalyticClosedSupport X z.1) :
    ∃ U : X.left.Opens, a.1.underlying ∈ U ∧
      U ≤ cycleComponentSmoothLocusAmbientOpen X z.1 ∧
      (ccm3_inverseIdeal f.left x).comap U.ι =
        (ccm3_primeIdeal X.left z.1).comap U.ι := by
  obtain ⟨U, haU, hU, heq⟩ := ccm5_primeGoodOpen_component_zariski_neighborhood f x a z hz
  letI := ccm5_inverseIdeal_isReduced f.left x
  have : IsIntegral (ccm3_primeIdeal X.left z.1).subscheme :=
    inferInstanceAs (IsIntegral (cycleComponent X.left z.1))
  exact ⟨U, haU, hU, ccm5_reducedIdeal_comap_eq_of_support_eq _ _ U heq⟩

set_option backward.isDefEq.respectTransparency false in
private theorem ccm5_component_restriction_smooth
    (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (z : X.left) (U : X.left.Opens)
    (hU : U ≤ cycleComponentSmoothLocusAmbientOpen X z) :
    Smooth (((ccm3_primeIdeal X.left z).comap U.ι).subschemeι ≫ U.ι ≫ X.hom) := by
  let J := ccm3_primeIdeal X.left z
  let k := (J.comapIso U.ι).hom ≫ CategoryTheory.Limits.pullback.snd U.ι J.subschemeι
  have hk : k ≫ J.subschemeι = (J.comap U.ι).subschemeι ≫ U.ι := by
    dsimp only [k]
    rw [Category.assoc, ← CategoryTheory.Limits.pullback.condition,
      ← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
  have : IsOpenImmersion k := by dsimp only [k]; infer_instance
  have hsm : Smooth (k ≫ J.subschemeι ≫ X.hom) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff,
      ← Scheme.Hom.preimage_smoothLocus_eq]
    apply top_unique
    intro b _
    change k b ∈ (J.subschemeι ≫ X.hom).smoothLocus
    by_contra hn
    have hb := hU ((J.comap U.ι).subschemeι b).2
    change (U.ι ((J.comap U.ι).subschemeι b)) ∉
      cycleComponentι X.left z ''
        (singularLocusClosed (cycleComponentι X.left z ≫ X.hom) : Set _) at hb
    exact hb ⟨k b, hn, congrArg (fun h => h b) hk⟩
  rw [← Category.assoc, hk] at hsm
  exact hsm

private theorem ccm5_primeGoodOpen_inverse_smooth_neighborhood_alt
    {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) [Smooth f.left] (x : Z.left) (a : ccm5_primeGoodOpen f x)
    (z : {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0})
    (hz : a.1 ∈ cycleComponentAnalyticClosedSupport X z.1) :
    ∃ U : X.left.Opens, a.1.underlying ∈ U ∧
      Smooth (((ccm3_inverseIdeal f.left x).comap U.ι).subschemeι ≫ U.ι ≫ X.hom) := by
  obtain ⟨U, haU, hU, heq⟩ := ccm5_primeGoodOpen_component_ideal_eq f x a z hz
  refine ⟨U, haU, ?_⟩
  rw [heq]
  exact ccm5_component_restriction_smooth X z.1 U hU

set_option backward.isDefEq.respectTransparency false in
private theorem ccm5_primeGoodOpen_inverse_mem_smoothLocus
    {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) [Smooth f.left] (x : Z.left) (a : ccm5_primeGoodOpen f x)
    (z : {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0})
    (hz : a.1 ∈ cycleComponentAnalyticClosedSupport X z.1)
    (b : (ccm3_inverseIdeal f.left x).subscheme)
    (hb : (ccm3_inverseIdeal f.left x).subschemeι b = a.1.underlying) :
    b ∈ ((ccm3_inverseIdeal f.left x).subschemeι ≫ X.hom).smoothLocus := by
  obtain ⟨U, haU, hsm⟩ := ccm5_primeGoodOpen_inverse_smooth_neighborhood_alt f x a z hz
  let I := ccm3_inverseIdeal f.left x
  let k := (I.comapIso U.ι).hom ≫ CategoryTheory.Limits.pullback.snd U.ι I.subschemeι
  have hk : k ≫ I.subschemeι = (I.comap U.ι).subschemeι ≫ U.ι := by
    dsimp only [k]
    rw [Category.assoc, ← CategoryTheory.Limits.pullback.condition,
      ← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
  have : IsOpenImmersion k := by dsimp only [k]; infer_instance
  have hkSmooth : Smooth (k ≫ I.subschemeι ≫ X.hom) := by
    rw [← Category.assoc, hk]
    exact hsm
  have hbr : b ∈ Set.range k := by
    dsimp only [k]
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr (I.comapIso U.ι).hom.surjective,
      Set.image_univ, AlgebraicGeometry.Scheme.Pullback.range_snd, Scheme.Opens.range_ι]
    change I.subschemeι b ∈ U
    rw [hb]
    exact haU
  obtain ⟨b', rfl⟩ := hbr
  have htop := (k ≫ I.subschemeι ≫ X.hom).smoothLocus_eq_top
  rw [← Scheme.Hom.preimage_smoothLocus_eq] at htop
  exact htop.ge (show b' ∈ (⊤ : ((I.comap U.ι).subscheme).Opens) from trivial)

set_option backward.isDefEq.respectTransparency false in
private theorem ccm5_primeGoodOpen_smooth_source_witness
    {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) [Smooth f.left] (x : Z.left) (a : ccm5_primeGoodOpen f x)
    (z : {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0})
    (hz : a.1 ∈ cycleComponentAnalyticClosedSupport X z.1) :
    ∃ (Y : Scheme) (g : Y ⟶ cycleComponent Z.left x) (b : Y),
      Smooth g ∧ Smooth (g ≫ cycleComponentι Z.left x ≫ Z.hom) ∧
      cycleComponentι Z.left x (g b) = f.left a.1.underlying := by
  obtain ⟨U, haU, hsm⟩ := ccm5_primeGoodOpen_inverse_smooth_neighborhood_alt f x a z hz
  let J := ccm3_primeIdeal Z.left x
  let I := ccm3_inverseIdeal f.left x
  let k := (I.comapIso U.ι).hom ≫ CategoryTheory.Limits.pullback.snd U.ι I.subschemeι
  let r := (J.comapIso f.left).hom ≫ CategoryTheory.Limits.pullback.snd f.left J.subschemeι
  have hk : k ≫ I.subschemeι = (I.comap U.ι).subschemeι ≫ U.ι := by
    dsimp only [k]
    rw [Category.assoc, ← CategoryTheory.Limits.pullback.condition,
      ← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
  have hr : r ≫ J.subschemeι = I.subschemeι ≫ f.left := by
    dsimp only [r]
    rw [Category.assoc, ← CategoryTheory.Limits.pullback.condition,
      ← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
    rfl
  have hkr : (k ≫ r) ≫ J.subschemeι = (I.comap U.ι).subschemeι ≫ U.ι ≫ f.left := by
    rw [Category.assoc, hr, ← Category.assoc k, hk, Category.assoc]
  have haI : a.1.underlying ∈ I.support := by
    change a.1.underlying ∈ ((ccm3_inverseIdeal f.left x).support : Set X.left)
    rw [ccm5_inverseSupport_eq_component_union]
    exact Set.mem_iUnion.mpr ⟨z, hz⟩
  have har : (⟨a.1.underlying, haU⟩ : U) ∈ Set.range (I.comap U.ι).subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.support_comap]
    exact haI
  obtain ⟨b, hb⟩ := har
  refine ⟨(I.comap U.ι).subscheme, k ≫ r, b, ?_, ?_, ?_⟩
  · dsimp only [k, r]
    infer_instance
  · change Smooth (((k ≫ r) ≫ J.subschemeι) ≫ Z.hom)
    rw [hkr, Category.assoc, Category.assoc, f.w]
    exact hsm
  · change ((k ≫ r) ≫ J.subschemeι) b = _
    rw [hkr]
    change f.left (U.ι ((I.comap U.ι).subschemeι b)) = _
    rw [hb]
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem ccm5_smoothLocus_comp_of_smooth
    {X Y S : Scheme} (f : X ⟶ Y) (g : Y ⟶ S)
    [Smooth f] [LocallyOfFinitePresentation g]
    (x : X) (hx : f x ∈ g.smoothLocus) :
    x ∈ (f ≫ g).smoothLocus := by
  have hf : x ∈ f.smoothLocus := f.smoothLocus_eq_top.ge (Set.mem_univ x)
  change ((f ≫ g).stalkMap x).hom.FormallySmooth
  rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp]
  exact hx.comp hf

open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency false in
private theorem ccm5_pullback_section_smoothLocus
    {P C D S : Scheme} (f : P ⟶ C) (u : D ⟶ C)
    (h : C ⟶ S) (s : D ⟶ P) (hs : s ≫ f = u)
    [Smooth u] [LocallyOfFinitePresentation h]
    [LocallyOfFinitePresentation f]
    (d : D) (hd : s d ∈ (f ≫ h).smoothLocus) :
    d ∈ (u ≫ h).smoothLocus := by
  let r : D ⟶ pullback f u := pullback.lift s (𝟙 D) (by simpa only [Category.id_comp] using hs)
  have hr : r ≫ pullback.snd f u = 𝟙 D := pullback.lift_snd ..
  have he : pullback.fst f u (r d) = s d := by
    exact congrArg (fun k : D ⟶ P => k d) (pullback.lift_fst s (𝟙 D) _)
  have hm : r d ∈ (pullback.fst f u ≫ f ≫ h).smoothLocus := by
    apply ccm5_smoothLocus_comp_of_smooth
    rwa [he]
  have hc : pullback.fst f u ≫ f ≫ h = pullback.snd f u ≫ u ≫ h := by
    rw [← Category.assoc, pullback.condition, Category.assoc]
  simp only [hc] at hm
  exact ccm5_smoothLocus_of_section (pullback.snd f u) (u ≫ h) r hr d hm
universe u_ccm5

open TensorProduct in
set_option backward.isDefEq.respectTransparency true in
private theorem ccm5_cotangent_split_after_etale
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (P : Algebra.Extension.{u_ccm5} R S) (Q : Algebra.Extension.{u_ccm5} R T)
    (f : P.Hom Q) [Algebra P.Ring Q.Ring]
    (halg : algebraMap P.Ring Q.Ring = f.toRingHom)
    (hEt : f.toRingHom.FormallyEtale)
    (hker : Function.Bijective ((f.mapKer halg).liftBaseChange Q.Ring))
    [Algebra.FormallySmooth R Q.Ring] [Algebra.FormallySmooth R T] :
    ∃ l, l ∘ₗ P.cotangentComplex.baseChange T = LinearMap.id := by
  let eI : T ⊗[S] P.Cotangent ≃ₗ[T] Q.Cotangent := Algebra.Extension.tensorCotangent (R := R) (S := S) (T := T) (P := P) (Q := Q) f halg hker
  let eD : T ⊗[S] P.CotangentSpace ≃ₗ[T] Q.CotangentSpace := Algebra.Extension.tensorCotangentSpaceOfFormallyEtale (R := R) (S := S) (T := T) (P := P) (Q := Q) f hEt
  obtain ⟨l, hl⟩ := Q.formallySmooth_iff_split_injection.mp inferInstance
  have hc : eD.toLinearMap ∘ₗ P.cotangentComplex.baseChange T =
      Q.cotangentComplex ∘ₗ eI.toLinearMap := by
    ext x
    simp only [eI, eD, Algebra.Extension.tensorCotangent,
      Algebra.Extension.tensorCotangentSpaceOfFormallyEtale,
      AlgebraTensorModule.curry_apply, TensorProduct.curry_apply, LinearMap.coe_comp,
      LinearMap.coe_restrictScalars, Function.comp_apply,
      LinearMap.baseChange_tmul, LinearMap.liftBaseChange_tmul, one_smul]
    exact Algebra.Extension.CotangentSpace.map_cotangentComplex f x
  refine ⟨eI.symm.toLinearMap ∘ₗ l ∘ₗ eD.toLinearMap, ?_⟩
  rw [LinearMap.comp_assoc, LinearMap.comp_assoc, hc,
    ← LinearMap.comp_assoc eI.toLinearMap Q.cotangentComplex l, hl, LinearMap.id_comp]
  apply LinearMap.ext
  intro x
  exact eI.symm_apply_apply x
open TensorProduct in
private theorem ccm5_injective_baseChange_of_split
    {S T K : Type*} [CommRing S] [CommRing T] [CommRing K]
    [Algebra S T] [Algebra S K] [Algebra T K] [IsScalarTower S T K]
    {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module S M] [Module S N]
    (c : M →ₗ[S] N) (l : T ⊗[S] N →ₗ[T] T ⊗[S] M)
    (hl : l ∘ₗ c.baseChange T = LinearMap.id) :
    Function.Injective (c.baseChange K) := by
  let aM := AlgebraTensorModule.cancelBaseChange S T K K M
  let aN := AlgebraTensorModule.cancelBaseChange S T K K N
  have hi : Function.Injective ((c.baseChange T).baseChange K) := by
    apply Function.LeftInverse.injective (g := l.baseChange K)
    intro x
    have hh := congrArg (fun m : T ⊗[S] M →ₗ[T] T ⊗[S] M => m.baseChange K) hl
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at hh
    exact DFunLike.congr_fun hh x
  have hc : aN.toLinearMap ∘ₗ (c.baseChange T).baseChange K ∘ₗ aM.symm.toLinearMap =
      c.baseChange K := by
    ext x
    simp only [AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
      LinearEquiv.coe_coe, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
      aM, aN, AlgebraTensorModule.cancelBaseChange_symm_tmul,
      LinearMap.baseChange_tmul, AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
  rw [← hc]
  exact aN.injective.comp (hi.comp aM.symm.injective)
open TensorProduct in
set_option backward.isDefEq.respectTransparency false in
private theorem ccm5_formallySmooth_of_cotangent_field
    {R S K : Type*} [CommRing R] [CommRing S] [IsLocalRing S] [Field K]
    [Algebra R S] [Algebra S K]
    (P : Algebra.Extension.{u_ccm5} R S)
    [Algebra.FormallySmooth R P.Ring]
    [Module.Free P.Ring (KaehlerDifferential R P.Ring)]
    [Module.Finite P.Ring (KaehlerDifferential R P.Ring)]
    (hfg : P.ker.FG)
    (hmax : IsLocalRing.maximalIdeal S ≤ RingHom.ker (algebraMap S K))
    (hinj : Function.Injective (P.cotangentComplex.baseChange K)) :
    Algebra.FormallySmooth R S := by
  let f : IsLocalRing.ResidueField S →ₐ[S] K :=
    Ideal.Quotient.liftₐ _ (Algebra.ofId _ _) hmax
  let := f.toAlgebra
  have : IsScalarTower S (IsLocalRing.ResidueField S) K :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  apply (Algebra.FormallySmooth.iff_injective_lTensor_residueField P hfg).mpr
  change Function.Injective (P.cotangentComplex.baseChange (IsLocalRing.ResidueField S))
  rw [← Module.FaithfullyFlat.lTensor_injective_iff_injective _ K]
  change Function.Injective
    ((P.cotangentComplex.baseChange (IsLocalRing.ResidueField S)).baseChange K)
  let aM := AlgebraTensorModule.cancelBaseChange S (IsLocalRing.ResidueField S) K K P.Cotangent
  let aN := AlgebraTensorModule.cancelBaseChange S (IsLocalRing.ResidueField S) K K P.CotangentSpace
  have hc : aN.toLinearMap ∘ₗ
      (P.cotangentComplex.baseChange (IsLocalRing.ResidueField S)).baseChange K ∘ₗ
      aM.symm.toLinearMap = P.cotangentComplex.baseChange K := by
    ext x
    simp only [AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
      LinearEquiv.coe_coe, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
      aM, aN, AlgebraTensorModule.cancelBaseChange_symm_tmul,
      LinearMap.baseChange_tmul, AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
  rw [← hc] at hinj
  exact (aN.comp_injective _).mp ((aM.symm.injective_comp _).mp hinj)
private theorem ccm5_formallySmooth_of_etale_presentation
    {R S T K : Type*} [CommRing R] [CommRing S] [CommRing T] [Field K]
    [IsLocalRing S] [Algebra R S] [Algebra R T] [Algebra S T]
    [IsScalarTower R S T] [Algebra S K] [Algebra T K] [IsScalarTower S T K]
    (P : Algebra.Extension.{u_ccm5} R S) (Q : Algebra.Extension.{u_ccm5} R T)
    (f : P.Hom Q) [Algebra P.Ring Q.Ring]
    (halg : algebraMap P.Ring Q.Ring = f.toRingHom)
    (hEt : f.toRingHom.FormallyEtale)
    (hker : Function.Bijective ((f.mapKer halg).liftBaseChange Q.Ring))
    [Algebra.FormallySmooth R P.Ring] [Algebra.FormallySmooth R Q.Ring]
    [Algebra.FormallySmooth R T]
    [Module.Free P.Ring (KaehlerDifferential R P.Ring)]
    [Module.Finite P.Ring (KaehlerDifferential R P.Ring)]
    (hfg : P.ker.FG)
    (hmax : IsLocalRing.maximalIdeal S ≤ RingHom.ker (algebraMap S K)) :
    Algebra.FormallySmooth R S := by
  obtain ⟨l, hl⟩ := ccm5_cotangent_split_after_etale P Q f halg hEt hker
  apply ccm5_formallySmooth_of_cotangent_field (K := K) P hfg hmax
  exact ccm5_injective_baseChange_of_split (K := K) P.cotangentComplex l hl
set_option backward.isDefEq.respectTransparency false in
private theorem ccm5_extension_kernel_baseChange
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (P : Algebra.Extension.{u_ccm5} R S) (Q : Algebra.Extension.{u_ccm5} R T)
    (f : P.Hom Q) [Algebra P.Ring Q.Ring]
    (halg : algebraMap P.Ring Q.Ring = f.toRingHom)
    [Algebra P.Ring T] [IsScalarTower P.Ring S T] [IsScalarTower P.Ring Q.Ring T]
    [Module.Flat P.Ring Q.Ring]
    (hbase : IsBaseChange Q.Ring (IsScalarTower.toAlgHom P.Ring S T).toLinearMap) :
    Function.Bijective ((f.mapKer halg).liftBaseChange Q.Ring) := by
  apply IsBaseChange.of_left_exact Q.Ring (f.mapKer halg)
    (Algebra.linearMap P.Ring Q.Ring) (IsScalarTower.toAlgHom P.Ring S T).toLinearMap
    (f := P.ker.subtype) (g := Algebra.linearMap P.Ring S)
    (f' := Q.ker.subtype) (g' := Algebra.linearMap Q.Ring T)
  · ext x
    exact congrArg (fun k : P.Ring →+* Q.Ring => k x.1) halg
  · apply LinearMap.ext
    intro x
    exact (IsScalarTower.algebraMap_apply P.Ring S T x).symm.trans
      (IsScalarTower.algebraMap_apply P.Ring Q.Ring T x)
  · exact IsBaseChange.linearMap P.Ring Q.Ring
  · exact hbase
  · exact LinearMap.exact_subtype_ker_map (Algebra.linearMap P.Ring S)
  · exact Subtype.val_injective
  · exact LinearMap.exact_subtype_ker_map (Algebra.linearMap Q.Ring T)
  · exact Subtype.val_injective
set_option backward.isDefEq.respectTransparency false in
private theorem ccm5_formallySmooth_of_local_etale_square
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [IsLocalRing S] [IsLocalRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [IsLocalHom (algebraMap S T)]
    (P : Algebra.Extension.{u_ccm5} R S) (Q : Algebra.Extension.{u_ccm5} R T)
    (f : P.Hom Q) [Algebra P.Ring Q.Ring]
    (halg : algebraMap P.Ring Q.Ring = f.toRingHom)
    (hEt : f.toRingHom.FormallyEtale)
    [Algebra P.Ring T] [IsScalarTower P.Ring S T] [IsScalarTower P.Ring Q.Ring T]
    [Module.Flat P.Ring Q.Ring]
    (hbase : IsBaseChange Q.Ring (IsScalarTower.toAlgHom P.Ring S T).toLinearMap)
    [Algebra.FormallySmooth R P.Ring] [Algebra.FormallySmooth R Q.Ring]
    [Algebra.FormallySmooth R T]
    [Module.Free P.Ring (KaehlerDifferential R P.Ring)]
    [Module.Finite P.Ring (KaehlerDifferential R P.Ring)]
    (hfg : P.ker.FG) : Algebra.FormallySmooth R S := by
  let K := IsLocalRing.ResidueField T
  let : Algebra S K := ((algebraMap T K).comp (algebraMap S T)).toAlgebra
  have : IsScalarTower S T K := IsScalarTower.of_algebraMap_eq' rfl
  have hmax : IsLocalRing.maximalIdeal S ≤ RingHom.ker (algebraMap S K) := by
    intro x hx
    change IsLocalRing.residue T (algebraMap S T x) = 0
    apply (IsLocalRing.residue_eq_zero_iff _).mpr
    exact IsLocalRing.map_maximalIdeal_le (algebraMap S T)
      (Ideal.mem_map_of_mem (algebraMap S T) hx)
  exact ccm5_formallySmooth_of_etale_presentation (K := K) P Q f halg hEt
    (ccm5_extension_kernel_baseChange P Q f halg hbase) hfg hmax
open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency false in
private theorem ccm5_primeGoodOpen_etale_smooth_source_witness
    {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) [Smooth f.left] (x : Z.left) (a : ccm5_primeGoodOpen f x)
    (z : {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0})
    (hz : a.1 ∈ cycleComponentAnalyticClosedSupport X z.1) :
    ∃ (D : Scheme) (u : D ⟶ cycleComponent Z.left x) (d : D)
      (hu : Etale u),
      letI := hu
      d ∈ (u ≫ cycleComponentι Z.left x ≫ Z.hom).smoothLocus ∧
      cycleComponentι Z.left x (u d) = f.left a.1.underlying := by
  obtain ⟨W, s, t, hW, w, ht, hst, hw⟩ :=
    ccm5_smooth_etale_local_section_aux X Z f (dim Z.left) a.1
  let := ht
  let J := ccm3_primeIdeal Z.left x
  let I := ccm3_inverseIdeal f.left x
  have haI : a.1.underlying ∈ I.support := by
    change a.1.underlying ∈ ((ccm3_inverseIdeal f.left x).support : Set X.left)
    rw [ccm5_inverseSupport_eq_component_union]
    exact Set.mem_iUnion.mpr ⟨z, hz⟩
  obtain ⟨b, hb⟩ := I.range_subschemeι.ge haI
  let e := J.comapIso f.left
  let p := e.hom b
  have hp : pullback.fst f.left J.subschemeι p = a.1.underlying := by
    change (e.hom ≫ pullback.fst f.left J.subschemeι) b = _
    rw [Scheme.IdealSheafData.comapIso_hom_fst]
    exact hb
  have hs : s.left ≫ f.left = t.left := congrArg Over.Hom.left hst
  have hw' : s.left w.underlying = a.1.underlying := by
    exact congrArg Point.underlying hw
  have hwC : t.left w.underlying =
      J.subschemeι (pullback.snd f.left J.subschemeι p) := by
    rw [← hs]
    change f.left (s.left w.underlying) = _
    rw [hw', ← hp]
    exact congrArg (fun k => k p) (pullback.condition (f := f.left) (g := J.subschemeι))
  obtain ⟨d, hdw, hdc⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := t.left) (g := J.subschemeι) w.underlying
    (pullback.snd f.left J.subschemeι p) hwC
  let v : pullback t.left J.subschemeι ⟶ pullback f.left J.subschemeι :=
    pullback.lift (pullback.fst t.left J.subschemeι ≫ s.left)
      (pullback.snd t.left J.subschemeι) (by
        rw [Category.assoc, hs, pullback.condition])
  have hv : v ≫ pullback.snd f.left J.subschemeι =
      pullback.snd t.left J.subschemeι := pullback.lift_snd ..
  have hvd : v d = p := by
    apply (pullback.fst f.left J.subschemeι).isClosedEmbedding.injective
    change (v ≫ pullback.fst f.left J.subschemeι) d = _
    rw [pullback.lift_fst]
    change s.left (pullback.fst t.left J.subschemeι d) = _
    rw [hdw, hw', hp]
  have hbsm := (ccm5_primeGoodOpen_inverse_mem_smoothLocus) f x a z hz b hb
  have hec : e.inv ≫ I.subschemeι = pullback.fst f.left J.subschemeι := by
    exact Scheme.IdealSheafData.comapIso_inv_subschemeι J f.left
  have hepb : e.inv p = b := by
    change (e.hom ≫ e.inv) b = b
    rw [e.hom_inv_id]
    rfl
  have hm := (ccm5_smoothLocus_comp_of_smooth) e.inv
    (I.subschemeι ≫ X.hom) p (by rw [hepb]; exact hbsm)
  have hec' : e.inv ≫ I.subschemeι ≫ X.hom =
      pullback.snd f.left J.subschemeι ≫ J.subschemeι ≫ Z.hom := by
    rw [← Category.assoc, hec, ← f.w, ← Category.assoc,
      pullback.condition, Category.assoc]
  simp only [hec'] at hm
  have hdsm := (ccm5_pullback_section_smoothLocus)
    (pullback.snd f.left J.subschemeι) (pullback.snd t.left J.subschemeι)
    (J.subschemeι ≫ Z.hom) v hv d (hvd.symm ▸ hm)
  refine ⟨pullback t.left J.subschemeι, pullback.snd t.left J.subschemeι,
    d, inferInstance, hdsm, ?_⟩
  change J.subschemeι (pullback.snd t.left J.subschemeι d) = _
  rw [hdc, ← hwC, ← hs]
  change f.left (s.left w.underlying) = _
  rw [hw']
open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency false in
private theorem ccm5_closed_pullback_stalk_square
    {W Z C : Scheme} (t : W ⟶ Z) (i : C ⟶ Z) [IsClosedImmersion i]
    (d : (pullback t i : Scheme)) :
    let e := Z.presheaf.stalkCongr (Inseparable.of_eq
      (congrArg (fun k : pullback t i ⟶ Z => k d) (pullback.condition (f := t) (g := i))))
    t.stalkMap (pullback.fst t i d) ≫ (pullback.fst t i).stalkMap d =
      e.hom ≫ i.stalkMap (pullback.snd t i d) ≫ (pullback.snd t i).stalkMap d := by
  dsimp only
  rw [← Scheme.Hom.stalkMap_comp, ← Scheme.Hom.stalkMap_comp]
  exact Scheme.Hom.stalkMap_congr_hom _ _ (pullback.condition (f := t) (g := i)) d

private theorem ccm5_factor_fromSpecStalk_at_closedPoint
    {X : Scheme} (R : CommRingCat) [IsLocalRing R]
    (k : Spec R ⟶ X) (x : X) (hx : k (IsLocalRing.closedPoint R) = x) :
    ∃ r : X.presheaf.stalk x ⟶ R,
      Spec.map r ≫ X.fromSpecStalk x = k := by
  subst x
  exact ⟨Scheme.stalkClosedPointTo k, Scheme.Spec_stalkClosedPointTo_fromSpecStalk k⟩

open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency false in
private theorem ccm5_closed_pullback_stalk_kernel
    {W Z C : Scheme} (t : W ⟶ Z) (i : C ⟶ Z) [IsClosedImmersion i]
    (d : (pullback t i : Scheme)) :
    let e := Z.presheaf.stalkCongr (Inseparable.of_eq
      (congrArg (fun k : pullback t i ⟶ Z => k d) (pullback.condition (f := t) (g := i))))
    RingHom.ker ((pullback.fst t i).stalkMap d).hom =
      (RingHom.ker (e.hom ≫ i.stalkMap (pullback.snd t i d)).hom).map
        (t.stalkMap (pullback.fst t i d)).hom := by
  let w := pullback.fst t i d
  let c := pullback.snd t i d
  let e := Z.presheaf.stalkCongr (Inseparable.of_eq
    (congrArg (fun k : pullback t i ⟶ Z => k d) (pullback.condition (f := t) (g := i))))
  let f := t.stalkMap w
  let p := e.hom ≫ i.stalkMap c
  let q := (pullback.fst t i).stalkMap d
  let g := (pullback.snd t i).stalkMap d
  have hcomm : f ≫ q = p ≫ g := ccm5_closed_pullback_stalk_square t i d
  let J := (RingHom.ker p.hom).map f.hom
  have hle : J ≤ RingHom.ker q.hom := by
    rw [Ideal.map_le_iff_le_comap, RingHom.comap_ker]
    change RingHom.ker p.hom ≤ RingHom.ker (f ≫ q).hom
    rw [hcomm]
    intro a ha
    change g.hom (p.hom a) = 0
    rw [ha, map_zero]
  let D := (W.presheaf.stalk w) ⧸ J
  have hJ : J ≠ ⊤ := ne_top_of_le_ne_top (RingHom.ker_ne_top q.hom) hle
  letI : Nontrivial D := Ideal.Quotient.nontrivial_iff.mpr hJ
  letI : IsLocalRing D := IsLocalRing.of_surjective' (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective
  let v : W.presheaf.stalk w ⟶ CommRingCat.of D := CommRingCat.ofHom (Ideal.Quotient.mk J)
  have : IsLocalHom v.hom := IsLocalHom.of_surjective v.hom Ideal.Quotient.mk_surjective
  have hp : Function.Surjective p.hom :=
    (i.stalkMap_surjective c).comp (ConcreteCategory.bijective_of_isIso e.hom).2
  have hpv : RingHom.ker p.hom ≤ RingHom.ker (f ≫ v).hom := by
    intro a ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem f.hom ha)
  let l : C.presheaf.stalk c ⟶ CommRingCat.of D :=
    CommRingCat.ofHom (p.hom.liftOfSurjective hp ⟨(f ≫ v).hom, hpv⟩)
  have hpl : p ≫ l = f ≫ v := by
    exact CommRingCat.hom_ext (RingHom.liftOfSurjective_comp p.hom hp _)
  let kw := Spec.map v ≫ W.fromSpecStalk w
  let kc := Spec.map l ≫ C.fromSpecStalk c
  have hcone : kw ≫ t = kc ≫ i := by
    dsimp only [kw, kc]
    rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Spec.map_comp_assoc, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Spec.map_comp_assoc]
    have he : Spec.map e.hom ≫ Z.fromSpecStalk (t w) = Z.fromSpecStalk (i c) :=
      by
        dsimp only [e, TopCat.Presheaf.stalkCongr]
        exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk _
    change Spec.map (f ≫ v) ≫ Z.fromSpecStalk (t w) = _
    rw [← hpl]
    dsimp only [p]
    rw [Category.assoc, Spec.map_comp, Category.assoc, he]
  let k := pullback.lift kw kc hcone
  have hkd : k (IsLocalRing.closedPoint (CommRingCat.of D)) = d := by
    apply (pullback.fst t i).isClosedEmbedding.injective
    change (k ≫ pullback.fst t i) _ = w
    rw [pullback.lift_fst]
    change W.fromSpecStalk w (Spec.map v (IsLocalRing.closedPoint (CommRingCat.of D))) = w
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  obtain ⟨r, hr⟩ := ccm5_factor_fromSpecStalk_at_closedPoint (CommRingCat.of D) k d hkd
  have hqr : q ≫ r = v := by
    apply Spec.map_injective
    apply (cancel_mono (W.fromSpecStalk w)).mp
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Category.assoc, hr]
    exact pullback.lift_fst ..
  apply le_antisymm _ hle
  intro a ha
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change v.hom a = 0
  rw [← hqr]
  change r.hom (q.hom a) = 0
  rw [ha, map_zero]

open TensorProduct in
set_option backward.isDefEq.respectTransparency false in
private theorem ccm5_extension_kernel_baseChange_of_map
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (P : Algebra.Extension.{u_ccm5} R S) (Q : Algebra.Extension.{u_ccm5} R T)
    (f : P.Hom Q) [Algebra P.Ring Q.Ring]
    (halg : algebraMap P.Ring Q.Ring = f.toRingHom)
    [Module.Flat P.Ring Q.Ring]
    (hmap : Q.ker = P.ker.map f.toRingHom) :
    Function.Bijective ((f.mapKer halg).liftBaseChange Q.Ring) := by
  let l := (f.mapKer halg).liftBaseChange Q.Ring
  let c := Q.ker.subtype ∘ₗ l
  have hc : c = (AlgebraTensorModule.rid P.Ring Q.Ring Q.Ring).toLinearMap ∘ₗ
      P.ker.subtype.baseChange Q.Ring := by
    ext a
    simp only [AlgebraTensorModule.curry_apply, TensorProduct.curry_apply, LinearMap.coe_restrictScalars, c, l, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.liftBaseChange_tmul, one_smul, Submodule.subtype_apply,
      LinearEquiv.coe_coe, LinearMap.baseChange_tmul,
      AlgebraTensorModule.rid_tmul, Algebra.smul_def, mul_one, halg]
    rfl
  constructor
  · apply Function.Injective.of_comp (f := Q.ker.subtype)
    change Function.Injective c
    rw [hc]
    exact (AlgebraTensorModule.rid P.Ring Q.Ring Q.Ring).injective.comp
      (Module.Flat.lTensor_preserves_injective_linearMap P.ker.subtype
        Subtype.val_injective)
  · have hr : LinearMap.range c = Q.ker := by
      dsimp only [c, l]
      rw [LinearMap.liftBaseChange_comp, LinearMap.range_liftBaseChange]
      conv_rhs => rw [hmap]
      congr 1
      ext y
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨a.1, a.2, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨⟨a, ha⟩, rfl⟩
    intro y
    obtain ⟨a, ha⟩ := hr.ge y.2
    exact ⟨a, Subtype.ext ha⟩

set_option backward.isDefEq.respectTransparency false in
private theorem ccm5_formallySmooth_of_local_etale_kernel
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [IsLocalRing S] [IsLocalRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [IsLocalHom (algebraMap S T)]
    (P : Algebra.Extension.{u_ccm5} R S) (Q : Algebra.Extension.{u_ccm5} R T)
    (f : P.Hom Q) [Algebra P.Ring Q.Ring]
    (halg : algebraMap P.Ring Q.Ring = f.toRingHom)
    (hEt : f.toRingHom.FormallyEtale)
    [Module.Flat P.Ring Q.Ring]
    (hmap : Q.ker = P.ker.map f.toRingHom)
    [Algebra.FormallySmooth R P.Ring] [Algebra.FormallySmooth R Q.Ring]
    [Algebra.FormallySmooth R T]
    [Module.Free P.Ring (KaehlerDifferential R P.Ring)]
    [Module.Finite P.Ring (KaehlerDifferential R P.Ring)]
    (hfg : P.ker.FG) : Algebra.FormallySmooth R S := by
  let K := IsLocalRing.ResidueField T
  let : Algebra S K := ((algebraMap T K).comp (algebraMap S T)).toAlgebra
  have : IsScalarTower S T K := IsScalarTower.of_algebraMap_eq' rfl
  have hmax : IsLocalRing.maximalIdeal S ≤ RingHom.ker (algebraMap S K) := by
    intro x hx
    change IsLocalRing.residue T (algebraMap S T x) = 0
    apply (IsLocalRing.residue_eq_zero_iff _).mpr
    exact IsLocalRing.map_maximalIdeal_le (algebraMap S T)
      (Ideal.mem_map_of_mem (algebraMap S T) hx)
  exact ccm5_formallySmooth_of_etale_presentation (K := K) P Q f halg hEt
    (ccm5_extension_kernel_baseChange_of_map P Q f halg hmap) hfg hmax


open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency false in
private theorem ccm5_smoothLocus_descend_closed_etale
    {W Z C B₀ : Scheme} (t : W ⟶ Z) (i : C ⟶ Z) (h : Z ⟶ B₀)
    [IsLocallyNoetherian Z] [IsClosedImmersion i] [Etale t] [Smooth h]
    (d : (pullback t i : Scheme))
    (hd : d ∈ (pullback.fst t i ≫ t ≫ h).smoothLocus) :
    pullback.snd t i d ∈ (i ≫ h).smoothLocus := by
  let w := pullback.fst t i d
  let c := pullback.snd t i d
  have he : t w = i c := congrArg (fun k : pullback t i ⟶ Z => k d)
    (pullback.condition (f := t) (g := i))
  let e := Z.presheaf.stalkCongr (Inseparable.of_eq he)
  let eR := B₀.presheaf.stalkCongr (Inseparable.of_eq (congrArg h he))
  let R := B₀.presheaf.stalk (h (t w))
  let A := Z.presheaf.stalk (t w)
  let B := W.presheaf.stalk w
  let S := C.presheaf.stalk c
  let T := (pullback t i).presheaf.stalk d
  let a : R ⟶ A := h.stalkMap (t w)
  let f : A ⟶ B := t.stalkMap w
  let p : A ⟶ S := e.hom ≫ i.stalkMap c
  let q : B ⟶ T := (pullback.fst t i).stalkMap d
  let g : S ⟶ T := (pullback.snd t i).stalkMap d
  have hcomm : f ≫ q = p ≫ g := ccm5_closed_pullback_stalk_square t i d
  letI : Algebra R A := a.hom.toAlgebra
  letI : Algebra A B := f.hom.toAlgebra
  letI : Algebra A S := p.hom.toAlgebra
  letI : Algebra B T := q.hom.toAlgebra
  letI : Algebra S T := g.hom.toAlgebra
  letI : Algebra R B := (a ≫ f).hom.toAlgebra
  letI : Algebra R S := (a ≫ p).hom.toAlgebra
  letI : Algebra R T := (a ≫ f ≫ q).hom.toAlgebra
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R A S := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R B T := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' (by
    change (a ≫ f ≫ q).hom = (a ≫ p ≫ g).hom
    rw [← hcomm])
  have : IsLocalHom (algebraMap S T) := inferInstanceAs (IsLocalHom g.hom)
  have hA : a.hom.FormallySmooth := by
    change t w ∈ h.smoothLocus
    rw [h.smoothLocus_eq_top]
    trivial
  have hB : (a ≫ f).hom.FormallySmooth := by
    change (h.stalkMap (t w) ≫ t.stalkMap w).hom.FormallySmooth
    rw [← Scheme.Hom.stalkMap_comp]
    change w ∈ (t ≫ h).smoothLocus
    rw [Scheme.Hom.smoothLocus_eq_top]
    trivial
  have hT : (a ≫ f ≫ q).hom.FormallySmooth := by
    change (h.stalkMap (t w) ≫ t.stalkMap w ≫ (pullback.fst t i).stalkMap d).hom.FormallySmooth
    change ((pullback.fst t i ≫ t ≫ h).stalkMap d).hom.FormallySmooth at hd
    simpa only [Scheme.Hom.stalkMap_comp, Category.assoc] using hd
  have : Algebra.FormallySmooth R A := hA
  have : Algebra.FormallySmooth R B := hB
  have : Algebra.FormallySmooth R T := hT
  have : Algebra.EssFiniteType R A := LocallyOfFiniteType.stalkMap h (t w)
  have : Module.Finite A (KaehlerDifferential R A) := inferInstance
  have : Module.Free A (KaehlerDifferential R A) := Module.free_of_flat_of_isLocalRing
  have : Module.Flat A B := Flat.stalkMap t w
  letI P : Algebra.Extension R S := Algebra.Extension.ofSurjective
    (IsScalarTower.toAlgHom R A S)
    ((i.stalkMap_surjective c).comp (ConcreteCategory.bijective_of_isIso e.hom).2)
  letI Q : Algebra.Extension R T := Algebra.Extension.ofSurjective
    (IsScalarTower.toAlgHom R B T) ((pullback.fst t i).stalkMap_surjective d)
  let F : P.Hom Q :=
    { toRingHom := f.hom
      toRingHom_algebraMap := fun _ => rfl
      algebraMap_toRingHom := fun x => congrArg (fun k : A ⟶ T => k.hom x) hcomm }
  have hEt : f.hom.FormallyEtale := by
    have hfs : f.hom.FormallySmooth := by
      change w ∈ t.smoothLocus
      rw [t.smoothLocus_eq_top]
      trivial
    have : Algebra.FormallySmooth A B := hfs
    have : Algebra.FormallyUnramified A B := FormallyUnramified.stalkMap t w
    exact Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth
  letI : Algebra P.Ring Q.Ring := F.toRingHom.toAlgebra
  have : Module.Flat P.Ring Q.Ring := inferInstanceAs (Module.Flat A B)
  have : Algebra.FormallySmooth R P.Ring := inferInstanceAs (Algebra.FormallySmooth R A)
  have : Algebra.FormallySmooth R Q.Ring := inferInstanceAs (Algebra.FormallySmooth R B)
  have : Module.Free P.Ring (KaehlerDifferential R P.Ring) :=
    inferInstanceAs (Module.Free A (KaehlerDifferential R A))
  have : Module.Finite P.Ring (KaehlerDifferential R P.Ring) :=
    inferInstanceAs (Module.Finite A (KaehlerDifferential R A))
  have hmap : Q.ker = P.ker.map F.toRingHom := ccm5_closed_pullback_stalk_kernel t i d
  have hfg : P.ker.FG := (isNoetherianRing_iff_ideal_fg A).mp inferInstance P.ker
  have hS : Algebra.FormallySmooth R S := ccm5_formallySmooth_of_local_etale_kernel
    P Q F rfl hEt hmap hfg
  have hap : a ≫ p = eR.hom ≫ (i ≫ h).stalkMap c := by
    dsimp only [a, p]
    rw [← Category.assoc, h.stalkMap_congr_point (t w) (i c) he,
      Category.assoc, ← Scheme.Hom.stalkMap_comp]
  have hs : (a ≫ p).hom.FormallySmooth := hS
  rw [hap] at hs
  exact (RingHom.FormallySmooth.respectsIso.cancel_left_isIso
    eR.hom ((i ≫ h).stalkMap c)).mp hs

open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency false in
private theorem ccm5_primeGoodOpen_etale_slice_witness
    {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) [Smooth f.left] (x : Z.left) (a : ccm5_primeGoodOpen f x)
    (z : {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0})
    (hz : a.1 ∈ cycleComponentAnalyticClosedSupport X z.1) :
    ∃ (W : Over (Spec ↧ℂ)) (t : W ⟶ Z)
      (d : (pullback t.left (cycleComponentι Z.left x) : Scheme))
      (ht : Etale t.left),
      letI := ht
      d ∈ (pullback.snd t.left (cycleComponentι Z.left x) ≫
        cycleComponentι Z.left x ≫ Z.hom).smoothLocus ∧
      cycleComponentι Z.left x (pullback.snd t.left (cycleComponentι Z.left x) d) =
        f.left a.1.underlying := by
  obtain ⟨W, s, t, hW, w, ht, hst, hw⟩ :=
    ccm5_smooth_etale_local_section_aux X Z f (dim Z.left) a.1
  let := ht
  let J := ccm3_primeIdeal Z.left x
  let I := ccm3_inverseIdeal f.left x
  have haI : a.1.underlying ∈ I.support := by
    change a.1.underlying ∈ ((ccm3_inverseIdeal f.left x).support : Set X.left)
    rw [ccm5_inverseSupport_eq_component_union]
    exact Set.mem_iUnion.mpr ⟨z, hz⟩
  obtain ⟨b, hb⟩ := I.range_subschemeι.ge haI
  let e := J.comapIso f.left
  let p := e.hom b
  have hp : pullback.fst f.left J.subschemeι p = a.1.underlying := by
    change (e.hom ≫ pullback.fst f.left J.subschemeι) b = _
    rw [Scheme.IdealSheafData.comapIso_hom_fst]
    exact hb
  have hs : s.left ≫ f.left = t.left := congrArg Over.Hom.left hst
  have hw' : s.left w.underlying = a.1.underlying := by
    exact congrArg Point.underlying hw
  have hwC : t.left w.underlying =
      J.subschemeι (pullback.snd f.left J.subschemeι p) := by
    rw [← hs]
    change f.left (s.left w.underlying) = _
    rw [hw', ← hp]
    exact congrArg (fun k => k p) (pullback.condition (f := f.left) (g := J.subschemeι))
  obtain ⟨d, hdw, hdc⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := t.left) (g := J.subschemeι) w.underlying
    (pullback.snd f.left J.subschemeι p) hwC
  let v : pullback t.left J.subschemeι ⟶ pullback f.left J.subschemeι :=
    pullback.lift (pullback.fst t.left J.subschemeι ≫ s.left)
      (pullback.snd t.left J.subschemeι) (by
        rw [Category.assoc, hs, pullback.condition])
  have hv : v ≫ pullback.snd f.left J.subschemeι =
      pullback.snd t.left J.subschemeι := pullback.lift_snd ..
  have hvd : v d = p := by
    apply (pullback.fst f.left J.subschemeι).isClosedEmbedding.injective
    change (v ≫ pullback.fst f.left J.subschemeι) d = _
    rw [pullback.lift_fst]
    change s.left (pullback.fst t.left J.subschemeι d) = _
    rw [hdw, hw', hp]
  have hbsm := (ccm5_primeGoodOpen_inverse_mem_smoothLocus) f x a z hz b hb
  have hec : e.inv ≫ I.subschemeι = pullback.fst f.left J.subschemeι := by
    exact Scheme.IdealSheafData.comapIso_inv_subschemeι J f.left
  have hepb : e.inv p = b := by
    change (e.hom ≫ e.inv) b = b
    rw [e.hom_inv_id]
    rfl
  have hm := (ccm5_smoothLocus_comp_of_smooth) e.inv
    (I.subschemeι ≫ X.hom) p (by rw [hepb]; exact hbsm)
  have hec' : e.inv ≫ I.subschemeι ≫ X.hom =
      pullback.snd f.left J.subschemeι ≫ J.subschemeι ≫ Z.hom := by
    rw [← Category.assoc, hec, ← f.w, ← Category.assoc,
      pullback.condition, Category.assoc]
  simp only [hec'] at hm
  have hdsm := (ccm5_pullback_section_smoothLocus)
    (pullback.snd f.left J.subschemeι) (pullback.snd t.left J.subschemeι)
    (J.subschemeι ≫ Z.hom) v hv d (hvd.symm ▸ hm)
  refine ⟨W, t, d, ht, hdsm, ?_⟩
  change J.subschemeι (pullback.snd t.left J.subschemeι d) = _
  rw [hdc, ← hwC, ← hs]
  change f.left (s.left w.underlying) = _
  rw [hw']

private theorem ccm5_component_image_mem_smoothSupport_of_stalk
    (Z : Over (Spec ↧ℂ))
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (x : Z.left) (b : cycleComponent Z.left x) (a : ComplexPoint Z)
    (hb : cycleComponentι Z.left x b = a.underlying)
    (hsm : ((cycleComponentι Z.left x ≫ Z.hom).stalkMap b).hom.FormallySmooth) :
    a ∈ cycleComponentSmoothSupportAmbientOpen Z x := by
  change a.underlying ∉ cycleComponentι Z.left x ''
    (singularLocusClosed (cycleComponentι Z.left x ≫ Z.hom) : Set _)
  rintro ⟨c, hc, he⟩
  have hcb : c = b := (cycleComponentι Z.left x).isClosedEmbedding.injective
    (he.trans hb.symm)
  subst c
  exact hc hsm

open CategoryTheory.Limits in
set_option backward.isDefEq.respectTransparency false in
private theorem ccm5_primeGoodOpen_image_mem_smoothSupport
    {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) [Smooth f.left] (q : ℕ) (x : Z.left)
    (hx : Order.coheight x = q) (a : ccm5_primeGoodOpen f x)
    (haS : a.1 ∈ (ccm4_inverseAnalyticSupport f
      (cycleComponentAnalyticClosedSupport Z x) : Set (ComplexPoint X))) :
    Point.map f a.1 ∈ cycleComponentSmoothSupportAmbientOpen Z x := by
  rw [ccm5_inverseAnalyticSupport_eq_component_union_aux] at haS
  obtain ⟨z, hz⟩ := Set.mem_iUnion.mp haS
  obtain ⟨W, t, d, ht, hd, he⟩ := ccm5_primeGoodOpen_etale_slice_witness f x a z hz
  letI := ht
  have : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  have hsm := ccm5_smoothLocus_descend_closed_etale t.left
    (cycleComponentι Z.left x) Z.hom d (by
      simpa only [← Category.assoc, pullback.condition] using hd)
  exact ccm5_component_image_mem_smoothSupport_of_stalk Z x
    (pullback.snd t.left (cycleComponentι Z.left x) d) (Point.map f a.1) he hsm

private theorem ccm5_reduced_closedImmersion_iso_of_range_eq
    {Y₁ Y₂ T : Scheme} (i₁ : Y₁ ⟶ T) (i₂ : Y₂ ⟶ T)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    [IsReduced Y₁] [IsReduced Y₂] (h : Set.range i₁ = Set.range i₂) :
    ∃ e : Y₁ ≅ Y₂, e.hom ≫ i₂ = i₁ := by
  have hk (Y : Scheme) [IsReduced Y] (i : Y ⟶ T) :
      i.ker = Scheme.IdealSheafData.vanishingIdeal (.closure (Set.range i)) := by
    have hi := Scheme.IdealSheafData.map_vanishingIdeal i (⊤ : Closeds Y)
    simpa only [Scheme.IdealSheafData.vanishingIdeal_top, Scheme.nilradical_eq_bot,
      Scheme.IdealSheafData.map_bot, Closeds.coe_top, Set.image_univ] using hi
  have he : i₂.ker = i₁.ker := by rw [hk Y₂ i₂, hk Y₁ i₁, h]
  let e := IsClosedImmersion.lift i₂ i₁ he.le
  have : IsIso e := IsClosedImmersion.isIso_lift i₂ i₁ he
  exact ⟨asIso e, IsClosedImmersion.lift_fac i₂ i₁ he.le⟩

private theorem ccm5_range_morphismRestrict {Y T : Scheme} (i : Y ⟶ T) (U : T.Opens) :
    Set.range (i ∣_ U) = U.ι ⁻¹' Set.range i := by
  ext b
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c.1, (morphismRestrict_base_coe i U c).symm⟩
  · rintro ⟨c, hc⟩
    have hcU : c ∈ i ⁻¹ᵁ U := by
      change i c ∈ U
      exact hc ▸ b.2
    refine ⟨⟨c, hcU⟩, Subtype.ext ?_⟩
    exact (morphismRestrict_base_coe i U ⟨c, hcU⟩).trans hc

private theorem ccm5_inverseIdeal_support_eq_component_union
    {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) (x : Z.left) :
    ((ccm3_inverseIdeal f.left x).support : Set X.left) =
      ⋃ z : {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0},
        closure ({z.1} : Set X.left) := by
  let I := ccm3_inverseIdeal f.left x
  have hrange : Set.range I.subschemeι = f.left ⁻¹' closure ({x} : Set Z.left) := by
    rw [I.range_subschemeι]
    simp only [I, ccm3_inverseIdeal, Scheme.IdealSheafData.support_comap,
      ccm3_primeIdeal]
    rfl
  ext a
  change a ∈ (I.support : Set X.left) ↔ _
  rw [← I.range_subschemeι, hrange]
  constructor
  · intro ha
    have har : a ∈ Set.range I.subschemeι := by
      rw [hrange]
      exact ha
    obtain ⟨b, hb⟩ := har
    let C := irreducibleComponent b
    have hC : C ∈ irreducibleComponents I.subscheme :=
      irreducibleComponent_mem_irreducibleComponents b
    let y := hC.1.genericPoint
    have hy : closure ({y} : Set I.subscheme) = C :=
      hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ hC)
    have hz : ccm3_flatPullbackPrime f.left x (I.subschemeι y) ≠ 0 :=
      (ccm3_flatPullbackPrime_support f x _).mpr ⟨y, rfl, hy ▸ hC⟩
    apply Set.mem_iUnion.mpr
    refine ⟨⟨I.subschemeι y, hz⟩, ?_⟩
    change a ∈ closure ({I.subschemeι y} : Set X.left)
    rw [← hb]
    have hbc : b ∈ closure ({y} : Set I.subscheme) := hy.symm ▸ mem_irreducibleComponent
    have him := image_closure_subset_closure_image I.subschemeι.continuous
      (s := ({y} : Set I.subscheme))
    simpa only [Set.image_singleton] using him ⟨b, hbc, rfl⟩
  · intro ha
    obtain ⟨z, hz⟩ := Set.mem_iUnion.mp ha
    obtain ⟨y, heq, hy⟩ := (ccm3_flatPullbackPrime_support f x z.1).mp z.2
    change a ∈ closure ({z.1} : Set X.left) at hz
    have hclosed : IsClosed (f.left ⁻¹' closure ({x} : Set Z.left)) :=
      isClosed_closure.preimage f.left.continuous
    apply (hclosed.closure_subset_iff.mpr ?_) hz
    rw [Set.singleton_subset_iff, ← heq, ← hrange]
    exact ⟨y, rfl⟩


private theorem ccm5_primeGoodOpen_algebraic_component_neighborhood
    {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) (x : Z.left) (a : ccm5_primeGoodOpen f x)
    (z : {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0})
    (hz : a.1 ∈ cycleComponentAnalyticClosedSupport X z.1) :
    ∃ U : X.left.Opens, a.1.underlying ∈ U ∧
      U ≤ cycleComponentSmoothLocusAmbientOpen X z.1 ∧
      ∀ b ∈ U, b ∈ (ccm3_inverseIdeal f.left x).support ↔
        b ∈ closure ({z.1} : Set X.left) := by
  classical
  have hothers : ∀ᶠ b in 𝓝 a.1.underlying,
      ∀ w : {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0},
        w ≠ z → b ∉ closure ({w.1} : Set X.left) := by
    rw [Filter.eventually_all]
    intro w
    by_cases hw : w = z
    · exact Filter.Eventually.of_forall (fun _ h => (h hw).elim)
    · have hij : (ccm5_primeEnumeration f x).symm z ≠
          (ccm5_primeEnumeration f x).symm w := by
        intro h
        exact hw ((ccm5_primeEnumeration f x).symm.injective h).symm
      have hn := ccm5_primeGoodOpen_component_disjoint f x a _ _ hij
      simp only [Equiv.apply_symm_apply] at hn
      have hn' : a.1.underlying ∉ closure ({w.1} : Set X.left) := hn hz
      have hn'' : ∀ᶠ b in 𝓝 a.1.underlying, b ∉ closure ({w.1} : Set X.left) :=
        isClosed_closure.isOpen_compl.mem_nhds hn'
      exact hn''.mono (fun _ hb _ => hb)
  have hs : a.1.underlying ∈ cycleComponentSmoothLocusAmbientOpen X z.1 := by
    have h := ccm5_primeGoodOpen_mem_smoothSupport f x a
      ((ccm5_primeEnumeration f x).symm z)
    simp only [Equiv.apply_symm_apply] at h
    change a.1.underlying ∉ cycleComponentSingularAmbientClosedFiltration X z.1 0
    exact h
  have hgood : ∀ᶠ b in 𝓝 a.1.underlying,
      b ∈ cycleComponentSmoothLocusAmbientOpen X z.1 :=
    (cycleComponentSmoothLocusAmbientOpen X z.1).isOpen.mem_nhds hs
  obtain ⟨U, hU, hopen, haU⟩ := mem_nhds_iff.mp (hgood.and hothers)
  refine ⟨⟨U, hopen⟩, haU, fun b hb => (hU hb).1, fun b hb => ?_⟩
  change b ∈ ((ccm3_inverseIdeal f.left x).support : Set X.left) ↔ _
  rw [ccm5_inverseIdeal_support_eq_component_union]
  constructor
  · intro h
    obtain ⟨w, hw⟩ := Set.mem_iUnion.mp h
    by_cases he : w = z
    · subst w
      exact hw
    · exact ((hU hb).2 w he hw).elim
  · intro hz'
    exact Set.mem_iUnion.mpr ⟨z, hz'⟩

private theorem ccm5_primeGoodOpen_inverse_smooth_neighborhood
    {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) [Smooth f.left] (x : Z.left) (a : ccm5_primeGoodOpen f x)
    (z : {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0})
    (hz : a.1 ∈ cycleComponentAnalyticClosedSupport X z.1) :
    ∃ U : X.left.Opens, a.1.underlying ∈ U ∧
      Smooth (((ccm3_inverseIdeal f.left x).subschemeι ⁻¹ᵁ U).ι ≫
        (ccm3_inverseIdeal f.left x).subschemeι ≫ X.hom) := by
  obtain ⟨U, haU, hUs, heq⟩ :=
    ccm5_primeGoodOpen_algebraic_component_neighborhood f x a z hz
  let i := cycleComponentι X.left z.1
  let j := (ccm3_inverseIdeal f.left x).subschemeι
  have hpre : i ⁻¹ᵁ U ≤ (i ≫ X.hom).smoothLocus := by
    intro b hb
    have h := hUs hb
    change i b ∉ i '' (singularLocusClosed (i ≫ X.hom) : Set _) at h
    by_contra hn
    exact h ⟨b, hn, rfl⟩
  have hsm : Smooth ((i ⁻¹ᵁ U).ι ≫ i ≫ X.hom) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    apply top_unique
    intro b _
    exact hpre b.2
  have : IsReduced (ccm3_inverseIdeal f.left x).subscheme :=
    ccm5_inverseIdeal_isReduced f.left x
  have hr : Set.range (j ∣_ U) = Set.range (i ∣_ U) := by
    rw [ccm5_range_morphismRestrict, ccm5_range_morphismRestrict]
    rw [show Set.range j = ((ccm3_inverseIdeal f.left x).support : Set X.left) from
      (ccm3_inverseIdeal f.left x).range_subschemeι, range_cycleComponentι]
    ext b
    exact heq b.1 b.2
  obtain ⟨e, he⟩ := ccm5_reduced_closedImmersion_iso_of_range_eq (j ∣_ U) (i ∣_ U) hr
  refine ⟨U, haU, ?_⟩
  have hcomp : e.hom ≫ (i ⁻¹ᵁ U).ι ≫ i ≫ X.hom =
      (j ⁻¹ᵁ U).ι ≫ j ≫ X.hom := by
    rw [← morphismRestrict_ι_assoc, ← Category.assoc e.hom, he,
      morphismRestrict_ι_assoc]
  rw [← hcomp]
  infer_instance

private theorem ccm5_inverseIdeal_projection_smooth
    {X Z : Scheme} (f : X ⟶ Z) [Smooth f] (x : Z) :
    Smooth (Scheme.IdealSheafData.subschemeMap (ccm3_inverseIdeal f x)
      (ccm3_primeIdeal Z x) f ((ccm3_primeIdeal Z x).le_map_comap f)) := by
  change Smooth (((ccm3_primeIdeal Z x).comap f).subschemeMap
    (ccm3_primeIdeal Z x) f ((ccm3_primeIdeal Z x).le_map_comap f))
  rw [← Scheme.IdealSheafData.comapIso_hom_snd]
  infer_instance

private theorem ccm5_primeGoodOpen_smooth_cover_of_component_point
    {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) [Smooth f.left] (x : Z.left) (a : ccm5_primeGoodOpen f x)
    (z : {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0})
    (hz : a.1 ∈ cycleComponentAnalyticClosedSupport X z.1) :
    ∃ (W : Scheme) (p : W ⟶ cycleComponent Z.left x) (w : W),
      Smooth p ∧ Smooth (p ≫ cycleComponentι Z.left x ≫ Z.hom) ∧
      cycleComponentι Z.left x (p w) = (Point.map f a.1).underlying := by
  obtain ⟨U, haU, hsm⟩ := ccm5_primeGoodOpen_inverse_smooth_neighborhood f x a z hz
  let I := ccm3_inverseIdeal f.left x
  let J := ccm3_primeIdeal Z.left x
  let k := Scheme.IdealSheafData.subschemeMap I J f.left (J.le_map_comap f.left)
  have hk : k ≫ J.subschemeι = I.subschemeι ≫ f.left :=
    Scheme.IdealSheafData.subschemeMap_subschemeι I J f.left (J.le_map_comap f.left)
  have hs : a.1.underlying ∈ I.support := by
    change a.1.underlying ∈ ((ccm3_inverseIdeal f.left x).support : Set X.left)
    rw [ccm5_inverseIdeal_support_eq_component_union]
    exact Set.mem_iUnion.mpr ⟨z, hz⟩
  obtain ⟨b, hb⟩ := I.range_subschemeι.symm.subset hs
  have hbU : b ∈ I.subschemeι ⁻¹ᵁ U := by
    change I.subschemeι b ∈ U
    rwa [hb]
  let V := I.subschemeι ⁻¹ᵁ U
  have : Smooth k := ccm5_inverseIdeal_projection_smooth f.left x
  refine ⟨V.toScheme, V.ι ≫ k, ⟨b, hbU⟩, ?_, ?_, ?_⟩
  · change Smooth (V.ι ≫ k)
    exact smooth_comp V.ι k
  · change Smooth (V.ι ≫ k ≫ J.subschemeι ≫ Z.hom)
    rw [← Category.assoc k, hk, Category.assoc, f.w]
    exact hsm
  · change J.subschemeι ((V.ι ≫ k) ⟨b, hbU⟩) = f.left a.1.underlying
    change (k ≫ J.subschemeι) b = f.left a.1.underlying
    rw [hk, Scheme.Hom.comp_apply, hb]

private theorem ccm5_formallySmooth_of_algebra_retract
    {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.FormallySmooth R B]
    (i : A →ₐ[R] B) (r : B →ₐ[R] A) (h : r.comp i = AlgHom.id R A) :
    Algebra.FormallySmooth R A := by
  refine Algebra.FormallySmooth.of_comp_surjective fun C _ _ I hI f => ?_
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.comp_surjective R B I hI (f.comp r)
  refine ⟨g.comp i, ?_⟩
  rw [← AlgHom.comp_assoc, hg, AlgHom.comp_assoc, h, AlgHom.comp_id]

private theorem ccm5_formallySmooth_of_ring_retract
    {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    (f : R →+* A) (i : A →+* B) (r : B →+* A)
    (h : r.comp i = RingHom.id A) (hs : (i.comp f).FormallySmooth) :
    f.FormallySmooth := by
  algebraize [f, i.comp f]
  let i' : A →ₐ[R] B := ⟨i, fun _ => rfl⟩
  let r' : B →ₐ[R] A := ⟨r, fun x => congr($h (f x))⟩
  exact ccm5_formallySmooth_of_algebra_retract i' r' (AlgHom.ext fun x => congr($h x))

set_option backward.isDefEq.respectTransparency false in
private theorem ccm5_smooth_of_section
    {W Y Z : Scheme.{0}} (p : W ⟶ Y) (s : Y ⟶ W) (g : Y ⟶ Z)
    (hsp : s ≫ p = 𝟙 Y) [LocallyOfFinitePresentation g] [Smooth (p ≫ g)] :
    Smooth g := by
  rw [← Scheme.Hom.smoothLocus_eq_top_iff]
  apply top_unique
  intro y _
  have hy : p (s y) = y := congr($(hsp) y)
  let e := Y.presheaf.stalkCongr (Inseparable.of_eq hy)
  let e' := Z.presheaf.stalkCongr (Inseparable.of_eq (congrArg g hy))
  let i := e.inv ≫ p.stalkMap (s y)
  have hret : i ≫ s.stalkMap y = 𝟙 _ := by
    dsimp only [i]
    rw [Category.assoc, ← Scheme.Hom.stalkMap_comp,
      Scheme.Hom.stalkMap_congr_hom _ _ hsp, Scheme.Hom.stalkMap_id]
    change e.inv ≫ e.hom ≫ 𝟙 _ = 𝟙 _
    rw [Category.comp_id, e.inv_hom_id]
  have hcomm : g.stalkMap y ≫ i = e'.inv ≫ (p ≫ g).stalkMap (s y) := by
    dsimp only [i]
    rw [Scheme.Hom.stalkMap_comp, ← Category.assoc, ← Category.assoc]
    congr 1
    rw [Iso.comp_inv_eq, Category.assoc]
    symm
    apply (Iso.inv_comp_eq e').mpr
    exact Scheme.Hom.stalkMap_congr_point g _ _ hy
  have hs : ((p ≫ g).stalkMap (s y)).hom.FormallySmooth := by
    apply (Scheme.Hom.mem_smoothLocus).mp
    rw [Scheme.Hom.smoothLocus_eq_top]
    trivial
  apply (Scheme.Hom.mem_smoothLocus).mpr
  apply ccm5_formallySmooth_of_ring_retract (g.stalkMap y).hom i.hom (s.stalkMap y).hom
  · exact congrArg CommRingCat.Hom.hom hret
  · rw [← CommRingCat.hom_comp, hcomm, CommRingCat.hom_comp]
    exact (RingHom.FormallySmooth.of_bijective
      (ConcreteCategory.bijective_of_isIso e'.inv)).comp hs

private theorem ccm5_smooth_cover_stalk_maps
    {W Y Z : Scheme.{0}} (p : W ⟶ Y) (g : Y ⟶ Z)
    [Smooth p] [Smooth (p ≫ g)] (w : W) :
    (p.stalkMap w).hom.FaithfullyFlat ∧
      (p.stalkMap w).hom.FormallySmooth ∧
      ((p.stalkMap w).hom.comp (g.stalkMap (p w)).hom).FormallySmooth := by
  have hs {V T : Scheme.{0}} (f : V ⟶ T) [Smooth f] (v : V) :
      (f.stalkMap v).hom.FormallySmooth := by
    apply Scheme.Hom.mem_smoothLocus.mp
    rw [Scheme.Hom.smoothLocus_eq_top]
    trivial
  refine ⟨?_, hs p w, ?_⟩
  · algebraize [(p.stalkMap w).hom]
    exact @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _
      (Flat.stalkMap p w) (p.toLRSHom.prop w)
  · rw [← CommRingCat.hom_comp, ← Scheme.Hom.stalkMap_comp]
    exact hs (p ≫ g) w

set_option backward.isDefEq.respectTransparency false in
private theorem ccm5_supportedPullback_germ_normalChart
    {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) (S : Closeds (ComplexPoint Z)) (q : ℕ)
    (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : OpenPartialHomeomorph (ComplexPoint X) (E × (Fin q → ℂ)))
    (d : OpenPartialHomeomorph (ComplexPoint Z) (F × (Fin q → ℂ)))
    (he : ∀ y ∈ e.source, y ∈ (ccm4_inverseAnalyticSupport f S : Set (ComplexPoint X)) ↔ (e y).2 = 0)
    (hd : ∀ y ∈ d.source, y ∈ (S : Set (ComplexPoint Z)) ↔ (d y).2 = 0)
    (V : Opens (ComplexPoint X)) (W : Opens (ComplexPoint Z))
    (hV : (V : Set (ComplexPoint X)) ⊆ e.source)
    (hW : (W : Set (ComplexPoint Z)) ⊆ d.source)
    (hf : ∀ y ∈ V, Point.map f y ∈ W)
    (hn : ∀ y ∈ V, (d (Point.map f y)).2 = (e y).2)
    (u : TopCat.Sheaf.supportH (TopCat.of (ComplexPoint Z)) S
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint Z))).obj
        (AddCommGrpCat.of ℚ)) (2 * q))
    (hu : relativeCohomologyMap ℚ (2 * q)
      (neighborhoodSupportInclusionPairMap (Set.subset_univ (W : Set (ComplexPoint Z)))
        (S : Set (ComplexPoint Z))) (supportedSingularClass Z S (2 * q) u) =
      chartNormalProjectionCoclass F q d (S : Set (ComplexPoint Z)) hd W hW)
    (a : ComplexPoint X) (ha : a ∈ V) :
    ccm5_supportGerm X (ccm4_inverseAnalyticSupport f S) (2 * q) a
      (ccm4_supportedPullback f S (2 * q) u) =
    supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
      (ccm4_inverseAnalyticSupport f S : Set (ComplexPoint X)) (2 * q) V a ha
      (chartNormalProjectionCoclass E q e
        (ccm4_inverseAnalyticSupport f S : Set (ComplexPoint X)) he V hV) := by
  let φ : neighborhoodSupportComplementPair (V : Set (ComplexPoint X))
      (ccm4_inverseAnalyticSupport f S : Set (ComplexPoint X)) ⟶
      neighborhoodSupportComplementPair (W : Set (ComplexPoint Z)) (S : Set (ComplexPoint Z)) :=
    TopPair.ofHom
      (TopCat.ofHom ⟨fun y => ⟨Point.continuousMap f y.1, hf y.1 y.2⟩, by fun_prop⟩)
      (TopCat.ofHom ⟨fun y => ⟨⟨Point.continuousMap f y.1.1, hf y.1.1 y.1.2⟩, y.2⟩, by fun_prop⟩)
      (by ext y; rfl)
  have hcomm : neighborhoodSupportInclusionPairMap (Set.subset_univ (V : Set (ComplexPoint X)))
      (ccm4_inverseAnalyticSupport f S : Set (ComplexPoint X)) ≫ ccm4_inverseSupportPairMap f S =
      φ ≫ neighborhoodSupportInclusionPairMap (Set.subset_univ (W : Set (ComplexPoint Z)))
        (S : Set (ComplexPoint Z)) := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext y <;> rfl
  rw [← ccm5_supportGerm_restriction_aux X (ccm4_inverseAnalyticSupport f S) V (2 * q) a ha]
  congr 1
  simp only [ccm4_supportedPullback, AddMonoidHom.comp_apply,
    AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply]
  change relativeCohomologyMap ℚ (2 * q) _
    (relativeCohomologyMap ℚ (2 * q) (ccm4_inverseSupportPairMap f S)
      (supportedSingularClass Z S (2 * q) u)) = _
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp, hcomm,
    relativeCohomologyMap_comp, LinearMap.comp_apply, hu]
  apply ccm5_chartNormalProjectionCoclass_pullback
  intro y
  exact hn y.1 y.2

set_option backward.isDefEq.respectTransparency false in
private theorem ccm5_chartNormalProjectionCoclass_germ_eq
    {M E : Type} [TopologicalSpace M]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (q : ℕ) (e d : OpenPartialHomeomorph M (E × (Fin q → ℂ)))
    (S : Set M)
    (he : ∀ y ∈ e.source, y ∈ S ↔ (e y).2 = 0)
    (hd : ∀ y ∈ d.source, y ∈ S ↔ (d y).2 = 0)
    (a : M) (hae : a ∈ e.source) (had : a ∈ d.source) (haS : a ∈ S)
    (ht : AnalyticAt ℂ (e.symm.trans d) (e a))
    (hti : AnalyticAt ℂ (e.symm.trans d).symm ((e.symm.trans d) (e a))) :
    supportRelativeCohomologyGerm (TopCat.of M) S (2 * q) ⟨e.source, e.open_source⟩ a hae
      (chartNormalProjectionCoclass E q e S he e.source (le_refl _)) =
    supportRelativeCohomologyGerm (TopCat.of M) S (2 * q) ⟨d.source, d.open_source⟩ a had
      (chartNormalProjectionCoclass E q d S hd d.source (le_refl _)) := by
  obtain ⟨W, hWe, hWd, haW, hW⟩ :=
    exists_open_chartNormalProjectionCoclass_eq q e d S he hd a hae
      ((he a hae).mp haS) had ht hti
  apply supportRelativeCohomologyGerm_eq_of_restrict_eq (TopCat.of M) S (2 * q)
    hWe hWd a haW
  exact (chartNormalProjectionCoclass_restrict E q e S he hWe (le_refl _)).trans
    (hW.trans (chartNormalProjectionCoclass_restrict E q d S hd hWd (le_refl _)).symm)

private theorem ccm5_base_component_restrict_normalChart_of_image_smooth
    {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) [Smooth f.left] (q : ℕ) (x : Z.left)
    (hx : Order.coheight x = q) (a : ccm5_primeGoodOpen f x)
    (hsm : Point.map f a.1 ∈ cycleComponentSmoothSupportAmbientOpen Z x)
    (z : {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0})
    (hz : a.1 ∈ cycleComponentAnalyticClosedSupport X z.1) :
    ∃ (e : OpenPartialHomeomorph (ComplexPoint Z)
        ((Fin (dim Z.left - q) → ℂ) × (Fin q → ℂ)))
      (he : ∀ y ∈ e.source, y ∈ cycleComponentSupport Z x ↔ (e y).2 = 0),
      (Point.map f a.1) ∈ e.source ∧
      AnalyticAt ℂ ((localChart Z (dim Z.left) (Point.map f a.1)).symm.trans e)
        (localChart Z (dim Z.left) (Point.map f a.1) (Point.map f a.1)) ∧
      AnalyticAt ℂ ((localChart Z (dim Z.left) (Point.map f a.1)).symm.trans e).symm (e (Point.map f a.1)) ∧
      ∃ (W : Opens (ComplexPoint Z)) (_haW : (Point.map f a.1) ∈ W) (hWe : (W : Set (ComplexPoint Z)) ⊆ e.source),
        relativeCohomologyMap ℚ (2 * q)
          (neighborhoodSupportInclusionPairMap (show (W : Set (ComplexPoint Z)) ⊆ Set.univ from Set.subset_univ _)
            (cycleComponentSupport Z x))
          (supportedSingularClass Z (cycleComponentAnalyticClosedSupport Z x) (2 * q)
            (cycleComponentSupportedInjectiveClass Z x hx)) =
        chartNormalProjectionCoclass (Fin (dim Z.left - q) → ℂ) q e
          (cycleComponentSupport Z x) he W hWe := by
  apply ccm5_componentClass_restrict_normalChart Z q x hx (Point.map f a.1) hsm
  exact ccm4_flatPullbackPrime_support_le_aux f x z.1 z.2 hz

private theorem ccm5_normal_chart_reindex
    {M E F G : Type} [TopologicalSpace M]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (q : ℕ) (C : OpenPartialHomeomorph M E)
    (e : OpenPartialHomeomorph M (F × (Fin q → ℂ))) (L : F ≃L[ℂ] G)
    (a : M) (he : AnalyticAt ℂ (C.symm.trans e) (C a))
    (hei : AnalyticAt ℂ (C.symm.trans e).symm (e a)) :
    ∃ d : OpenPartialHomeomorph M (G × (Fin q → ℂ)),
      d.source = e.source ∧ (∀ y, (d y).2 = (e y).2) ∧
      AnalyticAt ℂ (C.symm.trans d) (C a) ∧
      AnalyticAt ℂ (C.symm.trans d).symm (d a) := by
  let R := L.prodCongr (ContinuousLinearEquiv.refl ℂ (Fin q → ℂ))
  let d := e.trans R.toHomeomorph.toOpenPartialHomeomorph
  refine ⟨d, ?_, fun _ => rfl, ?_, ?_⟩
  · exact Set.inter_univ _
  · exact (R.toContinuousLinearMap.analyticAt _).comp he
  · have hi : AnalyticAt ℂ (C.symm.trans e).symm (R.symm (R (e a))) := by
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using hei
    exact hi.comp (R.symm.toContinuousLinearMap.analyticAt _)

private theorem ccm5_normal_chart_transition_analytic
    {M E F : Type} [TopologicalSpace M]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (C : OpenPartialHomeomorph M E) (e d : OpenPartialHomeomorph M F)
    (a : M) (haC : a ∈ C.source) (hae : a ∈ e.source) (had : a ∈ d.source)
    (he : AnalyticAt ℂ (C.symm.trans e) (C a))
    (hei : AnalyticAt ℂ (C.symm.trans e).symm (e a))
    (hd : AnalyticAt ℂ (C.symm.trans d) (C a))
    (hdi : AnalyticAt ℂ (C.symm.trans d).symm (d a)) :
    AnalyticAt ℂ (e.symm.trans d) (e a) ∧
      AnalyticAt ℂ (e.symm.trans d).symm ((e.symm.trans d) (e a)) := by
  have hcomp (u v : OpenPartialHomeomorph M F) (hau : a ∈ u.source)
      (hu : AnalyticAt ℂ (C.symm.trans u).symm (u a))
      (hv : AnalyticAt ℂ (C.symm.trans v) (C a)) :
      AnalyticAt ℂ (u.symm.trans v) (u a) := by
    have hv' : AnalyticAt ℂ (C.symm.trans v) ((C.symm.trans u).symm (u a)) := by
      change AnalyticAt ℂ (C.symm.trans v) (C (u.symm (u a)))
      rw [u.left_inv hau]
      exact hv
    apply (hv'.comp hu).congr
    have hc : ContinuousAt u.symm (u a) := u.continuousAt_symm (u.map_source hau)
    have hm : u.symm (u a) ∈ C.source := by rw [u.left_inv hau]; exact haC
    filter_upwards [hc (C.open_source.mem_nhds hm)] with w hw
    change v (C.symm (C (u.symm w))) = v (u.symm w)
    rw [C.left_inv hw]
  refine ⟨hcomp e d hae hei hd, ?_⟩
  have hval : (e.symm.trans d) (e a) = d a := by
    change d (e.symm (e a)) = d a
    rw [e.left_inv hae]
  rw [hval]
  exact hcomp d e had hdi he

private theorem ccm5_pullback_normal_chart
    {M N E F G K : Type} [TopologicalSpace M] [TopologicalSpace N]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    [NormedAddCommGroup K] [NormedSpace ℂ K]
    (q : ℕ) (f : M → N) (hf : Continuous f)
    (C : OpenPartialHomeomorph M E) (D : OpenPartialHomeomorph N F)
    (d : OpenPartialHomeomorph N (G × (Fin q → ℂ)))
    (S : Set N) (hd : ∀ y ∈ d.source, y ∈ S ↔ (d y).2 = 0)
    (a : M) (haC : a ∈ C.source) (haD : f a ∈ D.source) (had : f a ∈ d.source)
    (φ : OpenPartialHomeomorph E (F × K))
    (haφ : C a ∈ φ.source) (hφf : ∀ v, (φ v).1 = D (f (C.symm v)))
    (hφ : AnalyticAt ℂ φ (C a)) (hφi : AnalyticAt ℂ φ.symm (φ (C a)))
    (hdA : AnalyticAt ℂ (D.symm.trans d) (D (f a)))
    (hdI : AnalyticAt ℂ (D.symm.trans d).symm (d (f a))) :
    ∃ e : OpenPartialHomeomorph M ((G × K) × (Fin q → ℂ)),
      a ∈ e.source ∧ e.source ⊆ C.source ∧
      (∀ y ∈ e.source, f y ∈ D.source) ∧
      (∀ y ∈ e.source, (e y).2 = (d (f y)).2) ∧
      (∀ y ∈ e.source, y ∈ f ⁻¹' S ↔ (e y).2 = 0) ∧
      AnalyticAt ℂ (C.symm.trans e) (C a) ∧
      AnalyticAt ℂ (C.symm.trans e).symm (e a) := by
  let g : E → F := fun v => D (f (C.symm v))
  let d' := D.symm.trans d
  have hga : g (C a) = D (f a) := by dsimp [g]; rw [C.left_inv haC]
  have hgd : g (C a) ∈ d'.source := by
    rw [hga]
    refine ⟨D.map_source haD, ?_⟩
    change D.symm (D (f a)) ∈ d.source
    rwa [D.left_inv haD]
  have hd'S : ∀ v ∈ d'.source, v ∈ D.symm ⁻¹' S ↔ (d' v).2 = 0 :=
    fun v hv => hd (D.symm v) hv.2
  have hd'I : AnalyticAt ℂ d'.symm (d' (g (C a))) := by
    change AnalyticAt ℂ d'.symm (d (D.symm (g (C a))))
    rw [hga, D.left_inv haD]
    exact hdI
  obtain ⟨e', hae', hn', he', hA', hI'⟩ := ccm5_product_normal_chart q g φ hφf
    d' (D.symm ⁻¹' S) hd'S (C a) haφ hgd (hφ) hφi (hga.symm ▸ hdA) hd'I
  let e := (C.trans e').restrOpen (f ⁻¹' D.source) (D.open_source.preimage hf)
  have hae : a ∈ e.source := ⟨⟨haC, hae'⟩, haD⟩
  have hn : ∀ y ∈ e.source, (e y).2 = (d (f y)).2 := by
    intro y hy
    change (e' (C y)).2 = _
    rw [hn']
    change (d (D.symm (D (f (C.symm (C y)))))).2 = _
    rw [C.left_inv hy.1.1, D.left_inv hy.2]
  refine ⟨e, hae, fun y hy => hy.1.1, fun y hy => hy.2, hn, ?_, ?_, ?_⟩
  · intro y hy
    have h := he' (C y) hy.1.2
    change D.symm (D (f (C.symm (C y)))) ∈ S ↔ (e' (C y)).2 = 0 at h
    rw [C.left_inv hy.1.1, D.left_inv hy.2] at h
    exact h
  · apply hA'.congr
    filter_upwards [C.open_target.mem_nhds (C.map_source haC)] with v hv
    change e' v = e' (C (C.symm v))
    rw [C.right_inv hv]
  · change AnalyticAt ℂ (fun v => C (C.symm (e'.symm v))) (e' (C a))
    apply hI'.congr
    have hc : ContinuousAt e'.symm (e' (C a)) := e'.continuousAt_symm (e'.map_source hae')
    have hmem : e'.symm (e' (C a)) ∈ C.target := by
      rw [e'.left_inv hae']; exact C.map_source haC
    filter_upwards [hc (C.open_target.mem_nhds hmem)] with v hv
    exact (C.right_inv hv).symm

private theorem ccm5_smooth_pullback_normal_chart
    {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) [Smooth f.left] (q : ℕ) (x : Z.left)
    (hx : Order.coheight x = q) (a : ComplexPoint X)
    (d : OpenPartialHomeomorph (ComplexPoint Z)
      ((Fin (dim Z.left - q) → ℂ) × (Fin q → ℂ)))
    (hd : ∀ y ∈ d.source, y ∈ cycleComponentSupport Z x ↔ (d y).2 = 0)
    (had : Point.map f a ∈ d.source)
    (hdA : AnalyticAt ℂ ((localChart Z (dim Z.left) (Point.map f a)).symm.trans d)
      (localChart Z (dim Z.left) (Point.map f a) (Point.map f a)))
    (hdI : AnalyticAt ℂ ((localChart Z (dim Z.left) (Point.map f a)).symm.trans d).symm
      (d (Point.map f a))) :
    ∃ e : OpenPartialHomeomorph (ComplexPoint X)
        ((Fin (dim X.left - q) → ℂ) × (Fin q → ℂ)),
      a ∈ e.source ∧
      (∀ y ∈ e.source, (e y).2 = (d (Point.map f y)).2) ∧
      (∀ y ∈ e.source, y ∈ ccm4_inverseAnalyticSupport f
        (cycleComponentAnalyticClosedSupport Z x) ↔ (e y).2 = 0) ∧
      AnalyticAt ℂ ((localChart X (dim X.left) a).symm.trans e)
        (localChart X (dim X.left) a a) ∧
      AnalyticAt ℂ ((localChart X (dim X.left) a).symm.trans e).symm (e a) := by
  let C := localChart X (dim X.left) a
  let D := localChart Z (dim Z.left) (Point.map f a)
  let g := inclusionInComplexCharts Z X f (dim X.left) (dim Z.left) a
  let A := fderiv ℂ g (C a)
  obtain ⟨φ, haφ, hφg, hφ, hφi, _⟩ :=
    ccm5_smooth_chart_local_product X Z f (dim X.left) (dim Z.left) a
  obtain ⟨e, hae, _, _, hn, he, heA, heI⟩ := ccm5_pullback_normal_chart q
    (Point.map f) (Point.continuous_map f) C D d (cycleComponentSupport Z x) hd a
    (mem_localChart_source X (dim X.left) a)
    (mem_localChart_source Z (dim Z.left) (Point.map f a)) had
    φ haφ hφg hφ hφi hdA hdI
  have hq : q ≤ dim Z.left := by
    have h := SmoothOfRelativeDimension.coheight_le_complex (f := Z.hom) (d := dim Z.left) x
    rw [hx] at h
    exact_mod_cast h
  have hr := LinearMap.finrank_range_add_finrank_ker A.toLinearMap
  have hsurj : Function.Surjective A :=
    ccm5_smooth_chart_derivative_surjective_aux X Z f (dim X.left) (dim Z.left) a
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at hr
  simp only [Module.finrank_fin_fun] at hr
  let L : ((Fin (dim Z.left - q) → ℂ) × A.ker) ≃L[ℂ] (Fin (dim X.left - q) → ℂ) :=
    ContinuousLinearEquiv.ofFinrankEq (by
      rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun]
      change dim Z.left + Module.finrank ℂ A.ker = dim X.left at hr
      omega)
  obtain ⟨e', hes, hen, hA, hI⟩ := ccm5_normal_chart_reindex q C e L a heA heI
  refine ⟨e', hes.symm ▸ hae, ?_, ?_, hA, hI⟩
  · intro y hy
    rw [hen]
    exact hn y (hes ▸ hy)
  · intro y hy
    rw [hen]
    exact he y (hes ▸ hy)

set_option backward.isDefEq.respectTransparency false in
private theorem ccm5_enlarge_germ_normalChart
    (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {S T : Closeds (ComplexPoint X)} (hST : S ≤ T) (q : ℕ)
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : OpenPartialHomeomorph (ComplexPoint X) (E × (Fin q → ℂ)))
    (hd : ∀ y ∈ d.source, y ∈ S ↔ (d y).2 = 0)
    (U : Opens (ComplexPoint X))
    (hU : ∀ y ∈ U, y ∈ T ↔ y ∈ S)
    (W : Opens (ComplexPoint X)) (hW : (W : Set (ComplexPoint X)) ⊆ d.source)
    (u : TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X)) S
      ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
        (AddCommGrpCat.of ℚ)) (2 * q))
    (hu : relativeCohomologyMap ℚ (2 * q)
      (neighborhoodSupportInclusionPairMap (Set.subset_univ (W : Set (ComplexPoint X)))
        (S : Set (ComplexPoint X))) (supportedSingularClass X S (2 * q) u) =
      chartNormalProjectionCoclass E q d (S : Set (ComplexPoint X)) hd W hW)
    (a : ComplexPoint X) (haW : a ∈ W) (haU : a ∈ U) :
    let e := d.restrOpen U U.isOpen
    let he : ∀ y ∈ e.source, y ∈ (T : Set (ComplexPoint X)) ↔ (e y).2 = 0 :=
      fun y hy => (hU y hy.2).trans (hd y hy.1)
    ccm5_supportGerm X T (2 * q) a (supportEnlarge X hST (2 * q) u) =
    supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
      (T : Set (ComplexPoint X)) (2 * q) ⟨e.source, e.open_source⟩ a ⟨hW haW, haU⟩
      (chartNormalProjectionCoclass E q e (T : Set (ComplexPoint X)) he e.source (le_refl _)) := by
  let e := d.restrOpen U U.isOpen
  have he : ∀ y ∈ e.source, y ∈ (T : Set (ComplexPoint X)) ↔ (e y).2 = 0 :=
    fun y hy => (hU y hy.2).trans (hd y hy.1)
  change ccm5_supportGerm X T (2 * q) a (supportEnlarge X hST (2 * q) u) =
    supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
      (T : Set (ComplexPoint X)) (2 * q) ⟨e.source, e.open_source⟩ a ⟨hW haW, haU⟩
      (chartNormalProjectionCoclass E q e (T : Set (ComplexPoint X)) he e.source (le_refl _))
  let V : Opens (ComplexPoint X) := W ⊓ U
  have haV : a ∈ V := ⟨haW, haU⟩
  have hVW : (V : Set (ComplexPoint X)) ⊆ W := fun _ h => h.1
  have hVe : (V : Set (ComplexPoint X)) ⊆ (d.restrOpen U U.isOpen).source :=
    fun y hy => ⟨hW hy.1, hy.2⟩
  rw [← ccm5_supportGerm_restriction_aux X T V (2 * q) a haV]
  rw [← supportRelativeCohomologyGerm_restrict (TopCat.of (ComplexPoint X))
    (T : Set (ComplexPoint X)) (2 * q) (U := V)
    (V := ⟨(d.restrOpen U U.isOpen).source, (d.restrOpen U U.isOpen).open_source⟩) hVe a haV]
  congr 1
  rw [supportedSingularClass_restrict]
  have hc : neighborhoodSupportInclusionPairMap (Set.subset_univ (V : Set (ComplexPoint X)))
      (T : Set (ComplexPoint X)) ≫ neighborhoodSupportEnlargePairMap _ (SetLike.coe_subset_coe.mpr hST) =
    neighborhoodSupportEnlargePairMap (V : Set (ComplexPoint X)) (SetLike.coe_subset_coe.mpr hST) ≫
      neighborhoodSupportInclusionPairMap hVW (S : Set (ComplexPoint X)) ≫
      neighborhoodSupportInclusionPairMap (Set.subset_univ (W : Set (ComplexPoint X)))
        (S : Set (ComplexPoint X)) := by
    apply MorphismProperty.Arrow.Hom.ext <;> rfl
  rw [← LinearMap.comp_apply, ← relativeCohomologyMap_comp]
  erw [hc]
  rw [relativeCohomologyMap_comp, LinearMap.comp_apply, relativeCohomologyMap_comp,
    LinearMap.comp_apply]
  have huv := (congrArg (relativeCohomologyMap ℚ (2 * q)
    (neighborhoodSupportInclusionPairMap hVW (S : Set (ComplexPoint X)))) hu).trans
    (chartNormalProjectionCoclass_restrict E q d (S : Set (ComplexPoint X)) hd hVW hW)
  have hen := congrArg (relativeCohomologyMap ℚ (2 * q)
    (neighborhoodSupportEnlargePairMap (V : Set (ComplexPoint X))
      (SetLike.coe_subset_coe.mpr hST))) huv
  have hp := ccm5_chartNormalProjectionCoclass_pullback E E q e d
    (T : Set (ComplexPoint X)) (S : Set (ComplexPoint X)) he hd V V hVe (hVW.trans hW)
    (neighborhoodSupportEnlargePairMap (V : Set (ComplexPoint X))
      (SetLike.coe_subset_coe.mpr hST)) (fun _ => rfl)
  exact hen.trans (hp.trans (chartNormalProjectionCoclass_restrict E q e
    (T : Set (ComplexPoint X)) he hVe (le_refl _)).symm)

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
private theorem ccm5_submersion_germ_on_support_of_image_smooth
    {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) [Smooth f.left] (q : ℕ) (x : Z.left)
    (hx : Order.coheight x = q) (a : ccm5_primeGoodOpen f x)
    (hsm : Point.map f a.1 ∈ cycleComponentSmoothSupportAmbientOpen Z x)
    (z : {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0})
    (hz : a.1 ∈ cycleComponentAnalyticClosedSupport X z.1) :
    ccm5_supportGerm X
      (ccm4_inverseAnalyticSupport f (cycleComponentAnalyticClosedSupport Z x))
      (2 * q) a.1
      (ccm4_supportedPullback f (cycleComponentAnalyticClosedSupport Z x) (2 * q)
        (cycleComponentSupportedInjectiveClass Z x hx)) =
    ccm5_supportGerm X
      (ccm4_inverseAnalyticSupport f (cycleComponentAnalyticClosedSupport Z x))
      (2 * q) a.1
      (supportEnlarge X (ccm4_flatPullbackPrime_support_le_aux f x z.1 z.2) (2 * q)
        (cycleComponentSupportedInjectiveClass X z.1
          (ccm3_flatPullbackPrime_codimension f q x hx z.1 z.2))) := by
  obtain ⟨d, hd, had, hdA, hdI, W, haW, hWd, hu⟩ :=
    ccm5_base_component_restrict_normalChart_of_image_smooth f q x hx a hsm z hz
  obtain ⟨e, hae, hn, he, heA, heI⟩ :=
    ccm5_smooth_pullback_normal_chart f q x hx a.1 d hd had hdA hdI
  obtain ⟨U, haU, _, hU⟩ := ccm5_primeGoodOpen_component_neighborhood f x a z hz
  have haz : a.1 ∈ cycleComponentSmoothSupportAmbientOpen X z.1 := by
    simpa only [Equiv.apply_symm_apply] using
      ccm5_primeGoodOpen_mem_smoothSupport f x a ((ccm5_primeEnumeration f x).symm z)
  obtain ⟨d₂, hd₂, had₂, hd₂A, hd₂I, W₂, haW₂, hW₂, hu₂⟩ :=
    ccm5_componentClass_restrict_normalChart X q z.1
      (ccm3_flatPullbackPrime_codimension f q x hx z.1 z.2) a.1 haz hz
  let T := ccm4_inverseAnalyticSupport f (cycleComponentAnalyticClosedSupport Z x)
  let d₃ := d₂.restrOpen U U.isOpen
  have hd₃ : ∀ y ∈ d₃.source, y ∈ (T : Set (ComplexPoint X)) ↔ (d₃ y).2 = 0 :=
    fun y hy => (hU y hy.2).trans (hd₂ y hy.1)
  have had₃ : a.1 ∈ d₃.source := ⟨had₂, haU⟩
  have hc := ccm5_enlarge_germ_normalChart X
    (ccm4_flatPullbackPrime_support_le_aux f x z.1 z.2) q
    (Fin (dim X.left - q) → ℂ) d₂ hd₂ U hU W₂ hW₂
    (cycleComponentSupportedInjectiveClass X z.1
      (ccm3_flatPullbackPrime_codimension f q x hx z.1 z.2)) hu₂ a.1 haW₂ haU
  have ht := ccm5_normal_chart_transition_analytic (localChart X (dim X.left) a.1)
    e d₃ a.1 (mem_localChart_source X (dim X.left) a.1) hae had₃
    heA heI hd₂A hd₂I
  have hov := ccm5_chartNormalProjectionCoclass_germ_eq q e d₃
    (T : Set (ComplexPoint X)) he hd₃ a.1 hae had₃
    (ccm4_flatPullbackPrime_support_le_aux f x z.1 z.2 hz) ht.1 ht.2
  let V : Opens (ComplexPoint X) :=
    ⟨e.source ∩ Point.map f ⁻¹' (W : Set (ComplexPoint Z)),
      e.open_source.inter (W.isOpen.preimage (Point.continuous_map f))⟩
  have haV : a.1 ∈ V := ⟨hae, haW⟩
  have hVe : (V : Set (ComplexPoint X)) ⊆ e.source := fun _ h => h.1
  have hp := ccm5_supportedPullback_germ_normalChart f
    (cycleComponentAnalyticClosedSupport Z x) q
    (Fin (dim X.left - q) → ℂ) (Fin (dim Z.left - q) → ℂ)
    e d he hd V W hVe hWd (fun _ h => h.2)
    (fun y hy => (hn y hy.1).symm) (cycleComponentSupportedInjectiveClass Z x hx)
    hu a.1 haV
  have hr := supportRelativeCohomologyGerm_restrict (TopCat.of (ComplexPoint X))
    (T : Set (ComplexPoint X)) (2 * q) (U := V)
    (V := ⟨e.source, e.open_source⟩) hVe a.1 haV
    (chartNormalProjectionCoclass (Fin (dim X.left - q) → ℂ) q e
      (T : Set (ComplexPoint X)) he e.source (le_refl _))
  have hrest := chartNormalProjectionCoclass_restrict (Fin (dim X.left - q) → ℂ)
    q e (T : Set (ComplexPoint X)) he hVe (le_refl _)
  have hr' := (congrArg (supportRelativeCohomologyGerm (TopCat.of (ComplexPoint X))
    (T : Set (ComplexPoint X)) (2 * q) V a.1 haV) hrest).symm.trans hr
  exact hp.trans (hr'.trans (hov.trans hc.symm))

/-- Smooth pullback preserves normalized component germs on the separated open.
Source: complex submersion charts, normal-projection coclass functoriality,
and generic length of a reduced smooth inverse-image component. -/
theorem ccm5_submersion_normalized_germ_aux
    {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) [Smooth f.left] (q : ℕ) (x : Z.left)
    (hx : Order.coheight x = q) (a : ccm5_primeGoodOpen f x) :
    ccm5_supportGerm X
      (ccm4_inverseAnalyticSupport f (cycleComponentAnalyticClosedSupport Z x))
      (2 * q) a.1
      (ccm4_supportedPullback f (cycleComponentAnalyticClosedSupport Z x) (2 * q)
        (cycleComponentSupportedInjectiveClass Z x hx)) =
      ∑ᶠ z : {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0},
        ccm5_supportGerm X
          (ccm4_inverseAnalyticSupport f (cycleComponentAnalyticClosedSupport Z x))
          (2 * q) a.1
          (ccm3_flatPullbackPrime f.left x z.1 •
            supportEnlarge X (ccm4_flatPullbackPrime_support_le_aux f x z.1 z.2) (2 * q)
              (cycleComponentSupportedInjectiveClass X z.1
                (ccm3_flatPullbackPrime_codimension f q x hx z.1 z.2))) := by
  classical
  by_cases haS : a.1 ∈
      (ccm4_inverseAnalyticSupport f (cycleComponentAnalyticClosedSupport Z x) :
        Set (ComplexPoint X))
  · obtain ⟨z, hz, _⟩ := ccm5_primeGoodOpen_unique_component f x a haS
    rw [ccm5_primeGoodOpen_sum_eq_component f q x hx a z hz]
    exact ccm5_submersion_germ_on_support_of_image_smooth f q x hx a (ccm5_primeGoodOpen_image_mem_smoothSupport f q x hx a haS) z hz
  · have hzero (u : TopCat.Sheaf.supportH (TopCat.of (ComplexPoint X))
        (ccm4_inverseAnalyticSupport f (cycleComponentAnalyticClosedSupport Z x))
        ((TopCat.Sheaf.constantFunctor (TopCat.of (ComplexPoint X))).obj
          (AddCommGrpCat.of ℚ)) (2 * q)) :
        ccm5_supportGerm X
          (ccm4_inverseAnalyticSupport f (cycleComponentAnalyticClosedSupport Z x))
          (2 * q) a.1 u = 0 := by
      apply supportRelativeCohomologyGerm_eq_zero_of_not_mem
      · exact (ccm4_inverseAnalyticSupport f
          (cycleComponentAnalyticClosedSupport Z x)).isClosed
      · exact haS
    rw [hzero]
    rw [finsum_congr (fun z => hzero _), finsum_zero]

/-- Supported pullback of a prime cycle with its actual generic-length coefficients.
Source: Fulton, *Intersection Theory*, second edition, §1.7; complex local orientations. -/
theorem ccm5_ccm4_supportedPullback_prime_aux {X Z : Over (Spec ↧ℂ)}
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (f : X ⟶ Z) [Smooth f.left] (q : ℕ) (x : Z.left)
    (hx : Order.coheight x = q) :
    ccm4_supportedPullback f (cycleComponentAnalyticClosedSupport Z x) (2 * q)
        (cycleComponentSupportedInjectiveClass Z x hx) =
      ∑ᶠ z : {z : X.left // ccm3_flatPullbackPrime f.left x z ≠ 0},
        ccm3_flatPullbackPrime f.left x z.1 •
          supportEnlarge X (ccm4_flatPullbackPrime_support_le_aux f x z.1 z.2) (2 * q)
            (cycleComponentSupportedInjectiveClass X z.1
              (ccm3_flatPullbackPrime_codimension f q x hx z.1 z.2)) := by
  apply ccm5_primeGoodOpen_germs_injective_aux f q x hx
  funext a
  change ccm5_supportGerm X _ (2 * q) a.1 _ = ccm5_supportGerm X _ (2 * q) a.1 _
  rw [map_finsum _ (Set.toFinite _)]
  exact ccm5_submersion_normalized_germ_aux f q x hx a

end HodgeLean.Adapters
