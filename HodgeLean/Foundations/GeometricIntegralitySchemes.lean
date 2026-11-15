import HodgeLean.Foundations.GeometricIntegrality
import HodgeLean.Foundations.ComplexPointGroup
import Mathlib.Topology.Sets.OpenCover

/-!
# Products of integral complex schemes

HC no distance; AV milestone no distance.
-/

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace HodgeLean.Foundations

noncomputable section

private theorem geometricallyIntegral_spec
    (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] :
    GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap k A))) := by
  constructor
  rw [geometrically_iff_of_commRing]
  intro K _ _ Z fst snd h
  let := isDomain_tensorProduct_of_isAlgClosed k A K
  exact IsIntegral.of_isIso (h.isoPullback ≪≫ pullbackSpecIso k A K).inv

private theorem geometricallyIntegral_affine
    (k : Type) [Field k] [IsAlgClosed k] (X : Scheme) (f : X ⟶ Spec (.of k))
    [IsAffine X] [IsIntegral X] [LocallyOfFiniteType f] :
    GeometricallyIntegral f := by
  let A := Γ(X, ⊤)
  let a := Spec.preimage (X.isoSpec.inv ≫ f)
  let : Algebra k A := a.hom.toAlgebra
  have ha : Spec.map (CommRingCat.ofHom (algebraMap k A)) = X.isoSpec.inv ≫ f :=
    Spec.map_preimage _
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k A))) := by
    rw [ha]
    infer_instance
  let : Algebra.FiniteType k A := HasRingHomProperty.Spec_iff.mp ‹LocallyOfFiniteType
    (Spec.map (CommRingCat.ofHom (algebraMap k A)))›
  have h := geometricallyIntegral_spec k A
  rw [ha] at h
  constructor
  intro K _ y Z p q hpq
  exact h.geometrically_isIntegral y (p ≫ X.isoSpec.hom) q
    (hpq.of_iso (.refl _) X.isoSpec (.refl _) (.refl _)
      (by simp) (by simp) (by simp) (by simp))

private def pointedAffineCover (X : Scheme) : X.OpenCover where
  I₀ := X
  X x := X.affineCover.X (X.affineCover.idx x)
  f x := X.affineCover.f (X.affineCover.idx x)
  mem₀ := by
    rw [Scheme.ofArrows_mem_precoverage_iff]
    exact ⟨fun x ↦ ⟨x, X.affineCover.covers x⟩, fun _ ↦ inferInstance⟩

private instance pointedAffineCover_nonempty (X : Scheme) (x : X) :
    Nonempty ((pointedAffineCover X).X x) :=
  let ⟨y, _⟩ := X.affineCover.covers x
  ⟨y⟩

private instance pointedAffineCover_affine (X : Scheme) (x : X) :
    IsAffine ((pointedAffineCover X).X x) := by
  dsimp [pointedAffineCover]
  infer_instance

private instance pointedAffineCover_integral (X : Scheme) [IsIntegral X] (x : X) :
    IsIntegral ((pointedAffineCover X).X x) := by
  have : IsOpenImmersion ((pointedAffineCover X).f x) := (pointedAffineCover X).map_prop x
  exact isIntegral_of_isOpenImmersion ((pointedAffineCover X).f x)

set_option backward.isDefEq.respectTransparency false in
/-- Products of integral schemes locally of finite type over an algebraically closed
field are integral. Neither separatedness nor properness is required.

Source: Stacks Project, Tag 05P3, Lemma 33.3.3, its affine-cover argument.
HC no distance; AV milestone no distance. -/
theorem isIntegral_pullback_of_isAlgClosed
    (k : Type) [Field k] [IsAlgClosed k] (X Y : Scheme)
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [IsIntegral X] [IsIntegral Y] [LocallyOfFiniteType f] [LocallyOfFiniteType g] :
    IsIntegral (pullback f g) := by
  let C := pointedAffineCover X
  let D := Scheme.Pullback.openCoverOfLeft C f g
  have (i : C.I₀) : IsAffine (C.X i) := pointedAffineCover_affine X i
  have (i : C.I₀) : IsIntegral (C.X i) := pointedAffineCover_integral X i
  have (i : C.I₀) : IsOpenImmersion (C.f i) := C.map_prop i
  have (i : D.I₀) : IsOpenImmersion (D.f i) := D.map_prop i
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian g
  have (i : C.I₀) : GeometricallyIntegral (C.f i ≫ f) :=
    geometricallyIntegral_affine k (C.X i) (C.f i ≫ f)
  have (i : C.I₀) : IsIntegral (D.X i) := by
    change IsIntegral (pullback (C.f i ≫ f) g)
    let : Flat (C.f i ≫ f) := inferInstance
    let : UniversallyOpen (C.f i ≫ f) := inferInstance
    exact GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (pullback.snd _ _)
  let : IsReduced (pullback f g) := IsReduced.of_openCover _ D
  have hr (i : C.I₀) : Set.range (D.f i) =
      (pullback.fst f g) ⁻¹' Set.range (C.f i) := by
    convert! (Scheme.Pullback.range_map (f := C.f i ≫ f) (g := g)
      f g (C.f i) (𝟙 Y) (𝟙 (Spec (.of k))) (by simp) (by simp)) using 1
    simp
  have hn : Pairwise (fun i j : D.I₀ ↦
      ¬ Disjoint ((D.f i).opensRange) ((D.f j).opensRange)) := by
    intro i j _
    rw [← TopologicalSpace.Opens.coe_disjoint, Set.not_disjoint_iff]
    obtain ⟨x, hi, hj⟩ := nonempty_preirreducible_inter
      (C.f i).isOpenEmbedding.isOpen_range (C.f j).isOpenEmbedding.isOpen_range
      (Set.range_nonempty _) (Set.range_nonempty _)
    obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g)
      x (Classical.choice (inferInstance : Nonempty Y)) (Subsingleton.elim _ _)
    exact ⟨z, by change z ∈ Set.range (D.f i); rw [hr]; simpa [hz] using hi,
      by change z ∈ Set.range (D.f j); rw [hr]; simpa [hz] using hj⟩
  let : PreirreducibleSpace ↥(pullback f g) :=
    PreirreducibleSpace.of_isOpenCover hn D.isOpenCover_opensRange fun i ↦
      Subtype.preirreducibleSpace (by
        change IsPreirreducible (Set.range (D.f i))
        simpa only [Set.image_univ] using
          (IrreducibleSpace.isIrreducible_univ (D.X i)).isPreirreducible.image
            (D.f i) (D.f i).continuous.continuousOn)
  let : IrreducibleSpace ↥(pullback f g) := ⟨inferInstance⟩
  exact isIntegral_of_irreducibleSpace_of_isReduced _

example (k : Type) [Field k] [IsAlgClosed k] (X Y : Scheme)
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [IsIntegral X] [IsIntegral Y] [LocallyOfFiniteType f] [LocallyOfFiniteType g] :
    IsIntegral (pullback f g) := isIntegral_pullback_of_isAlgClosed k X Y f g

example (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsIntegral Y.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] : IsIntegral (X ⊗ Y).left :=
  isIntegral_pullback_of_isAlgClosed ℂ X.left Y.left X.hom Y.hom

/-- Ordinary integrality over the complex numbers discharges S9's self-product input.

Source: Stacks Project, Tag 05P3, Lemma 33.3.3.
HC no distance; AV milestone no distance. -/
theorem complexSelfProductIntegral_of_isIntegral (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [LocallyOfFiniteType X.hom] : ComplexSelfProductIntegral X :=
  isIntegral_pullback_of_isAlgClosed ℂ X.left X.left X.hom X.hom

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] :
    ComplexSelfProductIntegral X := complexSelfProductIntegral_of_isIntegral X

/-- Complex points of a proper integral group scheme commute, without an input
commutativity or self-product-integrality hypothesis. Properness supplies finite type.

Source: Stacks Project, Tag 05P3; Mathlib's rigidity theorem
`isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed`.
HC no distance; AV milestone no distance. -/
theorem complexPoint_mul_comm_of_proper_integral (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsProper X.hom] [IsIntegral X.left] (x y : ComplexPoint X) :
    x * y = y * x := by
  let := isCommMonObj_of_complexSelfProductIntegral X
    (complexSelfProductIntegral_of_isIntegral X)
  exact complexPoint_mul_comm X x y

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsProper X.hom] [Smooth X.hom]
    [IsIntegral X.left] (x y : ComplexPoint X) : x * y = y * x :=
  complexPoint_mul_comm_of_proper_integral X x y

example : IsIntegral ((Over.mk (𝟙 (Spec ↧ℂ))) ⊗ (Over.mk (𝟙 (Spec ↧ℂ)))).left := by
  change IsIntegral (pullback (𝟙 (Spec ↧ℂ)) (𝟙 (Spec ↧ℂ)))
  exact isIntegral_pullback_of_isAlgClosed ℂ _ _ _ _

end

end HodgeLean.Foundations

#print axioms HodgeLean.Foundations.isIntegral_pullback_of_isAlgClosed
#print axioms HodgeLean.Foundations.complexSelfProductIntegral_of_isIntegral
#print axioms HodgeLean.Foundations.complexPoint_mul_comm_of_proper_integral
