import HodgeLean.Foundations.Connected
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.AlgebraicGeometry.Group.Abelian
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.AffineScheme

/-!
# Products and group operations on complex points

Stage S9 (T13). HC no distance; AV milestone no distance. This retires nothing.
-/

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace HodgeLean.Foundations

noncomputable section

/-- The canonical product comparison on complex points, as an equivalence of sets.
No finiteness, separatedness, smoothness or integrality assumptions are needed.

Source: upstream `Definitions/AlgebraicGeometry/ComplexPoint/Basic.lean` at `2ead713`
(points as morphisms over the base); the universal property of the fibre product. -/
def complexPointProdEquiv (X Y : Over (Spec ↧ℂ)) :
    ComplexPoint (X ⊗ Y) ≃ ComplexPoint X × ComplexPoint Y :=
  homEquivToProd

example (X Y : Over (Spec ↧ℂ)) (z : ComplexPoint (X ⊗ Y)) :
    complexPointProdEquiv X Y z = (Point.map (fst X Y) z, Point.map (snd X Y) z) := rfl

/-- The product comparison is continuous for arbitrary complex schemes.

Source: upstream `Definitions/AlgebraicGeometry/ComplexPoint/Basic.lean` at `2ead713`,
`Point.continuous_map`, proved using `Point.continuous_iff_analyticSubbasis`. -/
theorem continuous_complexPointProdEquiv (X Y : Over (Spec ↧ℂ)) :
    Continuous (complexPointProdEquiv X Y) :=
  (Point.continuous_map (fst X Y)).prodMk (Point.continuous_map (snd X Y))

example (X Y : Over (Spec ↧ℂ)) : Continuous (complexPointProdEquiv X Y) :=
  continuous_complexPointProdEquiv X Y

open ComplexPoint

private def tensorPoint {A B : Type} [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] (p : (A →ₐ[ℂ] ℂ) × (B →ₐ[ℂ] ℂ)) :
    A ⊗[ℂ] B →ₐ[ℂ] ℂ :=
  Algebra.TensorProduct.lift p.1 p.2 (fun _ _ ↦ Commute.all _ _)

private theorem continuous_tensorPoint (A B : Type) [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] : Continuous (tensorPoint (A := A) (B := B)) := by
  rw [continuous_induced_rng]
  apply continuous_pi
  intro t
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
      simpa [tensorPoint, Pi.mul_def, Function.comp_def] using
        ((continuous_affineAlgebraHom_apply A a).comp continuous_fst).mul
          ((continuous_affineAlgebraHom_apply B b).comp continuous_snd)
  | add x y hx hy => simpa only [Function.comp_apply, map_add, Pi.add_def] using hx.add hy

private def affineTensorIso (A B : Type) [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] :
    (Over.mk (affineSpecStructureMap A) ⊗ Over.mk (affineSpecStructureMap B)) ≅
      Over.mk (affineSpecStructureMap (A ⊗[ℂ] B)) :=
  Over.isoMk (pullbackSpecIso ℂ A B) (pullbackSpecIso_hom_base ℂ A B)

private def affinePair (A B : Type) [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] :
    ComplexPoint (Over.mk (affineSpecStructureMap A)) ×
      ComplexPoint (Over.mk (affineSpecStructureMap B)) →
        ComplexPoint (Over.mk (affineSpecStructureMap A) ⊗
          Over.mk (affineSpecStructureMap B)) :=
  fun p ↦ Point.map (affineTensorIso A B).inv
    ((affineSpecEquiv (A ⊗[ℂ] B)).symm
      (tensorPoint (affineSpecEquiv A p.1, affineSpecEquiv B p.2)))

private theorem continuous_affinePair (A B : Type) [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] : Continuous (affinePair A B) :=
  (Point.continuous_map (affineTensorIso A B).inv).comp
    ((continuous_affineSpecEquiv_symm (A ⊗[ℂ] B)).comp
      ((continuous_tensorPoint A B).comp
        ((continuous_affineSpecEquiv A).prodMap (continuous_affineSpecEquiv B))))

private theorem affinePair_eq_lift (A B : Type) [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B]
    (p : ComplexPoint (Over.mk (affineSpecStructureMap A)) ×
      ComplexPoint (Over.mk (affineSpecStructureMap B))) :
    affinePair A B p = lift p.1 p.2 := by
  apply CartesianMonoidalCategory.hom_ext
  · apply Over.OverMorphism.ext
    simp only [affinePair, Point.map, affineTensorIso, Over.comp_left, Over.isoMk_inv_left,
      Over.fst_left, Category.assoc, Over.lift_left,
      Limits.pullback.lift_fst]
    apply Spec.homEquiv.injective
    ext a
    simp [affineSpecEquiv, tensorPoint, Spec.preimage_comp]
  · apply Over.OverMorphism.ext
    simp only [affinePair, Point.map, affineTensorIso, Over.comp_left, Over.isoMk_inv_left,
      Over.snd_left, Category.assoc, Over.lift_left,
      Limits.pullback.lift_snd]
    apply Spec.homEquiv.injective
    ext b
    simp [affineSpecEquiv, tensorPoint, Spec.preimage_comp]

private theorem continuous_lift_of_iso {X Y X' Y' : Over (Spec ↧ℂ)}
    (e : X ≅ X') (f : Y ≅ Y')
    (h : Continuous (fun p : ComplexPoint X' × ComplexPoint Y' ↦ lift p.1 p.2)) :
    Continuous (fun p : ComplexPoint X × ComplexPoint Y ↦ lift p.1 p.2) := by
  have hc := (Point.continuous_map (e.inv ⊗ₘ f.inv)).comp
    (h.comp ((Point.continuous_map e.hom).prodMap (Point.continuous_map f.hom)))
  convert hc using 1
  funext p
  simp [Point.map, Function.comp_def]

private theorem continuous_lift_affine (X Y : Over (Spec ↧ℂ))
    [IsAffine X.left] [IsAffine Y.left] :
    Continuous (fun p : ComplexPoint X × ComplexPoint Y ↦ lift p.1 p.2) := by
  let A := Γ(X.left, ⊤)
  let B := Γ(Y.left, ⊤)
  let a : ℂ →+* A := (Spec.preimage (X.left.isoSpec.inv ≫ X.hom)).hom
  let b : ℂ →+* B := (Spec.preimage (Y.left.isoSpec.inv ≫ Y.hom)).hom
  let : Algebra ℂ A := a.toAlgebra
  let : Algebra ℂ B := b.toAlgebra
  have ha : affineSpecStructureMap A = X.left.isoSpec.inv ≫ X.hom :=
    Spec.map_preimage _
  have hb : affineSpecStructureMap B = Y.left.isoSpec.inv ≫ Y.hom :=
    Spec.map_preimage _
  let e : X ≅ Over.mk (affineSpecStructureMap A) :=
    Over.isoMk X.left.isoSpec (by change _ ≫ affineSpecStructureMap A = _; rw [ha]; simp)
  let f : Y ≅ Over.mk (affineSpecStructureMap B) :=
    Over.isoMk Y.left.isoSpec (by change _ ≫ affineSpecStructureMap B = _; rw [hb]; simp)
  apply continuous_lift_of_iso e f
  exact (continuous_affinePair A B).congr (affinePair_eq_lift A B)

/-- Pairing complex points is continuous. The proof uses affine charts, tensor products
of their coordinate rings, and the analytic open embeddings of open subschemes.
No finiteness, separatedness or integrality assumptions are needed.

Source: upstream `Lemmas/AlgebraicGeometry/ComplexPoint/AffineScheme.lean` and
`Lemmas/AlgebraicGeometry/ComplexPoint/Open.lean` at `2ead713`. -/
theorem continuous_complexPointProdEquiv_symm (X Y : Over (Spec ↧ℂ)) :
    Continuous (complexPointProdEquiv X Y).symm := by
  change Continuous (fun p : ComplexPoint X × ComplexPoint Y ↦ lift p.1 p.2)
  rw [continuous_iff_continuousAt]
  intro p
  obtain ⟨U, hU, hpU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := p.1.underlying) (U := ⊤) trivial
  obtain ⟨V, hV, hpV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := p.2.underlying) (U := ⊤) trivial
  let : IsAffine (openScheme X U).left := hU
  let : IsAffine (openScheme Y V).left := hV
  let i := openInclusion X U
  let j := openInclusion Y V
  let q := ((openHomeomorph X U).symm ⟨p.1, hpU⟩,
    (openHomeomorph Y V).symm ⟨p.2, hpV⟩)
  have hq : Prod.map (Point.map i) (Point.map j) q = p := by
    apply Prod.ext
    · exact congrArg Subtype.val ((openHomeomorph X U).apply_symm_apply ⟨p.1, hpU⟩)
    · exact congrArg Subtype.val ((openHomeomorph Y V).apply_symm_apply ⟨p.2, hpV⟩)
  have hc := (Point.continuous_map (i ⊗ₘ j)).comp
    (continuous_lift_affine (openScheme X U) (openScheme Y V))
  have he := (isOpenEmbedding_map_open X U).prodMap (isOpenEmbedding_map_open Y V)
  rw [← hq]
  apply he.continuousAt_iff.mp
  convert hc.continuousAt (x := q) using 1
  funext r
  simp [Point.map, i, j]

example (X Y : Over (Spec ↧ℂ)) : Continuous (complexPointProdEquiv X Y).symm :=
  continuous_complexPointProdEquiv_symm X Y

/-- Complex points preserve binary products, with the analytic topology on the fibre product.
This holds for arbitrary schemes over `Spec ℂ`; no locally finite type, separatedness,
smoothness, projectivity or integrality hypothesis is used.

Source: upstream `Definitions/AlgebraicGeometry/ComplexPoint/Basic.lean`,
`Lemmas/AlgebraicGeometry/ComplexPoint/AffineScheme.lean` and
`Lemmas/AlgebraicGeometry/ComplexPoint/Open.lean` at `2ead713`. -/
def complexPointProdHomeomorph (X Y : Over (Spec ↧ℂ)) :
    ComplexPoint (X ⊗ Y) ≃ₜ ComplexPoint X × ComplexPoint Y where
  toEquiv := complexPointProdEquiv X Y
  continuous_toFun := continuous_complexPointProdEquiv X Y
  continuous_invFun := continuous_complexPointProdEquiv_symm X Y

example (X Y : Over (Spec ↧ℂ)) (p : ComplexPoint X × ComplexPoint Y) :
    (complexPointProdHomeomorph X Y).symm p = lift p.1 p.2 := rfl

/-! The group structure is Mathlib's `CategoryTheory.Hom.group`, available through
`open scoped CategoryTheory.MonObj`; multiplication is pairing followed by `μ`, and
inversion is composition with `ι`. Thus these results use the existing group structure. -/

/-- Multiplication of complex points of a group scheme is continuous.

Source: upstream `Definitions/AlgebraicGeometry/ComplexPoint/Basic.lean` at `2ead713`
(`Point.map` and `Point.continuous_map`), applied to the group object's multiplication. -/
theorem continuous_complexPoint_mul (X : Over (Spec ↧ℂ)) [GrpObj X] :
    Continuous (fun p : ComplexPoint X × ComplexPoint X ↦ p.1 * p.2) :=
  (Point.continuous_map (MonObj.mul : X ⊗ X ⟶ X)).comp
    (complexPointProdHomeomorph X X).symm.continuous

example (X : Over (Spec ↧ℂ)) [GrpObj X] :
    Continuous (fun p : ComplexPoint X × ComplexPoint X ↦ p.1 * p.2) :=
  continuous_complexPoint_mul X

/-- Inversion of complex points of a group scheme is continuous.

Source: upstream `Definitions/AlgebraicGeometry/ComplexPoint/Basic.lean` at `2ead713`,
`Point.continuous_map`, applied to the group object's inverse. -/
theorem continuous_complexPoint_inv (X : Over (Spec ↧ℂ)) [GrpObj X] :
    Continuous (fun p : ComplexPoint X ↦ p⁻¹) :=
  Point.continuous_map (GrpObj.inv : X ⟶ X)

example (X : Over (Spec ↧ℂ)) [GrpObj X] : Continuous (fun p : ComplexPoint X ↦ p⁻¹) :=
  continuous_complexPoint_inv X

/-- The analytic complex points of any group scheme form a topological group.
No properness, smoothness, integrality or commutativity assumption is needed.

Source: upstream `Definitions/AlgebraicGeometry/ComplexPoint/Basic.lean` at `2ead713`,
`Point.continuous_map`, and the product homeomorphism above. -/
instance complexPoint_isTopologicalGroup (X : Over (Spec ↧ℂ)) [GrpObj X] :
    IsTopologicalGroup (ComplexPoint X) where
  continuous_mul := continuous_complexPoint_mul X
  continuous_inv := continuous_complexPoint_inv X

example (X : Over (Spec ↧ℂ)) [GrpObj X] : IsTopologicalGroup (ComplexPoint X) :=
  inferInstance

/-- A commutative group scheme has commutative multiplication on its complex points.

Source: upstream `Definitions/AlgebraicGeometry/ComplexPoint/Basic.lean` at `2ead713`
(points as morphisms), with the commutative group-object laws on representable points. -/
theorem complexPoint_mul_comm (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X]
    (x y : ComplexPoint X) : x * y = y * x := mul_comm x y

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X] :
    CommGroup (ComplexPoint X) := inferInstance

/-- A projective complex scheme has compact analytic complex points.
This uses projectivity, not merely scheme-theoretic properness.

Source: upstream `Lemmas/AlgebraicGeometry/ComplexPoint/ProjectiveCompact.lean` at
`2ead713`, `IsProjective.complexPoint_compactSpace`. -/
theorem compactSpace_complexPoint_of_projective (X : Over (Spec ↧ℂ)) [IsProjective X.hom] :
    CompactSpace (ComplexPoint X) := inferInstance

example (X : Over (Spec ↧ℂ)) [IsProjective X.hom] : CompactSpace (ComplexPoint X) :=
  compactSpace_complexPoint_of_projective X

/-- Smooth integral projective complex schemes have connected analytic complex points.

Source: upstream `Other/AlgebraicGeometry/ComplexPoint/SmoothConnected.lean` at `2ead713`,
as ported and strengthened to path connectedness in `Foundations/Connected.lean`. -/
theorem connectedSpace_complexPoint (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    ConnectedSpace (ComplexPoint X) := by
  let := pathConnectedSpace_complexPoint X
  infer_instance

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    ConnectedSpace (ComplexPoint X) := connectedSpace_complexPoint X

/-- The remaining geometric input for deriving commutativity from properness:
the scheme-theoretic self-product is integral. For integral complex varieties this is
expected from the product-of-varieties theorem. It is not needed by the product
homeomorphism or the topological-group instance above. This is an ordinary proposition,
not a typeclass or a tagged hypothesis; callers must supply its proof explicitly.

Source: Stacks Project, Lemma 33.3.3, Tag 05P3,
https://stacks.math.columbia.edu/tag/05P3 (products over an algebraically closed field). -/
def ComplexSelfProductIntegral (X : Over (Spec ↧ℂ)) : Prop :=
  IsIntegral (X ⊗ X).left

example (X : Over (Spec ↧ℂ)) (h : IsIntegral (X ⊗ X).left) :
    ComplexSelfProductIntegral X := h

/-- Geometric integrality supplies the self-product input for a smooth integral
projective complex scheme. The remaining gap is deriving geometric integrality itself
from the ordinary integrality assumptions over `ℂ`.

Source: Stacks Project, Section 33.9, Tag 0366 (geometrically integral schemes),
and Lemma 33.3.3, Tag 05P3. -/
theorem complexSelfProductIntegral_of_geometricallyIntegral (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (h : GeometricallyIntegral X.hom) : ComplexSelfProductIntegral X := by
  let : GeometricallyIntegral X.hom := h
  let : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  change IsIntegral (CategoryTheory.Limits.pullback X.hom X.hom)
  infer_instance

example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (h : GeometricallyIntegral X.hom) : ComplexSelfProductIntegral X :=
  complexSelfProductIntegral_of_geometricallyIntegral X h

/-- A proper complex group scheme with integral self-product is commutative.
The self-product input is explicit and is not installed as a global instance.

Source: Milne, Abelian Varieties (2008), Corollary 1.4 (commutativity via rigidity);
Stacks Project, Lemma 33.3.3, Tag 05P3, for the self-product input. Implementation: Mathlib `AlgebraicGeometry/Group/Abelian.lean`,
`isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed`. -/
theorem isCommMonObj_of_complexSelfProductIntegral (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsProper X.hom] (h : ComplexSelfProductIntegral X) : IsCommMonObj X := by
  let : IsIntegral (X ⊗ X).left := h
  exact isCommMonObj_of_isProper_of_isIntegral_tensorObj_of_isAlgClosed X

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsProper X.hom]
    (h : ComplexSelfProductIntegral X) : IsCommMonObj X :=
  isCommMonObj_of_complexSelfProductIntegral X h

/-- The commutative group structure on complex points of a proper group scheme,
conditional on the explicitly supplied self-product integrality input.
Its underlying group structure is the existing representable-points group structure.

Source: upstream `Definitions/AlgebraicGeometry/ComplexPoint/Basic.lean` at `2ead713`
(points as morphisms); Stacks Project, Lemma 33.3.3, Tag 05P3, for the geometric input. -/
@[instance_reducible]
def complexPointCommGroup (X : Over (Spec ↧ℂ)) [GrpObj X] [IsProper X.hom]
    (h : ComplexSelfProductIntegral X) : CommGroup (ComplexPoint X) := by
  let := isCommMonObj_of_complexSelfProductIntegral X h
  infer_instance

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsProper X.hom]
    (h : ComplexSelfProductIntegral X) :
    (complexPointCommGroup X h).toGroup = (inferInstance : Group (ComplexPoint X)) := rfl

/-! Falsification checks on the trivial group scheme, namely `Spec ℂ` over itself. -/

private abbrev trivialComplexGroup : Over (Spec ↧ℂ) := 𝟙_ (Over (Spec ↧ℂ))

example : Group (ComplexPoint trivialComplexGroup) := inferInstance

example (x : ComplexPoint trivialComplexGroup) : x = 1 := Subsingleton.elim _ _

example (x y : ComplexPoint trivialComplexGroup) : x * y = 1 := Subsingleton.elim _ _

-- On the one-point base, both coordinates of the comparison are the identity section.
example (z : ComplexPoint (trivialComplexGroup ⊗ trivialComplexGroup)) :
    complexPointProdHomeomorph trivialComplexGroup trivialComplexGroup z =
      (𝟙 trivialComplexGroup, 𝟙 trivialComplexGroup) := by
  exact Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)

example :
    (complexPointProdHomeomorph trivialComplexGroup trivialComplexGroup).symm
      (𝟙 trivialComplexGroup, 𝟙 trivialComplexGroup) =
      lift (𝟙 trivialComplexGroup) (𝟙 trivialComplexGroup) := rfl

-- Identifying Spec ℂ × Spec ℂ with Spec ℂ by its left unitor, the comparison is
-- precisely the diagonal on the singleton, and its first coordinate is the identity.
example (z : ComplexPoint trivialComplexGroup) :
    (complexPointProdHomeomorph trivialComplexGroup trivialComplexGroup
      ((Point.isoMapHomeomorph (λ_ trivialComplexGroup)).symm z)).1 = z :=
  Subsingleton.elim _ _

example : Continuous (fun p : ComplexPoint trivialComplexGroup ×
    ComplexPoint trivialComplexGroup ↦ p.1 * p.2) :=
  continuous_complexPoint_mul trivialComplexGroup

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsProjective X.hom]
    [IsIntegral X.left] [Smooth X.hom] (h : ComplexSelfProductIntegral X) :
    let := complexPointCommGroup X h
    IsTopologicalGroup (ComplexPoint X) ∧ CompactSpace (ComplexPoint X) ∧
      PathConnectedSpace (ComplexPoint X) := by
  let := complexPointCommGroup X h
  exact ⟨complexPoint_isTopologicalGroup X, compactSpace_complexPoint_of_projective X,
    pathConnectedSpace_complexPoint X⟩

end

end HodgeLean.Foundations

#print axioms HodgeLean.Foundations.complexPointProdEquiv
#print axioms HodgeLean.Foundations.continuous_complexPointProdEquiv

#print axioms HodgeLean.Foundations.complexPointProdHomeomorph

#print axioms HodgeLean.Foundations.continuous_complexPoint_mul
#print axioms HodgeLean.Foundations.continuous_complexPoint_inv
#print axioms HodgeLean.Foundations.complexPoint_isTopologicalGroup
#print axioms HodgeLean.Foundations.complexPoint_mul_comm
#print axioms HodgeLean.Foundations.compactSpace_complexPoint_of_projective
#print axioms HodgeLean.Foundations.connectedSpace_complexPoint

#print axioms HodgeLean.Foundations.complexSelfProductIntegral_of_geometricallyIntegral
#print axioms HodgeLean.Foundations.isCommMonObj_of_complexSelfProductIntegral
#print axioms HodgeLean.Foundations.complexPointCommGroup

#print axioms HodgeLean.Foundations.continuous_complexPointProdEquiv_symm
#print axioms HodgeLean.Foundations.ComplexSelfProductIntegral
