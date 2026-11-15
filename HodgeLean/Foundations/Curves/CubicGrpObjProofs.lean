import HodgeLean.Foundations.Curves.CubicGroup
import HodgeLean.Foundations.ComplexPointGroup
import HodgeLean.Foundations.GeometricIntegralitySchemes

set_option maxHeartbeats 400000

/-! # Proofs for the curves C4 spec

The proofs of the `_aux` theorems that `CubicGrpObj.lean` (frozen) restates. Point
extensionality (T1) runs Mathlib's `ext_of_fromSpecResidueField_eq` over the closed points of the
Jacobson source, each of which is a complex point via `pointOfClosedPoint`. Reducedness of the
products (T2) comes from their integrality (`isIntegral_pullback_of_isAlgClosed`), and finite
type of a product (T2') from base change and composition. Each group-object axiom (T3) is checked
on complex points by T1, where it is Mathlib's group law on `W.toAffine.Point` transported by
`e`; T5 and T6 compute in the monoid of complex points. The C3 morphisms enter only through the
hypotheses `hm`, `hi`.
Relation to the goal: HC no distance; AV milestone no distance.
-/

namespace HodgeLean.Foundations.Curves

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

/-- Spec T1: morphisms out of a reduced complex scheme of locally finite type into a separated
one are determined by their values on complex points. -/
theorem complexPoint_hom_ext_aux {Y X : Over (Spec ↧ℂ)} [IsReduced Y.left]
    [LocallyOfFiniteType Y.hom] [IsSeparated X.hom] {f g : Y ⟶ X}
    (h : ∀ P : ComplexPoint Y, P ≫ f = P ≫ g) : f = g := by
  have : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  have hw : f.left ≫ X.hom = g.left ≫ X.hom := by rw [Over.w f, Over.w g]
  refine Over.OverMorphism.ext (ext_of_fromSpecResidueField_eq f.left g.left X.hom
    (closedPoints Y.left) ?_ ?_ hw)
  · rw [dense_iff_closure_eq, ← Set.univ_inter (closedPoints Y.left),
      JacobsonSpace.closure_inter_closedPoints_eq_closure isOpen_univ.isLocallyClosed,
      closure_univ]
  · intro x hx
    rw [← cancel_epi (Spec.map (residueFieldIsoBase Y.hom x hx).hom)]
    have := congrArg CommaMorphism.left
      (h (Over.homMk (pointOfClosedPoint Y.hom x hx) (pointOfClosedPoint_comp Y.hom x hx)))
    simpa [pointOfClosedPoint] using this

/-- The product over `Spec ℂ` of two schemes locally of finite type is locally of finite type:
its structure map is a base change of one factor's followed by the other's. -/
theorem locallyOfFiniteType_tensor_hom (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] : LocallyOfFiniteType (X ⊗ Y).hom := by
  change LocallyOfFiniteType (pullback.fst X.hom Y.hom ≫ X.hom)
  infer_instance

/-- Spec T2: the products of the cubic used by the group-object axioms are reduced. -/
theorem isReduced_cubic_tensor_aux :
    IsReduced (E ⊗ E).left ∧ IsReduced ((E ⊗ E) ⊗ E).left ∧ IsReduced (E ⊗ (E ⊗ E)).left := by
  have : IsIntegral (E ⊗ E).left :=
    isIntegral_pullback_of_isAlgClosed ℂ E.left E.left E.hom E.hom
  have := locallyOfFiniteType_tensor_hom E E
  have : IsIntegral ((E ⊗ E) ⊗ E).left :=
    isIntegral_pullback_of_isAlgClosed ℂ (E ⊗ E).left E.left (E ⊗ E).hom E.hom
  have : IsIntegral (E ⊗ (E ⊗ E)).left :=
    isIntegral_pullback_of_isAlgClosed ℂ E.left (E ⊗ E).left E.hom (E ⊗ E).hom
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Spec T2': products over `Spec ℂ` of schemes locally of finite type are locally of finite
type. -/
theorem locallyOfFiniteType_tensor_aux (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] : LocallyOfFiniteType (X ⊗ Y).hom :=
  locallyOfFiniteType_tensor_hom X Y

/-- Spec T3: point-level addition, negation and infinity assemble to a group object. -/
theorem exists_grpObj_aux (e : ComplexPoint E ≃ W.toAffine.Point) (he : IsCubicPointEquiv e)
    (m : E ⊗ E ⟶ E) (hm : ∀ P Q : ComplexPoint E, lift P Q ≫ m = e.symm (e P + e Q))
    (i : E ⟶ E) (hi : ∀ P : ComplexPoint E, P ≫ i = e.symm (-e P)) :
    ∃ G : GrpObj E, G.one = Over.homMk infinity infinity_over ∧ G.mul = m ∧ G.inv = i := by
  have hO : e (Over.homMk infinity infinity_over : ComplexPoint E) = 0 := he.1 _ rfl
  have hred := isReduced_cubic_tensor_aux
  have := hred.2.1
  have := locallyOfFiniteType_tensor_hom E E
  have := locallyOfFiniteType_tensor_hom (E ⊗ E) E
  have hu : ∀ P : ComplexPoint E, P ≫ toUnit E = 𝟙 _ := fun P ↦ toUnit_unique _ _
  refine ⟨{ one := Over.homMk infinity infinity_over, mul := m, inv := i
            one_mul := ?_, mul_one := ?_, mul_assoc := ?_, left_inv := ?_, right_inv := ?_ },
    rfl, rfl, rfl⟩
  · rw [← cancel_epi (λ_ E).inv, Iso.inv_hom_id]
    refine complexPoint_hom_ext_aux fun P ↦ ?_
    have : P ≫ (λ_ E).inv ≫ Over.homMk infinity infinity_over ▷ E =
        lift (Over.homMk infinity infinity_over) P := by
      ext <;> simp [reassoc_of% hu]
    rw [reassoc_of% this, hm, hO, zero_add, Equiv.symm_apply_apply, Category.comp_id]
  · rw [← cancel_epi (ρ_ E).inv, Iso.inv_hom_id]
    refine complexPoint_hom_ext_aux fun P ↦ ?_
    have : P ≫ (ρ_ E).inv ≫ E ◁ Over.homMk infinity infinity_over =
        lift P (Over.homMk infinity infinity_over) := by
      ext <;> simp [reassoc_of% hu]
    rw [reassoc_of% this, hm, hO, add_zero, Equiv.symm_apply_apply, Category.comp_id]
  · refine complexPoint_hom_ext_aux fun P ↦ ?_
    have hP : P = lift (lift (P ≫ fst _ _ ≫ fst _ _) (P ≫ fst _ _ ≫ snd _ _)) (P ≫ snd _ _) := by
      ext <;> simp
    rw [hP]
    simp [hm, add_assoc]
  · refine complexPoint_hom_ext_aux fun P ↦ ?_
    rw [comp_lift_assoc, Category.comp_id, hm, hi, Equiv.apply_symm_apply, reassoc_of% hu]
    simp [Equiv.symm_apply_eq, hO]
  · refine complexPoint_hom_ext_aux fun P ↦ ?_
    rw [comp_lift_assoc, Category.comp_id, hm, hi, Equiv.apply_symm_apply, reassoc_of% hu]
    simp [Equiv.symm_apply_eq, hO]

/-- Spec T5: the complex points of such a group object are Mathlib's points of `W`, via `e`. -/
theorem exists_complexPoint_addEquiv_aux (e : ComplexPoint E ≃ W.toAffine.Point) [GrpObj E]
    (hμ : ∀ P Q : ComplexPoint E, lift P Q ≫ μ[E] = e.symm (e P + e Q)) :
    ∃ φ : Additive (ComplexPoint E) ≃+ W.toAffine.Point,
      ∀ P : ComplexPoint E, φ (Additive.ofMul P) = e P := by
  refine ⟨{ toEquiv := Additive.toMul.trans e, map_add' := fun P Q ↦ ?_ }, fun P ↦ rfl⟩
  change e (Additive.toMul P * Additive.toMul Q) = e (Additive.toMul P) + e (Additive.toMul Q)
  rw [Hom.mul_def, hμ, Equiv.apply_symm_apply]

/-- Spec T6: the unit is not the finite point `(0,0)`, which is `2`-torsion. -/
theorem finitePoint_ne_one_aux (e : ComplexPoint E ≃ W.toAffine.Point) (he : IsCubicPointEquiv e)
    [GrpObj E] (hμ : ∀ P Q : ComplexPoint E, lift P Q ≫ μ[E] = e.symm (e P + e Q)) :
    (Over.homMk finitePoint finitePoint_over : ComplexPoint E) ≠ η[E] ∧
      lift (Over.homMk finitePoint finitePoint_over : ComplexPoint E)
        (Over.homMk finitePoint finitePoint_over) ≫ μ[E] = η[E] := by
  set P₀ : ComplexPoint E := Over.homMk finitePoint finitePoint_over
  have h0 : W.toAffine.Nonsingular 0 0 :=
    WeierstrassCurve.Affine.equation_iff_nonsingular.mp (by
      simp [WeierstrassCurve.Affine.equation_iff, W, WeierstrassCurve.ofJ1728])
  have hP₀ : e P₀ = .some 0 0 h0 := he.2 0 0 h0 P₀ finitePoint_chart.symm
  have hη : e η[E] = 0 := by
    have h1 : (1 : ComplexPoint E) * P₀ = P₀ := one_mul P₀
    rw [Hom.mul_def, Hom.one_def, hμ, show toUnit (Over.mk (𝟙 (Spec ↧ℂ))) = 𝟙 _ from toUnit_unique _ _,
      Category.id_comp, Equiv.symm_apply_eq] at h1
    simpa using h1.symm
  refine ⟨fun h ↦ ?_, ?_⟩
  · have := congrArg e h
    rw [hP₀, hη] at this
    exact WeierstrassCurve.Affine.Point.some_ne_zero h0 this
  · rw [hμ, hP₀, Equiv.symm_apply_eq, hη]
    exact WeierstrassCurve.Affine.Point.add_of_Y_eq rfl (by
      simp [WeierstrassCurve.Affine.negY, W, WeierstrassCurve.ofJ1728])

end HodgeLean.Foundations.Curves
