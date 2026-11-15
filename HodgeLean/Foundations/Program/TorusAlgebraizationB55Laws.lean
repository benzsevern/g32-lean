import HodgeLean.Foundations.Program.TorusAlgebraizationB55Graph

/-! # Group laws transported from complex points

Let `e : T ≃ X(ℂ)` identify an additive commutative group with the complex points of an integral
smooth projective complex scheme `X`, and let `add`, `neg`, `one` be morphisms realizing the
transported addition, inversion and zero on complex points. Then the unit, associativity,
inverse and commutativity diagrams hold, since morphisms out of integral schemes of finite type
over `ℂ` are determined by their complex points.
-/

noncomputable section
set_option maxHeartbeats 400000

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open CategoryTheory.CartesianMonoidalCategory
open scoped MonoidalCategory CategoryTheory.MonObj
open HodgeLean.Foundations HodgeLean.Adapters

namespace HodgeLean.Foundations.Program

private theorem b55_pointDomain_toUnit :
    toUnit (Over.mk (𝟙 (Spec ↧ℂ))) = 𝟙 (Over.mk (𝟙 (Spec ↧ℂ))) :=
  toUnit_unique _ _

private theorem b55_point_toUnit {X : Over (Spec ↧ℂ)} (x : ComplexPoint X) :
    x ≫ toUnit X = 𝟙 (Over.mk (𝟙 (Spec ↧ℂ))) :=
  toUnit_unique _ _

private theorem b55_leftUnitor_inv (X : Over (Spec ↧ℂ)) :
    (λ_ X).inv = lift (toUnit X) (𝟙 X) := by
  ext1 <;> simp

private theorem b55_rightUnitor_inv (X : Over (Spec ↧ℂ)) :
    (ρ_ X).inv = lift (𝟙 X) (toUnit X) := by
  ext1 <;> simp

private theorem b55_point_eta {X Y : Over (Spec ↧ℂ)} (p : ComplexPoint (X ⊗ Y)) :
    p = lift (p ≫ fst X Y) (p ≫ snd X Y) := by
  ext1 <;> simp

variable {T : Type} [AddCommGroup T] (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  (e : T ≃ ComplexPoint X) (add : X ⊗ X ⟶ X) (neg : X ⟶ X)

/-- The transported addition on pairs of complex points. -/
theorem b55_lift_add
    (hadd : Point.map add = fun p ↦ e (e.symm (Point.map (fst X X) p) +
      e.symm (Point.map (snd X X) p)))
    (a b : ComplexPoint X) : lift a b ≫ add = e (e.symm a + e.symm b) := by
  have := congrFun hadd (lift a b)
  simpa [Point.map] using this

/-- The diagram identities for transported operations.
Source: Serre, GAGA, §3, Proposition 13; Birkenhake–Lange, §1.1. -/
theorem b55_group_laws
    (hadd : Point.map add = fun p ↦ e (e.symm (Point.map (fst X X) p) +
      e.symm (Point.map (snd X X) p)))
    (hneg : Point.map neg = fun p ↦ e (-(e.symm p))) :
    ((e 0 : 𝟙_ (Over (Spec ↧ℂ)) ⟶ X) ▷ X) ≫ add = (λ_ X).hom ∧
    (X ◁ (e 0 : 𝟙_ (Over (Spec ↧ℂ)) ⟶ X)) ≫ add = (ρ_ X).hom ∧
    (add ▷ X) ≫ add = (α_ X X X).hom ≫ (X ◁ add) ≫ add ∧
    lift neg (𝟙 X) ≫ add = toUnit X ≫ (e 0 : 𝟙_ (Over (Spec ↧ℂ)) ⟶ X) ∧
    lift (𝟙 X) neg ≫ add = toUnit X ≫ (e 0 : 𝟙_ (Over (Spec ↧ℂ)) ⟶ X) ∧
    (β_ X X).hom ≫ add = add := by
  have hA := b55_lift_add X e add hadd
  have hN : ∀ a : ComplexPoint X, a ≫ neg = e (-(e.symm a)) := fun a ↦ congrFun hneg a
  have : IsIntegral (X ⊗ X).left := gagam_product_isIntegral X X
  have : Smooth (X ⊗ X).hom := gagam_product_smooth X X
  have : IsIntegral ((X ⊗ X) ⊗ X).left := gagam_product_isIntegral (X ⊗ X) X
  have : Smooth ((X ⊗ X) ⊗ X).hom := gagam_product_smooth (X ⊗ X) X
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← cancel_epi (λ_ X).inv, Iso.inv_hom_id]
    apply b55_hom_ext
    funext x
    change x ≫ (λ_ X).inv ≫ _ ≫ add = x ≫ 𝟙 X
    rw [b55_leftUnitor_inv, ← Category.assoc, comp_lift]
    simp only [b55_point_toUnit, Category.comp_id, ← Category.assoc, lift_whiskerRight,
      Category.id_comp]
    rw [hA]
    simp
  · rw [← cancel_epi (ρ_ X).inv, Iso.inv_hom_id]
    apply b55_hom_ext
    funext x
    change x ≫ (ρ_ X).inv ≫ _ ≫ add = x ≫ 𝟙 X
    rw [b55_rightUnitor_inv, ← Category.assoc, comp_lift]
    simp only [b55_point_toUnit, Category.comp_id, ← Category.assoc, lift_whiskerLeft,
      Category.id_comp]
    rw [hA]
    simp
  · apply b55_hom_ext
    funext p
    change p ≫ (add ▷ X) ≫ add = p ≫ (α_ X X X).hom ≫ (X ◁ add) ≫ add
    rw [b55_point_eta p, b55_point_eta (p ≫ fst (X ⊗ X) X)]
    simp only [← Category.assoc, lift_whiskerRight, lift_lift_associator_hom, lift_whiskerLeft]
    rw [hA, hA, hA, hA]
    simp [add_assoc]
  · apply b55_hom_ext
    funext x
    change x ≫ lift neg (𝟙 X) ≫ add = x ≫ toUnit X ≫ _
    rw [← Category.assoc, ← Category.assoc, comp_lift, b55_point_toUnit, Category.comp_id, hA,
      hN, Category.id_comp]
    simp
  · apply b55_hom_ext
    funext x
    change x ≫ lift (𝟙 X) neg ≫ add = x ≫ toUnit X ≫ _
    rw [← Category.assoc, ← Category.assoc, comp_lift, b55_point_toUnit, Category.comp_id, hA,
      hN, Category.id_comp]
    simp
  · apply b55_hom_ext
    funext p
    change p ≫ (β_ X X).hom ≫ add = p ≫ add
    rw [b55_point_eta p]
    simp only [← Category.assoc, lift_braiding_hom]
    rw [hA, hA, add_comm]

/-- The identification `e` is a group isomorphism onto the complex points of a group object whose
operations are the transported ones.
Source: Birkenhake–Lange, §1.1; Serre, GAGA, §3. -/
theorem b55_group_points [GrpObj X]
    (hadd : Point.map add = fun p ↦ e (e.symm (Point.map (fst X X) p) +
      e.symm (Point.map (snd X X) p)))
    (hneg : Point.map neg = fun p ↦ e (-(e.symm p)))
    (hone : η[X] = (e 0 : 𝟙_ (Over (Spec ↧ℂ)) ⟶ X)) (hmul : μ[X] = add) (hinv : ι[X] = neg) :
    e 0 = 1 ∧ (∀ t u, e (t + u) = e t * e u) ∧ ∀ t, e (-t) = (e t)⁻¹ := by
  have hA := b55_lift_add X e add hadd
  refine ⟨?_, fun t u ↦ ?_, fun t ↦ ?_⟩
  · rw [Hom.one_def, hone, b55_pointDomain_toUnit, Category.id_comp]
  · rw [Hom.mul_def, hmul, hA]
    simp
  · rw [Hom.inv_def, hinv]
    have := congrFun hneg (e t)
    simp only [Point.map, Equiv.symm_apply_apply] at this
    exact this.symm

end HodgeLean.Foundations.Program
