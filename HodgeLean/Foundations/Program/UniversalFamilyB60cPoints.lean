import HodgeLean.Foundations.Program.UniversalFamilyB60cHom
import HodgeLean.Adapters.CycleClassPullbackDefs

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open scoped CategoryTheory.MonObj
open HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

/-- Multiplication identities put the kernel in finite torsion and give surjectivity
by divisibility of the complex torus. -/
theorem b60c_isogeny_of_point_composites
    (X Y : Over (Spec ↧ℂ)) [GrpObj X] [GrpObj Y] [IsCommMonObj X] [IsCommMonObj Y]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (f : X ⟶ Y) (g : Y ⟶ X) [IsMonHom g] (n : ℕ) (hn : 0 < n)
    (hfg : ∀ x : ComplexPoint X, Point.map g (Point.map f x) = x ^ n)
    (hgf : ∀ y : ComplexPoint Y, Point.map f (Point.map g y) = y ^ n) :
    ccm2_IsogenyOnPoints f := by
  have ht : Set.Finite {x : ComplexPoint X | x ^ n = 1} := by
    let e := complexPointUniformization X (dim X.left)
    have hc := AddCircle.finite_torsion (1 : ℝ) hn
    have hp : (Set.univ.pi fun _ : Fin (2 * dim X.left) =>
        {x : UnitAddCircle | n • x = 0}).Finite := Set.Finite.pi fun _ => hc
    refine Set.Finite.of_injOn (f := fun x : ComplexPoint X => e (Additive.ofMul x))
      ?_ (e.injective.comp Additive.ofMul.injective).injOn hp
    intro x hx i _
    have h : n • e (Additive.ofMul x) = 0 := by
      rw [← map_nsmul]
      change e (Additive.ofMul (x ^ n)) = 0
      rw [hx]
      exact map_zero e
    exact congrFun h i
  refine ⟨ht.subset ?_, ?_⟩
  · intro x hx
    change x ^ n = 1
    rw [← hfg x, hx]
    exact MonObj.one_comp g
  · intro y
    let e := complexPointUniformization Y (dim Y.left)
    have h : ∀ i, ∃ z : UnitAddCircle, n • z = e (Additive.ofMul y) i := fun i => by
      obtain ⟨z, hz⟩ := DivisibleBy.surjective_smul UnitAddCircle ℤ
        (Int.natCast_ne_zero.mpr hn.ne') (e (Additive.ofMul y) i)
      exact ⟨z, by simpa only [natCast_zsmul] using hz⟩
    choose z hz using h
    refine ⟨Point.map g (e.symm z).toMul, ?_⟩
    rw [hgf]
    apply Additive.ofMul.injective
    apply e.injective
    change e (n • e.symm z) = e (Additive.ofMul y)
    rw [map_nsmul, e.apply_symm_apply]
    exact funext hz

#print axioms b60c_isogeny_of_point_composites

/-- Faithfulness identifies an endomorphism with multiplication by an integer. -/
theorem b60c_points_of_scalar_pullback
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsCommMonObj X]
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (f : X ⟶ X) [IsMonHom f] (n : ℕ)
    (hf : homPullback f 1 = (n : ℚ) • LinearMap.id) :
    ∀ x : ComplexPoint X, Point.map f x = x ^ n := by
  have hn : abelianEndAction X (n : AbelianEnd X) = n := by
    obtain ⟨ρ, hρ⟩ := spec_abelianEndAction_ringHom X
    apply MulOpposite.op_injective
    rw [← hρ, map_natCast, MulOpposite.op_natCast]
  have hEq : (⟨f, inferInstance⟩ : AbelianEnd X) = n := by
    apply spec_abelianEndAction_injective X
    change homPullback f 1 = _
    rw [hf, hn]
    ext x
    simp [Nat.cast_smul_eq_nsmul]
  have hhom : ∀ m : ℕ, (m : AbelianEnd X).hom = 𝟙 X ^ m := by
    intro m
    induction m with
    | zero => rfl
    | succ n ih =>
      change ((n : AbelianEnd X) + 1).hom = _
      rw [AbelianEnd.add_hom, ih, pow_succ, AbelianEnd.one_hom]
  intro x
  have h := congrArg AbelianEnd.hom hEq
  change f = (n : AbelianEnd X).hom at h
  change x ≫ f = _
  rw [h, hhom n, MonObj.comp_pow, Category.comp_id]

#print axioms b60c_points_of_scalar_pullback

end HodgeLean.Foundations.Program
