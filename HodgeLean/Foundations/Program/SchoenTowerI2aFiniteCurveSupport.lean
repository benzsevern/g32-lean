import HodgeLean.Foundations.Program.SchoenTowerI2aCurveBranchParameters

/-! # A common actual curve chart for finite branch and tuple support
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local instance] overSpecAlgebra

/-- A finite nonempty family of distinct curve points has simultaneous actual etale point-ideal parameters.
Source: Schoen (1988), Lemma 2.2; the checked simultaneous projective curve branch-parameter construction. -/
theorem s2v_i2a_finite_curve_point_parameters
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (hdimZ : TopologicalSpace.dim Z.left = 1)
    {I : Type} [Finite I] [Nonempty I] (p : I → ComplexPoint Z) (hp : Function.Injective p) :
    ∃ (V : Over (Spec ↧ℂ)) (hV : IsAffine V.left) (v : V ⟶ Z)
      (y : I → ComplexPoint V) (z : Γ(V.left, ⊤)),
      IsOpenImmersion v.left ∧ (∀ i, Point.map v (y i) = p i) ∧
      (MvPolynomial.eval₂Hom V.hom.appTop.hom (fun _ : Fin 1 => z)).Etale ∧
      Function.Injective (fun i => Point.evaluate ⊤ z (y i)) ∧
      ∀ i, (((p i).left.ker).comap v.left).ideal ⟨⊤, @isAffineOpen_top V.left hV⟩ =
        Ideal.span {z - algebraMap ℂ Γ(V.left, ⊤) (Point.evaluate ⊤ z (y i))} := by
  classical
  letI := Fintype.ofFinite I
  let n := Fintype.card I - 1
  have hn : n + 1 = Fintype.card I := Nat.sub_one_add_one (Fintype.card_pos.ne')
  let e : Fin (n + 1) ≃ I := (finCongr hn).trans (Fintype.equivFin I).symm
  obtain ⟨V, hV, v, y, z, hv, hy, hEt, hsep, hI⟩ :=
    s2v_i2a_simultaneous_curve_branch_parameters Z hdimZ n (fun i => p (e i)) (hp.comp e.injective)
  refine ⟨V, hV, v, (fun i => y (e.symm i)), z, hv, ?_, hEt, hsep.comp e.symm.injective, ?_⟩
  · intro i
    simpa only [e.apply_symm_apply] using hy (e.symm i)
  · intro i
    simpa only [e.apply_symm_apply] using hI (e.symm i)

/-- One actual etale curve chart retains every branch point and every tuple support point, allowing repeated tuple points.
Source: Schoen (1988), Lemma 2.2; the checked simultaneous finite-support curve parameter construction. -/
theorem s2v_i2a_branch_and_tuple_curve_parameters
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]
    (hdimZ : TopologicalSpace.dim Z.left = 1)
    {T : Type} [Finite T] (branch : T → ComplexPoint Z) (hbranch : Function.Injective branch)
    (n : ℕ) (tuple : Fin (n + 1) → ComplexPoint Z) :
    ∃ (V : Over (Spec ↧ℂ)) (hV : IsAffine V.left) (v : V ⟶ Z)
      (yb : T → ComplexPoint V) (yt : Fin (n + 1) → ComplexPoint V) (z : Γ(V.left, ⊤)),
      IsOpenImmersion v.left ∧ (∀ t, Point.map v (yb t) = branch t) ∧
      (∀ i, Point.map v (yt i) = tuple i) ∧
      (MvPolynomial.eval₂Hom V.hom.appTop.hom (fun _ : Fin 1 => z)).Etale ∧
      Function.Injective (fun t => Point.evaluate ⊤ z (yb t)) ∧
      (∀ t i, Point.evaluate ⊤ z (yb t) = Point.evaluate ⊤ z (yt i) ↔ branch t = tuple i) ∧
      (∀ i j, Point.evaluate ⊤ z (yt i) = Point.evaluate ⊤ z (yt j) ↔ tuple i = tuple j) ∧
      (∀ t, (((branch t).left.ker).comap v.left).ideal ⟨⊤, @isAffineOpen_top V.left hV⟩ =
        Ideal.span {z - algebraMap ℂ Γ(V.left, ⊤) (Point.evaluate ⊤ z (yb t))}) ∧
      (∀ i, (((tuple i).left.ker).comap v.left).ideal ⟨⊤, @isAffineOpen_top V.left hV⟩ =
        Ideal.span {z - algebraMap ℂ Γ(V.left, ⊤) (Point.evaluate ⊤ z (yt i))}) := by
  classical
  letI := Fintype.ofFinite T
  let support : Finset (ComplexPoint Z) := Finset.univ.image branch ∪ Finset.univ.image tuple
  let bi (t : T) : support := ⟨branch t, Finset.mem_union.mpr
    (Or.inl (Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩))⟩
  let ti (i : Fin (n + 1)) : support := ⟨tuple i, Finset.mem_union.mpr
    (Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))⟩
  haveI : Nonempty support := ⟨ti 0⟩
  obtain ⟨V, hV, v, y, z, hv, hy, hEt, hsep, hI⟩ :=
    s2v_i2a_finite_curve_point_parameters Z hdimZ (fun p : support => p.val) Subtype.val_injective
  refine ⟨V, hV, v, (fun t => y (bi t)), (fun i => y (ti i)), z,
    hv, (fun t => hy (bi t)), (fun i => hy (ti i)), hEt, ?_, ?_, ?_, ?_, ?_⟩
  · intro t u htu
    apply hbranch
    exact congrArg Subtype.val (hsep htu)
  · intro t i
    constructor
    · intro hti
      exact congrArg Subtype.val (hsep hti)
    · intro hti
      have H : bi t = ti i := Subtype.ext hti
      exact congrArg (fun p : support => Point.evaluate ⊤ z (y p)) H
  · intro i j
    constructor
    · intro hij
      exact congrArg Subtype.val (hsep hij)
    · intro hij
      have H : ti i = ti j := Subtype.ext hij
      exact congrArg (fun p : support => Point.evaluate ⊤ z (y p)) H
  · intro t
    exact hI (bi t)
  · intro i
    exact hI (ti i)

end HodgeLean.Foundations.Program
