import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedReesCharts
import HodgeLean.Foundations.Program.G32Native.PairedC3SliceChartCoverage
import HodgeLean.Foundations.Program.G32Native.PairedC3ResidualReesCover
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24

attribute [local instance] G32JointSlicedComponent.sliceImmersion
open HodgeLean.Foundations.Program.G32Native

/-- The actual last selected Rees charts cover the entire residual subscheme,
including the points not represented by complex points.
Source: Hartshorne, Algebraic Geometry, II.3 and II.7.13. -/
theorem pairedC3_selected_residual_open_cover
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) (hi : i.val + 1 = R.r) :
    let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
    let D := K ⊔ (P.C.slices i.castSucc).left.ker
    let ι := {x : ComplexPoint (Over.mk
      (ProjectiveSpace.toBase (Fin (R.P.k + 1)) (Spec ↧ℂ))) //
      x.underlying ∈ (s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i)).support}
    ∃ (U : ι → (P.T.B i.castSucc).left.affineOpens)
      (V : ι → Fin 2 → (P.T.B i.succ).left.affineOpens),
      (∀ x, (Point.map (P.C.slices i.castSucc) x.val).underlying ∈ (U x).1) ∧
      (∀ x, (V x 0).1 ⊔ (V x 1).1 = (P.T.b i).left ⁻¹ᵁ (U x).1) ∧
      (∀ x, ∃ (u v : Γ((P.T.B i.castSucc).left, U x))
        (h₀ : (V x 0).1 ≤ (P.T.b i).left ⁻¹ᵁ (U x).1)
        (h₁ : (V x 1).1 ≤ (P.T.b i).left ⁻¹ᵁ (U x).1)
        (s : Γ((P.T.B i.succ).left, V x 0))
        (t : Γ((P.T.B i.succ).left, V x 1)),
        (P.T.D i.castSucc ⟨2 * i.val, by omega⟩).ideal (U x) = Ideal.span {u} ∧
        (P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩).ideal (U x) = Ideal.span {v} ∧
        let f₀ : Γ((P.T.B i.castSucc).left, U x) →+*
          Γ((P.T.B i.succ).left, V x 0) := ((P.T.b i).left.appLE (U x).1 (V x 0).1 h₀).hom
        let f₁ : Γ((P.T.B i.castSucc).left, U x) →+*
          Γ((P.T.B i.succ).left, V x 1) := ((P.T.b i).left.appLE (U x).1 (V x 1).1 h₁).hom
        f₀ u = s * f₀ v ∧ f₁ v = t * f₁ u ∧
        Function.Surjective (Polynomial.eval₂RingHom f₀ s) ∧
        RingHom.ker (Polynomial.eval₂RingHom f₀ s) =
          Ideal.span {Polynomial.C u - (Polynomial.X : Polynomial Γ((P.T.B i.castSucc).left, U x)) * Polynomial.C v} ∧
        Function.Surjective (Polynomial.eval₂RingHom f₁ t) ∧
        RingHom.ker (Polynomial.eval₂RingHom f₁ t) =
          Ideal.span {Polynomial.C v - (Polynomial.X : Polynomial Γ((P.T.B i.castSucc).left, U x)) * Polynomial.C u}) ∧
      (⨆ j : ι × Fin 2, (D.comap (P.T.b i).left).subschemeι ⁻¹ᵁ (V j.1 j.2).1) = ⊤ := by
  classical
  dsimp only
  let ι := {x : ComplexPoint (Over.mk
      (ProjectiveSpace.toBase (Fin (R.P.k + 1)) (Spec ↧ℂ))) //
      x.underlying ∈ (s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i)).support}
  have hdata := fun x : ι => paired_c3_selected_last_rees_charts R P i hi x.val x.property
  choose U u v hx hu hv V₁ V₂ h₁ h₂ s t hcover hrest using hdata
  let V : ι → Fin 2 → (P.T.B i.succ).left.affineOpens :=
    fun x j => if j = 0 then V₁ x else V₂ x
  have hV (x : ι) : (V x 0).1 ⊔ (V x 1).1 = (P.T.b i).left ⁻¹ᵁ (U x).1 := by
    simpa only [V, if_pos rfl, if_neg (by decide : (1 : Fin 2) ≠ 0)] using hcover x
  refine ⟨U, V, hx, hV, ?_, ?_⟩
  · intro x
    simp only [V, if_pos rfl, if_neg (by decide : (1 : Fin 2) ≠ 0)]
    refine ⟨u x, v x, h₁ x, h₂ x, s x, t x, hu x, hv x, hrest x⟩
  · apply pairedC3_residual_rees_iSup (P.T.b i).left _ (fun x => (U x).1)
      (fun x j => (V x j).1) ?_ hV
    apply pairedC3_slice_charts_cover_base (P.C.slices i.castSucc)
    intro x hxK
    have hp := paired_c3_selected_unprocessed_restrictions R P i.castSucc i (by rfl)
    have hxH : x.underlying ∈
        (s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i)).support := by
      simpa only [Scheme.IdealSheafData.comap_sup, hp.1, hp.2, sup_idem] using hxK
    exact ⟨⟨x, hxH⟩, hx ⟨x, hxH⟩⟩

#print axioms pairedC3_selected_residual_open_cover
end HodgeLean.Foundations.Program.ResidueSelected
