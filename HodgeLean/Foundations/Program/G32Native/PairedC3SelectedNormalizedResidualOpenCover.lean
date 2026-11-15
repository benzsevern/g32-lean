import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedResidualOpenCover
import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedNormalizationUnit
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

/-- The entire selected residual component has a Rees cover carrying the
variable normalization coefficient and its unit value on the residual base.
Source: Hartshorne, Algebraic Geometry, II.3 and II.7.13. -/
theorem pairedC3_selected_normalized_residual_open_cover
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
      (∀ x, ∃ (u v α : Γ((P.T.B i.castSucc).left, U x))
        (h₀ : (V x 0).1 ≤ (P.T.b i).left ⁻¹ᵁ (U x).1)
        (h₁ : (V x 1).1 ≤ (P.T.b i).left ⁻¹ᵁ (U x).1)
        (s : Γ((P.T.B i.succ).left, V x 0))
        (t : Γ((P.T.B i.succ).left, V x 1)),
        (P.T.D i.castSucc ⟨2 * i.val, by omega⟩).ideal (U x) = Ideal.span {u} ∧
        (P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩).ideal (U x) = Ideal.span {v} ∧
        ((P.C.slices i.castSucc).left.app (U x).1).hom (v - α * u) = 0 ∧
        IsUnit (((P.C.slices i.castSucc).left.app (U x).1).hom α) ∧
        IsUnit (Ideal.Quotient.mk (D.ideal (U x)) α) ∧
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
  obtain ⟨U, V, hx, hcover, hcharts, htop⟩ :=
    pairedC3_selected_residual_open_cover R P i hi
  refine ⟨U, V, hx, hcover, ?_, htop⟩
  intro x
  obtain ⟨u, v, h₀, h₁, s, t, hu, hv, hdata⟩ := hcharts x
  letI : Nonempty ((P.C.slices i.castSucc).left ⁻¹ᵁ (U x).1) :=
    ⟨⟨x.val.underlying, by
      change (P.C.slices i.castSucc).left x.val.underlying ∈ (U x).1
      simpa only [Point.underlying_map] using hx x⟩⟩
  obtain ⟨α, hα, hunit, hbase⟩ :=
    pairedC3_selected_affine_normalization_unit R P i (U x) u v hu hv
  exact ⟨u, v, α, h₀, h₁, s, t, hu, hv, hα, hunit, hbase, hdata⟩

#print axioms pairedC3_selected_normalized_residual_open_cover
end HodgeLean.Foundations.Program.ResidueSelected
