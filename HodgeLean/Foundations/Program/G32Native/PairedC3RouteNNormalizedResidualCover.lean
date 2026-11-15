import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNSchemePairCharts
import HodgeLean.Foundations.Program.G32Native.PairedC3RouteNChartPresentation
import HodgeLean.Foundations.Program.G32Native.PairedC3AffineNormalizationUnit
import HodgeLean.Foundations.Program.G32Native.PairedC3SelectedRestrictions
import HodgeLean.Foundations.Program.G32Native.PairedC3ResidueSupport

/-! # A normalized residual chart cover at every retained step -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RegularPairChart
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program HodgeLean.Foundations.Program.ResidueSelected
attribute [local instance] G32JointPrefix.inst1 G32JointPrefix.inst2 G32JointPrefix.inst3 G32JointPrefix.inst4 G32JointPrefix.inst5 G32JointPrefix.inst6 G32JointPrefix.inst7 G32JointPrefix.inst8 G32JointPrefix.inst9 G32JointPrefix.inst10 G32JointPrefix.inst11 G32JointPrefix.inst12 G32JointPrefix.inst13 G32JointPrefix.inst14 G32JointPrefix.inst15 G32JointPrefix.inst16 G32JointPrefix.inst17 G32JointPrefix.inst18 G32JointPrefix.inst19 G32JointPrefix.inst25 G32JointPrefix.inst26 G32JointPrefix.inst27 G32JointPrefix.inst28 G32JointPrefix.inst29
attribute [local instance] G32JointBase.inst20 G32JointBase.inst21 G32JointBase.inst22 G32JointBase.inst23 G32JointBase.inst24

/-- The full actual residual subscheme at every retained step has a
normalized two-chart cover over all scheme points of its residue base.
The original ratios, coefficient maps and variable unit are retained.
Source: Hartshorne, Algebraic Geometry, II.3, II.6 and II.7.13;
Schoen, Compositio Mathematica 65 (1988), Sublemma 2.7. -/
theorem paired_c3_route_n_normalized_residual_cover
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (R : G32JointPrefix J aut S) (P : G32JointOrientedPositiveData R)
    (i : Fin R.r) :
    let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
      P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
    let D := K ⊔ (P.C.slices i.castSucc).left.ker
    let ι := {x : ProjectiveSpace (Fin (R.P.k + 1)) (Spec ↧ℂ) //
      x ∈ (s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i)).support}
    ∃ (U : ι → (P.T.B i.castSucc).left.affineOpens)
      (V : ι → Fin 2 → (P.T.B i.succ).left.affineOpens),
      (∀ x, (P.C.slices i.castSucc).left x.val ∈ (U x).1) ∧
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
  letI : IsIntegral (Over.mk (ProjectiveSpace.toBase (Fin (R.P.k + 1)) (Spec ↧ℂ))).left :=
    HodgeLean.Adapters.IntersectionProductScaf_projective_integral R.P.k
  letI := P.C.sliceImmersion i.castSucc
  let i₀ := (P.C.slices i.castSucc).left
  let σ := (P.T.b i).left
  let K := P.T.D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
    P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩
  let M₀ := K ⊔ i₀.ker
  let T := {x : ProjectiveSpace (Fin (R.P.k + 1)) (Spec ↧ℂ) //
    x ∈ (s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i)).support}
  have hdata := fun x : T => paired_c3_route_n_scheme_pair_charts R P i x.val x.property
  choose U u v hx hu hv V₁ V₂ h₁ h₂ e₁ e₂ hcover he₁ he₂ using hdata
  let V : T → Fin 2 → (P.T.B i.succ).left.affineOpens :=
    fun x j => if j = 0 then V₁ x else V₂ x
  have hV (x : T) : (V x 0).1 ⊔ (V x 1).1 = σ ⁻¹ᵁ (U x).1 := by
    simpa only [V, if_pos rfl, if_neg (by decide : (1 : Fin 2) ≠ 0)] using hcover x
  have hp := paired_c3_selected_unprocessed_restrictions R P i.castSucc i le_rfl
  refine ⟨U, V, hx, hV, ?_, ?_⟩
  · intro x
    simp only [V, if_pos rfl, if_neg (by decide : (1 : Fin 2) ≠ 0)]
    letI : Nonempty (i₀ ⁻¹ᵁ (U x).1) := ⟨⟨x.val, hx x⟩⟩
    obtain ⟨α, hα, hunit, hbase⟩ := pairedC3_affine_residual_normalization_unit i₀
      (P.T.D i.castSucc ⟨2 * i.val, by omega⟩)
      (P.T.D i.castSucc ⟨2 * i.val + 1, by omega⟩) M₀
      (hp.1.trans hp.2.symm)
      (by rw [hp.1]; exact paired_c3_residue_support_proper _ _)
      le_sup_right (U x) (u x) (v x) (hu x) (hv x)
    obtain ⟨hr₁, hs₁, hk₁⟩ := paired_c3_pair_chart_presentation (u x) (v x) (e₁ x)
      (σ.appLE (U x).1 (V₁ x).1 (h₁ x)).hom (he₁ x)
    obtain ⟨hr₂, hs₂, hk₂⟩ := paired_c3_pair_chart_presentation (v x) (u x) (e₂ x)
      (σ.appLE (U x).1 (V₂ x).1 (h₂ x)).hom (he₂ x)
    exact ⟨u x, v x, α, h₁ x, h₂ x, e₁ x (ratio (u x) (v x)),
      e₂ x (ratio (v x) (u x)), hu x, hv x, hα, hunit, hbase,
      hr₁, hr₂, hs₁, hk₁, hs₂, hk₂⟩
  · apply top_unique
    intro z _
    let M := M₀.comap σ
    have hzM : M.subschemeι z ∈ (M.support : Set _) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact Set.mem_range_self z
    have hz₀ : σ (M.subschemeι z) ∈ (M₀.support : Set _) := by
      rw [Scheme.IdealSheafData.support_comap] at hzM
      exact hzM
    change σ (M.subschemeι z) ∈ ((K ⊔ i₀.ker).support : Set _) at hz₀
    rw [Scheme.IdealSheafData.support_sup] at hz₀
    have hrange : σ (M.subschemeι z) ∈ Set.range i₀ := by
      have h := hz₀.2
      rw [Scheme.Hom.support_ker] at h
      rwa [i₀.isClosedEmbedding.isClosed_range.closure_eq] at h
    obtain ⟨x, hxx⟩ := hrange
    have hK : K.comap i₀ = s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i) := by
      rw [Scheme.IdealSheafData.comap_sup, hp.1, hp.2, sup_idem]
    have hxH : x ∈ (s2e_s2b_residueIdeal R.P.k (P.C.residue.indices i)).support := by
      rw [← hK, Scheme.IdealSheafData.support_comap]
      change i₀ x ∈ (K.support : Set _)
      rw [hxx]
      exact hz₀.1
    let q : T := ⟨x, hxH⟩
    have hmem : M.subschemeι z ∈ (V₁ q).1 ⊔ (V₂ q).1 := by
      rw [hcover q]
      change σ (M.subschemeι z) ∈ (U q).1
      rw [← hxx]
      exact hx q
    rcases hmem with hz | hz
    · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨(q, 0), by
        change M.subschemeι z ∈ (V₁ q).1
        exact hz⟩
    · exact TopologicalSpace.Opens.mem_iSup.mpr ⟨(q, 1), by
        change M.subschemeι z ∈ (V₂ q).1
        exact hz⟩

#print axioms paired_c3_route_n_normalized_residual_cover
end HodgeLean.Foundations.Program.G32Native
