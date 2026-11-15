import HodgeLean.Adapters.NormalConeB4aClassJacobian
import HodgeLean.Adapters.NormalConeB4aClassAnalyticZeros
import HodgeLean.Adapters.NormalConeB4aClassAnalyticImage
import HodgeLean.Adapters.NormalConeB4aClassRemovableSet

/-! # Analytic inverses of holomorphic local homeomorphisms

Route: the critical set is the zero set of the analytic Jacobian. The finite
mapping theorem makes its image analytic; regular points give density of its
complement. The inverse is analytic there and continuous everywhere, so
continuous analytic extension applies to each coordinate.
-/
noncomputable section
namespace HodgeLean.Adapters
open Set Filter Topology AlgebraicTopology.Singular
open HodgeLean.Foundations.Analytic

/-- An analytic local homeomorphism of complex coordinate spaces has an
analytic inverse on its target. -/
theorem a3b4a_classAnalyticInverse
    {n : ℕ} (e : OpenPartialHomeomorph (Fin n → ℂ) (Fin n → ℂ))
    (ha : AnalyticOnNhd ℂ e e.source) : AnalyticOnNhd ℂ e.symm e.target := by
  cases n with
  | zero =>
    intro y hy
    apply AnalyticAt.pi
    intro j
    exact Fin.elim0 j
  | succ d =>
    let δ := fun x => (complexMatrixOfContinuousLinearMap (d+1) (fderiv ℂ e x)).det
    have hδ : AnalyticOnNhd ℂ δ e.source :=
      a3b4a_classJacobian_analytic e e.source e.open_source ha
    let A : Set e.source := {x | δ x = 0}
    let B : Set (Fin (d+1) → ℂ) := Subtype.val '' (e.toHomeomorphSourceTarget '' A)
    have hA : an_IsClosedAnalytic (anrem_openSpace (an_euclidSpace (d+1)) e.open_source) A :=
      a3b4a_classAnalytic_zeroSet_openSpace e.source e.open_source δ hδ
    have hloc : ∀ y ∈ e.target ∩ B, anrem_LocEq B y := by
      intro y hy
      obtain ⟨w, hw, rfl⟩ := hy.2
      exact a3b4a_classAnalyticChart_image_localEquations e ha A hA w hw
    have hdense : e.target ⊆ closure (e.target \ B) := by
      intro y hy
      apply mem_closure_iff.mpr
      intro W hW hyW
      let V := e.source ∩ e ⁻¹' W
      have hV : IsOpen V := e.isOpen_inter_preimage hW
      have hne : V.Nonempty := ⟨e.symm y, e.map_target hy, by
        simpa only [Set.mem_preimage, e.right_inv hy] using hyW⟩
      obtain ⟨v, hv, hinj, -⟩ := a3b4a_classAnalyticInverse_exists_regular e ha V hV hne
        (fun _ h => h.1)
      have hdet : δ v ≠ 0 :=
        complexMatrixOfContinuousLinearMap_det_ne_zero (d+1) (fderiv ℂ e v) hinj
      refine ⟨e v, hv.2, e.map_source hv.1, ?_⟩
      rintro ⟨_, ⟨z, hz, rfl⟩, hze⟩
      have heq : z.1 = v := e.injOn z.2 hv.1 hze
      change δ z.1 = 0 at hz
      rw [heq] at hz
      exact hdet hz
    have hinverse : AnalyticOnNhd ℂ e.symm (e.target \ B) := by
      intro y hy
      let x := e.symm y
      have hx : x ∈ e.source := e.map_target hy.1
      have hn : δ x ≠ 0 := by
        intro hz
        apply hy.2
        refine ⟨e.toHomeomorphSourceTarget ⟨x, hx⟩, ⟨⟨x, hx⟩, hz, rfl⟩, ?_⟩
        exact e.right_inv hy.1
      let M := complexMatrixOfContinuousLinearMap (d+1) (fderiv ℂ e x)
      have hmu : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr hn.isUnit
      have hmi : Function.Injective M.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr hmu
      have hi : Function.Injective (fderiv ℂ e x) := by
        intro u v huv
        apply hmi
        simpa only [M, complexMatrixOfContinuousLinearMap_mulVec] using huv
      have h := a3b4a_classAnalyticInverse_of_injective_derivative e x hx (ha x hx) hi
      change AnalyticAt ℂ e.symm (e (e.symm y)) at h
      rwa [e.right_inv hy.1] at h
    intro y hy
    apply AnalyticAt.pi
    intro j
    apply a3b4a_classAnalytic_extend_across_set d e.target B e.open_target hloc hdense
      (fun w => e.symm w j) ?_ ?_ y hy
    · intro w hw
      exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d+1) => ℂ) j).analyticAt _).comp
        (hinverse w hw)
    · exact (continuous_apply j).comp_continuousOn e.symm.continuousOn

end HodgeLean.Adapters
