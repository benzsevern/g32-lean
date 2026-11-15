import HodgeLean.Foundations.Program.RelativeFrameOperatorRecoveryInner

set_option maxHeartbeats 400000
noncomputable section
open Set Manifold Filter Topology
open scoped ContDiff BoundedContinuousFunction
namespace HodgeLean.Foundations.Program

theorem rf4_correction_annulus_difference {C : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] {O : Set C} {D : rf4_OuterData C O} {ε : Fin D.m → ℂ}
    {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ, ℂ) ω X]
    (S : rf4_Plumbing D ε X) (χ : Fin D.m → ℂ → ℂ) (φ : rf4_Tgt D)
    (v : rf2_smoothForms X 1 0) (x : Fin D.m) (u : b63r_annulus (D.deg x) D.r) :
    rf4_outerCorrection S χ φ v (S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart (D.ann x)) u -
      rf4_innerCorrection S χ φ v x (S.w x) (rf4_rootMap (D.deg x) (ε x) u) *
        deriv (rf4_rootMap (D.deg x) (ε x)) u = (φ x : b63r_annulus (D.deg x) D.r →ᵇ ℂ) u := by
  classical
  let e : Fin D.m → OpenPartialHomeomorph X ℂ := fun y ↦
    S.h.symm.toOpenPartialHomeomorph ≫ₕ D.P.chart (D.ann y)
  have hut : (u : ℂ) ∈ (e x).target := by
    dsimp only [e]
    rw [rf4_stationaryChart_target]
    exact D.P.contained (D.ann x) (subset_closure ((D.hann x).ge u.property))
  have hi : (e x).symm u ∈ (S.w x).symm '' rf4_innerDisc (D.deg x) D.r (ε x) :=
    rf4_annulus_in_inner S x ⟨(D.P.chart (D.ann x)).symm u, ⟨u, u.property, rfl⟩, rfl⟩
  have hsum : (∑ y, rf4_tensorInChart (e y) (e x)
      (fun z ↦ χ y z * rf4_extendBdd (φ y) z) 1 0 u) =
      rf4_tensorInChart (e x) (e x) (fun z ↦ χ x z * rf4_extendBdd (φ x) z) 1 0 u := by
    apply Finset.sum_eq_single x
    · intro y _ hyx
      refine rf4_tensorInChart_zero_off (e y) (e x)
        (fun z ↦ χ y z * rf4_extendBdd (φ y) z) (b63r_annulus (D.deg y) D.r) ?_ 1 0 u ?_
      · intro z hz
        simp only [rf4_extendBdd, dif_neg hz, mul_zero]
      · intro hp
        have hpAnn : (e x).symm u ∈
            S.h '' ((D.P.chart (D.ann y)).symm '' b63r_annulus (D.deg y) D.r) := by
          obtain ⟨z, hz, heq⟩ := hp
          exact ⟨(D.P.chart (D.ann y)).symm z, ⟨z, hz, rfl⟩, heq⟩
        exact Set.disjoint_left.mp (S.disjoint hyx) (rf4_annulus_in_inner S y hpAnn) hi
    · intro hx
      exact False.elim (hx (Finset.mem_univ x))
  have hself (f : ℂ → ℂ) : rf4_tensorInChart (e x) (e x) f 1 0 u = f u := by
    simp only [rf4_tensorInChart, if_pos ((e x).map_target hut), (e x).right_inv hut,
      pow_one, pow_zero, mul_one, rf4_atlas_inverse_deriv (e x) u hut]
  have hdiff : rf4_outerCorrection S χ φ v (e x) u -
      rf4_innerCorrection S χ φ v x (e x) u = (φ x : b63r_annulus (D.deg x) D.r →ᵇ ℂ) u := by
    change ((∑ y, rf4_tensorInChart (e y) (e x)
      (fun z ↦ χ y z * rf4_extendBdd (φ y) z) 1 0 u) + rf4_smoothFormCoeff v (e x) u) -
      (rf4_tensorInChart (e x) (e x) (fun z ↦ (χ x z - 1) * rf4_extendBdd (φ x) z) 1 0 u +
        rf4_smoothFormCoeff v (e x) u) = _
    rw [hsum, hself, hself]
    rw [rf4_extendBdd, dif_pos u.property]
    ring
  have hglue := S.glue x u u.property
  have hw : rf4_rootMap (D.deg x) (ε x) u ∈ (S.w x).target := by
    rw [← hglue.2]
    exact (S.w x).map_source hglue.1
  have hsame : (e x).symm u = (S.w x).symm (rf4_rootMap (D.deg x) (ε x) u) := by
    rw [← hglue.2, (S.w x).left_inv hglue.1]
    rfl
  have htrans := rf4_innerCorrection_transition S χ φ v x (e x) (S.w x)
    (S.stationary (D.ann x)) (S.w_mem x) u (rf4_rootMap (D.deg x) (ε x) u) hut hw hsame
  rw [rf4_plumbing_transition_deriv S x u] at htrans
  rw [htrans] at hdiff
  exact hdiff

end HodgeLean.Foundations.Program
