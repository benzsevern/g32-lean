import HodgeLean.Foundations.Program.G32SelectedRealizationReferenceProjection
import HodgeLean.Foundations.Program.G32SelectedRealizationModelPeriod

noncomputable section
set_option maxRecDepth 2000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open scoped TensorProduct CategoryTheory.MonObj Manifold ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.fibreChart
  b65z_SharedFamily.fibreMan b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact
  b65z_SharedFamily.fibreConnected b65z_SharedFamily.totalChart b65z_SharedFamily.totalMan

attribute [local irreducible] b63l_saturation b5_model b2_abelianF b5_periodEquiv

set_option maxHeartbeats 400000 in
theorem g32y_marked_period_equivalence {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (B : Module.Basis (Fin 12) ℤ
      (b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _) (b65z_s₀ c))) :
    ∃ e : b63l_parameterLattice c D.C D.hC (b6t_polydisc c)
        (Set.Subset.refl _) (b65z_s₀ c) ≃+ b2_abelianLattice (b65z_fiber D B t).X,
      (b63e_transportedF c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _)
        D.P (b65z_s₀ c) t).map (b2_cplxMap e.toAddMonoidHom) =
          b2_abelianF (b65z_fiber D B t).X ∧
      ∀ x l, abelianPeriod (b65z_fiber D B t).X ((b65z_fiber D B t).W.J x) (e l) =
        abelianPeriod (b65z_fiber D B t).X x
          (e (b63g2_operator c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _) (b65z_s₀ c) l)) := by
  dsimp only [b65z_fiber, b63g5_fiber, b63g2_sixfold]
  classical
  letI := Module.Free.of_basis B
  letI := Module.Finite.of_basis B
  let W := b63e_weight_one_riemann c D.C D.hC (b6t_polydisc c)
    (Set.Subset.refl _) D.hG D.atlas.hb D.atlas.f D.atlas.hf D.atlas.hsurj
    D.hk D.Q₀ D.hQ₀ D.Q D.hQ D.P D.hP (b65z_s₀ c) t
  let L : Type := b63l_parameterLattice c D.C D.hC (b6t_polydisc c)
    (Set.Subset.refl _) (b65z_s₀ c)
  let F := b63e_transportedF c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _)
    D.P (b65z_s₀ c) t
  let Q := b63e_singularQ c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _)
    (b65z_s₀ c) (D.P (b65z_s₀ c)) (D.Q (b65z_s₀ c))
  letI := b5_groupObj L F W.1 Q W.2
  have hX : (b5_model L F W.1 Q).left = b5_X L F W.1 Q := by
    unfold b5_model
    rfl
  letI : IsIntegral (b5_model L F W.1 Q).left := by
    rw [hX]
    exact b5_integral_aux L F W.1 Q W.2
  letI := b5_smooth_aux L F W.1 Q W.2
  letI := b5_projective_aux L F W.1 Q W.2
  let e := b5_periodEquiv L F W.1 Q W.2
  refine ⟨e, ?_, ?_⟩
  · change F.map (b2_cplxMap e.toAddMonoidHom) = b2_abelianF (b5_model L F W.1 Q)
    have hm := b5_period_filtration L F W.1 Q W.2
    simpa only [e, L, F, Q] using hm
  · intro x l
    change abelianPeriod (b5_model L F W.1 Q)
      (b63g_dualOperator (b5_model L F W.1 Q)
        (b63g_modelMap L F W.1 Q W.2
          (b63g2_operator c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _)
            (b65z_s₀ c)).toAddMonoidHom) x) (e l) = _
    rw [g32y_dualOperator_period]
    let φ := (b63g2_operator c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _)
      (b65z_s₀ c)).toAddMonoidHom
    have he : b63g_modelMap L F W.1 Q W.2 φ (e l) = e (φ l) := by
      change e (φ (e.symm (e l))) = e (φ l)
      rw [e.symm_apply_apply]
    exact congrArg (abelianPeriod (b5_model L F W.1 Q) x) he

end HodgeLean.Foundations.Program
