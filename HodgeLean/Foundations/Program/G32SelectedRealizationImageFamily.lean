import HodgeLean.Foundations.Program.G32SelectedRealizationLattice

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open scoped TensorProduct CategoryTheory.MonObj Manifold ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.fibreChart
  b65z_SharedFamily.fibreMan b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact
  b65z_SharedFamily.fibreConnected b65z_SharedFamily.totalChart b65z_SharedFamily.totalMan

set_option maxHeartbeats 400000 in
set_option maxRecDepth 2048 in
theorem g32x_image_maps {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (B : Module.Basis (Fin 12) ℤ
      (b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Set.Subset.refl _) (b65z_s₀ c))) :
    ∃ i : (b65z_fiber D B t).X ⟶ g32x_J D t,
    ∃ q : g32x_J D t ⟶ (b65z_fiber D B t).X,
      IsMonHom i ∧ IsMonHom q ∧ i ≫ q = 𝟙 (b65z_fiber D B t).X ^ (116640 : ℕ) ∧
        homPullback (q ≫ i) 1 = g32x_projector D t := by
  let M := b63l_parameterLattice c D.C D.hC (b6t_polydisc c)
    (Set.Subset.refl _) (b65z_s₀ c)
  letI : Module.Finite ℤ M := Module.Finite.of_basis B
  letI : Module.Free ℤ M := Module.Free.of_basis B
  let FM := b63e_transportedF c D.C D.hC (b6t_polydisc c)
    (Set.Subset.refl _) D.P (b65z_s₀ c) t
  let QM := b63e_singularQ c D.C D.hC (b6t_polydisc c)
    (Set.Subset.refl _) (b65z_s₀ c) (D.P (b65z_s₀ c)) (D.Q (b65z_s₀ c))
  have hW := b63e_weight_one_riemann c D.C D.hC (b6t_polydisc c)
    (Set.Subset.refl _) D.hG D.atlas.hb D.atlas.f D.atlas.hf D.atlas.hsurj D.hk
    D.Q₀ D.hQ₀ D.Q D.hQ D.P D.hP (b65z_s₀ c) t
  dsimp only [b65z_fiber, b63g5_fiber, b63g2_sixfold, g32x_J]
  let Y := b5_model M FM hW.1 QM
  letI : GrpObj Y := b5_groupObj M FM hW.1 QM hW.2
  letI : IsCommMonObj Y := b5_commutative_aux M FM hW.1 QM hW.2
  letI : IsIntegral Y.left := b5_integral M FM hW.1 QM hW.2
  letI : Smooth Y.hom := b5_smooth M FM hW.1 QM hW.2
  letI : IsProjective Y.hom := b5_projective M FM hW.1 QM hW.2
  let L := g32x_L D t
  let F := b3_periodF ℂ (b65z_fibre c D.C t)
  have hF : b2_IsWeightOne L F := b3_isWeightOne (by simp)
  have hQ : b2_IsRiemannForm L F (D.Q t) :=
    b3_intersectionForm_isRiemannForm (by simp) (D.Q t) (D.hQ t)
  let X := b5_model L F hF (D.Q t)
  letI : GrpObj X := b5_groupObj L F hF (D.Q t) hQ
  letI : IsCommMonObj X := b5_commutative_aux L F hF (D.Q t) hQ
  letI : IsIntegral X.left := b5_integral L F hF (D.Q t) hQ
  letI : Smooth X.hom := b5_smooth L F hF (D.Q t) hQ
  letI : IsProjective X.hom := b5_projective L F hF (D.Q t) hQ
  let eX : L ≃+ b2_abelianLattice X := b5_periodEquiv L F hF (D.Q t) hQ
  let eY : M ≃+ b2_abelianLattice Y := b5_periodEquiv M FM hW.1 QM hW.2
  have heX : F.map (b2_cplxMap eX.toAddMonoidHom) = b2_abelianF X :=
    b5_period_filtration L F hF (D.Q t) hQ
  have heY : FM.map (b2_cplxMap eY.toAddMonoidHom) = b2_abelianF Y :=
    b5_period_filtration M FM hW.1 QM hW.2
  let U : L →+ L := b4_groupEnd ℂ (C := b65z_fibre c D.C t) b4b_projectorCoeff
  obtain ⟨j, p, hjp, hpj, hjF, hpF⟩ := g32x_lattice_factorization D t
  obtain ⟨i, q, hiMon, hqMon, hret, hperiod⟩ :=
    g32x_marked_comparison X Y L M eX eY F FM heX heY j p hjF hpF 116640 hpj
  have hU : homPullback (q ≫ i) 1 = g32x_projector D t := by
    apply LinearMap.ext
    intro x
    apply (abelianPeriodEquiv X).injective
    apply AddMonoidHom.ext
    intro m
    obtain ⟨l, rfl⟩ := eX.surjective m
    rw [hperiod, hjp]
    exact (g32x_modelOperator_period L F hF (D.Q t) hQ U x l).symm
  exact ⟨i, q, hiMon, hqMon, hret, hU⟩

end HodgeLean.Foundations.Program
