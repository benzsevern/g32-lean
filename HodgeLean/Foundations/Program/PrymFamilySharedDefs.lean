import HodgeLean.Foundations.Program.PeriodFunctionIntegrated

/-! # Prym fibres on the retained geometric family
Implication from shared geometry to the stage-P family fields.
HC no distance; AV milestone no distance.
-/
noncomputable section
open Set Manifold Filter Topology HodgeLean.Papers
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint HodgeLean.RealDefs
open HodgeLean.Foundations HodgeLean.Foundations.Symplectic HodgeLean.Adapters TopologicalSpace
open scoped ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful

/-- A rank-twelve basis on the retained reference fibre.
Source: `b63d_lattice_rank`. -/
def b63gR_basis (R : rf8_SharedFamily) : Module.Basis (Fin 12) ℤ
    (b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) b63gP_s₀) :=
  (b63d_lattice_rank mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
    b63gP_s₀ (R.hG _) mr_base_mem_chart R.atlas.f (R.hk _) (R.hsurj _)
    (R.hgal _) (R.hbranch _) (R.hrot _)).1.some

example (R : rf8_SharedFamily) : Module.finrank ℤ
    (b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) b63gP_s₀) = 12 := by
  rw [Module.finrank_eq_card_basis (b63gR_basis R), Fintype.card_fin]

/-- The stage-P construction with the retained surface, structures and period comparison.
Source: `b63gP_family_of_cover`, its constructor and `b63gP_fiber_positive`. -/
def b63gR_family (R : rf8_SharedFamily) : g32h_PrymFamily := by
  let X : (b6t_polydisc mr_base) → g32t_Sixfold := fun t ↦ b63g5_fiber mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) R.hG mr_base_mem_chart R.atlas.f R.atlas.hf R.atlas.hsurj R.hk R.Q₀ R.hQ₀ R.Q R.hQ R.P R.hP b63gP_s₀ (b63gR_basis R) t
  have key : ∀ t : (b6t_polydisc mr_base), (dim (X t).X.left : ℤ) = g32h_multCW b63g5_tuple ∧
      (((g32h_h10 (X t) : ℝ) = g32h_holoCW b63g5_tuple ∧
          (g32h_h01 (X t) : ℝ) = g32h_multCW b63g5_tuple - g32h_holoCW b63g5_tuple) ∨
        ((g32h_h01 (X t) : ℝ) = g32h_holoCW b63g5_tuple ∧
          (g32h_h10 (X t) : ℝ) = g32h_multCW b63g5_tuple - g32h_holoCW b63g5_tuple)) ∧
      IsNondegenerate (polarizationVec (torusCohomology_cupProductOf (X t).X) (X t).pol) ∧
      (letI := (torusCohomology_cupProductOf (X t).X).finite
       IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf (X t).X) (X t).pol)
        (X t).W.J) := by
    intro t
    have hb : mr_base ∈ b6_chart := mr_base_mem_chart
    let _ : Module.Free ℤ (b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) b63gP_s₀) := Module.Free.of_basis (b63gR_basis R)
    let _ : Module.Finite ℤ (b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) b63gP_s₀) := Module.Finite.of_basis (b63gR_basis R)
    have W := b63e_weight_one_riemann mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) R.hG hb R.atlas.f R.atlas.hf R.atlas.hsurj R.hk R.Q₀ R.hQ₀ R.Q R.hQ R.P R.hP b63gP_s₀ t
    have hsq := b63g2_operator_sq mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) b63gP_s₀ (R.hG b63gP_s₀)
    have hφ := b63g2_operator_filtration mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) R.hG R.P R.hP b63gP_s₀ t
    have hX : X t = b63g2_sixfold _ _ W.1 _ W.2 _ hsq hφ := rfl
    have hE := b63g2_eigen_rank mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) R.hG R.P R.hP b63gP_s₀ t hb R.atlas.f (R.hk t)
      (R.hsurj t) (R.hgal t) (R.hbranch t) (R.hrot t)
    have h10 : g32h_h10 (X t) = 3 := by
      have h := (b63g2_sixfold_h10 _ _ W.1 _ W.2 _ hsq hφ).trans
        (b63g2_weil_h10 _ _ W.1 _ W.2 3 (by norm_num) _ hsq hφ)
      rw [show HodgeBlocks.WeilAction.omegaC ((3 : ℤ) : ℚ) = HodgeBlocks.WeilAction.omegaC 3 by
        norm_num] at h
      rw [hX]
      exact h.trans hE.2
    have h01 : g32h_h01 (X t) = 3 := by
      have h := (b63g2_sixfold_h01 _ _ W.1 _ W.2 _ hsq hφ).trans
        (b63g2_weil_h01 _ _ W.1 _ W.2 3 (by norm_num) _ hsq hφ)
      rw [show HodgeBlocks.WeilAction.omegaC ((3 : ℤ) : ℚ) = HodgeBlocks.WeilAction.omegaC 3 by
        norm_num] at h
      rw [hX]
      exact h.trans hE.1
    have hdim : (dim (X t).X.left : ℤ) = 6 := by
      let _ : IsIntegral (b5_model _ _ W.1
          (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) b63gP_s₀ (R.P b63gP_s₀) (R.Q b63gP_s₀))).left :=
        b5_integral_aux _ _ W.1 _ W.2
      have h := b63g_model_finrank _ _ W.1 _ W.2
      rw [Module.finrank_eq_card_basis (b63gR_basis R), Fintype.card_fin] at h
      rw [hX]
      change (dim (b5_model _ _ W.1 (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) b63gP_s₀ (R.P b63gP_s₀) (R.Q b63gP_s₀))).left : ℤ)
        = 6
      omega
    have hN : g32h_Nielsen b63g5_tuple := b63d_root_nielsen
    refine ⟨?_, Or.inl ?_, ?_, ?_⟩
    · rw [hdim, g32h_multCW_of_nielsen _ hN]
    · rw [h10, h01, g32h_holoCW_of_nielsen _ hN, g32h_multCW_of_nielsen _ hN]
      norm_num
    · have h :=
        letI := b5_groupObj _ _ W.1 _ W.2
        letI : IsIntegral (b5_model _ _ W.1
            (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) b63gP_s₀ (R.P b63gP_s₀) (R.Q b63gP_s₀))).left :=
          b5_integral_aux _ _ W.1 _ W.2
        letI := b5_smooth_aux _ _ W.1 _ W.2
        letI := b5_projective_aux _ _ W.1 _ W.2
        b2_abelian_nondegenerate _ _ (b63g_modelForm_riemann _ _ W.1 _ W.2)
      rw [hX]
      unfold b63g2_sixfold
      exact h
    · rw [hX]
      exact b63g2_sixfold_rosati _ _ W.1 _ W.2 _ hsq hφ
        (b63g2_operator_skew mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) b63gP_s₀ (R.hG b63gP_s₀) (R.P b63gP_s₀) (R.hP b63gP_s₀) (R.Q b63gP_s₀) (R.hQ b63gP_s₀))
  exact {
           S := (b6t_polydisc mr_base)
           tuple := fun _ ↦ b63g5_tuple
           tuple_nielsen := fun _ ↦ b63d_root_nielsen
           fiber := X
           dim_eq := fun t ↦ (key t).1
           hodge := fun t ↦ (key t).2.1
           nondegenerate := fun t ↦ (key t).2.2.1
           rosati := fun t ↦ (key t).2.2.2
           positive := fun t ↦ b63gP_fiber_positive_aux mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _) R.hG mr_base_mem_chart R.atlas.f
             R.atlas.hf R.atlas.hsurj R.hk R.Q₀ R.hQ₀ R.Q R.hQ R.P R.hP b63gP_s₀ (b63gR_basis R) t _ }

example (R : rf8_SharedFamily) : (b63gR_family R).S = b6t_polydisc mr_base := rfl

example (R : rf8_SharedFamily) : Nonempty (b63gR_family R).S := ⟨b63gP_s₀⟩

/-- Checked shared-cover inputs for the based marking, with positive lattice rank.
This example uses only existing statements with bodies. -/
example : ∃ (R : rf8_SharedFamily) (u₀ : R.atlas.π ⁻¹' {b63gP_basePoint}),
    (∀ i, R.atlas.hπ.fundamentalGroupToMulOpposite u₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i)) ∧
    Module.finrank ℤ (b63l_parameterLattice mr_base R.C R.hC
      (b6t_polydisc mr_base) (Subset.refl _) b63gP_s₀) = 12 ∧ b4b_root 0 ≠ 1 := by
  obtain ⟨R, y₀, γ, u₀, hγ, hroot⟩ := rf8_shared_root
  have hy : y₀ = b63gP_basePoint := by
    apply Subtype.ext
    obtain ⟨p, hp, -⟩ := hγ 12
    calc
      (y₀ : OnePoint ℂ) = mr_curve 12 0 := by simpa using hp 0
      _ = (b63gP_basePoint : OnePoint ℂ) := by
        change mr_curve 12 0 = ((mr_basePoint : ℂ) : OnePoint ℂ)
        simp [mr_curve, mr_outer, mr_basePoint]
  subst y₀
  have hγeq : γ = b63gP_loops := by
    funext i
    exact (mr_loop_existsUnique mr_base b63gP_s₀.property b63gP_basePoint rfl i).unique
      (hγ i) (mr_loop_existsUnique mr_base b63gP_s₀.property b63gP_basePoint rfl i).exists.choose_spec
  subst γ
  refine ⟨R, u₀, hroot, ?_, ?_⟩
  · rw [Module.finrank_eq_card_basis (b63gR_basis R), Fintype.card_fin]
  · intro h
    have ho := b63_root_order (0 : Fin 13)
    rw [h, orderOf_one] at ho
    norm_num at ho

/-- Every retained fibre has dimension six and Hodge numbers three and three. -/
example (R : rf8_SharedFamily) (t : (b63gR_family R).S) :
    dim ((b63gR_family R).fiber t).X.left = 6 ∧
      g32h_h10 ((b63gR_family R).fiber t) = 3 ∧
      g32h_h01 ((b63gR_family R).fiber t) = 3 :=
  ⟨(g32h_fiber_polarized _ t).dim_eq, g32h_h10_eq_three _ t⟩

/-- A nonidentity tuple entry excludes the trivial monodromy case. -/
example (R : rf8_SharedFamily) (t : (b63gR_family R).S) (i : Fin 13) :
    (b63gR_family R).tuple t i ≠ 1 := by
  intro hi
  change b63g5_tuple i = 1 at hi
  have h1 : b4b_root i = 1 :=
    Subtype.val_injective (hi.trans (map_one b4b_toMatrix).symm)
  have h3 := b63_root_order i
  rw [h1, orderOf_one] at h3
  split_ifs at h3 <;> omega

/-- The universal-family equality used by S7 has a checked instance. -/
example : ∃ F : g32m_UniversalFamily, F.univ = b60b_univ :=
  ⟨{ univ := b60b_univ, member := b60b_member, cover := b60c_cover }, rfl⟩

end HodgeLean.Foundations.Program
