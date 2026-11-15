import HodgeLean.Foundations.Program.PathCoverFamilyDefs
import HodgeLean.Foundations.Program.PathCoverFamilyRanks
import HodgeLean.Foundations.Program.PathCoverFamilyPeriod
import HodgeLean.Foundations.Program.PathCoverFamilyComparisonPolarization

/-! # B6-5: the retained cover family along the G32 Schlesinger path (proofs)

One auxiliary per public statement of `PathCoverFamily.lean`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Manifold Filter Topology HodgeLean.Papers
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint HodgeLean.RealDefs
open HodgeLean.Foundations HodgeLean.Foundations.Symplectic HodgeLean.Adapters TopologicalSpace
open scoped ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

theorem b65z_local_period_aux (c : Fin 10 → ℂ) (g : Fin 13 → b4b_Group)
    (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i))) (D : b65z_SharedFamily c g)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) (b65z_s₀ c)) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ y, m ((D.A (b65z_s₀ c)).baseChange ℚ y) = b60_omega.baseChange ℚ (m y))
    (hpair : ∀ y z, b60_E.baseChange ℚ (m y) (m z) =
      (b63e_singularQ c D.C D.hC (b6t_polydisc c) (Subset.refl _) (b65z_s₀ c)
        (D.P (b65z_s₀ c)) (D.Q (b65z_s₀ c))).baseChange ℚ y z) :
    AnalyticOnNhd ℂ (b65z_period D (b65z_s₀ c) m) (b6t_polydisc c) ∧
    (∀ t ∈ b6t_polydisc c, b65z_period D (b65z_s₀ c) m t ∈ g32m_Domain ∧
      b60_F (b65z_period D (b65z_s₀ c) m t) =
        b64c_markedF _ m (b65z_transportedFamily D (b65z_s₀ c)) t) ∧
    ∀ (B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) (b65z_s₀ c))) (t : b6t_polydisc c)
      (hm : b65z_period D (b65z_s₀ c) m t.val ∈ g32m_Domain),
      g32t_KIsog (b65z_fiber D B t) (b60b_univ ⟨b65z_period D (b65z_s₀ c) m t.val, hm⟩) := by
  refine ⟨b65z_period_analytic hg D (b65z_s₀ c) m hJ hpair,
    b65z_period_chart hg D (b65z_s₀ c) m hJ hpair, ?_⟩
  intro B t hm
  letI := Module.Free.of_basis B
  letI := Module.Finite.of_basis B
  let W := b63e_weight_one_riemann c D.C D.hC (b6t_polydisc c) (Subset.refl _)
    D.hG D.atlas.hb D.atlas.f D.atlas.hf D.atlas.hsurj D.hk
    D.Q₀ D.hQ₀ D.Q D.hQ D.P D.hP (b65z_s₀ c) t
  let A := b63g2_operator c D.C D.hC (b6t_polydisc c) (Subset.refl _) (b65z_s₀ c)
  have hA : D.A (b65z_s₀ c) = A := by
    ext l
    exact (D.hA _ l).trans (b63g2_operator_val _ _ _ _ _ _ l).symm
  apply b65z_model_kIsog _ _ W.1 _ W.2 A
    (b63g2_operator_sq c D.C D.hC (b6t_polydisc c) (Subset.refl _)
      (b65z_s₀ c) (D.hG _))
    (b63g2_operator_filtration c D.C D.hC (b6t_polydisc c) (Subset.refl _)
      D.hG D.P D.hP (b65z_s₀ c) t) m
    (by simpa only [hA] using hJ)
    (b63g2_operator_skew c D.C D.hC (b6t_polydisc c) (Subset.refl _)
      (b65z_s₀ c) (D.hG _) (D.P _) (D.hP _) (D.Q _) (D.hQ _)) hpair
    ⟨b65z_period D (b65z_s₀ c) m t.val, hm⟩
  have hh := (b65z_period_chart hg D (b65z_s₀ c) m hJ hpair t.val t.property).2
  simpa only [b64c_markedF, b64c_transportedFamily, b65z_period,
    dite_eq_left t.property] using hh


theorem b65z_prym_family_aux (c : Fin 10 → ℂ) (g : Fin 13 → b4b_Group)
    (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i))) (D : b65z_SharedFamily c g) :
    Nonempty (Module.Basis (Fin 12) ℤ (b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) (b65z_s₀ c))) ∧
    ∀ B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) (b65z_s₀ c)), ∃ P : g32h_PrymFamily, b65z_IsLocalPrym D B P := by
  refine ⟨b65z_lattice_basis hg D (b65z_s₀ c), fun B ↦ ?_⟩
  let X : (b6t_polydisc c) → g32t_Sixfold := fun t ↦ b63g5_fiber c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.hG D.atlas.hb D.atlas.f D.atlas.hf D.atlas.hsurj D.hk D.Q₀ D.hQ₀ D.Q D.hQ D.P D.hP (b65z_s₀ c) B t
  have key : ∀ t : (b6t_polydisc c), (dim (X t).X.left : ℤ) = g32h_multCW (fun i ↦ b4b_toMatrix (g i)) ∧
      (((g32h_h10 (X t) : ℝ) = g32h_holoCW (fun i ↦ b4b_toMatrix (g i)) ∧
          (g32h_h01 (X t) : ℝ) = g32h_multCW (fun i ↦ b4b_toMatrix (g i)) - g32h_holoCW (fun i ↦ b4b_toMatrix (g i))) ∨
        ((g32h_h01 (X t) : ℝ) = g32h_holoCW (fun i ↦ b4b_toMatrix (g i)) ∧
          (g32h_h10 (X t) : ℝ) = g32h_multCW (fun i ↦ b4b_toMatrix (g i)) - g32h_holoCW (fun i ↦ b4b_toMatrix (g i)))) ∧
      IsNondegenerate (polarizationVec (torusCohomology_cupProductOf (X t).X) (X t).pol) ∧
      (letI := (torusCohomology_cupProductOf (X t).X).finite
       IsRosatiSkew (polarizationVec (torusCohomology_cupProductOf (X t).X) (X t).pol)
        (X t).W.J) := by
    intro t
    have hb : c ∈ b6_chart := D.atlas.hb
    let _ : Module.Free ℤ (b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) (b65z_s₀ c)) := Module.Free.of_basis B
    let _ : Module.Finite ℤ (b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) (b65z_s₀ c)) := Module.Finite.of_basis B
    have W := b63e_weight_one_riemann c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.hG hb D.atlas.f D.atlas.hf D.atlas.hsurj D.hk D.Q₀ D.hQ₀ D.Q D.hQ D.P D.hP (b65z_s₀ c) t
    have hsq := b63g2_operator_sq c D.C D.hC (b6t_polydisc c) (Subset.refl _) (b65z_s₀ c) (D.hG (b65z_s₀ c))
    have hφ := b63g2_operator_filtration c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.hG D.P D.hP (b65z_s₀ c) t
    have hX : X t = b63g2_sixfold _ _ W.1 _ W.2 _ hsq hφ := rfl
    have hE := b65z_eigen_rank hg D (b65z_s₀ c) t
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
          (b63e_singularQ c D.C D.hC (b6t_polydisc c) (Subset.refl _) (b65z_s₀ c) (D.P (b65z_s₀ c)) (D.Q (b65z_s₀ c)))).left :=
        b5_integral_aux _ _ W.1 _ W.2
      have h := b63g_model_finrank _ _ W.1 _ W.2
      rw [Module.finrank_eq_card_basis B, Fintype.card_fin] at h
      rw [hX]
      change (dim (b5_model _ _ W.1 (b63e_singularQ c D.C D.hC (b6t_polydisc c) (Subset.refl _) (b65z_s₀ c) (D.P (b65z_s₀ c)) (D.Q (b65z_s₀ c)))).left : ℤ)
        = 6
      omega
    have hN : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i)) := hg
    refine ⟨?_, Or.inl ?_, ?_, ?_⟩
    · rw [hdim, g32h_multCW_of_nielsen _ hN]
    · rw [h10, h01, g32h_holoCW_of_nielsen _ hN, g32h_multCW_of_nielsen _ hN]
      norm_num
    · have h :=
        letI := b5_groupObj _ _ W.1 _ W.2
        letI : IsIntegral (b5_model _ _ W.1
            (b63e_singularQ c D.C D.hC (b6t_polydisc c) (Subset.refl _) (b65z_s₀ c) (D.P (b65z_s₀ c)) (D.Q (b65z_s₀ c)))).left :=
          b5_integral_aux _ _ W.1 _ W.2
        letI := b5_smooth_aux _ _ W.1 _ W.2
        letI := b5_projective_aux _ _ W.1 _ W.2
        b2_abelian_nondegenerate _ _ (b63g_modelForm_riemann _ _ W.1 _ W.2)
      rw [hX]
      unfold b63g2_sixfold
      exact h
    · rw [hX]
      exact b63g2_sixfold_rosati _ _ W.1 _ W.2 _ hsq hφ
        (b63g2_operator_skew c D.C D.hC (b6t_polydisc c) (Subset.refl _) (b65z_s₀ c) (D.hG (b65z_s₀ c)) (D.P (b65z_s₀ c)) (D.hP (b65z_s₀ c)) (D.Q (b65z_s₀ c)) (D.hQ (b65z_s₀ c)))
  let P : g32h_PrymFamily := {
           S := (b6t_polydisc c)
           tuple := fun _ ↦ (fun i ↦ b4b_toMatrix (g i))
           tuple_nielsen := fun _ ↦ hg
           fiber := X
           dim_eq := fun t ↦ (key t).1
           hodge := fun t ↦ (key t).2.1
           nondegenerate := fun t ↦ (key t).2.2.1
           rosati := fun t ↦ (key t).2.2.2
           positive := fun t ↦ b63gP_fiber_positive_aux c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.hG D.atlas.hb D.atlas.f
             D.atlas.hf D.atlas.hsurj D.hk D.Q₀ D.hQ₀ D.Q D.hQ D.P D.hP (b65z_s₀ c) B t _ }
  refine ⟨P, Equiv.refl _, fun t ↦ ⟨rfl, rfl⟩⟩


theorem b65z_theoremA_of_transport_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily (b65z_centre p) g)
    (B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _) (b65z_s₀ (b65z_centre p))))
    (P : g32h_PrymFamily) (hP : b65z_IsLocalPrym D B P)
    (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ) (h46 : g32s_Prop46 P)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _) (b65z_s₀ (b65z_centre p))) ≃ₗ[ℚ]
      (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ y, m ((D.A (b65z_s₀ (b65z_centre p))).baseChange ℚ y) = b60_omega.baseChange ℚ (m y))
    (hpair : ∀ y z, b60_E.baseChange ℚ (m y) (m z) =
      (b63e_singularQ (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _)
        (b65z_s₀ (b65z_centre p)) (D.P (b65z_s₀ (b65z_centre p)))
        (D.Q (b65z_s₀ (b65z_centre p)))).baseChange ℚ y z)
    (jet : ℂ → Matrix (Fin 9) (Fin 10) ℂ) (jet_certified : g32r_CertifiedJet jet)
    (codiff : ∀ᶠ θ in 𝓝 (0 : ℂ), ∃ L : Matrix (Fin 9) (Fin 9) ℂ,
      ∃ T : Matrix (Fin 10) (Fin 10) ℂ, IsUnit L ∧ IsUnit T ∧
        jet θ = L * LinearMap.toMatrix'
          (fderiv ℂ (b65z_period D (b65z_s₀ (b65z_centre p)) m) (b65p_curve p θ) :
            (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) * T)
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized P s))
    (transport : ∀ P Q, g32t_KIsog P Q → (g32t_WeilAlg P ↔ g32t_WeilAlg Q))
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol := by
  obtain ⟨j, hj⟩ := hP
  have hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i)) := by
    rw [← (hj (b65z_s₀ _)).1]
    exact P.tuple_nielsen _
  obtain ⟨han, hch, hiso⟩ := b65z_local_period_aux _ g hg D m hJ hpair
  let R : g32r_PeriodMap F P := {
            V := b6t_polydisc (b65z_centre p),
            isOpen_V := b65z_polydisc_open _,
            period := b65z_period D (b65z_s₀ (b65z_centre p)) m,
            analytic := han,
            mapsTo := fun t ht ↦ (hch t ht).1,
            isog := fun t ht ↦ ⟨j ⟨t, ht⟩, by
              rw [(hj ⟨t, ht⟩).2, hF]
              exact hiso B ⟨t, ht⟩ _⟩,
            curve := b65p_curve p,
            curve_cont := O.curve_cont,
            curve_zero := b65z_centre_mem _,
            jet := jet,
            jet_certified := jet_certified,
            codiff := codiff }

  exact g32a_theoremA F P h46 R hpol
    (hk7_spread F hF P h46 R fun q hq h => by
      have hq' : g32t_KIsog (P.fiber q.2) (F.univ q.1) := by
        rw [hF]
        exact hq
      have hr := (transport _ _ hq').1 h
      rwa [hF] at hr) transport A W pol


theorem b65z_theoremA_of_reverse_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily (b65z_centre p) g)
    (B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _) (b65z_s₀ (b65z_centre p))))
    (P : g32h_PrymFamily) (hP : b65z_IsLocalPrym D B P)
    (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ) (h46 : g32s_Prop46 P)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _) (b65z_s₀ (b65z_centre p))) ≃ₗ[ℚ]
      (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ y, m ((D.A (b65z_s₀ (b65z_centre p))).baseChange ℚ y) = b60_omega.baseChange ℚ (m y))
    (hpair : ∀ y z, b60_E.baseChange ℚ (m y) (m z) =
      (b63e_singularQ (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _)
        (b65z_s₀ (b65z_centre p)) (D.P (b65z_s₀ (b65z_centre p)))
        (D.Q (b65z_s₀ (b65z_centre p)))).baseChange ℚ y z)
    (jet : ℂ → Matrix (Fin 9) (Fin 10) ℂ) (jet_certified : g32r_CertifiedJet jet)
    (codiff : ∀ᶠ θ in 𝓝 (0 : ℂ), ∃ L : Matrix (Fin 9) (Fin 9) ℂ,
      ∃ T : Matrix (Fin 10) (Fin 10) ℂ, IsUnit L ∧ IsUnit T ∧
        jet θ = L * LinearMap.toMatrix'
          (fderiv ℂ (b65z_period D (b65z_s₀ (b65z_centre p)) m) (b65p_curve p θ) :
            (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) * T)
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized P s))
    (reverse : ∀ P Q, g32t_IsMember P → g32t_IsMember Q → g32t_KIsog P Q → g32t_KIsog Q P)
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol := by
  obtain ⟨j, hj⟩ := hP
  have hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i)) := by
    rw [← (hj (b65z_s₀ _)).1]
    exact P.tuple_nielsen _
  obtain ⟨han, hch, hiso⟩ := b65z_local_period_aux _ g hg D m hJ hpair
  let R : g32r_PeriodMap F P := {
            V := b6t_polydisc (b65z_centre p),
            isOpen_V := b65z_polydisc_open _,
            period := b65z_period D (b65z_s₀ (b65z_centre p)) m,
            analytic := han,
            mapsTo := fun t ht ↦ (hch t ht).1,
            isog := fun t ht ↦ ⟨j ⟨t, ht⟩, by
              rw [(hj ⟨t, ht⟩).2, hF]
              exact hiso B ⟨t, ht⟩ _⟩,
            curve := b65p_curve p,
            curve_cont := O.curve_cont,
            curve_zero := b65z_centre_mem _,
            jet := jet,
            jet_certified := jet_certified,
            codiff := codiff }

  exact g32n_theoremA_of_premises
    { F, P, h46, R, hpol, reverse
      spread := hk7_spread_of_members F hF P h46 R hpol reverse } A W pol


theorem b65z_theoremA_of_qinv_aux (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily (b65z_centre p) g)
    (B : Module.Basis (Fin 12) ℤ (b63l_parameterLattice (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _) (b65z_s₀ (b65z_centre p))))
    (P : g32h_PrymFamily) (hP : b65z_IsLocalPrym D B P)
    (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ) (h46 : g32s_Prop46 P)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _) (b65z_s₀ (b65z_centre p))) ≃ₗ[ℚ]
      (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ y, m ((D.A (b65z_s₀ (b65z_centre p))).baseChange ℚ y) = b60_omega.baseChange ℚ (m y))
    (hpair : ∀ y z, b60_E.baseChange ℚ (m y) (m z) =
      (b63e_singularQ (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _)
        (b65z_s₀ (b65z_centre p)) (D.P (b65z_s₀ (b65z_centre p)))
        (D.Q (b65z_s₀ (b65z_centre p)))).baseChange ℚ y z)
    (jet : ℂ → Matrix (Fin 9) (Fin 10) ℂ) (jet_certified : g32r_CertifiedJet jet)
    (codiff : ∀ᶠ θ in 𝓝 (0 : ℂ), ∃ L : Matrix (Fin 9) (Fin 9) ℂ,
      ∃ T : Matrix (Fin 10) (Fin 10) ℂ, IsUnit L ∧ IsUnit T ∧
        jet θ = L * LinearMap.toMatrix'
          (fderiv ℂ (b65z_period D (b65z_s₀ (b65z_centre p)) m) (b65p_curve p θ) :
            (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) * T)
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized P s))
    (qinv : qinv_premise)
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol := by
  obtain ⟨j, hj⟩ := hP
  have hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i)) := by
    rw [← (hj (b65z_s₀ _)).1]
    exact P.tuple_nielsen _
  obtain ⟨han, hch, hiso⟩ := b65z_local_period_aux _ g hg D m hJ hpair
  let R : g32r_PeriodMap F P := {
            V := b6t_polydisc (b65z_centre p),
            isOpen_V := b65z_polydisc_open _,
            period := b65z_period D (b65z_s₀ (b65z_centre p)) m,
            analytic := han,
            mapsTo := fun t ht ↦ (hch t ht).1,
            isog := fun t ht ↦ ⟨j ⟨t, ht⟩, by
              rw [(hj ⟨t, ht⟩).2, hF]
              exact hiso B ⟨t, ht⟩ _⟩,
            curve := b65p_curve p,
            curve_cont := O.curve_cont,
            curve_zero := b65z_centre_mem _,
            jet := jet,
            jet_certified := jet_certified,
            codiff := codiff }

  exact qinv_g32_theoremA_of_premises
    { F, P, h46, R, hpol, qinv
      spread := hk7_spread_of_witness F hF P h46 R
        fun _ _ f hf hi => qinv _ _ f hf hi } A W pol


end HodgeLean.Foundations.Program
