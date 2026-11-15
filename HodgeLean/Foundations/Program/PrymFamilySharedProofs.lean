import HodgeLean.Foundations.Program.PrymFamilySharedDefs

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

theorem b63gR_marked_aux (R : rf8_SharedFamily)
    (u₀ : R.atlas.π ⁻¹' {b63gP_basePoint})
    (hroot : ∀ i, R.atlas.hπ.fundamentalGroupToMulOpposite u₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i)) :
    b63gP_IsMarked (b63gR_family R) ∧ Nonempty (b63gR_family R).S := by
  have hs := rf8_filling_stabilizers mr_base R.atlas.U R.C R.atlas.π R.atlas.hπ
    u₀.val R.atlas.f R.atlas.ι R.atlas.hι.injective R.atlas.hrange R.atlas.hequiv
  letI : FaithfulSMul b4b_Group R.C := hs.1
  have hγ : ∀ i, mr_IsLoop mr_base b63gP_basePoint i (b63gP_loops i) := fun i ↦
    (mr_loop_existsUnique mr_base b63gP_s₀.property b63gP_basePoint rfl i).exists.choose_spec
  have hrot := rf8_cover_roots mr_base b63gP_s₀.property b63gP_basePoint b63gP_loops hγ
    R.atlas.U R.atlas.π R.atlas.hπ u₀ hroot R.C R.atlas.f R.atlas.ι
    R.atlas.hact R.atlas.hf R.atlas.hgal R.atlas.hι.continuous
    R.atlas.hproj R.atlas.hequiv hs.2
  refine ⟨?_, ⟨b63gP_s₀⟩⟩
  exact ⟨R.atlas.U, inferInstance, inferInstance, inferInstance, R.atlas.π, R.atlas.hπ,
    u₀, hroot, R.C, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, R.atlas.f, R.atlas.ι,
    R.atlas.hf, R.atlas.hsurj, R.atlas.hact, R.atlas.hgal, R.atlas.hι,
    R.atlas.hrange, R.atlas.hproj, R.atlas.hequiv, hs.2, hrot,
    R.fibreChart, R.fibreMan, R.hG, R.hk, R.Q₀, R.hQ₀, R.Q, R.hQ, R.P, R.hP,
    b63gR_basis R, Equiv.refl _, fun _ ↦ ⟨rfl, rfl⟩⟩

theorem b63gR_compare_aux (R : rf8_SharedFamily) :
    ∀ t : b6t_polydisc mr_base,
      (b63gR_family R).tuple ((Equiv.refl _) t) = b63g5_tuple ∧
      (b63gR_family R).fiber ((Equiv.refl _) t) = b63g5_fiber mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
      R.hG mr_base_mem_chart R.atlas.f R.atlas.hf R.atlas.hsurj R.hk
      R.Q₀ R.hQ₀ R.Q R.hQ R.P R.hP b63gP_s₀ (b63gR_basis R) t := by
  intro t
  exact ⟨rfl, rfl⟩

theorem b63gR_theoremA_of_transport_aux (D : rf8_SharedFamily) (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (h46 : g32s_Prop46 (b63gR_family D)) (R : g32r_PeriodMap F (b63gR_family D))
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized (b63gR_family D) s))
    (transport : ∀ P Q, g32t_KIsog P Q → (g32t_WeilAlg P ↔ g32t_WeilAlg Q))
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol := by
  exact g32a_theoremA F (b63gR_family D) h46 R hpol
    (hk7_spread F hF (b63gR_family D) h46 R fun p hp h => by
      have hp' : g32t_KIsog ((b63gR_family D).fiber p.2) (F.univ p.1) := by
        rw [hF]
        exact hp
      have hq := (transport _ _ hp').1 h
      rwa [hF] at hq) transport A W pol

theorem b63gR_theoremA_of_reverse_aux (D : rf8_SharedFamily) (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (h46 : g32s_Prop46 (b63gR_family D)) (R : g32r_PeriodMap F (b63gR_family D))
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized (b63gR_family D) s))
    (reverse : ∀ P Q, g32t_IsMember P → g32t_IsMember Q → g32t_KIsog P Q → g32t_KIsog Q P)
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol := by
  exact g32n_theoremA_of_premises
    { F, P := b63gR_family D, h46, R, hpol, reverse
      spread := hk7_spread_of_members F hF (b63gR_family D) h46 R hpol reverse } A W pol

theorem b63gR_theoremA_of_qinv_aux (D : rf8_SharedFamily) (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (h46 : g32s_Prop46 (b63gR_family D)) (R : g32r_PeriodMap F (b63gR_family D))
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized (b63gR_family D) s))
    (qinv : qinv_premise)
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol := by
  exact qinv_g32_theoremA_of_premises
    { F, P := b63gR_family D, h46, R, hpol, qinv
      spread := hk7_spread_of_witness F hF (b63gR_family D) h46 R
        fun _ _ f hf hi => qinv _ _ f hf hi } A W pol

theorem b63gR_periodMap_aux (R : rf8_SharedFamily)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) b63gP_s₀) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A b63gP_s₀).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        b63gP_s₀ (R.P b63gP_s₀) (R.Q b63gP_s₀)).baseChange ℚ x y)
    (Fm : g32m_UniversalFamily)
    (hisog : ∀ (t : b6t_polydisc mr_base)
      (hm : b64i_period R b63gP_s₀ m t.val ∈ g32m_Domain),
      g32t_KIsog (b63g5_fiber mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        R.hG mr_base_mem_chart R.atlas.f R.atlas.hf R.atlas.hsurj R.hk
        R.Q₀ R.hQ₀ R.Q R.hQ R.P R.hP b63gP_s₀ (b63gR_basis R) t) (Fm.univ ⟨b64i_period R b63gP_s₀ m t.val, hm⟩))
    (curve : ℂ → Fin 10 → ℂ) (curve_cont : ContinuousAt curve 0)
    (curve_zero : curve 0 ∈ b6t_polydisc mr_base)
    (jet : ℂ → Matrix (Fin 9) (Fin 10) ℂ) (jet_certified : g32r_CertifiedJet jet)
    (codiff : ∀ᶠ θ in 𝓝 (0 : ℂ), ∃ L : Matrix (Fin 9) (Fin 9) ℂ,
      ∃ T : Matrix (Fin 10) (Fin 10) ℂ, IsUnit L ∧ IsUnit T ∧
        jet θ = L * LinearMap.toMatrix'
          (fderiv ℂ (b64i_period R b63gP_s₀ m) (curve θ) :
            (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) * T) :
    ∃ F : g32r_PeriodMap Fm (b63gR_family R),
      F.V = b6t_polydisc mr_base ∧ F.period = b64i_period R b63gP_s₀ m := by
  refine ⟨{
    V := b6t_polydisc mr_base
    isOpen_V := (b6t_polydisc_neighbourhood mr_base mr_base_mem_chart).2.2.1
    period := b64i_period R b63gP_s₀ m
    analytic := b64i_analytic R b63gP_s₀ m hJ hpol
    mapsTo := fun _ ht ↦ (b64i_chart R b63gP_s₀ m hJ hpol _ ht).1
    isog := fun t ht ↦ ⟨⟨t, ht⟩, hisog ⟨t, ht⟩ _⟩
    curve := curve
    curve_cont := curve_cont
    curve_zero := curve_zero
    jet := jet
    jet_certified := jet_certified
    codiff := codiff }, rfl, rfl⟩

end HodgeLean.Foundations.Program
