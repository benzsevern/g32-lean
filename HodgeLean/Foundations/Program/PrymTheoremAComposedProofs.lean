import HodgeLean.Foundations.Program.PrymTheoremAComposedDefs

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

theorem b63gT_theoremA_of_transport_aux (D : rf8_SharedFamily) (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (h46 : g32s_Prop46 (b63gR_family D)) 
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base D.C D.hC (b6t_polydisc mr_base)
      (Subset.refl _) b63gP_s₀) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((D.A b63gP_s₀).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpair : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base D.C D.hC (b6t_polydisc mr_base) (Subset.refl _)
        b63gP_s₀ (D.P b63gP_s₀) (D.Q b63gP_s₀)).baseChange ℚ x y)
    (hisog : ∀ (t : b6t_polydisc mr_base)
      (hm : b64i_period D b63gP_s₀ m t.val ∈ g32m_Domain),
      g32t_KIsog (b63g5_fiber mr_base D.C D.hC (b6t_polydisc mr_base) (Subset.refl _)
        D.hG mr_base_mem_chart D.atlas.f D.atlas.hf D.atlas.hsurj D.hk
        D.Q₀ D.hQ₀ D.Q D.hQ D.P D.hP b63gP_s₀ (b63gR_basis D) t) (F.univ ⟨b64i_period D b63gP_s₀ m t.val, hm⟩))
    (curve : ℂ → Fin 10 → ℂ) (curve_cont : ContinuousAt curve 0)
    (curve_zero : curve 0 ∈ b6t_polydisc mr_base)
    (jet : ℂ → Matrix (Fin 9) (Fin 10) ℂ) (jet_certified : g32r_CertifiedJet jet)
    (codiff : ∀ᶠ θ in 𝓝 (0 : ℂ), ∃ L : Matrix (Fin 9) (Fin 9) ℂ,
      ∃ T : Matrix (Fin 10) (Fin 10) ℂ, IsUnit L ∧ IsUnit T ∧
        jet θ = L * LinearMap.toMatrix'
          (fderiv ℂ (b64i_period D b63gP_s₀ m) (curve θ) :
            (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) * T)
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
  obtain ⟨R, _, _⟩ := b63gR_periodMap D m hJ hpair F hisog curve curve_cont
    curve_zero jet jet_certified codiff
  exact b63gR_theoremA_of_transport D F hF h46 R hpol transport A W pol

theorem b63gT_theoremA_of_reverse_aux (D : rf8_SharedFamily) (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (h46 : g32s_Prop46 (b63gR_family D)) 
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base D.C D.hC (b6t_polydisc mr_base)
      (Subset.refl _) b63gP_s₀) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((D.A b63gP_s₀).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpair : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base D.C D.hC (b6t_polydisc mr_base) (Subset.refl _)
        b63gP_s₀ (D.P b63gP_s₀) (D.Q b63gP_s₀)).baseChange ℚ x y)
    (hisog : ∀ (t : b6t_polydisc mr_base)
      (hm : b64i_period D b63gP_s₀ m t.val ∈ g32m_Domain),
      g32t_KIsog (b63g5_fiber mr_base D.C D.hC (b6t_polydisc mr_base) (Subset.refl _)
        D.hG mr_base_mem_chart D.atlas.f D.atlas.hf D.atlas.hsurj D.hk
        D.Q₀ D.hQ₀ D.Q D.hQ D.P D.hP b63gP_s₀ (b63gR_basis D) t) (F.univ ⟨b64i_period D b63gP_s₀ m t.val, hm⟩))
    (curve : ℂ → Fin 10 → ℂ) (curve_cont : ContinuousAt curve 0)
    (curve_zero : curve 0 ∈ b6t_polydisc mr_base)
    (jet : ℂ → Matrix (Fin 9) (Fin 10) ℂ) (jet_certified : g32r_CertifiedJet jet)
    (codiff : ∀ᶠ θ in 𝓝 (0 : ℂ), ∃ L : Matrix (Fin 9) (Fin 9) ℂ,
      ∃ T : Matrix (Fin 10) (Fin 10) ℂ, IsUnit L ∧ IsUnit T ∧
        jet θ = L * LinearMap.toMatrix'
          (fderiv ℂ (b64i_period D b63gP_s₀ m) (curve θ) :
            (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) * T)
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
  obtain ⟨R, _, _⟩ := b63gR_periodMap D m hJ hpair F hisog curve curve_cont
    curve_zero jet jet_certified codiff
  exact b63gR_theoremA_of_reverse D F hF h46 R hpol reverse A W pol

theorem b63gT_theoremA_of_qinv_aux (D : rf8_SharedFamily) (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (h46 : g32s_Prop46 (b63gR_family D)) 
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base D.C D.hC (b6t_polydisc mr_base)
      (Subset.refl _) b63gP_s₀) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((D.A b63gP_s₀).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpair : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base D.C D.hC (b6t_polydisc mr_base) (Subset.refl _)
        b63gP_s₀ (D.P b63gP_s₀) (D.Q b63gP_s₀)).baseChange ℚ x y)
    (hisog : ∀ (t : b6t_polydisc mr_base)
      (hm : b64i_period D b63gP_s₀ m t.val ∈ g32m_Domain),
      g32t_KIsog (b63g5_fiber mr_base D.C D.hC (b6t_polydisc mr_base) (Subset.refl _)
        D.hG mr_base_mem_chart D.atlas.f D.atlas.hf D.atlas.hsurj D.hk
        D.Q₀ D.hQ₀ D.Q D.hQ D.P D.hP b63gP_s₀ (b63gR_basis D) t) (F.univ ⟨b64i_period D b63gP_s₀ m t.val, hm⟩))
    (curve : ℂ → Fin 10 → ℂ) (curve_cont : ContinuousAt curve 0)
    (curve_zero : curve 0 ∈ b6t_polydisc mr_base)
    (jet : ℂ → Matrix (Fin 9) (Fin 10) ℂ) (jet_certified : g32r_CertifiedJet jet)
    (codiff : ∀ᶠ θ in 𝓝 (0 : ℂ), ∃ L : Matrix (Fin 9) (Fin 9) ℂ,
      ∃ T : Matrix (Fin 10) (Fin 10) ℂ, IsUnit L ∧ IsUnit T ∧
        jet θ = L * LinearMap.toMatrix'
          (fderiv ℂ (b64i_period D b63gP_s₀ m) (curve θ) :
            (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) * T)
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
  obtain ⟨R, _, _⟩ := b63gR_periodMap D m hJ hpair F hisog curve curve_cont
    curve_zero jet jet_certified codiff
  exact b63gR_theoremA_of_qinv D F hF h46 R hpol qinv A W pol

end HodgeLean.Foundations.Program
