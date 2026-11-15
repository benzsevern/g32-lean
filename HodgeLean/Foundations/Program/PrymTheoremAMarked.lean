import HodgeLean.Foundations.Program.PrymTheoremAMarkedProofs

/-! # Theorem A with the retained fibre isogenies supplied
Implication from based root monodromy, curve, certified jet,
codifferential, Proposition 4.6, fibre polarizations and a route input to Theorem A.
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

/-- The constructed marking preserves the action.
Source: `hg7g_rational_marking`, `b63gW_marking`. -/
theorem b63gW_marking_hJ (D : rf8_SharedFamily)
    (u₀ : D.atlas.π ⁻¹' {b63gP_basePoint})
    (hroot : ∀ i, D.atlas.hπ.fundamentalGroupToMulOpposite u₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i)) :
    ∀ x, b63gW_marking D u₀ hroot ((D.A b63gP_s₀).baseChange ℚ x) =
      b60_omega.baseChange ℚ (b63gW_marking D u₀ hroot x) :=
  b63gW_marking_hJ_aux D u₀ hroot

example := @b63gW_marking_hJ

/-- The constructed marking preserves the pairing.
Source: `hg7g_rational_marking`, `b63gW_marking`. -/
theorem b63gW_marking_hpair (D : rf8_SharedFamily)
    (u₀ : D.atlas.π ⁻¹' {b63gP_basePoint})
    (hroot : ∀ i, D.atlas.hπ.fundamentalGroupToMulOpposite u₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i)) :
    ∀ x y, b60_E.baseChange ℚ (b63gW_marking D u₀ hroot x)
      (b63gW_marking D u₀ hroot y) =
      (b63e_singularQ mr_base D.C D.hC (b6t_polydisc mr_base) (Subset.refl _)
        b63gP_s₀ (D.P b63gP_s₀) (D.Q b63gP_s₀)).baseChange ℚ x y :=
  b63gW_marking_hpair_aux D u₀ hroot

example := @b63gW_marking_hpair

/-- Theorem A from based root monodromy and comparison at the constructed marking.
Source: `hg7g_rational_marking`, `b63gU_theoremA_of_transport`; G32 v0.16, Theorem A. -/
theorem b63gW_theoremA_of_transport (D : rf8_SharedFamily) (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (h46 : g32s_Prop46 (b63gR_family D))
    (u₀ : D.atlas.π ⁻¹' {b63gP_basePoint})
    (hroot : ∀ i, D.atlas.hπ.fundamentalGroupToMulOpposite u₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i))
    (curve : ℂ → Fin 10 → ℂ) (curve_cont : ContinuousAt curve 0)
    (curve_zero : curve 0 ∈ b6t_polydisc mr_base)
    (jet : ℂ → Matrix (Fin 9) (Fin 10) ℂ) (jet_certified : g32r_CertifiedJet jet)
    (codiff : ∀ᶠ θ in 𝓝 (0 : ℂ), ∃ L : Matrix (Fin 9) (Fin 9) ℂ,
      ∃ T : Matrix (Fin 10) (Fin 10) ℂ, IsUnit L ∧ IsUnit T ∧
        jet θ = L * LinearMap.toMatrix'
          (fderiv ℂ (b64i_period D b63gP_s₀ (b63gW_marking D u₀ hroot)) (curve θ) :
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
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  b63gW_theoremA_of_transport_aux D F hF h46 u₀ hroot curve curve_cont
    curve_zero jet jet_certified codiff hpol transport A W pol

example := @b63gW_theoremA_of_transport

/-- Theorem A from based root monodromy and comparison at the constructed marking.
Source: `hg7g_rational_marking`, `b63gU_theoremA_of_reverse`; G32 v0.16, Theorem A. -/
theorem b63gW_theoremA_of_reverse (D : rf8_SharedFamily) (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (h46 : g32s_Prop46 (b63gR_family D))
    (u₀ : D.atlas.π ⁻¹' {b63gP_basePoint})
    (hroot : ∀ i, D.atlas.hπ.fundamentalGroupToMulOpposite u₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i))
    (curve : ℂ → Fin 10 → ℂ) (curve_cont : ContinuousAt curve 0)
    (curve_zero : curve 0 ∈ b6t_polydisc mr_base)
    (jet : ℂ → Matrix (Fin 9) (Fin 10) ℂ) (jet_certified : g32r_CertifiedJet jet)
    (codiff : ∀ᶠ θ in 𝓝 (0 : ℂ), ∃ L : Matrix (Fin 9) (Fin 9) ℂ,
      ∃ T : Matrix (Fin 10) (Fin 10) ℂ, IsUnit L ∧ IsUnit T ∧
        jet θ = L * LinearMap.toMatrix'
          (fderiv ℂ (b64i_period D b63gP_s₀ (b63gW_marking D u₀ hroot)) (curve θ) :
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
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  b63gW_theoremA_of_reverse_aux D F hF h46 u₀ hroot curve curve_cont
    curve_zero jet jet_certified codiff hpol reverse A W pol

example := @b63gW_theoremA_of_reverse

/-- Theorem A from based root monodromy and comparison at the constructed marking.
Source: `hg7g_rational_marking`, `b63gU_theoremA_of_qinv`; G32 v0.16, Theorem A. -/
theorem b63gW_theoremA_of_qinv (D : rf8_SharedFamily) (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (h46 : g32s_Prop46 (b63gR_family D))
    (u₀ : D.atlas.π ⁻¹' {b63gP_basePoint})
    (hroot : ∀ i, D.atlas.hπ.fundamentalGroupToMulOpposite u₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i))
    (curve : ℂ → Fin 10 → ℂ) (curve_cont : ContinuousAt curve 0)
    (curve_zero : curve 0 ∈ b6t_polydisc mr_base)
    (jet : ℂ → Matrix (Fin 9) (Fin 10) ℂ) (jet_certified : g32r_CertifiedJet jet)
    (codiff : ∀ᶠ θ in 𝓝 (0 : ℂ), ∃ L : Matrix (Fin 9) (Fin 9) ℂ,
      ∃ T : Matrix (Fin 10) (Fin 10) ℂ, IsUnit L ∧ IsUnit T ∧
        jet θ = L * LinearMap.toMatrix'
          (fderiv ℂ (b64i_period D b63gP_s₀ (b63gW_marking D u₀ hroot)) (curve θ) :
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
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  b63gW_theoremA_of_qinv_aux D F hF h46 u₀ hroot curve curve_cont
    curve_zero jet jet_certified codiff hpol qinv A W pol

example := @b63gW_theoremA_of_qinv

end HodgeLean.Foundations.Program
