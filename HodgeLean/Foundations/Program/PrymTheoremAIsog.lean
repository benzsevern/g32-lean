import HodgeLean.Foundations.Program.PrymTheoremAIsogProofs

/-! # Theorem A with the retained fibre isogenies supplied
Implication from the marking, curve, certified jet,
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

/-- Theorem A using the specified shared-family period construction.
Source: `b64e_hisog`, `b63gT_theoremA_of_transport`; G32 v0.16, Theorem A. -/
theorem b63gU_theoremA_of_transport (D : rf8_SharedFamily) (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (h46 : g32s_Prop46 (b63gR_family D)) 
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base D.C D.hC (b6t_polydisc mr_base)
      (Subset.refl _) b63gP_s₀) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((D.A b63gP_s₀).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpair : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base D.C D.hC (b6t_polydisc mr_base) (Subset.refl _)
        b63gP_s₀ (D.P b63gP_s₀) (D.Q b63gP_s₀)).baseChange ℚ x y)
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
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  b63gU_theoremA_of_transport_aux D F hF h46 m hJ hpair curve curve_cont
    curve_zero jet jet_certified codiff hpol transport A W pol

example := @b63gU_theoremA_of_transport

/-- Theorem A using the specified shared-family period construction.
Source: `b64e_hisog`, `b63gT_theoremA_of_reverse`; G32 v0.16, Theorem A. -/
theorem b63gU_theoremA_of_reverse (D : rf8_SharedFamily) (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (h46 : g32s_Prop46 (b63gR_family D)) 
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base D.C D.hC (b6t_polydisc mr_base)
      (Subset.refl _) b63gP_s₀) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((D.A b63gP_s₀).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpair : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base D.C D.hC (b6t_polydisc mr_base) (Subset.refl _)
        b63gP_s₀ (D.P b63gP_s₀) (D.Q b63gP_s₀)).baseChange ℚ x y)
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
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  b63gU_theoremA_of_reverse_aux D F hF h46 m hJ hpair curve curve_cont
    curve_zero jet jet_certified codiff hpol reverse A W pol

example := @b63gU_theoremA_of_reverse

/-- Theorem A using the specified shared-family period construction.
Source: `b64e_hisog`, `b63gT_theoremA_of_qinv`; G32 v0.16, Theorem A. -/
theorem b63gU_theoremA_of_qinv (D : rf8_SharedFamily) (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (h46 : g32s_Prop46 (b63gR_family D)) 
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base D.C D.hC (b6t_polydisc mr_base)
      (Subset.refl _) b63gP_s₀) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((D.A b63gP_s₀).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpair : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base D.C D.hC (b6t_polydisc mr_base) (Subset.refl _)
        b63gP_s₀ (D.P b63gP_s₀) (D.Q b63gP_s₀)).baseChange ℚ x y)
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
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  b63gU_theoremA_of_qinv_aux D F hF h46 m hJ hpair curve curve_cont
    curve_zero jet jet_certified codiff hpol qinv A W pol

example := @b63gU_theoremA_of_qinv

/-- The retained fibre supplies the index in the period-map isogeny field.
This check uses the existing period-domain statement and the rational marking identities. -/
example (R : rf8_SharedFamily)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) b63gP_s₀) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A b63gP_s₀).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        b63gP_s₀ (R.P b63gP_s₀) (R.Q b63gP_s₀)).baseChange ℚ x y)
    (Fm : g32m_UniversalFamily)
    (hFm : Fm.univ = b60b_univ)
 :
    ∀ t (ht : t ∈ b6t_polydisc mr_base),
      ∃ u : (b63gR_family R).S,
        g32t_KIsog ((b63gR_family R).fiber u)
          (Fm.univ ⟨b64i_period R b63gP_s₀ m t,
            (b64i_chart R b63gP_s₀ m hJ hpol t ht).1⟩) := by
  intro t ht
  exact ⟨⟨t, ht⟩, b64e_hisog R m hJ hpol Fm hFm ⟨t, ht⟩ _⟩


end HodgeLean.Foundations.Program
