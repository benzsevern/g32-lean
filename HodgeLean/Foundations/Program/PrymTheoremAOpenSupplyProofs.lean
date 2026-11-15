import HodgeLean.Foundations.Program.PrymTheoremAOpenSupplyDefs

/-! # Theorem A from an open retained supply
Implication from algebraic fibres above a nonempty open locus to Theorem A.
The geometric supply remains open. HC no distance; AV milestone no distance.
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

theorem b63gV_theoremA_of_open_transport_aux (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (U : Set g32m_Domain) (hU : IsOpen U) (hne : U.Nonempty)
    (hAlg : ∀ m ∈ U, g32t_WeilAlg (F.univ m))
    (transport : ∀ P Q, g32t_KIsog P Q → (g32t_WeilAlg P ↔ g32t_WeilAlg Q))
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol := by
  intro hM
  let P : g32t_Sixfold := ⟨A, W, pol⟩
  obtain ⟨τ, hτ⟩ := F.cover P hM
  have hAll : g32t_WeilAlg (F.univ τ) := by
    rw [hF] at hAlg ⊢
    exact hk_weilAlg_of_open hU hne hAlg τ
  exact ((transport P (F.univ τ) hτ).2 hAll) hM.isWeilType

theorem b63gV_theoremA_of_open_reverse_aux (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (U : Set g32m_Domain) (hU : IsOpen U) (hne : U.Nonempty)
    (hAlg : ∀ m ∈ U, g32t_WeilAlg (F.univ m))
    (reverse : ∀ P Q, g32t_IsMember P → g32t_IsMember Q → g32t_KIsog P Q → g32t_KIsog Q P)
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol := by
  intro hM
  let P : g32t_Sixfold := ⟨A, W, pol⟩
  obtain ⟨τ, hτ⟩ := F.cover P hM
  have hAll : g32t_WeilAlg (F.univ τ) := by
    rw [hF] at hAlg ⊢
    exact hk_weilAlg_of_open hU hne hAlg τ
  exact (g32tr_weilAlg_pullback P (F.univ τ)
    ((g32t_isMember_iff P).1 hM).1
    ((g32t_isMember_iff _).1 (F.member τ)).1 hτ hAll) hM.isWeilType

theorem b63gV_theoremA_of_open_qinv_aux (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (U : Set g32m_Domain) (hU : IsOpen U) (hne : U.Nonempty)
    (hAlg : ∀ m ∈ U, g32t_WeilAlg (F.univ m))
    (qinv : qinv_premise)
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol := by
  intro hM
  let P : g32t_Sixfold := ⟨A, W, pol⟩
  obtain ⟨τ, hτ⟩ := F.cover P hM
  have hAll : g32t_WeilAlg (F.univ τ) := by
    rw [hF] at hAlg ⊢
    exact hk_weilAlg_of_open hU hne hAlg τ
  exact (g32tr_weilAlg_pullback P (F.univ τ)
    ((g32t_isMember_iff P).1 hM).1
    ((g32t_isMember_iff _).1 (F.member τ)).1 hτ hAll) hM.isWeilType

theorem b63gV_openSupply_of_prop46_aux (D : rf8_SharedFamily)
    (F : g32m_UniversalFamily) (h46 : g32s_Prop46 (b63gR_family D))
    (R : g32r_PeriodMap F (b63gR_family D)) : Nonempty (b63gV_OpenSupply D F) := by
  classical
  obtain ⟨U, hU, hne, hdom⟩ := g32r_dominant F (b63gR_family D) R
  refine ⟨{ U := U, isOpen := hU, nonempty := hne
            fibre := fun m => Classical.choose (hdom m.val m.property)
            isog := fun m => Classical.choose_spec (hdom m.val m.property)
            algebraic := fun m => g32s_fiber_alg (b63gR_family D) h46 _ }⟩

theorem b63gV_theoremA_of_transport_aux (D : rf8_SharedFamily) (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (supply : b63gV_OpenSupply D F) 
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
    (pol : HQ A 2) : G32TheoremAStatement A W pol := by
  apply b63gV_theoremA_of_open_transport_aux F hF supply.U supply.isOpen supply.nonempty
    (fun x hx => (transport _ _ (supply.isog ⟨x, hx⟩)).1
      (supply.algebraic ⟨x, hx⟩)) transport A W pol

theorem b63gV_theoremA_of_reverse_aux (D : rf8_SharedFamily) (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (supply : b63gV_OpenSupply D F) 
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
    (pol : HQ A 2) : G32TheoremAStatement A W pol := by
  apply b63gV_theoremA_of_open_reverse_aux F hF supply.U supply.isOpen supply.nonempty
    ?_ reverse A W pol
  intro x hx
  let t : supply.U := ⟨x, hx⟩
  have hmem : g32t_IsMember ((b63gR_family D).fiber (supply.fibre t)) :=
    (g32t_isMember_iff _).2 ⟨g32h_fiber_polarized _ _,
      g32a_fiber_disc (b63gR_family D) hpol _ _⟩
  exact g32tr_weilAlg_pullback _ _
    ((g32t_isMember_iff _).1 (F.member x)).1 (g32h_fiber_polarized _ _)
    (reverse _ _ hmem (F.member x) (supply.isog t)) (supply.algebraic t)

set_option maxRecDepth 2000 in
theorem b63gV_theoremA_of_qinv_aux (D : rf8_SharedFamily) (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (supply : b63gV_OpenSupply D F) 
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
    (pol : HQ A 2) : G32TheoremAStatement A W pol := by
  apply b63gV_theoremA_of_open_qinv_aux F hF supply.U supply.isOpen supply.nonempty
    ?_ qinv A W pol
  intro x hx
  let t : supply.U := ⟨x, hx⟩
  obtain ⟨f, hf, hi, hK, c, hc, hp⟩ := supply.isog t
  obtain ⟨w⟩ := qinv _ _ f hf hi
  exact g32tr_weilAlg_pullback _ _
    ((g32t_isMember_iff _).1 (F.member x)).1 (g32h_fiber_polarized _ _)
    (qinv_KIsog_reverse_of_witness _ _ f hf hi hK c hc hp w)
    (supply.algebraic t)


end HodgeLean.Foundations.Program
