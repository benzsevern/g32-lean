import HodgeLean.Foundations.Program.PrymFamilySharedProofs

/-! # Prym family from shared geometry
Implication from retained geometry to a named family with identical geometric fibres;
from based marking data to stage-P marking; and from the remaining G32 inputs to Theorem A.
The period-map statement retains H7, isogeny, curve, jet and codifferential inputs.
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

/-- Stage-P marking from based monodromy on the retained cover.
Source: `b63gP_IsMarked`, `rf8_filling_stabilizers`; G32 v0.16, Lemma 3.6. -/
theorem b63gR_marked (R : rf8_SharedFamily)
    (u₀ : R.atlas.π ⁻¹' {b63gP_basePoint})
    (hroot : ∀ i, R.atlas.hπ.fundamentalGroupToMulOpposite u₀ (b63gP_loops i) =
      MulOpposite.op (b4b_root i)) :
    b63gP_IsMarked (b63gR_family R) ∧ Nonempty (b63gR_family R).S :=
  b63gR_marked_aux R u₀ hroot

example := @b63gR_marked

/-- The identity indexing compares the exact retained fibres.
Source: `b63gR_family`; stage-P constructor. -/
theorem b63gR_compare (R : rf8_SharedFamily) :
    ∀ t : b6t_polydisc mr_base,
      (b63gR_family R).tuple ((Equiv.refl _) t) = b63g5_tuple ∧
      (b63gR_family R).fiber ((Equiv.refl _) t) = b63g5_fiber mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
      R.hG mr_base_mem_chart R.atlas.f R.atlas.hf R.atlas.hsurj R.hk
      R.Q₀ R.hQ₀ R.Q R.hQ R.P R.hP b63gP_s₀ (b63gR_basis R) t :=
  b63gR_compare_aux R

example := @b63gR_compare

/-- Theorem A on the retained family using S7 spreading.
Source: G32 v0.16, Theorem A, Lemmas 2.2 and 7.1; `hk7_spread`. -/
theorem b63gR_theoremA_of_transport (D : rf8_SharedFamily) (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
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
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  b63gR_theoremA_of_transport_aux D F hF h46 R hpol transport A W pol

example := @b63gR_theoremA_of_transport

/-- Theorem A on the retained family using S7 spreading.
Source: G32 v0.16, Theorem A, Lemmas 2.2 and 7.1; `hk7_spread_of_members`. -/
theorem b63gR_theoremA_of_reverse (D : rf8_SharedFamily) (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
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
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  b63gR_theoremA_of_reverse_aux D F hF h46 R hpol reverse A W pol

example := @b63gR_theoremA_of_reverse

/-- Theorem A on the retained family using S7 spreading.
Source: G32 v0.16, Theorem A, Lemmas 2.2 and 7.1; `hk7_spread_of_witness`. -/
theorem b63gR_theoremA_of_qinv (D : rf8_SharedFamily) (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
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
    (pol : HQ A 2) : G32TheoremAStatement A W pol :=
  b63gR_theoremA_of_qinv_aux D F hF h46 R hpol qinv A W pol

example := @b63gR_theoremA_of_qinv

/-- Period map on the retained family with identity fibre comparison.
Source: `b64i_analytic`, `b64i_chart`; `g32r_PeriodMap` fields. -/
theorem b63gR_periodMap (R : rf8_SharedFamily)
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
      F.V = b6t_polydisc mr_base ∧ F.period = b64i_period R b63gP_s₀ m :=
  b63gR_periodMap_aux R m hJ hpol Fm hisog curve curve_cont curve_zero jet jet_certified codiff

example := @b63gR_periodMap

/-- `g32a_premises` with `P := (b63gR_family D)` and `spread := hk7_spread`. -/
example (D : rf8_SharedFamily) (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (h46 : g32s_Prop46 (b63gR_family D)) (R : g32r_PeriodMap F (b63gR_family D))
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized (b63gR_family D) s))
    (transport : ∀ P Q, g32t_KIsog P Q → (g32t_WeilAlg P ↔ g32t_WeilAlg Q)) :
    ∃ B : g32a_premises, B.F = F ∧ B.P = (b63gR_family D) :=
  ⟨{ F, P := (b63gR_family D), h46, R, hpol, transport
     spread := hk7_spread F hF (b63gR_family D) h46 R fun p hp h => by
       have hp' : g32t_KIsog ((b63gR_family D).fiber p.2) (F.univ p.1) := by rw [hF]; exact hp
       have := (transport _ _ hp').1 h
       rwa [hF] at this }, rfl, rfl⟩

/-- `g32n_premises` with `P := (b63gR_family D)` and `spread := hk7_spread_of_members`. -/
example (D : rf8_SharedFamily) (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (h46 : g32s_Prop46 (b63gR_family D)) (R : g32r_PeriodMap F (b63gR_family D))
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized (b63gR_family D) s))
    (reverse : ∀ P Q, g32t_IsMember P → g32t_IsMember Q → g32t_KIsog P Q → g32t_KIsog Q P) :
    ∃ B : g32n_premises, B.F = F ∧ B.P = (b63gR_family D) :=
  ⟨{ F, P := (b63gR_family D), h46, R, hpol, reverse
     spread := hk7_spread_of_members F hF (b63gR_family D) h46 R hpol reverse }, rfl, rfl⟩

/-- `qinv_premises` with `P := (b63gR_family D)` and `spread := hk7_spread_of_witness`. -/
example (D : rf8_SharedFamily) (F : g32m_UniversalFamily) (hF : F.univ = b60b_univ)
    (h46 : g32s_Prop46 (b63gR_family D)) (R : g32r_PeriodMap F (b63gR_family D))
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized (b63gR_family D) s))
    (qinv : qinv_premise) :
    ∃ B : qinv_premises, B.F = F ∧ B.P = (b63gR_family D) :=
  ⟨{ F, P := (b63gR_family D), h46, R, hpol, qinv
     spread := hk7_spread_of_witness F hF (b63gR_family D) h46 R
       fun _ _ f hf hi => qinv _ _ f hf hi }, rfl, rfl⟩

/-- The retained fibre supplies the index in the period-map isogeny field.
This check uses the existing period-domain statement and the geometric isogeny input. -/
example (R : rf8_SharedFamily)
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
 :
    ∀ t (ht : t ∈ b6t_polydisc mr_base),
      ∃ u : (b63gR_family R).S,
        g32t_KIsog ((b63gR_family R).fiber u)
          (Fm.univ ⟨b64i_period R b63gP_s₀ m t,
            (b64i_chart R b63gP_s₀ m hJ hpol t ht).1⟩) := by
  intro t ht
  exact ⟨⟨t, ht⟩, hisog ⟨t, ht⟩ _⟩

end HodgeLean.Foundations.Program
