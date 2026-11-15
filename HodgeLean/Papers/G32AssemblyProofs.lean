import HodgeLean.Papers.G32AssemblyDefs

/-! # G32 Theorem A, assembly: proofs of the frozen statements -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open scoped CategoryTheory.MonObj
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Adapters

namespace HodgeLean.Papers

theorem g32a_fiber_disc_aux (P : g32h_PrymFamily)
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized P s)) :
    ∀ s (h : g32t_PolarizedWeil (P.fiber s)), g32t_disc h = classNegTwo := by
  intro s h
  simpa only [Subsingleton.elim h (g32h_fiber_polarized P s)] using
    g32d_fiber_disc P.fiber (g32h_fiber_polarized P) hpol s

theorem g32a_remainingFields_aux (F : g32m_UniversalFamily) (P : g32h_PrymFamily)
    (h46 : g32s_Prop46 P) (R : g32r_PeriodMap F P)
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized P s))
    (spread : ∃ C : Set (Set g32m_Domain), C.Countable ∧
      (∀ Z ∈ C, IsClosedAnalytic (Fin 9 → ℂ) Z) ∧ {m | g32t_WeilAlg (F.univ m)} = ⋃₀ C)
    (transport : ∀ P Q, g32t_KIsog P Q → (g32t_WeilAlg P ↔ g32t_WeilAlg Q)) :
    g32h_RemainingFields F P := by
  exact ⟨g32a_fiber_disc_aux P hpol, g32s_fiber_alg P h46,
    g32r_dominant F P R, spread, transport⟩

theorem g32a_theoremA_aux (F : g32m_UniversalFamily) (P : g32h_PrymFamily)
    (h46 : g32s_Prop46 P) (R : g32r_PeriodMap F P)
    (hpol : ∀ s, g32d_ParabolicPolarization (g32h_fiber_polarized P s))
    (spread : ∃ C : Set (Set g32m_Domain), C.Countable ∧
      (∀ Z ∈ C, IsClosedAnalytic (Fin 9 → ℂ) Z) ∧ {m | g32t_WeilAlg (F.univ m)} = ⋃₀ C)
    (transport : ∀ P Q, g32t_KIsog P Q → (g32t_WeilAlg P ↔ g32t_WeilAlg Q))
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol := by
  exact g32m_theoremA_of_stages F
    (g32h_stageFields_partial F P
      (g32a_remainingFields_aux F P h46 R hpol spread transport)) A W pol

theorem g32a_theoremA_of_premises_aux (B : g32a_premises) (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol := by
  exact g32a_theoremA_aux B.F B.P B.h46 B.R B.hpol B.spread B.transport A W pol

theorem g32a_exists_member_fiber_aux (B : g32a_premises) :
    ∃ s, g32t_IsMember (B.P.fiber s) := by
  obtain ⟨s, _⟩ := B.R.isog (B.R.curve 0) B.R.curve_zero
  exact ⟨s, (g32t_isMember_iff _).2
    ⟨g32h_fiber_polarized B.P s, g32d_fiber_disc B.P.fiber
      (g32h_fiber_polarized B.P) B.hpol s⟩⟩

end HodgeLean.Papers
