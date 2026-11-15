import HodgeLean.Papers.G32NarrowDefs
import HodgeLean.Papers.G32Transport

/-! # G32 Theorem A with reverse isogenies: proofs of the frozen statements -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open scoped CategoryTheory.MonObj Manifold ContDiff
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Adapters

namespace HodgeLean.Papers

theorem g32n_transport_of_reverse_aux (P Q : g32t_Sixfold)
    (hP : g32t_PolarizedWeil P) (hQ : g32t_PolarizedWeil Q)
    (reverse : g32t_KIsog P Q → g32t_KIsog Q P) :
    g32t_KIsog P Q → (g32t_WeilAlg P ↔ g32t_WeilAlg Q) := by
  intro h
  exact ⟨g32tr_weilAlg_pullback Q P hQ hP (reverse h),
    g32tr_weilAlg_pullback P Q hP hQ h⟩

theorem g32n_theoremA_of_transfer_aux (D : g32n_TransferDatum) (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol := by
  have transport (P Q : g32t_Sixfold) (hP : g32t_IsMember P)
      (hQ : g32t_IsMember Q) (h : g32t_KIsog P Q) :
      g32t_WeilAlg P ↔ g32t_WeilAlg Q := by
    obtain ⟨hP', _⟩ := (g32t_isMember_iff P).1 hP
    obtain ⟨hQ', _⟩ := (g32t_isMember_iff Q).1 hQ
    exact g32n_transport_of_reverse_aux P Q hP' hQ' (D.reverse P Q hP hQ) h
  have open_locus : ∃ U : Set D.M, IsOpen U ∧ U.Nonempty ∧
      U ⊆ {m | g32t_WeilAlg (D.univ m)} := by
    obtain ⟨U, hUo, hUne, hU⟩ := D.dominant
    refine ⟨U, hUo, hUne, fun m hm ↦ ?_⟩
    obtain ⟨s, hs⟩ := hU m hm
    have hF : g32t_IsMember (D.fiber s) :=
      (g32t_isMember_iff _).2 ⟨D.fiber_polarized s, D.fiber_disc s⟩
    exact (transport _ _ hF (D.univ_member m) hs).1 (D.fiber_alg s)
  have locus (m : D.M) : g32t_WeilAlg (D.univ m) := by
    obtain ⟨U, hUo, hUne, hU⟩ := open_locus
    obtain ⟨C, hCc, hCZ, hC⟩ := D.spread
    have hall : ⋃₀ C = univ :=
      g32t_eq_univ_of_open_subset_aux hCc hCZ hUo hUne (hC ▸ hU)
    have hm : m ∈ ⋃₀ C := hall.symm ▸ mem_univ m
    change m ∈ {m | g32t_WeilAlg (D.univ m)}
    rw [hC]
    exact hm
  intro hM
  let P : g32t_Sixfold := ⟨A, W, pol⟩
  obtain ⟨m, hm⟩ := D.cover P hM
  exact (transport P (D.univ m) hM (D.univ_member m) hm).2 (locus m) hM.isWeilType

theorem g32n_theoremA_of_premises_aux (B : g32n_premises) (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol := by
  letI : ConnectedSpace g32m_Domain := g32m_domain_connectedSpace
  let D : g32n_TransferDatum :=
    { S := B.P.S
      fiber := B.P.fiber
      fiber_polarized := g32h_fiber_polarized B.P
      fiber_disc := fun s ↦ g32a_fiber_disc_aux B.P B.hpol s _
      fiber_alg := g32s_fiber_alg B.P B.h46
      M := g32m_Domain
      univ := B.F.univ
      univ_member := B.F.member
      dominant := g32r_dominant B.F B.P B.R
      spread := B.spread
      cover := B.F.cover
      reverse := B.reverse }
  exact g32n_theoremA_of_transfer_aux D A W pol

end HodgeLean.Papers
