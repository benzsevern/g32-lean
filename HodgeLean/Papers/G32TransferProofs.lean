import HodgeLean.Papers.G32TransferDefs

/-! # G32 Theorem A, the transfer layer: open proof obligations -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open scoped CategoryTheory.MonObj Manifold ContDiff
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Adapters

namespace HodgeLean.Papers

theorem g32t_baire_step_aux {M : Type*} [TopologicalSpace M] [BaireSpace M]
    {C : Set (Set M)} (hC : C.Countable) (hcl : ∀ Z ∈ C, IsClosed Z) {U : Set M}
    (hU : IsOpen U) (hne : U.Nonempty) (hsub : U ⊆ ⋃₀ C) :
    ∃ Z ∈ C, (interior Z).Nonempty := by
  let _ : BaireSpace U := hU.baireSpace
  let _ : Nonempty U := hne.to_subtype
  let _ : Countable C := hC.to_subtype
  let G : C → Set U := fun Z ↦ Subtype.val ⁻¹' (Z : Set M)
  have hGclosed : ∀ Z, IsClosed (G Z) := fun Z ↦
    (hcl Z Z.property).preimage continuous_subtype_val
  have hGcover : ⋃ Z, G Z = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨Z, hZC, hxZ⟩ := Set.mem_sUnion.1 (hsub x.property)
    exact Set.mem_iUnion.2 ⟨⟨Z, hZC⟩, hxZ⟩
  obtain ⟨Z, x, hx⟩ := nonempty_interior_of_iUnion_of_closed hGclosed hGcover
  obtain ⟨V, hVopen, hV⟩ := (isOpen_interior : IsOpen (interior (G Z))).image_val
  have hxVU : x.1 ∈ V ∩ U := hV ▸ ⟨x, hx, rfl⟩
  refine ⟨Z, Z.property, x.1, interior_maximal ?_ (hVopen.inter hU) hxVU⟩
  intro y hy
  obtain ⟨z, hz, rfl⟩ : y ∈ Subtype.val '' interior (G Z) := hV.symm ▸ hy
  have hzG : z ∈ G Z := interior_subset hz
  change z.1 ∈ (Z : Set M)
  exact hzG

theorem g32t_baireSpace_aux {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (Fin 9 → ℂ) M] : BaireSpace M := by
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (Fin 9 → ℂ) M
  exact BaireSpace.of_t2Space_locallyCompactSpace

theorem g32t_eq_univ_of_open_subset_aux {M : Type*} [TopologicalSpace M] [T2Space M]
    [ConnectedSpace M] [ChartedSpace (Fin 9 → ℂ) M] {C : Set (Set M)} (hC : C.Countable)
    (hZ : ∀ Z ∈ C, IsClosedAnalytic (Fin 9 → ℂ) Z) {U : Set M} (hU : IsOpen U)
    (hne : U.Nonempty) (hsub : U ⊆ ⋃₀ C) : ⋃₀ C = univ := by
  let _ : BaireSpace M := g32t_baireSpace_aux
  obtain ⟨Z, hZC, hZi⟩ := g32t_baire_step_aux hC (fun Z h ↦ (hZ Z h).isClosed) hU hne hsub
  have hZu : Z = univ := (hZ Z hZC).eq_univ_of_nonempty_interior hZi
  apply eq_univ_of_forall
  intro x
  exact Set.mem_sUnion.2 ⟨Z, hZC, hZu.symm ▸ mem_univ x⟩

theorem g32t_fiber_isMember_aux (D : G32TransferDatum) (s : D.S) :
    g32t_IsMember (D.fiber s) := by
  exact (g32t_isMember_iff _).2 ⟨D.fiber_polarized s, D.fiber_disc s⟩

theorem g32t_exists_member_aux (D : G32TransferDatum) : ∃ P, g32t_IsMember P := by
  obtain ⟨U, _, hU, hdom⟩ := D.dominant
  obtain ⟨m, hm⟩ := hU
  obtain ⟨s, _⟩ := hdom m hm
  exact ⟨D.fiber s, g32t_fiber_isMember_aux D s⟩

theorem g32t_open_subset_locus_aux (D : G32TransferDatum) :
    ∃ U : Set D.M, IsOpen U ∧ U.Nonempty ∧ U ⊆ {m | g32t_WeilAlg (D.univ m)} := by
  obtain ⟨U, hUo, hUne, hU⟩ := D.dominant
  refine ⟨U, hUo, hUne, fun m hm ↦ ?_⟩
  obtain ⟨s, hs⟩ := hU m hm
  exact (D.transport _ _ hs).1 (D.fiber_alg s)

theorem g32t_locus_eq_univ_aux (D : G32TransferDatum) (m : D.M) :
    g32t_WeilAlg (D.univ m) := by
  obtain ⟨U, hUo, hUne, hU⟩ := g32t_open_subset_locus_aux D
  obtain ⟨C, hCc, hCZ, hC⟩ := D.spread
  have hall : ⋃₀ C = univ :=
    g32t_eq_univ_of_open_subset_aux hCc hCZ hUo hUne (hC ▸ hU)
  have hm : m ∈ ⋃₀ C := hall.symm ▸ mem_univ m
  change m ∈ {m | g32t_WeilAlg (D.univ m)}
  rw [hC]
  exact hm

theorem g32t_weilAlg_of_isMember_aux (D : G32TransferDatum) (P : g32t_Sixfold)
    (hP : g32t_IsMember P) : g32t_WeilAlg P := by
  obtain ⟨m, hm⟩ := D.cover P hP
  exact (D.transport _ _ hm).2 (g32t_locus_eq_univ_aux D m)

theorem g32t_theoremA_of_transfer_aux (D : G32TransferDatum) (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol := by
  intro hM
  let P : g32t_Sixfold := ⟨A, W, pol⟩
  exact g32t_weilAlg_of_isMember_aux D P hM hM.isWeilType

end HodgeLean.Papers
