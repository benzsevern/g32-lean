import HodgeLean.Papers.WeilTransferDefs
import HodgeLean.Papers.G32Moduli
import HodgeLean.Papers.SkeletonG34
import Mathlib.Analysis.Matrix.Order

/-! # The generic Weil transfer: open proof obligations -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open scoped CategoryTheory.MonObj Manifold ContDiff ComplexOrder Matrix MatrixOrder
  Matrix.Norms.L2Operator
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower
open HodgeLean.Foundations.Symplectic HodgeLean.Foundations.HermitianForm HodgeLean.Adapters

namespace HodgeLean.Papers

section Topology

theorem wtr_baireSpace_aux (n : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (Fin (n ^ 2) → ℂ) M] : BaireSpace M := by
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (Fin (n ^ 2) → ℂ) M
  exact BaireSpace.of_t2Space_locallyCompactSpace

theorem wtr_eq_univ_of_open_subset_aux (n : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M]
    [ConnectedSpace M] [ChartedSpace (Fin (n ^ 2) → ℂ) M] {C : Set (Set M)} (hC : C.Countable)
    (hZ : ∀ Z ∈ C, IsClosedAnalytic (Fin (n ^ 2) → ℂ) Z) {U : Set M} (hU : IsOpen U)
    (hne : U.Nonempty) (hsub : U ⊆ ⋃₀ C) : ⋃₀ C = univ := by
  let _ : BaireSpace M := wtr_baireSpace_aux n
  obtain ⟨Z, hZC, hZi⟩ :=
    g32t_baire_step_aux hC (fun Z h ↦ (hZ Z h).isClosed) hU hne hsub
  have hZu : Z = univ := (hZ Z hZC).eq_univ_of_nonempty_interior hZi
  apply eq_univ_of_forall
  intro x
  exact Set.mem_sUnion.2 ⟨Z, hZC, hZu.symm ▸ mem_univ x⟩

end Topology

section Datum

theorem wtr_fiber_isMember_aux {n : ℕ} {δ : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)}
    (D : WeilTransferDatum n δ) (s : D.S) :
    wtr_IsMember n δ (D.fiber s) := by
  exact ⟨D.fiber_polarized s, D.fiber_disc s⟩

theorem wtr_exists_member_aux {n : ℕ} {δ : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)}
    (D : WeilTransferDatum n δ) :
    ∃ P : wtr_Variety n, wtr_IsMember n δ P := by
  obtain ⟨U, _, hU, hdom⟩ := D.dominant
  obtain ⟨m, hm⟩ := hU
  obtain ⟨s, _⟩ := hdom m hm
  exact ⟨D.fiber s, wtr_fiber_isMember_aux D s⟩

theorem wtr_open_subset_locus_aux {n : ℕ} {δ : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)}
    (D : WeilTransferDatum n δ) :
    ∃ U : Set D.M, IsOpen U ∧ U.Nonempty ∧ U ⊆ {m | wtr_WeilAlg (D.univ m)} := by
  obtain ⟨U, hUo, hUne, hU⟩ := D.dominant
  refine ⟨U, hUo, hUne, fun m hm ↦ ?_⟩
  obtain ⟨s, hs⟩ := hU m hm
  exact (D.transport _ _ hs).1 (D.fiber_alg s)

theorem wtr_locus_eq_univ_aux {n : ℕ} {δ : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)}
    (D : WeilTransferDatum n δ) (m : D.M) :
    wtr_WeilAlg (D.univ m) := by
  obtain ⟨U, hUo, hUne, hU⟩ := wtr_open_subset_locus_aux D
  obtain ⟨C, hCc, hCZ, hC⟩ := D.spread
  have hall : ⋃₀ C = univ :=
    wtr_eq_univ_of_open_subset_aux n hCc hCZ hUo hUne (hC ▸ hU)
  have hm : m ∈ ⋃₀ C := hall.symm ▸ mem_univ m
  change m ∈ {m | wtr_WeilAlg (D.univ m)}
  rw [hC]
  exact hm

theorem wtr_weilAlg_of_isMember_aux {n : ℕ} {δ : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)}
    (D : WeilTransferDatum n δ) (P : wtr_Variety n)
    (hP : wtr_IsMember n δ P) : wtr_WeilAlg P := by
  obtain ⟨m, hm⟩ := D.cover P hP
  exact (D.transport _ _ hm).2 (wtr_locus_eq_univ_aux D m)

theorem wtr_theoremA_of_transfer_aux {n : ℕ} {δ : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)}
    (D : WeilTransferDatum n δ) (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) (hM : wtr_IsMember n δ (⟨A, W, pol⟩ : wtr_Variety n)) :
    WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W
      hM.polarized.isWeilType := by
  exact wtr_weilAlg_of_isMember_aux D (⟨A, W, pol⟩ : wtr_Variety n) hM
    hM.polarized.isWeilType

end Datum

section Domain

theorem wtr_periodSet_isOpen_aux (n : ℕ) : IsOpen (wtr_periodSet n) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [wtr_periodSet, wtr_toMat]
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hnorm (A : Matrix (Fin n) (Fin n) ℂ) :
      (1 - Aᴴ * A).PosDef ↔ ‖A‖ < 1 := by
    constructor
    · intro h
      have hs : IsStrictlyPositive (1 - Aᴴ * A) := h.isStrictlyPositive
      obtain ⟨r, hr, hrle⟩ : ∃ r > 0, algebraMap ℝ _ r ≤ 1 - Aᴴ * A :=
        (CFC.exists_pos_algebraMap_le_iff (1 - Aᴴ * A) hs.isSelfAdjoint).2
          (fun x hx => hs.spectrum_pos (𝕜 := ℝ) hx)
      have hsum : algebraMap ℝ _ r + Aᴴ * A ≤ 1 := by
        rwa [le_sub_iff_add_le] at hrle
      have hle : Aᴴ * A ≤ algebraMap ℝ _ (1 - r) := by
        rw [map_sub, map_one, le_sub_iff_add_le]
        simpa [add_comm] using hsum
      have hr1 : 0 ≤ 1 - r := by
        have har : 0 ≤ algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ) (1 - r) :=
          (star_mul_self_nonneg A).trans hle
        exact (algebraMap_le_algebraMap (β := Matrix (Fin n) (Fin n) ℂ)).mp <| by
          simpa only [map_sub, map_one, map_zero] using har
      have hn : ‖Aᴴ * A‖ ≤ 1 - r :=
        (CStarAlgebra.norm_le_iff_le_algebraMap (Aᴴ * A) hr1
          (star_mul_self_nonneg A)).2 hle
      change ‖star A * A‖ ≤ 1 - r at hn
      rw [CStarRing.norm_star_mul_self] at hn
      nlinarith [norm_nonneg A]
    · intro h
      have hn : ‖Aᴴ * A‖ < 1 := by
        change ‖star A * A‖ < 1
        rw [CStarRing.norm_star_mul_self]
        nlinarith [norm_nonneg A]
      have hnon : 0 ≤ 1 - Aᴴ * A := sub_nonneg.mpr <|
        (CStarAlgebra.norm_le_one_iff_of_nonneg (Aᴴ * A)
          (star_mul_self_nonneg A)).mp hn.le
      exact Matrix.isStrictlyPositive_iff_posDef.mp
        ((IsUnit.one_sub_of_norm_lt_one hn).isStrictlyPositive hnon)
  rw [show wtr_periodSet n = {z | ‖wtr_toMat n z‖ < 1} by
    ext z
    exact hnorm (wtr_toMat n z)]
  exact isOpen_lt
    (continuous_norm.comp <| continuous_matrix fun i j => continuous_apply _)
    continuous_const

theorem wtr_domain_coe_aux (n : ℕ) : (wtr_Domain n : Set (Fin (n ^ 2) → ℂ)) = wtr_periodSet n := by
  exact (wtr_periodSet_isOpen_aux n).interior_eq

theorem wtr_periodSet_convex_aux (n : ℕ) : Convex ℝ (wtr_periodSet n) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · rw [show wtr_periodSet 0 = univ by
      ext z
      simp only [wtr_periodSet, Set.mem_setOf_eq, mem_univ, iff_true]
      refine ⟨?_, ?_⟩
      · ext i
        exact Fin.elim0 i
      intro x hx
      exact (hx (Subsingleton.elim _ _)).elim]
    exact convex_univ
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hnorm (A : Matrix (Fin n) (Fin n) ℂ) :
      (1 - Aᴴ * A).PosDef ↔ ‖A‖ < 1 := by
    constructor
    · intro h
      have hs : IsStrictlyPositive (1 - Aᴴ * A) := h.isStrictlyPositive
      obtain ⟨r, hr, hrle⟩ : ∃ r > 0, algebraMap ℝ _ r ≤ 1 - Aᴴ * A :=
        (CFC.exists_pos_algebraMap_le_iff (1 - Aᴴ * A) hs.isSelfAdjoint).2
          (fun x hx => hs.spectrum_pos (𝕜 := ℝ) hx)
      have hsum : algebraMap ℝ _ r + Aᴴ * A ≤ 1 := by rwa [le_sub_iff_add_le] at hrle
      have hle : Aᴴ * A ≤ algebraMap ℝ _ (1 - r) := by
        rw [map_sub, map_one, le_sub_iff_add_le]
        simpa [add_comm] using hsum
      have hr1 : 0 ≤ 1 - r := by
        have har : 0 ≤ algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ) (1 - r) :=
          (star_mul_self_nonneg A).trans hle
        exact (algebraMap_le_algebraMap (β := Matrix (Fin n) (Fin n) ℂ)).mp <| by
          simpa only [map_sub, map_one, map_zero] using har
      have hn : ‖Aᴴ * A‖ ≤ 1 - r :=
        (CStarAlgebra.norm_le_iff_le_algebraMap (Aᴴ * A) hr1
          (star_mul_self_nonneg A)).2 hle
      change ‖star A * A‖ ≤ 1 - r at hn
      rw [CStarRing.norm_star_mul_self] at hn
      nlinarith [norm_nonneg A]
    · intro h
      have hn : ‖Aᴴ * A‖ < 1 := by
        change ‖star A * A‖ < 1
        rw [CStarRing.norm_star_mul_self]
        nlinarith [norm_nonneg A]
      have hnon : 0 ≤ 1 - Aᴴ * A := sub_nonneg.mpr <|
        (CStarAlgebra.norm_le_one_iff_of_nonneg (Aᴴ * A)
          (star_mul_self_nonneg A)).mp hn.le
      exact Matrix.isStrictlyPositive_iff_posDef.mp
        ((IsUnit.one_sub_of_norm_lt_one hn).isStrictlyPositive hnon)
  rw [show wtr_periodSet n = {z | ‖wtr_toMat n z‖ < 1} by
    ext z
    exact hnorm (wtr_toMat n z)]
  intro x hx y hy a b ha hb hab
  have hmap : wtr_toMat n (a • x + b • y) =
      a • wtr_toMat n x + b • wtr_toMat n y := by
    ext i j
    simp [wtr_toMat]
  rw [Set.mem_setOf_eq, hmap]
  calc
    ‖a • wtr_toMat n x + b • wtr_toMat n y‖
        ≤ ‖a • wtr_toMat n x‖ + ‖b • wtr_toMat n y‖ := norm_add_le _ _
    _ = a * ‖wtr_toMat n x‖ + b * ‖wtr_toMat n y‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * max ‖wtr_toMat n x‖ ‖wtr_toMat n y‖ +
        b * max ‖wtr_toMat n x‖ ‖wtr_toMat n y‖ := by gcongr <;> simp
    _ = max ‖wtr_toMat n x‖ ‖wtr_toMat n y‖ := by rw [← add_mul, hab, one_mul]
    _ < 1 := max_lt hx hy

theorem wtr_zero_mem_aux (n : ℕ) : (0 : Fin (n ^ 2) → ℂ) ∈ wtr_Domain n := by
  change (0 : Fin (n ^ 2) → ℂ) ∈ (wtr_Domain n : Set (Fin (n ^ 2) → ℂ))
  rw [wtr_domain_coe_aux]
  change (1 - (wtr_toMat n 0)ᴴ * wtr_toMat n 0).PosDef
  have hz : wtr_toMat n (0 : Fin (n ^ 2) → ℂ) = 0 := by ext; simp [wtr_toMat]
  rw [hz]
  simpa using (Matrix.PosDef.one : (1 : Matrix (Fin n) (Fin n) ℂ).PosDef)

theorem wtr_periodSet_isBounded_aux (n : ℕ) : Bornology.IsBounded (wtr_periodSet n) := by
  refine (Metric.isBounded_ball : Bornology.IsBounded
    (Metric.ball (0 : Fin (n ^ 2) → ℂ) 1)).subset ?_
  intro z hz
  rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos]
  intro k
  change (1 - (wtr_toMat n z)ᴴ * wtr_toMat n z).PosDef at hz
  rcases n.eq_zero_or_pos with rfl | hn
  · exact Fin.elim0 k
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hs : IsStrictlyPositive (1 - (wtr_toMat n z)ᴴ * wtr_toMat n z) :=
    hz.isStrictlyPositive
  obtain ⟨r, hr, hrle⟩ : ∃ r > 0,
      algebraMap ℝ _ r ≤ 1 - (wtr_toMat n z)ᴴ * wtr_toMat n z :=
    (CFC.exists_pos_algebraMap_le_iff
      (1 - (wtr_toMat n z)ᴴ * wtr_toMat n z) hs.isSelfAdjoint).2
      (fun x hx => hs.spectrum_pos (𝕜 := ℝ) hx)
  have hsum : algebraMap ℝ _ r + (wtr_toMat n z)ᴴ * wtr_toMat n z ≤ 1 := by
    rwa [le_sub_iff_add_le] at hrle
  have hle : (wtr_toMat n z)ᴴ * wtr_toMat n z ≤ algebraMap ℝ _ (1 - r) := by
    rw [map_sub, map_one, le_sub_iff_add_le]
    simpa [add_comm] using hsum
  have hr1 : 0 ≤ 1 - r := by
    have har : 0 ≤ algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ) (1 - r) :=
      (star_mul_self_nonneg (wtr_toMat n z)).trans hle
    exact (algebraMap_le_algebraMap (β := Matrix (Fin n) (Fin n) ℂ)).mp <| by
      simpa only [map_sub, map_one, map_zero] using har
  have hmat : ‖wtr_toMat n z‖ < 1 := by
    have hsq : ‖(wtr_toMat n z)ᴴ * wtr_toMat n z‖ ≤ 1 - r :=
      (CStarAlgebra.norm_le_iff_le_algebraMap _ hr1
        (star_mul_self_nonneg (wtr_toMat n z))).2 hle
    change ‖star (wtr_toMat n z) * wtr_toMat n z‖ ≤ 1 - r at hsq
    rw [CStarRing.norm_star_mul_self] at hsq
    nlinarith [norm_nonneg (wtr_toMat n z)]
  let p : Fin n × Fin n := finProdFinEquiv.symm (Fin.cast (sq n) k)
  have hcoord : wtr_toMat n z p.1 p.2 = z k := by
    change z _ = z k
    have hp : finProdFinEquiv p = Fin.cast (sq n) k := by
      exact Equiv.apply_symm_apply finProdFinEquiv (Fin.cast (sq n) k)
    rw [hp]
    rfl
  rw [← hcoord]
  have hentry : ‖wtr_toMat n z p.1 p.2‖ ≤ ‖wtr_toMat n z‖ := by
    calc
      ‖wtr_toMat n z p.1 p.2‖ =
          ‖((Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℂ ≃⋆ₐ[ℂ] _)
            (wtr_toMat n z) (EuclideanSpace.single p.2 1)) p.1‖ := by
        congr 1
        rw [Matrix.ofLp_toEuclideanCLM]
        simp [Matrix.mulVec]
      _ ≤ ‖(Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℂ ≃⋆ₐ[ℂ] _)
          (wtr_toMat n z) (EuclideanSpace.single p.2 1)‖ := PiLp.norm_apply_le _ _
      _ ≤ ‖(Matrix.toEuclideanCLM : Matrix (Fin n) (Fin n) ℂ ≃⋆ₐ[ℂ] _)
          (wtr_toMat n z)‖ * ‖EuclideanSpace.single p.2 (1 : ℂ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖wtr_toMat n z‖ := by rw [← Matrix.cstar_norm_def]; simp
  exact hentry.trans_lt hmat

theorem wtr_not_mem_of_toMat_eq_one_aux (n : ℕ) (hn : 0 < n) (z : Fin (n ^ 2) → ℂ)
    (hz : wtr_toMat n z = 1) : z ∉ wtr_periodSet n := by
  intro h
  change (1 - (wtr_toMat n z)ᴴ * wtr_toMat n z).PosDef at h
  rw [hz] at h
  let i : Fin n := ⟨0, hn⟩
  have hv : (fun j : Fin n => if j = i then (1 : ℂ) else 0) ≠ 0 := by
    intro he
    have := congrFun he i
    simp at this
  have hp := h.dotProduct_mulVec_pos hv
  simpa [i] using hp

theorem wtr_domain_connectedSpace_aux (n : ℕ) : ConnectedSpace (wtr_Domain n) := by
  apply Subtype.connectedSpace
  refine ⟨⟨0, wtr_zero_mem_aux n⟩, ?_⟩
  rw [wtr_domain_coe_aux]
  exact (wtr_periodSet_convex_aux n).isPreconnected

end Domain

section Family

theorem wtr_family_exists_member_aux {n : ℕ} {δ : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)}
    (F : wtr_UniversalFamily n δ) :
    ∃ P : wtr_Variety n, wtr_IsMember n δ P := by
  refine ⟨F.univ ⟨0, ?_⟩, F.member _⟩
  exact wtr_zero_mem_aux n

theorem wtr_theoremA_of_stages_aux {n : ℕ} {δ : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0)}
    (F : wtr_UniversalFamily n δ) (R : wtr_StageFields F)
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) (hM : wtr_IsMember n δ (⟨A, W, pol⟩ : wtr_Variety n)) :
    WeilClassesAlgebraic (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
      (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) W
      hM.polarized.isWeilType := by
  letI : ConnectedSpace (wtr_Domain n) := wtr_domain_connectedSpace_aux n
  exact wtr_theoremA_of_transfer_aux (wtr_transferFields F R) A W pol hM

end Family

section Bridge

theorem wtr_g32_instance_aux
    (h : ∀ P : wtr_Variety 3, wtr_IsMember 3 classNegTwo P → wtr_WeilAlg P)
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (W : letI := (torusCohomology_cupProductOf A).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian A)
          (spec_bettiDeRhamIso_abelian A) (hodgeDecomposition_of_abelian A)
          (torusCohomology_cupProductOf A)).weight1 3)
    (pol : HQ A 2) : G32TheoremAStatement A W pol := by
  intro hM
  exact h (⟨A, W, pol⟩ : wtr_Variety 3)
    ((wtr_isMember_three_iff _).2 hM) hM.isWeilType

theorem wtr_g32_statement_iff_aux :
    (∀ P : wtr_Variety 3, wtr_IsMember 3 classNegTwo P → wtr_WeilAlg P) ↔
      ∀ P : g32t_Sixfold, G32TheoremAStatement P.X P.W P.pol := by
  constructor
  · intro h P hP
    exact h P ((wtr_isMember_three_iff P).2 hP) hP.isWeilType
  · intro h P hP hW
    simpa using h P ((wtr_isMember_three_iff P).1 hP)

theorem wtr_g34A_of_transfer_aux (D : WeilTransferDatum 4 1) (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] :
    G34TheoremAStatement A := by
  intro W hW pol hη hRos hPos hDim hDisc
  let P : wtr_Variety 4 := ⟨A, W, pol⟩
  let hpol : wtr_PolarizedWeil 4 P := ⟨hDim, hW, hη, hRos, hPos⟩
  have hM : wtr_IsMember 4 1 P := ⟨hpol, hDisc⟩
  exact wtr_theoremA_of_transfer_aux D A W pol hM

theorem wtr_g34B_of_transfer_aux
    (D : ∀ δ : ℚˣ ⧸ normSubgroup (QuadraticAlgebra ℚ (-3) 0),
      (∃ P : wtr_Variety 3, wtr_IsMember 3 δ P) → WeilTransferDatum 3 δ)
    (A : Over (Spec ↧ℂ))
    [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] :
    G34TheoremBStatement A := by
  intro W hW pol hη hRos hPos hDim
  let P : wtr_Variety 3 := ⟨A, W, pol⟩
  let hpol : wtr_PolarizedWeil 3 P := ⟨hDim, hW, hη, hRos, hPos⟩
  let δ := wtr_disc hpol
  have hM : wtr_IsMember 3 δ P := ⟨hpol, rfl⟩
  exact wtr_theoremA_of_transfer_aux (D δ ⟨P, hM⟩) A W pol hM

end Bridge

end HodgeLean.Papers
