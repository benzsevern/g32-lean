import HodgeLean.Foundations.Program.G32Native.PairedC3NegativeSectionComparison
import HodgeLean.Ported.NYLL.SchemeTheory.ProjectiveSpace.TwistingSheafCechComparison

/-! # Cech comparison for the original native negative twisting line -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open ProjSpaceCech AlgebraicGeometry.ProjSpace Scheme.Modules
open AlgebraicCurves.Cohomology.Cech.Proofs
open OModulePresheaf_cechFinite_unit_of_isClosedImmersion_proj.AlgebraicGeometry.ProjSpace
attribute [local instance] GradedModule.acg GradedModule.modR GradedModule.Frac.setoid
  GradedModule.sec.instAddCommGroup GradedModule.sec.instModule
attribute [local instance] MvPolynomial.gradedAlgebra
variable (R : Type) [CommRing R] (n : ℕ)
local notation "A" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/-- The original native negative line with its original structural action. -/
abbrev pairedC3NegativeSectionPresheaf : OModulePresheaf ((𝟙 (Proj A)) ≫ π R n) :=
  toOModulePresheaf ((𝟙 (Proj A)) ≫ π R n) (twistingSheaf R n).dual

/-- The actual coordinate-section comparisons give a cochain equivalence. -/
def pairedC3NegativeCochainEquiv (q : ℕ) :
    GradedModule.cochain (GradedModule.FD R n (-1)) q ≃ₗ[R]
      (pairedC3NegativeSectionPresheaf R n).cochain (stdCoverPullback (𝟙 (Proj A))) q :=
  (LinearEquiv.piCongrLeft' R
    (fun s : Idx n q => GradedModule.sec (GradedModule.FD R n (-1)) (Idx.img n s))
    (ClosedImmCech.idxEquiv (𝟙 (Proj A)) q).symm) ≪≫ₗ
    (LinearEquiv.piCongrRight (fun s =>
      pairedC3NegativeFractionSectionEquiv R n
        (Idx.img n (ClosedImmCech.idxEquiv (𝟙 (Proj A)) q s))
        (ClosedImmCech.altImg_nonempty _) ≪≫ₗ
      restrictionAlongEquality (pairedC3NegativeSectionPresheaf R n)
        (ClosedImmCech.altOpen_eq (𝟙 (Proj A)) q s).symm))

/-- The cochain equivalence has the literal original restriction component. -/
theorem paired_c3_negative_cochain_apply (q : ℕ)
    (c : GradedModule.cochain (GradedModule.FD R n (-1)) q)
    (s : (stdCoverPullback (𝟙 (Proj A))).Idx q) :
    pairedC3NegativeCochainEquiv R n q c s =
      (pairedC3NegativeSectionPresheaf R n).res (ClosedImmCech.altOpen_eq (𝟙 (Proj A)) q s).le
        (pairedC3NegativeFractionSectionEquiv R n
          (Idx.img n (ClosedImmCech.idxEquiv (𝟙 (Proj A)) q s))
          (ClosedImmCech.altImg_nonempty _) (c (ClosedImmCech.idxEquiv (𝟙 (Proj A)) q s))) := rfl

#print axioms pairedC3NegativeCochainEquiv
#print axioms paired_c3_negative_cochain_apply
/-- A coordinate face keeps the actual section comparison and its restriction map. -/
theorem paired_c3_negative_cochain_face (q : ℕ)
    (s : (stdCoverPullback (𝟙 (Proj A))).Idx (q + 1)) (j : Fin (q + 2))
    (z : GradedModule.sec (GradedModule.FD R n (-1))
      (Idx.img n (Idx.face n (ClosedImmCech.idxEquiv (𝟙 (Proj A)) (q + 1) s) j))) :
    (pairedC3NegativeSectionPresheaf R n).res
        (ClosedImmCech.altOpen_eq (𝟙 (Proj A)) (q + 1) s).le
        (pairedC3NegativeFractionSectionEquiv R n
          (Idx.img n (ClosedImmCech.idxEquiv (𝟙 (Proj A)) (q + 1) s))
          (ClosedImmCech.altImg_nonempty _)
          (GradedModule.secIncl _ (Idx.img_face_subset n _ j) z)) =
      (pairedC3NegativeSectionPresheaf R n).res
        ((stdCoverPullback (𝟙 (Proj A))).inter_le_inter_face s j)
        ((pairedC3NegativeSectionPresheaf R n).res
          (ClosedImmCech.altOpen_eq (𝟙 (Proj A)) q
            ((stdCoverPullback (𝟙 (Proj A))).face s j)).le
          (pairedC3NegativeFractionSectionEquiv R n
            (Idx.img n (Idx.face n (ClosedImmCech.idxEquiv (𝟙 (Proj A)) (q + 1) s) j))
            (ClosedImmCech.altImg_nonempty _) z)) := by
  let F := pairedC3NegativeSectionPresheaf R n
  let a : Idx n (q + 1) := ClosedImmCech.idxEquiv (𝟙 (Proj A)) (q + 1) s
  let v := pairedC3NegativeFractionSectionEquiv R n (Idx.img n (Idx.face n a j))
    (ClosedImmCech.altImg_nonempty _) z
  have hloc : F.res (coordinateIntersection_mono R n (Idx.img_face_subset n a j)) v =
      pairedC3NegativeFractionSectionEquiv R n (Idx.img n a)
        (ClosedImmCech.altImg_nonempty _)
        (GradedModule.secIncl _ (Idx.img_face_subset n a j) z) :=
    paired_c3_negative_section_restrict R n (Idx.img_face_subset n a j)
      (ClosedImmCech.altImg_nonempty _) (ClosedImmCech.altImg_nonempty _) z
  calc
    _ = F.res (ClosedImmCech.altOpen_eq (𝟙 (Proj A)) (q + 1) s).le
        (F.res (coordinateIntersection_mono R n (Idx.img_face_subset n a j)) v) :=
      congrArg (F.res (ClosedImmCech.altOpen_eq (𝟙 (Proj A)) (q + 1) s).le) hloc.symm
    _ = F.res
        ((ClosedImmCech.altOpen_eq (𝟙 (Proj A)) (q + 1) s).le.trans
          (coordinateIntersection_mono R n (Idx.img_face_subset n a j))) v := F.res_res _ _ v
    _ = _ := (F.res_res
      ((stdCoverPullback (𝟙 (Proj A))).inter_le_inter_face s j)
      (ClosedImmCech.altOpen_eq (𝟙 (Proj A)) q
        ((stdCoverPullback (𝟙 (Proj A))).face s j)).le v).symm


#print axioms paired_c3_negative_cochain_face
/-- The actual section comparison commutes with the two original
Čech differentials, rather than merely comparing their cochain modules. -/
theorem paired_c3_negative_cochain_d (q : ℕ)
    (c : GradedModule.cochain (GradedModule.FD R n (-1)) q) :
    pairedC3NegativeCochainEquiv R n (q + 1) (GradedModule.d (GradedModule.FD R n (-1)) q c) =
      (pairedC3NegativeSectionPresheaf R n).d (stdCoverPullback (𝟙 (Proj A))) q
        (pairedC3NegativeCochainEquiv R n q c) := by
  funext s
  let F := pairedC3NegativeSectionPresheaf R n
  let a : Idx n (q + 1) := ClosedImmCech.idxEquiv (𝟙 (Proj A)) (q + 1) s
  let e : GradedModule.sec (GradedModule.FD R n (-1)) (Idx.img n a) →ₗ[R]
      F.obj ((stdCoverPullback (𝟙 (Proj A))).inter s) :=
    (F.res (ClosedImmCech.altOpen_eq (𝟙 (Proj A)) (q + 1) s).le).comp
      (pairedC3NegativeFractionSectionEquiv R n (Idx.img n a)
        (ClosedImmCech.altImg_nonempty _)).toLinearMap
  simp only [paired_c3_negative_cochain_apply, OModulePresheaf.d_apply]
  change e (GradedModule.d (GradedModule.FD R n (-1)) q c a) = _
  rw [GradedModule.d_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [e.map_smul]
  rw [show (-1 : R) ^ (j : ℕ) = (((-1 : ℤ) ^ (j : ℕ) : ℤ) : R) by
    simp only [Int.cast_pow, Int.cast_neg, Int.cast_one], Int.cast_smul_eq_zsmul]
  exact congrArg (fun v => ((-1 : ℤ) ^ (j : ℕ)) • v)
    (paired_c3_negative_cochain_face R n q s j
      (c (Idx.face n (ClosedImmCech.idxEquiv (𝟙 (Proj A)) (q + 1) s) j)))


#print axioms paired_c3_negative_cochain_d
end HodgeLean.Foundations.Program.G32Native
