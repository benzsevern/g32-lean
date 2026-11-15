import HodgeLean.Foundations.RationalHomologyManifold.SubdivisionGlobalSections

/-! Soft opcycles in an actual bounded-below exact sheaf complex.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- In an exact complex of soft sheaves, softness of one opcycle object propagates to the next.
Source: Bredon, Sheaf Theory, second edition, Theorem II.9.10; quotients of soft sheaves by soft subsheaves.
HC no distance; AV milestone no distance.
-/
theorem soft_opcycles_succ (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℤ) (i : ℤ)
    (hi : K.ExactAt i) (hs : IsSoft (K.opcycles i)) (ht : IsSoft (K.X (i + 1))) :
    IsSoft (K.opcycles (i + 1)) := by
  let g := K.fromOpcycles i (i + 1)
  letI : Mono g := by
    exact Preadditive.mono_of_isZero_kernel' _
      (K.homologyIsKernel i (i + 1) (by rw [CochainComplex.next])) hi.isZero_homology
  let S := ShortComplex.mk g (cokernel.π g) (cokernel.condition g)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel g }
  have hq : IsSoft (cokernel g) := spec_isSoft_of_shortExact hS hs ht
  let e0 : K.opcycles (i + 1) ≅ cokernel (K.d i (i + 1)) :=
    (K.opcyclesIsCokernel i (i + 1) (by rw [CochainComplex.prev]; omega)).coconePointUniqueUpToIso
      (colimit.isColimit _)
  let e1 : cokernel (K.d i (i + 1)) ≅ cokernel g :=
    (cokernelIsoOfEq (K.p_fromOpcycles i (i + 1))).symm ≪≫
      cokernelEpiComp (K.pOpcycles i) g
  exact isSoft_of_sheaf_iso (e0 ≪≫ e1).symm hq

#print axioms soft_opcycles_succ
/-- Every opcycle object at or above the bound in an exact bounded-below complex of soft sheaves is soft.
Source: Bredon, Sheaf Theory, second edition, Theorem II.9.10; induction from the zero lower tail.
HC no distance; AV milestone no distance.
-/
theorem bounded_soft_opcycles (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℤ) (b : ℤ)
    [K.IsStrictlyGE b] (hK : K.Acyclic) (hs : ∀ i, IsSoft (K.X i)) (m : ℕ) :
    IsSoft (K.opcycles (b + m)) := by
  induction m with
  | zero =>
      have hd : K.d (b - 1) b = 0 :=
        (K.isZero_of_isStrictlyGE b (b - 1) (by omega)).eq_of_src _ _
      letI := K.isIso_pOpcycles (b - 1) b (by rw [CochainComplex.prev]) hd
      simpa only [Nat.cast_zero, add_zero] using
        (isSoft_of_sheaf_iso (asIso (K.pOpcycles b)) (hs b))
  | succ m ih =>
      have h := soft_opcycles_succ X K (b + m) (hK _) ih (hs _)
      simpa only [Nat.cast_succ, add_assoc] using h

#print axioms bounded_soft_opcycles
end HodgeLean.Foundations.RationalHomologyManifold
