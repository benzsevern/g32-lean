import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

noncomputable section
set_option maxHeartbeats 400000
open AlgebraicGeometry
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency.types false in
/-- On an affine open disjoint from an ideal's support, its section ideal is the unit ideal. -/
theorem s2v_l1b_ideal_top_off_support
    (X : Scheme) (I : X.IdealSheafData) (U : X.affineOpens)
    (hU : ∀ x ∈ U.1, x ∉ I.support) : I.ideal U = ⊤ := by
  have hempty : X.zeroLocus (U := U.1) (I.ideal U) ∩ U.1 = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hU x hx.2 ((I.mem_support_iff_of_mem hx.2).mpr hx.1)
  have h := U.2.fromSpec_image_zeroLocus (I.ideal U)
  rw [hempty] at h
  have h := Set.image_eq_empty.mp h
  exact PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp h

/-- Finitely many avoided branch supports are simultaneously absent on an affine neighborhood. -/
theorem s2v_l1b_affine_avoid_finite_supports
    (X : Scheme) {J : Type*} [Finite J] (I : J → X.IdealSheafData)
    (x : X) (hx : ∀ j, x ∉ (I j).support)
    (V : X.Opens) (hxV : x ∈ V) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧ U.1 ≤ V ∧ ∀ j, (I j).ideal U = ⊤ := by
  let O : X.Opens := ⟨⋂ j, ((I j).support : Set X)ᶜ,
    isOpen_iInter_of_finite fun j => (I j).support.isClosed.isOpen_compl⟩
  have hxO : x ∈ O := Set.mem_iInter.mpr hx
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ V ⊓ O from ⟨hxV, hxO⟩)
  refine ⟨⟨U, hU⟩, hxU, fun y hy => (hUV hy).1, ?_⟩
  intro j
  apply s2v_l1b_ideal_top_off_support
  intro y hy
  exact Set.mem_iInter.mp (hUV hy).2 j

/-- Away from the two selected branches, principal generators of all other branch ideals are regular units. -/
theorem s2v_l1b_unselected_branch_units
    (X : Scheme) {J : Type*} [Finite J] (I : J → X.IdealSheafData)
    (a b : J) (x : X)
    (hx : ∀ j, j ≠ a → j ≠ b → x ∉ (I j).support)
    (V : X.Opens) (hxV : x ∈ V) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧ U.1 ≤ V ∧
      ∀ j, j ≠ a → j ≠ b → ∀ g : Γ(X, U),
        (I j).ideal U = Ideal.span {g} → IsUnit g := by
  obtain ⟨U, hxU, hUV, hI⟩ := s2v_l1b_affine_avoid_finite_supports X
    (fun j : {j : J // j ≠ a ∧ j ≠ b} => I j.val) x
    (fun j => hx j.val j.property.1 j.property.2) V hxV
  refine ⟨U, hxU, hUV, ?_⟩
  intro j hja hjb g hg
  apply Ideal.span_singleton_eq_top.mp
  rw [← hg]
  exact hI ⟨j, hja, hjb⟩

end HodgeLean.Foundations.Program
