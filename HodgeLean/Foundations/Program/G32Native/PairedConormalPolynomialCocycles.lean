import HodgeLean.Ported.NYLL.SchemeTheory.Cohomology.Cech.ProjSpaceCechTwistFiniteCohomology

/-! # Polynomial representatives of projective degree-zero cocycles -/
noncomputable section
set_option maxHeartbeats 200000
open AlgebraicCurves.Cohomology.Cech.Proofs.ProjSpaceCech_Twist_finite_cohomology.ProjSpaceCech
open ProjSpaceCech
open scoped ProjSpaceCech.Twist
namespace HodgeLean.Foundations.Program.G32Native

/-- Every compatible homogeneous Laurent family is a single homogeneous polynomial family. -/
theorem conormal_projective_polynomial_cocycle_surjective
    (R : Type) [CommRing R] (n : ℕ) (hn : 1 ≤ n) (d : ℤ) :
    Function.Surjective
      ((Twist.constSec R d).codRestrict
        (LinearMap.ker (Twist.d R n d 0)) (Twist.constSec_mem_ker R d)) := by
  intro x
  obtain ⟨c, hc⟩ := x
  let p := Finsupp.comapDomain (Twist.Mon.incl n d (Finset.empty_subset _))
    (c (Twist.vtx 0)) (Set.injOn_of_injective (Twist.Mon.incl_injective n d _))
  refine ⟨p, Subtype.ext (Twist.ext_coeff R d fun t a => ?_)⟩
  change Twist.coeff R d (Twist.constSec R d p) t a = Twist.coeff R d c t a
  rw [Twist.coeff_constSec]
  split_ifs with h
  · erw [Finsupp.comapDomain_apply,
      show Twist.Mon.incl n d (Finset.empty_subset _) ⟨a, h.1, h.2.le⟩ =
        (⟨a, h.1, h.2.le.trans (Finset.empty_subset _)⟩ :
          Twist.Mon n d (Idx.img n (Twist.vtx 0))) from rfl,
      ← Twist.coeff_eq R d c (Twist.vtx 0), Twist.eq_vtx t, Twist.ker_edge R d hc]
  · by_cases ht : ∑ j, a j = d ∧ Twist.negSupp n a ⊆ Idx.img n t
    · have hs : Twist.negSupp n a ⊆ {t.1 0} := by
        rw [← Twist.img_vtx (t.1 0), ← Twist.eq_vtx t]
        exact ht.2
      have hne : Twist.negSupp n a ≠ ∅ := fun he => h ⟨ht.1, he⟩
      obtain ⟨j, hj⟩ : ∃ j : Fin (n + 1), j ≠ t.1 0 :=
        Fintype.exists_ne_of_one_lt_card (by rw [Fintype.card_fin]; omega) (t.1 0)
      rw [Twist.eq_vtx t, Twist.ker_edge R d hc (t.1 0) j, Twist.coeff_of_not]
      rw [Twist.img_vtx]
      intro hj'
      obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      exact hj ((Finset.mem_singleton.mp (hj' hz)).symm.trans
        (Finset.mem_singleton.mp (hs hz)))
    · rw [Twist.coeff, dite_eq_right ht]

end HodgeLean.Foundations.Program.G32Native
