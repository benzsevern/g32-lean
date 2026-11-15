import HodgeLean.Ported.NYLL.SchemeTheory.Cohomology.Cech.ProjSpaceCechTwistFiniteCohomology

/-! # Homogeneous coordinates of projective zero cocycles -/

noncomputable section
set_option maxHeartbeats 400000
open AlgebraicCurves.Cohomology.Cech.Proofs.ProjSpaceCech_Twist_finite_cohomology
open ProjSpaceCech
namespace HodgeLean.Foundations.Program.G32Native

/-- Every projective Laurent zero cocycle is the restriction of a homogeneous
polynomial with nonnegative exponents, retaining all coordinate coefficients. -/
theorem paired_twist_zero_cocycle_polynomial (R : Type*) [CommRing R]
    {n : ℕ} (d : ℤ) (hn : 1 ≤ n) (f : Twist.cochain R n d 0)
    (hf : f ∈ LinearMap.ker (Twist.d R n d 0)) :
    ∃ g : Twist.Mon n d ∅ →₀ R, Twist.constSec R d g = f := by
  classical
  refine ⟨Finsupp.comapDomain (Twist.Mon.incl n d (Finset.empty_subset _))
    (f (Twist.vtx 0))
    (Set.injOn_of_injective (Twist.Mon.incl_injective n d _)),
    Twist.ext_coeff R d fun t a => ?_⟩
  change Twist.coeff R d (Twist.constSec R d _) t a
    = Twist.coeff R d f t a
  rw [Twist.coeff_constSec]
  split_ifs with hok
  · erw [Finsupp.comapDomain_apply,
      show Twist.Mon.incl n d (Finset.empty_subset _) ⟨a, hok.1, hok.2.le⟩
        = (⟨a, hok.1, hok.2.le.trans (Finset.empty_subset _)⟩ :
          Twist.Mon n d (Idx.img n (Twist.vtx 0))) from rfl,
      ← Twist.coeff_eq R d f (Twist.vtx 0),
      Twist.eq_vtx t, Twist.ker_edge R d hf]
  · by_cases hokt : ∑ j, a j = d ∧ Twist.negSupp n a ⊆ Idx.img n t
    · have hns : Twist.negSupp n a ⊆ {t.1 0} := by
        rw [← Twist.img_vtx (t.1 0), ← Twist.eq_vtx t]; exact hokt.2
      have hne : Twist.negSupp n a ≠ ∅ := fun h => hok ⟨hokt.1, h⟩
      obtain ⟨k, hk⟩ : ∃ k : Fin (n + 1), k ≠ t.1 0 :=
        Fintype.exists_ne_of_one_lt_card (by rw [Fintype.card_fin]; omega) (t.1 0)
      rw [Twist.eq_vtx t, Twist.ker_edge R d hf (t.1 0) k,
        Twist.coeff_of_not]
      rw [Twist.img_vtx]
      exact fun h => hk ((Finset.mem_singleton.mp
        (h (Finset.nonempty_iff_ne_empty.mpr hne).choose_spec)).symm.trans
        (Finset.mem_singleton.mp (hns (Finset.nonempty_iff_ne_empty.mpr hne).choose_spec)))
    · rw [Twist.coeff, dite_eq_right hokt]


end HodgeLean.Foundations.Program.G32Native
