import HodgeLean.Foundations.AlgebraicTopology.Singular.PuncturedPlaneLoop
import HodgeLean.Foundations.Program.SchoenTowerL1bActionWindingChains
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cPeriods
import Mathlib.Analysis.Normed.Module.Connected

noncomputable section
set_option maxHeartbeats 200000
open Set Topology CategoryTheory AlgebraicTopology AlgebraicTopology.Singular HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Every punctured-plane circle map has a continuous logarithmic lift on
its real covering line and a constant integral deck coefficient. -/
theorem s2v_l1b_action_circle_lift_exists
    (p : C(UnitAddCircle, {z : ℂ // z ≠ 0})) :
    ∃ L : ℝ → ℂ, Continuous L ∧
      (∀ s : ℝ, Complex.exp (L s) = (p (s : UnitAddCircle)).val) ∧
      ∃ k : ℤ, ∀ s : ℝ,
        L (s + 1) = L s + (k : ℂ) * (2 * Real.pi * Complex.I) := by
  let g : ℝ → ℂ := fun s => (p (s : UnitAddCircle)).val
  have hg : Continuous g := continuous_subtype_val.comp
    (p.continuous.comp (AddCircle.continuous_mk' 1))
  letI : ContractibleSpace (univ : Set ℝ) :=
    (convex_univ : Convex ℝ (univ : Set ℝ)).contractibleSpace univ_nonempty
  have hs : IsSimplyConnected (univ : Set ℝ) := by
    change SimplyConnectedSpace (univ : Set ℝ)
    infer_instance
  obtain ⟨L, hL, he⟩ := Complex.exists_continuousOn_eqOn_exp_comp hs isOpen_univ
    hg.continuousOn (by
      rintro ⟨s, _, hs⟩
      exact (p (s : UnitAddCircle)).property hs)
  have hLc : Continuous L := continuousOn_univ.mp hL
  have hp (s : ℝ) : Complex.exp (L s) = (p (s : UnitAddCircle)).val := he (mem_univ s)
  refine ⟨L, hLc, hp, ?_⟩
  apply s2v_l1b_action_log_lifts_differ_int (fun s : ℝ => L (s + 1)) L
    (hLc.comp (continuous_id.add continuous_const)) hLc _ 0
  intro s
  rw [hp, hp, AddCircle.coe_add_period]

/-- A specified logarithmic deck increment computes the integral class of
its punctured-plane circle map. -/
theorem s2v_l1b_action_circle_loop_class_of_lift
    (p : C(UnitAddCircle, {z : ℂ // z ≠ 0}))
    (L : ℝ → ℂ) (hL : Continuous L)
    (hp : ∀ s : ℝ, Complex.exp (L s) = (p (s : UnitAddCircle)).val)
    (k : ℤ) (hk : ∀ s, L (s + 1) = L s + (k : ℂ) * (2 * Real.pi * Complex.I)) :
    ((SingularChainComplex ℤ (TopCat.of {z : ℂ // z ≠ 0})).sc 1).moduleCatHomologyClass
      (loopCycle ℤ p) =
    k • ((SingularChainComplex ℤ (TopCat.of {z : ℂ // z ≠ 0})).sc 1).moduleCatHomologyClass
      (loopCycle ℤ (s2v_l1b_action_windingCircleMap 0 1)) := by
  exact PuncturedPlane.loopClass_of_lift p L hL hp k hk

/-- Changing the initial logarithm of a winding circle leaves its integral
homology coefficient unchanged. -/
theorem s2v_l1b_action_winding_circle_class (c : ℂ) (k : ℤ) :
    ((SingularChainComplex ℤ (TopCat.of {z : ℂ // z ≠ 0})).sc 1).moduleCatHomologyClass
      (loopCycle ℤ (s2v_l1b_action_windingCircleMap c k)) =
    k • ((SingularChainComplex ℤ (TopCat.of {z : ℂ // z ≠ 0})).sc 1).moduleCatHomologyClass
      (loopCycle ℤ (s2v_l1b_action_windingCircleMap 0 1)) := by
  apply s2v_l1b_action_circle_loop_class_of_lift (s2v_l1b_action_windingCircleMap c k)
    (fun s : ℝ => c + (s : ℂ) * ((k : ℂ) * (2 * Real.pi * Complex.I)))
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))
  · intro s
    rw [s2v_l1b_action_windingCircleMap_coe]
  · intro s
    rw [Complex.ofReal_add, Complex.ofReal_one, add_mul, one_mul, add_assoc]

/-- Every punctured-plane loop class is an integral multiple of the canonical
one-turn exponential loop class. -/
theorem s2v_l1b_action_circle_loop_class_exists
    (p : C(UnitAddCircle, {z : ℂ // z ≠ 0})) :
    ∃ k : ℤ,
      ((SingularChainComplex ℤ (TopCat.of {z : ℂ // z ≠ 0})).sc 1).moduleCatHomologyClass
        (loopCycle ℤ p) =
      k • ((SingularChainComplex ℤ (TopCat.of {z : ℂ // z ≠ 0})).sc 1).moduleCatHomologyClass
        (loopCycle ℤ (s2v_l1b_action_windingCircleMap 0 1)) := by
  obtain ⟨L, hL, hp, k, hk⟩ := s2v_l1b_action_circle_lift_exists p
  exact ⟨k, s2v_l1b_action_circle_loop_class_of_lift p L hL hp k hk⟩

/-- The canonical one-turn exponential loop generates integral H₁ of the
punctured plane. -/
theorem s2v_l1b_action_winding_class_smul_surjective :
    Function.Surjective (fun k : ℤ =>
      k • ((SingularChainComplex ℤ (TopCat.of {z : ℂ // z ≠ 0})).sc 1).moduleCatHomologyClass
        (loopCycle ℤ (s2v_l1b_action_windingCircleMap 0 1))) := by
  haveI : PathConnectedSpace {z : ℂ // z ≠ 0} := by
    change PathConnectedSpace ({(0 : ℂ)}ᶜ : Set ℂ)
    apply isPathConnected_iff_pathConnectedSpace.mp
    apply isPathConnected_compl_singleton_of_one_lt_rank
    rw [← Module.finrank_eq_rank, Complex.finrank_real_complex]
    norm_num
  intro a
  obtain ⟨p, rfl⟩ := b6m_continuous_loopClass_surjective {z : ℂ // z ≠ 0} a
  obtain ⟨k, hk⟩ := s2v_l1b_action_circle_loop_class_exists p
  exact ⟨k, hk.symm⟩

end HodgeLean.Foundations.Program
