import HodgeLean.Foundations.Program.SchoenTowerHardtCad5SectionTuples
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5Relations

/-! Boolean base loci for actual tuples of supplied root sections. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_section_tuple_membership_formula {n q r : ℕ}
    (C : s2v_t11b_Formula n) (ψ : Fin r → C.realize → ℝ)
    (g : Fin r → s2v_t11b_Formula (n + 1))
    (hg : ∀ j y, y ∈ (g j).realize ↔ ∃ a : C.realize,
      (∀ v, y v.succ = a.val v) ∧ y 0 = ψ j a)
    (S : s2v_t11b_Formula (q + n)) (f : Fin q → Fin r) :
    ∃ M : s2v_t11b_Formula n, ∀ a : C.realize,
      a.val ∈ M.realize ↔ WithLp.toLp 2
        (Fin.append (fun i => ψ (f i) a) (fun i => a.val i)) ∈ S.realize := by
  obtain ⟨H, hH⟩ := s2v_hardt_cad5_section_tuple_formula C ψ g hg f
  obtain ⟨M, hM⟩ := s2v_hardt_cad5_block_projection_formula (.inter S H)
  refine ⟨M, ?_⟩
  intro a
  rw [hM]
  constructor
  · rintro ⟨t, htS, htH⟩
    obtain ⟨ha, hcoords⟩ := (hH t a.val).mp htH
    have ht : t = WithLp.toLp 2 (fun i => ψ (f i) a) := by
      ext i
      exact hcoords i
    simpa only [ht] using htS
  · intro hs
    exact ⟨WithLp.toLp 2 (fun i => ψ (f i) a), hs,
      (hH _ a.val).mpr ⟨a.property, fun _ => rfl⟩⟩

end HodgeLean.Foundations.Program
