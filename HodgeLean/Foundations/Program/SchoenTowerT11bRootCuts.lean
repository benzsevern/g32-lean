import HodgeLean.Foundations.Program.SchoenTowerT11bLineDecomposition
import HodgeLean.Foundations.Program.SchoenTowerT11bConnectedFibers

/-! Connected Boolean pieces cut out by finitely many real values.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A truth-pattern piece for the two comparisons with every cut is order connected.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, one-dimensional CAD step. -/
theorem s2v_t11b_root_cut_piece_preconnected {k : ℕ} (d : Fin k → ℝ)
    (s : Fin (k + k) → Bool) :
    IsPreconnected {t : ℝ | WithLp.toLp 2 (fun _ : Fin 1 => t) ∈
      (s2v_t11b_refinementFormula (s2v_t11b_rootCutTests d) s).realize} := by
  apply Set.OrdConnected.isPreconnected
  constructor
  intro a ha b hb t ht
  have ha' := (s2v_t11b_realize_refinementFormula _ s _).mp ha
  have hb' := (s2v_t11b_realize_refinementFormula _ s _).mp hb
  apply (s2v_t11b_realize_refinementFormula _ s _).mpr
  intro j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · have ha₁ := ha' (i.castAdd k)
    have hb₁ := hb' (i.castAdd k)
    simp only [s2v_t11b_rootCutTests_lower] at ha₁ hb₁ ⊢
    constructor
    · intro h
      exact (ha₁.mp h).trans ht.1
    · intro h
      apply hb₁.mpr
      exact h.trans ht.2
  · have ha₂ := ha' (Fin.natAdd k i)
    have hb₂ := hb' (Fin.natAdd k i)
    simp only [s2v_t11b_rootCutTests_upper] at ha₂ hb₂ ⊢
    constructor
    · intro h
      exact ht.2.trans (hb₂.mp h)
    · intro h
      apply ha₂.mpr
      exact ht.1.trans h

/-- A comparison piece meeting a cut consists of that single real value.
Source: Coste, Real Algebraic Sets (2005), Theorem 1.3, one-dimensional CAD step. -/
theorem s2v_t11b_root_cut_piece_at_cut {k : ℕ} (d : Fin k → ℝ)
    (s : Fin (k + k) → Bool) (i : Fin k)
    (hi : WithLp.toLp 2 (fun _ : Fin 1 => d i) ∈
      (s2v_t11b_refinementFormula (s2v_t11b_rootCutTests d) s).realize)
    (t : ℝ) (ht : WithLp.toLp 2 (fun _ : Fin 1 => t) ∈
      (s2v_t11b_refinementFormula (s2v_t11b_rootCutTests d) s).realize) : t = d i := by
  have hi' := (s2v_t11b_realize_refinementFormula _ s _).mp hi
  have ht' := (s2v_t11b_realize_refinementFormula _ s _).mp ht
  have hlo : d i ≤ t := (s2v_t11b_rootCutTests_lower d i t).mp
    ((ht' (i.castAdd k)).mp ((hi' (i.castAdd k)).mpr
      ((s2v_t11b_rootCutTests_lower d i (d i)).mpr le_rfl)))
  have hhi : t ≤ d i := (s2v_t11b_rootCutTests_upper d i t).mp
    ((ht' (Fin.natAdd k i)).mp ((hi' (Fin.natAdd k i)).mpr
      ((s2v_t11b_rootCutTests_upper d i (d i)).mpr le_rfl)))
  exact le_antisymm hhi hlo

end HodgeLean.Foundations.Program
