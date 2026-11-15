import HodgeLean.Foundations.Program.SchoenTransferJ12CurveSubfamilyZero

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- A repeated source assignment has zero pairing with a cup containing every curve coordinate once.
Source: the three factors in the repeated curve coordinate and its top-degree bound. -/
theorem s4_selected_curve_assignment_pair_zero
    (Y T : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    [IsIntegral T.left] [Smooth T.hom] [IsProjective T.hom]
    (hdim : TopologicalSpace.dim Y.left = 1) (n : ℕ) (f : Fin n → (T ⟶ Y))
    (a : Fin n → Fin n) (ha : ¬ Function.Injective a) (b v : Fin n → HQ Y 1) :
    (cupProductOf T).cup rfl
      ((cupProductOf T).cupMulti n (fun i => homPullback (f i) 1 (b i)))
      ((cupProductOf T).cupMulti n (fun i => homPullback (f (a i)) 1 (v i))) =
      (0 : HQ T (n + n)) := by
  classical
  obtain ⟨i, j, hij, hne⟩ : ∃ i j, a i = a j ∧ i ≠ j := by
    simpa only [Function.Injective, not_forall, not_imp, exists_prop] using ha
  let c : Fin (n + n) → HQ T 1 := Fin.append
    (fun i => homPullback (f i) 1 (b i))
    (fun i => homPullback (f (a i)) 1 (v i))
  let e : Fin 3 → Fin (n + n) := ![Fin.castAdd n (a i), Fin.natAdd n i, Fin.natAdd n j]
  have he : Function.Injective e := by
    intro r s hrs
    fin_cases r <;> fin_cases s <;> simp_all [e, Fin.ext_iff] <;> omega
  have hv (r : Fin 3) : c (e r) =
      homPullback (f (a i)) 1 (![b (a i), v i, v j] r) := by
    fin_cases r
    · exact Fin.append_left _ _ (a i)
    · exact Fin.append_right _ _ i
    · change c (Fin.natAdd n j) = homPullback (f (a i)) 1 (v j)
      have hh := Fin.append_right
        (fun i => homPullback (f i) 1 (b i))
        (fun i => homPullback (f (a i)) 1 (v i)) j
      exact hh.trans (by rw [hij])
  have hz := s4_selected_curve_subfamily_zero Y T hdim 3 (n + n) (by omega)
    e he (f (a i)) ![b (a i), v i, v j] c hv
  rw [(cupProductOf T).cupMulti_append n
    (fun i => homPullback (f (a i)) 1 (v i)) n
    (fun i => homPullback (f i) 1 (b i)) (n + n) rfl c
    (fun i => Fin.append_left _ _ i) (fun i => Fin.append_right _ _ i)] at hz
  exact hz

#print axioms s4_selected_curve_assignment_pair_zero
end HodgeLean.Foundations.Program
