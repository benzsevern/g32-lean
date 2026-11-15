import HodgeLean.Foundations.Program.G32Native.TypeIIISkewBasis

noncomputable section
open Module
namespace HodgeLean.Foundations.Program.G32Native

/-- The full form is the diagonal quaternionic sum in an orthogonal basis. -/
theorem typeIII_skew_basis_expansion {D V I : Type*} [DivisionRing D] [StarRing D]
    [AddCommGroup V] [Module D V] [Fintype I] [DecidableEq I]
    (H : V → V → D)
    (haddL : ∀ v w x, H (v + w) x = H v x + H w x)
    (haddR : ∀ v w x, H v (w + x) = H v w + H v x)
    (hsmulL : ∀ (q : D) v x, H (q • v) x = q * H v x)
    (hsmulR : ∀ (q : D) v x, H v (q • x) = H v x * star q)
    (e : Basis I D V) (horth : ∀ i j, i ≠ j → H (e i) (e j) = 0) (x y : V) :
    H x y = ∑ i, e.equivFun x i * H (e i) (e i) * star (e.equivFun y i) := by
  classical
  have hzL (v : V) : H 0 v = 0 := by
    simpa only [zero_smul, zero_mul] using hsmulL 0 v v
  have hzR (v : V) : H v 0 = 0 := by
    simpa only [zero_smul, star_zero, mul_zero] using hsmulR 0 v v
  have hsumL (s : Finset I) (v : I → V) (w : V) :
      H (s.sum v) w = s.sum (fun i => H (v i) w) := by
    induction s using Finset.induction_on with
    | empty => simp [hzL]
    | @insert a s ha ih => simp only [Finset.sum_insert ha, haddL, ih]
  have hsumR (s : Finset I) (v : V) (w : I → V) :
      H v (s.sum w) = s.sum (fun i => H v (w i)) := by
    induction s using Finset.induction_on with
    | empty => simp [hzR]
    | @insert a s ha ih => simp only [Finset.sum_insert ha, haddR, ih]
  conv_lhs => rw [← e.sum_repr x, ← e.sum_repr y]
  rw [hsumL]
  simp_rw [hsumR, hsmulL, hsmulR]
  simp only [Basis.equivFun_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · exact (mul_assoc _ _ _).symm
  · intro j _ hij
    rw [horth i j (Ne.symm hij), zero_mul, mul_zero]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.typeIII_skew_basis_expansion
