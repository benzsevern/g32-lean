import HodgeLean.Foundations.Program.SchoenTowerL1bEarlierMaps

namespace HodgeLean.Foundations.Program
open CategoryTheory

/-- The maps retained by any two final tower charts coincide at every
original stage when their transition squares and final identity agree. -/
theorem s2e_c1_earlier_maps_unique
    {C : Type*} [Category C] {r : ℕ} (X : Fin (r + 1) → C)
    (b : ∀ i : Fin r, X i.succ ⟶ X i.castSucc)
    (c d : ∀ i, X (Fin.last r) ⟶ X i)
    (hc : c (Fin.last r) = 𝟙 _) (hd : d (Fin.last r) = 𝟙 _)
    (hbc : ∀ i : Fin r, c i.succ ≫ b i = c i.castSucc)
    (hbd : ∀ i : Fin r, d i.succ ≫ b i = d i.castSucc) : c = d := by
  funext i
  apply Fin.reverseInduction (motive := fun i => c i = d i) ?_ ?_ i
  · exact hc.trans hd.symm
  · intro j ih
    rw [← hbc j, ← hbd j, ih]

end HodgeLean.Foundations.Program
