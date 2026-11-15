import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

noncomputable section
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour

theorem basis_of_spanning_range {k V T : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
    [Module.Finite k V] (d : T → V) (hd : Submodule.span k (Set.range d) = ⊤) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) k V) (w : Fin n → T), ∀ i, b i = d (w i) := by
  classical
  obtain ⟨f, hf, hspan, hlin⟩ := Submodule.exists_fun_fin_finrank_span_eq k (Set.range d)
  choose w hw using hf
  have htop : ⊤ ≤ Submodule.span k (Set.range f) := by rw [hspan, hd]
  refine ⟨_, Module.Basis.mk hlin htop, w, ?_⟩
  intro i
  exact (Module.Basis.mk_apply hlin htop i).trans (hw i).symm

end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
