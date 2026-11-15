import HodgeLean.Foundations.Polarization

/-! # Rational evaluations span complex homogeneous multilinear diagonals -/

noncomputable section
namespace HodgeLean.Foundations

open SchurWeyl

variable {N : Type*} [AddCommGroup N] [Module ℂ N]

/-- Rational parameter evaluations span all complex evaluations of the diagonal
of a multilinear map. No continuity or algebraic closure argument is needed:
expand in the rational coordinate basis and polarize the symmetrized map. -/
theorem multilinear_diagonal_mem_span_rat {n m : ℕ}
    (f : MultilinearMap ℂ (fun _ : Fin n => Fin m → ℂ) N) (a : Fin m → ℂ) :
    f (fun _ => a) ∈ Submodule.span ℂ
      (Set.range (fun r : Fin m → ℚ => f (fun _ i => (r i : ℂ)))) := by
  classical
  let P := Submodule.span ℂ
    (Set.range (fun r : Fin m → ℚ => f (fun _ i => (r i : ℂ))))
  let b := Pi.basisFun ℂ (Fin m)
  let g : MultilinearMap ℂ (fun _ : Fin n => Fin m → ℂ) N :=
    ∑ σ : Equiv.Perm (Fin n), MultilinearMap.domDomCongr σ f
  have hg (x : Fin n → (Fin m → ℂ)) :
      g x = ∑ σ : Equiv.Perm (Fin n), f (fun i => x (σ i)) := by
    simp [g, MultilinearMap.domDomCongr]
  have hb (t : Fin n → Fin m) : g (fun i => b (t i)) ∈ P := by
    rw [hg, ← polarization f (fun i => b (t i))]
    apply Submodule.sum_mem
    intro s hs
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨∑ i ∈ s, (Pi.single (t i) 1 : Fin m → ℚ), ?_⟩
    apply congrArg f
    funext k j
    simp [b, Pi.basisFun_apply, Pi.single_apply]
  have ha : a = ∑ i, a i • b i := by
    simpa [b] using (b.sum_repr a).symm
  have hga : g (fun _ => a) ∈ P := by
    rw [ha, g.map_sum]
    apply Submodule.sum_mem
    intro t ht
    rw [g.map_smul_univ]
    exact P.smul_mem _ (hb t)
  have hc : g (fun _ => a) = (n.factorial : ℂ) • f (fun _ => a) := by
    simp [hg, Fintype.card_perm, Nat.cast_smul_eq_nsmul]
  rw [hc] at hga
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  simpa only [smul_smul, inv_mul_cancel₀ hn, one_smul] using
    P.smul_mem (n.factorial : ℂ)⁻¹ hga

end HodgeLean.Foundations
