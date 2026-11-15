module

public import Mathlib

/-! # Kato's criterion: finite kernel and finite algebraic cokernel give a Fredholm operator

Following Kato, *Perturbation Theory for Linear Operators*, IV §5.1: pick an algebraic
complement `C` of `range T` (finite-dimensional), and let `S : E × C → F`, `(x, c) ↦ T x + c`.
`S` is a bounded surjection between Banach spaces with kernel inside `ker T × 0`, hence Fredholm
by the open mapping theorem; then `T = S ∘ inl` with `inl` Fredholm.
-/

@[expose] public noncomputable section

open Set Filter Topology Module

namespace HodgeLean.Foundations

theorem b63r_kato_isFredholm {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (T : E →L[ℂ] F) (hker : FiniteDimensional ℂ T.ker)
    (hcoker : T.range.CoFG) :
    T.IsFredholm := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.range (T : E →ₗ[ℂ] F))
  have : FiniteDimensional ℂ C :=
    Module.Finite.iff_fg.mpr (Submodule.CoFG.fg_of_isCompl hC hcoker)
  have : CompleteSpace C := FiniteDimensional.complete ℂ C
  let S : E × C →L[ℂ] F := T.comp (ContinuousLinearMap.fst ℂ E C) +
    C.subtypeL.comp (ContinuousLinearMap.snd ℂ E C)
  have hS : ∀ p : E × C, S p = T p.1 + (p.2 : F) := fun p => rfl
  have hSsurj : Function.Surjective S := by
    intro y
    have hy : y ∈ LinearMap.range (T : E →ₗ[ℂ] F) ⊔ C := by rw [hC.sup_eq_top]; trivial
    obtain ⟨a, ⟨x, rfl⟩, c, hc, rfl⟩ := Submodule.mem_sup.mp hy
    exact ⟨(x, ⟨c, hc⟩), rfl⟩
  have hkerS : (S : E × C →ₗ[ℂ] F).ker ≤
      Submodule.map (LinearMap.inl ℂ E C) (T : E →ₗ[ℂ] F).ker := by
    rintro ⟨x, c⟩ h
    have h0 : T x + (c : F) = 0 := h
    have hc : (c : F) ∈ LinearMap.range (T : E →ₗ[ℂ] F) :=
      ⟨-x, by simp [eq_neg_of_add_eq_zero_right h0]⟩
    have hc0 : (c : F) = 0 := by
      have := hC.disjoint.le_bot ⟨hc, c.2⟩
      simpa using this
    have hc0' : c = 0 := Subtype.ext hc0
    subst hc0'
    refine ⟨x, ?_, rfl⟩
    simpa using h0
  have : FiniteDimensional ℂ (S : E × C →ₗ[ℂ] F).ker :=
    Submodule.finiteDimensional_of_le hkerS
  have hSF : S.IsFredholm :=
    (hSsurj.isFredholm_iff S).mpr ⟨S.isQuotientMap hSsurj,
      Submodule.ClosedComplemented.of_finiteDimensional _, inferInstance⟩
  have hinl : (ContinuousLinearMap.inl ℂ E C).IsFredholm := by
    refine Topology.IsClosedEmbedding.isFredholm ?_ ?_
    · refine ⟨isEmbedding_prodMkLeft (0 : C), ?_⟩
      have : Set.range (fun x : E => (x, (0 : C))) = Set.univ ×ˢ {0} := by
        ext ⟨a, b⟩; simp [eq_comm]
      change IsClosed (Set.range (fun x : E => (x, (0 : C))))
      rw [this]
      exact (isClosed_univ (X := E)).prod (isClosed_singleton (x := (0 : C)))
    · change (LinearMap.range (LinearMap.inl ℂ E C)).CoFG
      rw [LinearMap.range_inl]
      exact Submodule.range_fg_iff_ker_cofg.mp (IsNoetherian.noetherian _)
  have hT : T = S.comp (ContinuousLinearMap.inl ℂ E C) := by
    ext x; simp [hS]
  rw [hT]
  exact hSF.comp hinl

end HodgeLean.Foundations
