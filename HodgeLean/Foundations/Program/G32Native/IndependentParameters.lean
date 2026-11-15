import HodgeLean.Ported.Hironaka.Algebra.RegularSmooth.QuotientRegular
import HodgeLean.Ported.Hironaka.Algebra.Local.Defs

/-! Extend independent branch equations to local parameters. -/
noncomputable section
set_option maxHeartbeats 400000
open IsLocalRing
namespace HodgeLean.Foundations.Program

/-- Independent classes of labelled equations in the cotangent space extend to parameters. -/
theorem g32l4_extend_independent_parameters
    {R : Type*} [CommRing R] [IsRegularLocalRing R]
    {ι : Type*} [Fintype ι] (f : ι → R)
    (hf : ∀ i, f i ∈ maximalIdeal R)
    (hli : LinearIndependent (ResidueField R)
      (fun i => (maximalIdeal R).toCotangent ⟨f i, hf i⟩)) :
    ∃ (n : ℕ) (z : Fin n → R) (c : ι ↪ Fin n),
      IsRegularSystemOfParameters z ∧ ∀ i, z (c i) = f i := by
  classical
  let b := Module.Basis.sumExtend hli
  have hfin := Module.Finite.finite_basis b
  have : Finite (Module.Basis.sumExtendIndex hli) :=
    Finite.of_injective (Sum.inr : Module.Basis.sumExtendIndex hli → ι ⊕ _)
      Sum.inr_injective
  letI : Fintype (Module.Basis.sumExtendIndex hli) := Fintype.ofFinite _
  have hb : ∀ i, b (Sum.inl i) = (maximalIdeal R).toCotangent ⟨f i, hf i⟩ := by
    intro i
    dsimp only [b]
    unfold Module.Basis.sumExtend
    rw [Module.Basis.reindex_apply, Module.Basis.extend_apply_self]
    rfl
  choose y hy using fun j : Module.Basis.sumExtendIndex hli =>
    (maximalIdeal R).toCotangent_surjective (b (Sum.inr j))
  let g : ι ⊕ Module.Basis.sumExtendIndex hli → maximalIdeal R :=
    Sum.elim (fun i => ⟨f i, hf i⟩) y
  have hg : (maximalIdeal R).toCotangent ∘ g = b := by
    funext s
    cases s with
    | inl i => exact (hb i).symm
    | inr j => exact hy j
  have hspan : Submodule.span R (Set.range g) = ⊤ := by
    rw [← CotangentSpace.span_image_eq_top_iff, ← Set.range_comp, hg]
    exact b.span_eq
  have hm : Ideal.span (Set.range (fun s => (g s : R))) = maximalIdeal R := by
    have h := congrArg (Submodule.map (maximalIdeal R).subtype) hspan
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype,
      ← Set.range_comp] at h
    exact h
  let e := Fintype.equivFin (ι ⊕ Module.Basis.sumExtendIndex hli)
  let z : Fin (Fintype.card (ι ⊕ Module.Basis.sumExtendIndex hli)) → R :=
    fun k => g (e.symm k)
  let c : ι ↪ Fin (Fintype.card (ι ⊕ Module.Basis.sumExtendIndex hli)) :=
    ⟨fun i => e (Sum.inl i), e.injective.comp Sum.inl_injective⟩
  refine ⟨_, z, c, ⟨?_, ?_⟩, ?_⟩
  · have hz : Set.range z = Set.range (fun s => (g s : R)) := by
      exact e.symm.surjective.range_comp (fun s => (g s : R))
    rw [hz]
    exact hm
  · rw [← IsRegularLocalRing.spanFinrank_maximalIdeal,
      spanFinrank_maximalIdeal_eq_finrank_cotangentSpace,
      Module.finrank_eq_card_basis b]
  · intro i
    dsimp only [z, c, Function.Embedding.coeFn_mk]
    rw [e.symm_apply_apply]
    rfl

end HodgeLean.Foundations.Program
