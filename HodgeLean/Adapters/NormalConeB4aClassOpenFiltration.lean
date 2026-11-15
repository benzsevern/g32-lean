import HodgeLean.Adapters.NormalConeB4aClassLocalGlobal
import HodgeConjecture.Definitions.AlgebraicTopology.Support.NeighborhoodPairImage

/-! # Finite support vanishing on analytic opens

Route: restrict the filtration to an open subspace. Ambient cofinal local
calculations pull back through its open embedding, and finite support
localization applies in that subspace.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory Limits AlgebraicTopology.Singular TopologicalSpace Topology

set_option backward.isDefEq.respectTransparency false in
/-- Local lower vanishing on every regular layer detects vanishing on any open
subspace satisfying the section-comparison hypotheses. -/
theorem a3b4a_classRelative_vanishing_onOpen_of_finite_localFiltration
    (X : TopCat.{0}) [T2Space X] (U : Opens X)
    [∀ V : Opens U, ParacompactSpace V]
    (S : ℕ → Closeds X) (hS : Antitone S) (N : ℕ) (hN : S N = ⊥) (n : ℕ)
    (hlocal : ∀ k, k < N → ∀ j : ℕ, j ≤ n → ∀ x : X, x ∉ S (k + 1) →
      ∀ V : Opens X, x ∈ V → ∃ W : Opens X, W ≤ V ∧ x ∈ W ∧
        IsZero (RelativeCohomology ℚ (neighborhoodSupportComplementPair (W : Set X) (S k)) j)) :
    IsZero (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (U : Set X) (S 0)) n) := by
  let Y := TopCat.of U
  let f : Y → X := Subtype.val
  have hf : IsOpenEmbedding f := U.isOpen.isOpenEmbedding_subtypeVal
  let T : ℕ → Closeds Y := fun k => (S k).preimage hf.continuous
  have hT : Antitone T := fun i j hij x hx => hS hij hx
  have hN' : T N = ⊥ := by simp [T, hN]; rfl
  have hzero := a3b4a_classRelative_vanishing_of_finiteFiltration Y T hT N hN' n
  have hzero' : IsZero (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (Set.univ : Set Y) (T 0)) n) := by
    apply hzero
    intro k hk
    apply a3b4a_classRelative_vanishing_of_cofinal_local_vanishing
    intro j hj x hx V hxV
    let V' : Opens X := ⟨f '' (V : Set Y), hf.isOpenMap _ V.isOpen⟩
    obtain ⟨W, hWV, hxW, hW⟩ := hlocal k hk j hj (f x) hx V' ⟨x, hxV, rfl⟩
    let W' : Opens Y := ⟨f ⁻¹' (W : Set X), W.isOpen.preimage hf.continuous⟩
    have hW' : f '' (W' : Set Y) = (W : Set X) := by
      apply Set.Subset.antisymm
      · rintro _ ⟨y, hy, rfl⟩; exact hy
      · intro y hy
        obtain ⟨x, hx, rfl⟩ := hWV hy
        exact ⟨x, hy, rfl⟩
    refine ⟨W', ?_, hxW, ?_⟩
    · intro y hy
      obtain ⟨z, hz, he⟩ := hWV hy
      exact hf.injective he ▸ hz
    · have hWimage : IsZero (RelativeCohomology ℚ
          (neighborhoodSupportComplementPair (f '' (W' : Set Y)) (S k)) j) := by
        rw [hW']
        exact hW
      exact hWimage.of_iso (neighborhoodSupportPairImageCohomologyIso f hf.isEmbedding
        W' (T k) (S k) (fun _ _ => Iff.rfl) j).symm
  have himage : f '' (Set.univ : Set Y) = (U : Set X) := by
    ext x
    simp [f, Y]
  have hout := hzero'.of_iso (neighborhoodSupportPairImageCohomologyIso f hf.isEmbedding
    Set.univ (T 0) (S 0) (fun _ _ => Iff.rfl) n)
  rw [himage] at hout
  exact hout

end HodgeLean.Adapters
