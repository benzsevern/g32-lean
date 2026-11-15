import HodgeLean.Foundations.Program.G32Native.TensorFrameEquiv
import HodgeLean.Ported.NYLL.SchemeTheory.ProjectiveSpace.TwistingSheafGlobalGeneration

/-! Finite global twisted sections with generating normalized coordinates on every standard chart. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.ProjSpace
namespace HodgeLean.Foundations.Program

attribute [local instance] MvPolynomial.gradedAlgebra

/-- One finite list of twisted global sections gives generators on each standard chart after normalization. -/
theorem g32l4_projective_twisted_generators
    (R : Type) [CommRing R] (n : ℕ)
    (F : (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).Modules)
    [F.IsQuasicoherent] [SheafOfModules.IsFiniteType F] :
    ∃ d m : ℕ,
      ∃ t : Fin (m + 1) → Γ(F ⊗ (twistingSheaf R n).tensorPow d, ⊤),
      ∃ g : ∀ i : Fin (n + 1), Fin (m + 1) → Γ(F, standardOpen R n i),
        (∀ i, Submodule.span Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R),
          standardOpen R n i) (Set.range (g i)) = ⊤) ∧
        ∀ i k, (F ⊗ (twistingSheaf R n).tensorPow d).presheaf.map
            (homOfLE (le_top : standardOpen R n i ≤ ⊤)).op (t k) =
          tensorSections (g i k) (((twistingSheaf R n).tensorPow d).presheaf.map
            (homOfLE (le_top : standardOpen R n i ≤ ⊤)).op
              (tensorPowSection (twistingCoordinateSection R n i) d)) := by
  classical
  obtain ⟨r, s, hs, N, hN⟩ := exists_finite_generators_twisting_extensions R n F
  obtain ⟨z, hz⟩ := hN N le_rfl
  let K := Σ i : Fin (n + 1), Fin (r i)
  let e : Option K ≃ Fin (Fintype.card K + 1) := Fintype.equivFinOfCardEq (by simp)
  let L := (twistingSheaf R n).tensorPow N
  let M := F ⊗ L
  let t : Fin (Fintype.card K + 1) → Γ(M, ⊤) :=
    fun k => (e.symm k).elim 0 (fun a => z a.1 a.2)
  let l (i : Fin (n + 1)) := g32l4_tensorFrameEquiv F L
    (tensorPowSection (twistingCoordinateSection R n i) N) (standardOpen R n i)
    ((isFrameOn_twistingCoordinateSection R n i).tensorPowSection_monoidalV2 N)
  let g (i : Fin (n + 1)) (k : Fin (Fintype.card K + 1)) :=
    (l i).symm (M.presheaf.map (homOfLE (le_top : standardOpen R n i ≤ ⊤)).op (t k))
  have hself (i : Fin (n + 1)) (a : Fin (r i)) :
      g i (e (some ⟨i, a⟩)) = s i a := by
    apply (l i).injective
    dsimp only [g]
    rw [LinearEquiv.apply_symm_apply]
    have ht : t (e (some ⟨i, a⟩)) = z i a := by
      dsimp only [t]
      rw [Equiv.symm_apply_apply]
      rfl
    rw [ht]
    exact hz i a
  refine ⟨N, Fintype.card K, t, g, ?_, ?_⟩
  · intro i
    apply top_unique
    rw [← hs i]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    rw [← hself i a]
    exact Submodule.subset_span (Set.mem_range_self (e (some ⟨i, a⟩)))
  · intro i k
    exact ((l i).apply_symm_apply
      (M.presheaf.map (homOfLE (le_top : standardOpen R n i ≤ ⊤)).op (t k))).symm

end HodgeLean.Foundations.Program
