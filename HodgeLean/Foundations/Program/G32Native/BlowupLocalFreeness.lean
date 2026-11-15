import HodgeLean.Ported.Hironaka.Scheme.BlowUp.Glue.Global
import HodgeLean.Foundations.Program.SchoenCycleCartierAlgebra

/-! # The native local-freeness test and global scheme blowups
HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The native rank-one test is equivalent to invertibility of an ideal sheaf. -/
theorem g32t5_isInvertible_iff_local_free {X : Scheme} (I : X.IdealSheafData) :
    I.IsInvertible ↔ ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      Nonempty ((I.ideal U) ≃ₗ[Γ(X, U)] Γ(X, U)) := by
  constructor
  · intro h x
    obtain ⟨U, hx, a, ha, hI⟩ := h x
    refine ⟨U, hx, ?_⟩
    rw [hI]
    have hr := (isRegular_iff_mem_nonZeroDivisors.mpr ha).right
    exact ⟨((LinearEquiv.ofInjective (LinearMap.toSpanSingleton _ _ a) hr).trans
      (LinearEquiv.ofEq _ _ (LinearMap.range_toSpanSingleton a))).symm⟩
  · intro h x
    obtain ⟨U, hx, ⟨e⟩⟩ := h x
    obtain ⟨a, hI, hr⟩ := s2e_free_ideal_regular_generator (I.ideal U) e
    refine ⟨U, hx, a, isRegular_iff_mem_nonZeroDivisors.mp ?_, hI⟩
    exact ⟨fun b c hbc => hr (by simpa only [mul_comm] using hbc), hr⟩

/-- The actual global blowup satisfies both native clauses over a specified base. -/
theorem g32t5_blowup_over {S : Scheme} (B : Over S) (K : B.left.IdealSheafData) :
    let X : Over S := Over.mk (K.blowUpπ ≫ B.hom)
    let b : X ⟶ B := Over.homMk K.blowUpπ
    (∀ x : X.left, ∃ U : X.left.affineOpens, x ∈ U.1 ∧
      Nonempty (((K.comap b.left).ideal U) ≃ₗ[Γ(X.left, U)] Γ(X.left, U))) ∧
    (∀ (T : Over S) (f : T ⟶ B),
      (∀ x : T.left, ∃ U : T.left.affineOpens, x ∈ U.1 ∧
        Nonempty (((K.comap f.left).ideal U) ≃ₗ[Γ(T.left, U)] Γ(T.left, U))) →
      ∃! u : T ⟶ X, u ≫ b = f) := by
  dsimp only
  constructor
  · exact (g32t5_isInvertible_iff_local_free _).mp
      (Scheme.IdealSheafData.blowUp.isInvertible_comap_π K)
  · intro T f hf
    obtain ⟨u, hu, huniq⟩ := Scheme.IdealSheafData.blowUp.existsUnique_lift K f.left
      ((g32t5_isInvertible_iff_local_free _).mpr hf)
    have hw : u ≫ (K.blowUpπ ≫ B.hom) = T.hom := by
      rw [← Category.assoc, hu, Over.w f]
    refine ⟨Over.homMk u hw, ?_, ?_⟩
    · apply Over.OverMorphism.ext
      exact hu
    · intro v hv
      apply Over.OverMorphism.ext
      apply huniq v.left
      exact congrArg (fun g => g.left) hv

end HodgeLean.Foundations.Program
