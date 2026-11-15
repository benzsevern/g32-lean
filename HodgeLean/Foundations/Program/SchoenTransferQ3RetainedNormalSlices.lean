import HodgeLean.Foundations.Program.SchoenTransferQ3RetainedSmoothBase
import HodgeLean.Foundations.Program.SchoenTransferQ3CartesianSlices

/-! Actual finite flat smooth normal slices of the common tangential morphism. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open TopologicalSpace Topology HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The actual common tangential morphism supplies finite flat maps between
smooth cartesian slices over every complex point of a common dense base open. -/
theorem s4_q3_retained_generic_normal_slices_finite_flat
    {C D X W : Over (Spec ↧ℂ)} (r : ℕ) [SmoothOfRelativeDimension r D.hom]
    [IsIntegral X.left] [Smooth X.hom] [IsIntegral W.left] [Smooth W.hom]
    (f : C ⟶ D) [Etale f.left] (i : C ⟶ X) (j : D ⟶ W)
    [IsClosedImmersion j.left] (q : X ⟶ W) [IsFinite q.left] [Surjective q.left]
    (hsquare : i ≫ q = f ≫ j) (p : C.left) :
    ∃ (U : W.left.Opens) (_ : IsAffineOpen U) (_ : j.left (f.left p) ∈ U)
      (g : Fin r → Γ(W.left, U)) (V : D.left.Opens) (_ : f.left p ∈ V)
      (hVU : V ≤ j.left ⁻¹ᵁ U)
      (hCi : f.left ⁻¹ᵁ V ≤ i.left ⁻¹ᵁ (q.left ⁻¹ᵁ U))
      (A : (ComplexPoint.complexAffineSpace (Fin r)).Opens),
      Dense (A : Set (ComplexPoint.complexAffineSpace (Fin r))) ∧
      let h := s4_q3_tangentialCoordinateMorphism W U r g
      Etale (j.left.resLE U V hVU ≫ h) ∧
      Etale (i.left.resLE (q.left ⁻¹ᵁ U) (f.left ⁻¹ᵁ V) hCi ≫ (q.left ∣_ U) ≫ h) ∧
      let hA := h ∣_ A
      let qA := (q.left ∣_ U) ∣_ (h ⁻¹ᵁ A)
      ∀ t : Spec ↧ℂ ⟶ A.toScheme,
        IsFinite (pullback.snd qA (pullback.fst hA t)) ∧
          Flat (pullback.snd qA (pullback.fst hA t)) ∧
          Smooth (pullback.snd hA t) ∧
          Smooth (pullback.snd qA (pullback.fst hA t) ≫ pullback.snd hA t) := by
  obtain ⟨U, hU, hpU, g, V, hpV, hVU, hCi, ht, hs, _, _, A, hA, hsW, hsX⟩ :=
    s4_q3_retained_shared_smooth_tangential_base r f i j q hsquare p
  let h := s4_q3_tangentialCoordinateMorphism W U r g
  letI : Flat q.left := IntersectionProductScaf_finite_smooth_flat X W q
  letI : Smooth (h ∣_ A) := hsW
  have hcomp : Smooth (((q.left ∣_ U) ∣_ (h ⁻¹ᵁ A)) ≫ (h ∣_ A)) := by
    rw [← morphismRestrict_comp]
    exact hsX
  letI := hcomp
  refine ⟨U, hU, hpU, g, V, hpV, hVU, hCi, A, hA, ht, hs, ?_⟩
  dsimp only
  intro t
  exact s4_q3_cartesian_slices_finite_flat_of_smooth
    ((q.left ∣_ U) ∣_ (h ⁻¹ᵁ A)) (h ∣_ A) t

end HodgeLean.Foundations.Program
