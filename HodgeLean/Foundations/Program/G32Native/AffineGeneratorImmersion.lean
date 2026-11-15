import HodgeLean.Foundations.Analytic.AnalytificationChow3Charts

/-! Affine embeddings from specified algebra generators. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Specified algebra generators give an affine-space embedding over a compatible base. -/
theorem g32l4_affine_generator_closedImmersion {X S : Scheme.{0}} [IsAffine X] [IsAffine S]
    {R K : Type} [CommRing R] [Algebra R Γ(X, ⊤)] (s : X ⟶ S)
    (q : R →+* Γ(S, ⊤)) (hq : ∀ r, s.appTop.hom (q r) = algebraMap R Γ(X, ⊤) r)
    (v : K → Γ(X, ⊤)) (hv : Algebra.adjoin R (Set.range v) = ⊤) :
    IsClosedImmersion (AffineSpace.homOfVector s v) := by
  apply IsClosedImmersion.of_surjective_of_isAffine
  intro a
  let f := AffineSpace.homOfVector s v
  let B : Subalgebra R Γ(X, ⊤) := {
    f.appTop.hom.range with
    algebraMap_mem' := fun r => ⟨(𝔸(K; S) ↘ S).appTop (q r), by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, AffineSpace.homOfVector_over]
      exact hq r⟩ }
  have hB : Algebra.adjoin R (Set.range v) ≤ B := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨k, rfl⟩
    exact ⟨AffineSpace.coord S k, AffineSpace.homOfVector_appTop_coord s v k⟩
  exact hB (hv ▸ Algebra.mem_top)

end HodgeLean.Foundations.Program
