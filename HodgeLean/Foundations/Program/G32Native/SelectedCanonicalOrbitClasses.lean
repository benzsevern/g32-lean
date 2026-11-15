import HodgeLean.Foundations.Program.G32Native.CanonicalOrbitClasses
import HodgeLean.Foundations.Program.SchoenCycleC2ProjectiveCoheightHelpers

noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Program
open scoped BigOperators
namespace HodgeLean.Foundations.Program.G32Native

/-- The retained canonical component and inverse-orbit coordinates supply U09. -/
theorem selected_canonical_orbit_classes
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    [IsProjective W.hom]
    (ι : Q ⟶ W) [IsClosedImmersion ι.left]
    (d : W ⟶ W) (m k : ℕ) (hm : 0 < m) (hperiod : End.of d ^ m = 1)
    (hdis : ∀ s t : Fin m, s ≠ t → Disjoint
      (Set.range (ι ≫ (End.of d ^ s.val).asHom).left)
      (Set.range (ι ≫ (End.of d ^ t.val).asHom).left))
    {B : Over (Spec ↧ℂ)} [IsIntegral B.left] [Smooth B.hom]
    [Smooth Q.hom]
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (ℓ : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ B)
    [IsClosedImmersion ℓ.left]
    (β : W ⟶ B) [IsFinite β.left] [Etale β.left]
    (hd : d ≫ β = β) (hproj : ι ≫ β = eQ.hom ≫ ℓ)
    (hB : dim B.left = 2 * k)
    (c : s2e_supportedClass W (s2e_componentCycle ι ℚ) k)
    (hc : a3b4_IsCycleClass W.hom (s2e_componentCycle ι ℚ) k c)
    (a : Fin (Nat.totient m) → Fin m → ℚ)
    (v : Fin (Nat.totient m) → AlgebraicTopology.Singular.Cohomology ℚ
      (TopCat.of (ComplexPoint W)) (2 * k))
    (hv : ∀ j, ∑ t : Fin m, a j t •
      s2e_pullback ℚ (End.of d ^ (m - t.val)).asHom (2 * k)
        (s2e_classToAbsolute W (s2e_componentCycle ι ℚ) k c) = v j) :
    ∀ j,
      let γ := s2e_rationalOrbitCycle ι d m (a j)
      (∀ x ∈ γ.support, Order.coheight x = k) ∧
      ∃ cj, a3b4_IsCycleClass W.hom γ k cj ∧
        AlgebraicTopology.Singular.relativeCohomologyToAbsolute ℚ _ _ cj = v j := by
  letI : Smooth W.hom := by
    rw [← Over.w β]
    infer_instance
  have hcodim : ∀ x ∈ (s2e_componentCycle ι ℚ).support, Order.coheight x = k := by
    have hh := s2e_projective_orbit_component_coheight k eQ ℓ ι d β hd hproj
      ⊤ (by intro x hx; trivial) (by infer_instance) (by infer_instance) hB 0
    simpa only [pow_zero, End.one_asHom, Category.comp_id] using hh
  exact canonical_orbit_classes ι d m k hm hperiod hdis hcodim c hc a v hv

#print axioms selected_canonical_orbit_classes
end HodgeLean.Foundations.Program.G32Native
