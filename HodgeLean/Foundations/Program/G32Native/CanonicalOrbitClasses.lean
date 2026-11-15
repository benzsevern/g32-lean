import HodgeLean.Foundations.Program.SchoenCycleC2OrbitSupportHelpers
import HodgeLean.Foundations.Program.SchoenCycleOrbitHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2DeckTransportHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2NormalizedSumHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2CoheightHelpers
import HodgeLean.Adapters.NormalConeB4aClassExistsPure

/-! # Normalized representatives of the actual rational orbit cycles -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Program
open scoped BigOperators
namespace HodgeLean.Foundations.Program.G32Native

/-- The inverse of a retained generator power is its complementary period power. -/
theorem endomorphism_inverse_power {W : Over (Spec ↧ℂ)}
    (d : W ⟶ W) (m : ℕ) (hm : 0 < m) (hperiod : End.of d ^ m = 1) (t : Fin m) :
    letI := s2e_generator_power_isIso d hm.ne' hperiod t.val
    inv (End.of d ^ t.val).asHom = (End.of d ^ (m - t.val)).asHom := by
  letI := s2e_generator_power_isIso d hm.ne' hperiod t.val
  apply IsIso.inv_eq_of_hom_inv_id
  change (End.of d ^ (m - t.val) * End.of d ^ t.val).asHom = 𝟙 W
  rw [← pow_add, Nat.sub_add_cancel (Nat.le_of_lt t.isLt), hperiod]
  rfl

#print axioms endomorphism_inverse_power
/-- Rational combinations retain normalized representatives of the same inverse-pullback orbit. -/
theorem rational_orbit_cycle_class
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    [Smooth W.hom] [IsProjective W.hom]
    (ι : Q ⟶ W) [IsClosedImmersion ι.left]
    (d : W ⟶ W) (m k : ℕ) (hm : 0 < m) (hperiod : End.of d ^ m = 1)
    (hdis : ∀ s t : Fin m, s ≠ t → Disjoint
      (Set.range (ι ≫ (End.of d ^ s.val).asHom).left)
      (Set.range (ι ≫ (End.of d ^ t.val).asHom).left))
    (hcodim : ∀ x ∈ (s2e_componentCycle ι ℚ).support, Order.coheight x = k)
    (c : s2e_supportedClass W (s2e_componentCycle ι ℚ) k)
    (hc : a3b4_IsCycleClass W.hom (s2e_componentCycle ι ℚ) k c)
    (a : Fin m → ℚ) :
    (∀ x ∈ (s2e_rationalOrbitCycle ι d m a).support, Order.coheight x = k) ∧
    ∃ cj, a3b4_IsCycleClass W.hom (s2e_rationalOrbitCycle ι d m a) k cj ∧
      s2e_classToAbsolute W (s2e_rationalOrbitCycle ι d m a) k cj =
        ∑ t : Fin m, a t • s2e_pullback ℚ (End.of d ^ (m - t.val)).asHom (2 * k)
          (s2e_classToAbsolute W (s2e_componentCycle ι ℚ) k c) := by
  letI : IsLocallyNoetherian W.left := LocallyOfFiniteType.isLocallyNoetherian W.hom
  have himm (t : Fin m) : IsClosedImmersion (ι ≫ (End.of d ^ t.val).asHom).left :=
    s2e_translated_component_isClosedImmersion ι d hm.ne' hperiod t.val
  have hbase : Order.coheight (ι.left (genericPoint Q.left)) = k :=
    hcodim _ (by rw [s2e_componentCycle_support]; exact Set.mem_singleton _)
  have hcodimT (t : Fin m) :
      ∀ x ∈ (s2e_componentCycle (ι ≫ (End.of d ^ t.val).asHom) ℚ).support,
        Order.coheight x = k := by
    intro x hx
    rw [s2e_componentCycle_support] at hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    letI := s2e_generator_power_isIso d hm.ne' hperiod t.val
    exact (s2e_coheight_eq_of_flat_locallyQuasiFinite
      (End.of d ^ t.val).asHom.left (ι.left (genericPoint Q.left))).symm.trans hbase
  have hex (t : Fin m) :
      ∃ ct : s2e_supportedClass W (s2e_componentCycle (ι ≫ (End.of d ^ t.val).asHom) ℚ) k,
        a3b4_IsCycleClass W.hom (s2e_componentCycle (ι ≫ (End.of d ^ t.val).asHom) ℚ) k ct := by
    apply a3b4a_cycleClass_exists_of_codimension
    intro x hx
    exact (hcodimT t x hx).ge
  choose ct hct using hex
  have hAbs (t : Fin m) :
      s2e_classToAbsolute W (s2e_componentCycle (ι ≫ (End.of d ^ t.val).asHom) ℚ) k (ct t) =
        s2e_pullback ℚ (End.of d ^ (m - t.val)).asHom (2 * k)
          (s2e_classToAbsolute W (s2e_componentCycle ι ℚ) k c) := by
    letI := s2e_generator_power_isIso d hm.ne' hperiod t.val
    have he := s2e_componentCycle_absolute_deck_transport ι (End.of d ^ t.val).asHom k
      ⊤ (by intro x hx; trivial) (by infer_instance) hcodim c (ct t) hc (hct t)
    rw [endomorphism_inverse_power d m hm hperiod t] at he
    exact he
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨t, ht⟩ := Set.mem_iUnion.mp (s2e_rationalOrbitCycle_support_subset ι d m a hx)
    exact hcodimT t x ht
  · obtain ⟨cj, hcj, he⟩ := s2e_rationalOrbitCycle_normalized_sum ι d k m himm hdis ct hct a
    refine ⟨cj, hcj, ?_⟩
    simpa only [hAbs] using he

#print axioms rational_orbit_cycle_class

/-- The retained inverse-orbit coordinates supply the native U09 family. -/
theorem canonical_orbit_classes
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    [Smooth W.hom] [IsProjective W.hom]
    (ι : Q ⟶ W) [IsClosedImmersion ι.left]
    (d : W ⟶ W) (m k : ℕ) (hm : 0 < m) (hperiod : End.of d ^ m = 1)
    (hdis : ∀ s t : Fin m, s ≠ t → Disjoint
      (Set.range (ι ≫ (End.of d ^ s.val).asHom).left)
      (Set.range (ι ≫ (End.of d ^ t.val).asHom).left))
    (hcodim : ∀ x ∈ (s2e_componentCycle ι ℚ).support, Order.coheight x = k)
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
  intro j
  obtain ⟨hh, cj, hcj, he⟩ :=
    rational_orbit_cycle_class ι d m k hm hperiod hdis hcodim c hc (a j)
  exact ⟨hh, cj, hcj, he.trans (hv j)⟩

#print axioms canonical_orbit_classes

end HodgeLean.Foundations.Program.G32Native
