import HodgeLean.Foundations.Program.SchoenTransferQ3OrbitInjective
import HodgeLean.Foundations.Program.SchoenTransferQ3OrbitDescent
import HodgeLean.Foundations.Program.SchoenTransferQ3OrbitTopology
import HodgeLean.Foundations.Program.SchoenCycleRetainedAction
import HodgeLean.Foundations.Program.SchoenTransferQuotientLinear

/-! Invariant images for the retained original point-orbit interface. -/
noncomputable section
set_option maxRecDepth 2000
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.Foundations HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- The original orbit-fibre data give the specified singular and sheaf invariant images.
Source: Bredon, Sheaf Theory, second edition, II.6 and III.1; Schoen (1988), Lemma 1.1 and Theorem 2.0. -/
theorem s4_q3_retained_invariant_range (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a u ≫ a v)
    (h : ℕ)
    [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom]
    (W : Over (Spec ↧ℂ)) [IsIntegral W.left] [IsProjective W.hom]
    (q : g3_power Y h ⟶ W) [IsFinite q.left]
    (hqsurj : Function.Surjective (Point.map q))
    (hqinv : ∀ (v : Fin h → ZMod S.m) (σ : Equiv.Perm (Fin h)),
      ∑ i, v i = 0 → s2_action S Y a e h v σ ≫ q = q)
    (hqfib : ∀ x y : ComplexPoint (g3_power Y h),
      Point.map q x = Point.map q y →
        ∃ (v : Fin h → ZMod S.m) (σ : Equiv.Perm (Fin h)),
          (∑ i, v i) = 0 ∧ Point.map (s2_action S Y a e h v σ) x = y) (n : ℕ) :
    Function.Injective (s4_singularPullback q n) ∧
      (LinearMap.range (s4_singularPullback q n) =
        ⨅ v : {v : Fin h → ZMod S.m // ∑ i, v i = 0},
          ⨅ σ : Equiv.Perm (Fin h),
            LinearMap.ker (s4_singularPullback (s2_action S Y a e h v.val σ) n -
              LinearMap.id)) ∧
      Function.Injective (s4_quotientPullback q n) ∧
      LinearMap.range (s4_quotientPullback q n) =
        ⨅ v : {v : Fin h → ZMod S.m // ∑ i, v i = 0},
          ⨅ σ : Equiv.Perm (Fin h),
            LinearMap.ker (HodgeLean.Adapters.homPullback (s2_action S Y a e h v.val σ) n -
              LinearMap.id) := by
  classical
  let T := g3_power Y h
  let G := s2e_Retained S.m h
  let A := s2e_retainedAction S Y a e h
  obtain ⟨h1, hm⟩ := s2e_retainedAction_laws S Y a e ha1 (s4_q3_action_reverse_mul S Y a e hamul) h
  have hi (g : G) : A g ≫ q = q := hqinv g.vector g.perm g.zero_sum
  have horbit (x y : ComplexPoint T) (hxy : Point.map q x = Point.map q y) :
      ∃ g : G, Point.map (A g) x = y := by
    obtain ⟨v, σ, hv, hxy⟩ := hqfib x y hxy
    exact ⟨⟨v, hv, σ⟩, hxy⟩
  have hinj : Function.Injective (s4_singularPullback q n) :=
    s4_q3_orbit_pullback_injective T W G A h1 hm q hqsurj hi horbit n
  have hdesc (b : Cohomology ℚ (TopCat.of (ComplexPoint T)) n)
      (hb : ∀ g : G, s4_singularPullback (A g) n b = b) :
      ∃ c, s4_singularPullback q n c = b :=
    s4_q3_orbit_invariant_descent T W G A h1 hm q hqsurj hi horbit n b hb
  have hs : LinearMap.range (s4_singularPullback q n) =
      ⨅ v : {v : Fin h → ZMod S.m // ∑ i, v i = 0},
        ⨅ σ : Equiv.Perm (Fin h),
          LinearMap.ker (s4_singularPullback (s2_action S Y a e h v.val σ) n -
            LinearMap.id) := by
    ext b
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero, LinearMap.mem_range]
    constructor
    · rintro ⟨c, rfl⟩ v σ
      change s4_singularPullback _ n (s4_singularPullback q n c) = _
      rw [← LinearMap.comp_apply, ← s4_singularPullback_comp, hqinv _ _ v.property]
    · intro hb
      exact hdesc b (fun g => hb ⟨g.vector, g.zero_sum⟩ g.perm)
  letI : ∀ U : Opens (ComplexPoint T), ParacompactSpace U :=
    fun U => openParacompactSpace T U
  have hc := spec_singularToFieldCohomology_bijective ℚ T n
  have hquotinj : Function.Injective (s4_quotientPullback q n) :=
    hc.1.comp hinj
  have hn (g : T ⟶ T) (b : Cohomology ℚ (TopCat.of (ComplexPoint T)) n) :
      homPullback g n (singularToFieldCohomology ℚ T n b) =
      singularToFieldCohomology ℚ T n (s4_singularPullback g n b) := by
    have H := LinearMap.congr_fun
      (s4_quotientPullback_naturality (𝟙 T) g g (by simp) n) b
    change homPullback g n (singularToFieldCohomology ℚ T n
      (s4_singularPullback (𝟙 T) n b)) = singularToFieldCohomology ℚ T n
        (s4_singularPullback (𝟙 T) n (s4_singularPullback g n b)) at H
    simpa only [s4_singularPullback_id, LinearMap.id_apply] using H
  refine ⟨hinj, hs, hquotinj, ?_⟩
  ext z
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero, LinearMap.mem_range]
  constructor
  · rintro ⟨c, rfl⟩ v σ
    exact s4_quotientPullback_fixed q _ (hqinv _ _ v.property) n c
  · intro hz
    obtain ⟨b, rfl⟩ := hc.2 z
    obtain ⟨c, hc'⟩ := hdesc b (fun g => hc.1 (by
      rw [← hn]
      exact hz ⟨g.vector, g.zero_sum⟩ g.perm))
    exact ⟨c, congrArg (singularToFieldCohomology ℚ T n) hc'⟩

end HodgeLean.Foundations.Program
