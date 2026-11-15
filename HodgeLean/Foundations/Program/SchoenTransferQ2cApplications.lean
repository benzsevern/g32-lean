import HodgeLean.Foundations.Program.SchoenCycleRetainedAction
import HodgeLean.Foundations.Program.SchoenCycleFiniteQuotientComparison
import HodgeLean.Foundations.Program.SchoenTransferQuotientLinear

/-! Comparison for the retained Schoen transfer maps and coefficient normalization.
Implication from the displayed geometric inputs; invariant images are separate from kernels.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxRecDepth 2000
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Opposite
open AlgebraicTopology.Singular HodgeLean.Foundations
open scoped BigOperators
namespace HodgeLean.Foundations.Program
namespace Q2
open HodgeLean.Adapters
/-- Q2.4 uses the literal retained semidirect group and its coordinate realization.
Source: Bredon, Sheaf Theory, second edition, II.6 and III.1; Schoen (1988), Lemma 1.1 and Theorem 2.0. -/
theorem q2c_semidirect_action_application (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (h : ℕ) :
    Finite (s2e_Retained S.m h) ∧
      (∀ g : s2e_Retained S.m h,
        Continuous (Point.map (s2e_retainedAction S Y a e h g))) ∧
      s2e_retainedAction S Y a e h 1 = 𝟙 _ ∧
      (∀ u v : s2e_Retained S.m h,
        s2e_retainedAction S Y a e h (u * v) =
          s2e_retainedAction S Y a e h v ≫ s2e_retainedAction S Y a e h u) ∧
      (∀ (g : s2e_Retained S.m h) (i : Fin h),
        s2e_retainedAction S Y a e h g ≫ g3_proj Y h i =
          g3_proj Y h (g.perm.symm i) ≫ a (e.symm (.ofAdd (g.vector i)))) := by
  obtain ⟨h1, hm⟩ := s2e_retainedAction_laws S Y a e ha1 hamul h
  exact ⟨inferInstance, fun g => Point.continuous_map _, h1, hm,
    fun g i => s2_check_lift_proj _ _ _⟩

/-- Q2.4 identifies fibres of the categorical quotient with the actual coordinate orbits.
Source: Bredon, Sheaf Theory, second edition, II.6 and III.1; Schoen (1988), Lemma 1.1 and Theorem 2.0. -/
theorem q2c_orbit_fibres_application (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (h : ℕ)
    [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom]
    (W : Over (Spec ↧ℂ)) [IsIntegral W.left] [IsProjective W.hom]
    (q : g3_power Y h ⟶ W) [IsFinite q.left]
    (hqsurj : Function.Surjective (Point.map q))
    (hqinv : ∀ (v : Fin h → ZMod S.m) (σ : Equiv.Perm (Fin h)),
      ∑ i, v i = 0 → s2_action S Y a e h v σ ≫ q = q)
    (hquot : ∀ (Z : Over (Spec ↧ℂ)) (f : g3_power Y h ⟶ Z),
      (∀ (v : Fin h → ZMod S.m) (σ : Equiv.Perm (Fin h)),
        ∑ i, v i = 0 → s2_action S Y a e h v σ ≫ f = f) →
      ∃! g : W ⟶ Z, q ≫ g = f) :
    ∀ x y : ComplexPoint (g3_power Y h),
      Point.map q x = Point.map q y ↔
        ∃ g : s2e_Retained S.m h, Point.map (s2e_retainedAction S Y a e h g) x = y := by
  haveI : Surjective q.left :=
    s2e_step1_surjective_of_complexPoint_surjective (g3_power Y h) W q hqsurj
  obtain ⟨h1, hm⟩ := s2e_retainedAction_laws S Y a e ha1 hamul h
  have hi (g : s2e_Retained S.m h) : s2e_retainedAction S Y a e h g ≫ q = q :=
    hqinv g.vector g.perm g.zero_sum
  have hQ (Z : Over (Spec ↧ℂ)) (f : g3_power Y h ⟶ Z)
      (hf : ∀ g : s2e_Retained S.m h, s2e_retainedAction S Y a e h g ≫ f = f) :
      ∃! g : W ⟶ Z, q ≫ g = f :=
    hquot Z f (fun v σ hv => hf ⟨v, hv, σ⟩)
  intro x y
  constructor
  · exact s2e_step1_finite_quotient_point_orbits (g3_power Y h) W
      (s2e_Retained S.m h) (s2e_retainedAction S Y a e h) h1 hm q hi hQ x y
  · rintro ⟨g, rfl⟩
    rw [← Point.map_comp_apply, hi]

/-- Q2.5 transports the Q1 invariant summand through the specified quotient comparison.
Source: Bredon, Sheaf Theory, second edition, II.6 and III.1; Schoen (1988), Lemma 1.1 and Theorem 2.0. -/
theorem q2c_invariant_range_application (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (h : ℕ)
    [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom]
    (W : Over (Spec ↧ℂ)) [IsIntegral W.left] [IsProjective W.hom]
    (q : g3_power Y h ⟶ W) [IsFinite q.left]
    (hqsurj : Function.Surjective (Point.map q))
    (hqinv : ∀ (v : Fin h → ZMod S.m) (σ : Equiv.Perm (Fin h)),
      ∑ i, v i = 0 → s2_action S Y a e h v σ ≫ q = q)
    (hquot : ∀ (Z : Over (Spec ↧ℂ)) (f : g3_power Y h ⟶ Z),
      (∀ (v : Fin h → ZMod S.m) (σ : Equiv.Perm (Fin h)),
        ∑ i, v i = 0 → s2_action S Y a e h v σ ≫ f = f) →
      ∃! g : W ⟶ Z, q ≫ g = f) (n : ℕ) :
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
  obtain ⟨h1, hm⟩ := s2e_retainedAction_laws S Y a e ha1 hamul h
  have hi (g : G) : A g ≫ q = q := hqinv g.vector g.perm g.zero_sum
  have hQ (Z : Over (Spec ↧ℂ)) (f : T ⟶ Z)
      (hf : ∀ g : G, A g ≫ f = f) : ∃! g : W ⟶ Z, q ≫ g = f :=
    hquot Z f (fun v σ hv => hf ⟨v, hv, σ⟩)
  have hinj : Function.Injective (s4_singularPullback q n) :=
    s2e_chain_finite_quotient_pullback_injective_aux T W G A h1 hm q hqsurj hi hQ n
  have hdesc (b : Cohomology ℚ (TopCat.of (ComplexPoint T)) n)
      (hb : ∀ g : G, s4_singularPullback (A g) n b = b) :
      ∃ c, s4_singularPullback q n c = b :=
    s2e_finite_quotient_invariant_descent T W G A h1 hm q hqsurj hi hQ n b hb
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

/-- Q2.6 identifies the residual cyclotomic kernel with the specified U, after the invariant image step.
Source: Bredon, Sheaf Theory, second edition, II.6 and III.1; Schoen (1988), Lemma 1.1 and Theorem 2.0. -/
theorem q2c_residual_kernel_application (S : g32p_Supplier) (Y : Over (Spec ↧ℂ))
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (ha1 : a 1 = 𝟙 Y) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (h : ℕ)
    [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom]
    (W : Over (Spec ↧ℂ)) [IsIntegral W.left] [IsProjective W.hom]
    (q : g3_power Y h ⟶ W) [IsFinite q.left]
    (hqsurj : Function.Surjective (Point.map q))
    (hqinv : ∀ (v : Fin h → ZMod S.m) (σ : Equiv.Perm (Fin h)),
      ∑ i, v i = 0 → s2_action S Y a e h v σ ≫ q = q)
    (hquot : ∀ (Z : Over (Spec ↧ℂ)) (f : g3_power Y h ⟶ Z),
      (∀ (v : Fin h → ZMod S.m) (σ : Equiv.Perm (Fin h)),
        ∑ i, v i = 0 → s2_action S Y a e h v σ ≫ f = f) →
      ∃! g : W ⟶ Z, q ≫ g = f)
    (hh : 0 < h) (d : W ⟶ W)
    (hd : s2_action S Y a e h (s2_delta S h hh 1) 1 ≫ q = q ≫ d) :
    (LinearMap.ker (Polynomial.aeval (s4_singularPullback d h)
      (Polynomial.cyclotomic S.m ℚ))).map (s4_quotientPullback q h) =
        s4_invariantPrimitive S Y a e h hh := by
  obtain ⟨_, _, hi, hr⟩ :=
    q2c_invariant_range_application S Y a e ha1 hamul h W q hqsurj hqinv hquot h
  exact s4_quotient_primitive_image_eq S Y h hh a e W q hqinv d hd hi hr


end Q2
end HodgeLean.Foundations.Program
