import HodgeLean.Foundations.Program.G32SelectedRealizationCyclotomic
import HodgeLean.Foundations.Program.SchoenTransferDefs
import HodgeLean.Adapters.HolomorphicPeriodsComparison
import HodgeLean.Adapters.AbelianHomPullback

/-! Functoriality and comparison normalization for singular quotient pullback. -/
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular HodgeLean.RealDefs HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program

theorem s4_singularPullback_comp {X Y Z : Over (Spec ↧ℂ)}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    s4_singularPullback (f ≫ g) n =
      (s4_singularPullback f n).comp (s4_singularPullback g n) := by
  unfold s4_singularPullback
  rw [ofHom_continuousMap_comp, cohomologyMap_comp]

theorem s4_quotientPullback_factor {T W : Over (Spec ↧ℂ)}
    [IsIntegral T.left] [Smooth T.hom] [IsProjective T.hom]
    (q : T ⟶ W) (n : ℕ) :
    ∃ r : ℚ, r ≠ 0 ∧ ∀ x,
      s4_quotientPullback q n x =
        r • (cupComparison T n).symm (s4_singularPullback q n x) := by
  obtain ⟨r, hr, hcmp⟩ := spec_singularToFieldCohomology_cupComparison T n
  refine ⟨r, hr, fun x => ?_⟩
  have h := hcmp ((cupComparison T n).symm (s4_singularPullback q n x))
  rw [LinearEquiv.apply_symm_apply] at h
  exact h

theorem s4_quotientPullback_naturality {T W : Over (Spec ↧ℂ)}
    [IsIntegral T.left] [Smooth T.hom] [IsProjective T.hom]
    (q : T ⟶ W) (g : T ⟶ T) (d : W ⟶ W) (hsquare : g ≫ q = q ≫ d)
    (n : ℕ) :
    (homPullback g n).comp (s4_quotientPullback q n) =
      (s4_quotientPullback q n).comp (s4_singularPullback d n) := by
  obtain ⟨r, _, hcmp⟩ := s4_quotientPullback_factor q n
  ext x
  simp only [LinearMap.comp_apply, hcmp, map_smul]
  apply congrArg (fun z => r • z)
  apply (cupComparison T n).injective
  simp only [homPullback, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  change s4_singularPullback g n (s4_singularPullback q n x) =
    s4_singularPullback q n (s4_singularPullback d n x)
  rw [← LinearMap.comp_apply, ← s4_singularPullback_comp, hsquare,
    s4_singularPullback_comp, LinearMap.comp_apply]

theorem s4_singularPullback_id (W : Over (Spec ↧ℂ)) (n : ℕ) :
    s4_singularPullback (𝟙 W) n = LinearMap.id := by
  unfold s4_singularPullback
  rw [ofHom_continuousMap_id, cohomologyMap_id]

theorem s4_quotientPullback_fixed {T W : Over (Spec ↧ℂ)}
    [IsIntegral T.left] [Smooth T.hom] [IsProjective T.hom]
    (q : T ⟶ W) (g : T ⟶ T) (hg : g ≫ q = q) (n : ℕ) (x) :
    homPullback g n (s4_quotientPullback q n x) = s4_quotientPullback q n x := by
  have hn := s4_quotientPullback_naturality q g (𝟙 W)
    (by rw [Category.comp_id]; exact hg) n
  rw [s4_singularPullback_id, LinearMap.comp_id] at hn
  exact LinearMap.congr_fun hn x

theorem s4_quotientPullback_polynomial_kernel {T W : Over (Spec ↧ℂ)}
    [IsIntegral T.left] [Smooth T.hom] [IsProjective T.hom]
    (q : T ⟶ W) (g : T ⟶ T) (d : W ⟶ W) (hsquare : g ≫ q = q ≫ d)
    (n : ℕ) (p : Polynomial ℚ) :
    (LinearMap.ker (Polynomial.aeval (s4_singularPullback d n) p)).map
      (s4_quotientPullback q n) ≤ LinearMap.ker (Polynomial.aeval (homPullback g n) p) := by
  rintro _ ⟨x, hx, rfl⟩
  have hn := g32y_aeval_intertwine (s4_quotientPullback q n)
    (s4_singularPullback d n) (homPullback g n)
    (s4_quotientPullback_naturality q g d hsquare n).symm p
  have h := LinearMap.congr_fun hn x
  change Polynomial.aeval (s4_singularPullback d n) p x = 0 at hx
  change Polynomial.aeval (homPullback g n) p (s4_quotientPullback q n x) = 0
  simpa only [LinearMap.comp_apply, hx, map_zero] using h.symm

theorem s4_quotient_primitive_image_le (S : g32p_Supplier)
    (Y : Over (Spec ↧ℂ)) (h : ℕ) (hh : 0 < h)
    [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (W : Over (Spec ↧ℂ)) (q : g3_power Y h ⟶ W)
    (hqinv : ∀ (v : Fin h → ZMod S.m) (σ : Equiv.Perm (Fin h)),
      (∑ i, v i) = 0 → s2_action S Y a e h v σ ≫ q = q)
    (d : W ⟶ W)
    (hd : s2_action S Y a e h (s2_delta S h hh 1) 1 ≫ q = q ≫ d) :
    (LinearMap.ker (Polynomial.aeval (s4_singularPullback d h)
      (Polynomial.cyclotomic S.m ℚ))).map (s4_quotientPullback q h) ≤
      s4_invariantPrimitive S Y a e h hh := by
  intro z hz
  refine ⟨s4_quotientPullback_polynomial_kernel q _ d hd h _ hz, ?_⟩
  obtain ⟨x, _, rfl⟩ := hz
  change s4_quotientPullback q h x ∈
    ⨅ v : {v : Fin h → ZMod S.m // ∑ i, v i = 0},
      ⨅ σ : Equiv.Perm (Fin h),
        LinearMap.ker (homPullback (s2_action S Y a e h v.val σ) h - LinearMap.id)
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero]
  intro v σ
  exact s4_quotientPullback_fixed q _ (hqinv v.val σ v.property) h x

theorem s4_quotient_primitive_image_eq (S : g32p_Supplier)
    (Y : Over (Spec ↧ℂ)) (h : ℕ) (hh : 0 < h)
    [IsIntegral (g3_power Y h).left] [Smooth (g3_power Y h).hom]
    [IsProjective (g3_power Y h).hom]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y))
    (e : (S.H ⧸ S.χ.ker) ≃* Multiplicative (ZMod S.m))
    (W : Over (Spec ↧ℂ)) (q : g3_power Y h ⟶ W)
    (hqinv : ∀ (v : Fin h → ZMod S.m) (σ : Equiv.Perm (Fin h)),
      (∑ i, v i) = 0 → s2_action S Y a e h v σ ≫ q = q)
    (d : W ⟶ W)
    (hd : s2_action S Y a e h (s2_delta S h hh 1) 1 ≫ q = q ≫ d)
    (hinj : Function.Injective (s4_quotientPullback q h))
    (hrange : LinearMap.range (s4_quotientPullback q h) =
      ⨅ v : {v : Fin h → ZMod S.m // ∑ i, v i = 0},
        ⨅ σ : Equiv.Perm (Fin h),
          LinearMap.ker (homPullback (s2_action S Y a e h v.val σ) h - LinearMap.id)) :
    (LinearMap.ker (Polynomial.aeval (s4_singularPullback d h)
      (Polynomial.cyclotomic S.m ℚ))).map (s4_quotientPullback q h) =
      s4_invariantPrimitive S Y a e h hh := by
  apply le_antisymm (s4_quotient_primitive_image_le S Y h hh a e W q hqinv d hd)
  intro z hz
  have hzr : z ∈ LinearMap.range (s4_quotientPullback q h) := by
    rw [hrange]
    exact hz.2
  obtain ⟨x, rfl⟩ := hzr
  refine Submodule.mem_map.mpr ⟨x, ?_, rfl⟩
  change Polynomial.aeval (s4_singularPullback d h) (Polynomial.cyclotomic S.m ℚ) x = 0
  apply hinj
  have hn := g32y_aeval_intertwine (s4_quotientPullback q h)
    (s4_singularPullback d h)
    (homPullback (s2_action S Y a e h (s2_delta S h hh 1) 1) h)
    (s4_quotientPullback_naturality q _ d hd h).symm (Polynomial.cyclotomic S.m ℚ)
  have hx := LinearMap.congr_fun hn x
  have hk := hz.1
  change Polynomial.aeval (homPullback (s2_action S Y a e h (s2_delta S h hh 1) 1) h)
    (Polynomial.cyclotomic S.m ℚ) (s4_quotientPullback q h x) = 0 at hk
  simpa only [LinearMap.comp_apply, hk, map_zero] using hx

end HodgeLean.Foundations.Program
