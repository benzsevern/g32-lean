import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cRelativeCoefficients
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.MetricSpace.Bounded

noncomputable section

namespace HodgeLean.Foundations.Program

open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular

theorem b6m_singularChainMap_quasiIso_of_homotopy (R : Type) [CommRing R] {X Y : TopCat.{0}} (f : X ⟶ Y) (g : Y ⟶ X)
    (H₁ : TopCat.Homotopy (f ≫ g) (𝟙 X)) (H₂ : TopCat.Homotopy (g ≫ f) (𝟙 Y)) :
    QuasiIso (((singularChainComplexFunctor (ModuleCat.{0} R)).obj
      (ModuleCat.of R R)).map f) := by
  let F := (singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)
  let e : HomotopyEquiv (F.obj X) (F.obj Y) :=
    { hom := F.map f
      inv := F.map g
      homotopyHomInvId := (Homotopy.ofEq (F.map_comp f g).symm).trans
        ((H₁.singularChainComplexFunctorObjMap (ModuleCat.of R R)).trans
          (Homotopy.ofEq (F.map_id X)))
      homotopyInvHomId := (Homotopy.ofEq (F.map_comp g f).symm).trans
        ((H₂.singularChainComplexFunctorObjMap (ModuleCat.of R R)).trans
          (Homotopy.ofEq (F.map_id Y))) }
  exact e.quasiIso_hom

theorem b6m_radial_coeff_bounds {a t : ℝ} (ha : 0 < a) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < (1 - t) * a + t ∧ ((1 - t) * a + t < 1 → a ≤ (1 - t) * a + t) := by
  constructor
  · rcases eq_or_lt_of_le ht0 with h | h
    · subst h; simpa using ha
    · nlinarith
  · intro h
    by_contra h'
    rw [not_le] at h'
    have e1 : (1 - t) * a + t - a = t * (1 - a) := by ring
    have e2 : (1 - t) * (a - 1) = (1 - t) * a + t - 1 := by ring
    have ha1 : 1 < a := by
      by_contra h2
      rw [not_lt] at h2
      have := mul_nonneg ht0 (sub_nonneg.2 h2)
      linarith
    have := mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 ha1.le)
    linarith

theorem b6m_radial_notMem {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} (hK : Convex ℝ K) {x : E} (hx : x ∈ K) {R : ℝ}
    (hR : K ⊆ Metric.ball x R) {y : E} (hy : y ∉ K) {c : ℝ}
    (hc0 : 0 < c) (hc : c < 1 → R / ‖y - x‖ ≤ c) : x + c • (y - x) ∉ K := by
  intro hz
  have hyx : y - x ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; exact hy (h ▸ hx)
  have hn : 0 < ‖y - x‖ := norm_pos_iff.mpr hyx
  by_cases h1 : 1 ≤ c
  · apply hy
    have hmem := hK.add_smul_sub_mem hx hz
      (t := c⁻¹) ⟨inv_nonneg.mpr hc0.le, inv_le_one_of_one_le₀ h1⟩
    have : x + c⁻¹ • (x + c • (y - x) - x) = y := by
      rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hc0.ne', one_smul, add_sub_cancel]
    rwa [this] at hmem
  · have hc' := hc (lt_of_not_ge h1)
    have hball := hR hz
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hc0.le] at hball
    rw [div_le_iff₀ hn] at hc'
    linarith

theorem b6m_convex_complement_homotopy_inverse
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} (hK : Convex ℝ K) (hKc : IsCompact K) {x : E}
    (hx : x ∈ K)
    (ι : TopCat.of ↥(Kᶜ : Set E) ⟶ TopCat.of ↥(({x} : Set E)ᶜ : Set E))
    (hι : ∀ y, (ι y).1 = y.1) :
    ∃ r : TopCat.of ↥(({x} : Set E)ᶜ : Set E) ⟶ TopCat.of ↥(Kᶜ : Set E),
      Nonempty (TopCat.Homotopy (ι ≫ r) (𝟙 _)) ∧
        Nonempty (TopCat.Homotopy (r ≫ ι) (𝟙 _)) := by
  obtain ⟨R, hR⟩ := hKc.isBounded.subset_ball x
  have hR0 : 0 < R := by
    have := hR hx; rw [Metric.mem_ball, dist_self] at this; exact this
  have hne : ∀ y : ↥(({x} : Set E)ᶜ : Set E), ‖y.1 - x‖ ≠ 0 := fun y h =>
    y.2 (by rw [norm_eq_zero, sub_eq_zero] at h; exact h)
  have hpos : ∀ y : ↥(({x} : Set E)ᶜ : Set E), 0 < ‖y.1 - x‖ := fun y =>
    lt_of_le_of_ne (norm_nonneg _) (hne y).symm
  -- the coefficient of the radial homotopy
  let c : unitInterval × ↥(({x} : Set E)ᶜ : Set E) → ℝ := fun p =>
    (1 - (p.1 : ℝ)) * (R / ‖p.2.1 - x‖) + p.1
  have hc_cont : Continuous c := by
    have h1 : Continuous fun p : unitInterval × ↥(({x} : Set E)ᶜ : Set E) => ‖p.2.1 - x‖ := by
      fun_prop
    have h2 : Continuous fun p : unitInterval × ↥(({x} : Set E)ᶜ : Set E) =>
        R / ‖p.2.1 - x‖ :=
      continuous_const.div h1 (fun p => hne p.2)
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul h2).add
      (continuous_subtype_val.comp continuous_fst)
  have hc_bounds : ∀ p, 0 < c p ∧ (c p < 1 → R / ‖p.2.1 - x‖ ≤ c p) := fun p =>
    b6m_radial_coeff_bounds (div_pos hR0 (hpos p.2)) p.1.2.1 p.1.2.2
  have hc_ne : ∀ p, x + c p • (p.2.1 - x) ≠ x := by
    intro p h
    rw [add_eq_left, smul_eq_zero] at h
    rcases h with h | h
    · exact (hc_bounds p).1.ne' h
    · exact hne p.2 (by rw [h, norm_zero])
  let G : unitInterval × ↥(({x} : Set E)ᶜ : Set E) → E := fun p => x + c p • (p.2.1 - x)
  have hG : Continuous G := by
    exact continuous_const.add (hc_cont.smul
      ((continuous_subtype_val.comp continuous_snd).sub continuous_const))
  -- radial projection `E \ x → E \ K`
  let toT : ↥(Kᶜ : Set E) → ↥(({x} : Set E)ᶜ : Set E) := fun y =>
    ⟨y.1, fun h => y.2 (by rw [Set.mem_singleton_iff.mp h]; exact hx)⟩
  have htoT : Continuous toT := continuous_subtype_val.subtype_mk _
  have hGK : ∀ p : unitInterval × ↥(Kᶜ : Set E), G (p.1, toT p.2) ∈ (Kᶜ : Set E) := by
    intro p
    have hb := hc_bounds (p.1, toT p.2)
    exact b6m_radial_notMem hK hx hR p.2.2 hb.1 hb.2
  have hr_mem : ∀ y : ↥(({x} : Set E)ᶜ : Set E),
      x + (R / ‖y.1 - x‖) • (y.1 - x) ∈ (Kᶜ : Set E) := by
    intro y hy
    have h := hR hy
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg (div_pos hR0 (hpos y)).le, div_mul_cancel₀ _ (hne y)] at h
    exact lt_irrefl _ h
  let r : TopCat.of ↥(({x} : Set E)ᶜ : Set E) ⟶ TopCat.of ↥(Kᶜ : Set E) :=
    TopCat.ofHom ⟨fun y => ⟨x + (R / ‖y.1 - x‖) • (y.1 - x), hr_mem y⟩, by
      apply Continuous.subtype_mk
      exact continuous_const.add ((continuous_const.div
        (continuous_subtype_val.sub continuous_const).norm hne).smul
        (continuous_subtype_val.sub continuous_const))⟩
  have hιeq : ι = TopCat.ofHom ⟨toT, htoT⟩ := by
    ext y; exact hι y
  have hG0 : ∀ y : ↥(({x} : Set E)ᶜ : Set E), G (0, y) = x + (R / ‖y.1 - x‖) • (y.1 - x) := by
    intro y; simp [G, c]
  have hG1 : ∀ y : ↥(({x} : Set E)ᶜ : Set E), G (1, y) = y.1 := by
    intro y; simp [G, c]
  refine ⟨r, ⟨?_⟩, ⟨?_⟩⟩
  · exact
      { toFun := fun p => ⟨G (p.1, toT p.2), hGK p⟩
        continuous_toFun := (hG.comp (continuous_fst.prodMk (htoT.comp continuous_snd))).subtype_mk _
        map_zero_left := fun y => by
          apply Subtype.ext
          simp only [TopCat.hom_comp, ContinuousMap.comp_apply]
          rw [hG0]
          simp [r, hι, toT]
        map_one_left := fun y => by
          apply Subtype.ext
          show G (1, toT y) = y.1
          rw [hG1] }
  · exact
      { toFun := fun p => ⟨G p, hc_ne p⟩
        continuous_toFun := hG.subtype_mk _
        map_zero_left := fun y => by
          apply Subtype.ext
          simp only [TopCat.hom_comp, ContinuousMap.comp_apply]
          rw [hG0, hι]
          rfl
        map_one_left := fun y => by
          apply Subtype.ext
          exact hG1 y }

theorem b6m_convexComplement_quasiIso (R : Type) [CommRing R]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hK : Convex ℝ K) (hKc : IsCompact K) {x : E} (hx : x ∈ K)
    (ι : TopCat.of ↥(Kᶜ : Set E) ⟶ TopCat.of ↥(({x} : Set E)ᶜ : Set E))
    (hι : ∀ y, (ι y).1 = y.1) :
    QuasiIso (((singularChainComplexFunctor (ModuleCat.{0} R)).obj
      (ModuleCat.of R R)).map ι) := by
  obtain ⟨r, ⟨H₁⟩, ⟨H₂⟩⟩ := b6m_convex_complement_homotopy_inverse hK hKc hx ι hι
  exact b6m_singularChainMap_quasiIso_of_homotopy R ι r H₁ H₂

theorem b6m_convex_restrict_bijective (R : Type) [CommRing R]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hK : Convex ℝ K) (hKc : IsCompact K) {x : E}
    (hx : x ∈ K) (i : ℕ) :
    Function.Bijective (relativeHomologyMap R i
      (supportInclusionPairMap (TopCat.of E) (Set.singleton_subset_iff.mpr hx))) := by
  refine b6m_relativeHomologyMap_bijective R _ ?_ ?_ i
  · exact b6m_convexComplement_quasiIso R hK hKc hx _ (fun _ => rfl)
  · change QuasiIso (((singularChainComplexFunctor (ModuleCat.{0} R)).obj
      (ModuleCat.of R R)).map (𝟙 (TopCat.of E)))
    rw [CategoryTheory.Functor.map_id]
    infer_instance

end HodgeLean.Foundations.Program
