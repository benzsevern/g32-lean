import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDefs
import HodgeLean.Adapters.NormalConeB4aGysinRegularDegree
import HodgeLean.Adapters.NormalConeB4aGysinDegreeDeformation

/-! # Counting regular zeros on an open chart domain

The local contribution at a regular complex zero is positive. The source
map needs continuity only on the open chart domain.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Adapters
open scoped BigOperators
set_option maxHeartbeats 400000
namespace AlgebraicGeometry.SingularCycles

theorem regular_fibre_point_class_on_open
    (d : ℕ) (U : Set (Fin d → ℂ)) (hU : IsOpen U)
    (g : (Fin d → ℂ) → (Fin d → ℂ)) (hg : ContinuousOn g U)
    (S : Finset (Fin d → ℂ)) (hSU : (S : Set (Fin d → ℂ)) ⊆ U)
    (hS : ∀ x ∈ U, g x = 0 ↔ x ∈ S)
    (x : S) (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.det ≠ 0)
    (hd : HasFDerivAt (fun z => g (z + x.1))
      (A.mulVecLin.toContinuousLinearMap : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) 0) :
    let E := Fin d → ℂ
    let J := a3b4_neighborhoodPairMap U (S : Set E)
    let G := a3b4_supportPairMap
      (TopCat.ofHom ⟨fun u : U => g u.1, hg.domRestrict⟩)
      {u : U | u.1 ∈ S} ({0} : Set E) (fun u hu => (hS u.1 u.2).mp hu)
    ∃ z : RelativeHomology ℚ (neighborhoodSupportComplementPair U (S : Set E)) (2 * d),
      relativeHomologyMap ℚ (2 * d)
        (J ≫ supportInclusionPairMap (TopCat.of E) (Set.singleton_subset_iff.mpr x.2)) z =
          HodgeLean.RealDefs.translatedStandardComplexLocalClass d x.1 ∧
      (∀ y : S, y ≠ x → relativeHomologyMap ℚ (2 * d)
        (J ≫ supportInclusionPairMap (TopCat.of E) (Set.singleton_subset_iff.mpr y.2)) z = 0) ∧
      relativeHomologyMap ℚ (2 * d) G z = standardComplexLocalClass ℚ d := by
  classical
  dsimp only
  let E := Fin d → ℂ
  let V₀ : Set E := (fun z : E => z + x.1) ⁻¹' U
  have hV₀ : IsOpen V₀ := hU.preimage (continuous_id.add continuous_const)
  have h0V₀ : (0 : E) ∈ V₀ := by simpa only [V₀, Set.mem_preimage, zero_add] using hSU x.2
  have hg₀ : ContinuousOn (fun z : E => g (z + x.1)) V₀ :=
    hg.comp (continuous_id.add continuous_const).continuousOn (fun _ h => h)
  have hg0 : g (0 + x.1) = 0 := by simpa only [zero_add] using (hS x.1 (hSU x.2)).mpr x.2
  obtain ⟨V, hVV₀, hne, hVo, h0V, hmap⟩ :=
    exists_open_complexDifferentiable_localClass_invariance d A hA V₀ hV₀ h0V₀
      (fun z => g (z + x.1)) hg₀ hg0 hd
  obtain ⟨v, hv⟩ := (neighborhoodPointComplement_relativeHomologyMap_bijective
    V 0 hVo h0V (2 * d)).2 (standardComplexLocalClass ℚ d)
  let t : TopCat.of V ⟶ TopCat.of U :=
    TopCat.ofHom ⟨fun u => ⟨u.1 + x.1, hVV₀ u.2⟩,
      (continuous_subtype_val.add continuous_const).subtype_mk _⟩
  have hsingle : ∀ u : V, (t u).1 ∈ S → u.1 = 0 := by
    intro u hu
    by_contra hu0
    exact hne u.1 u.2 hu0 ((hS (t u).1 (t u).2).mpr hu)
  let F := a3b4_supportPairMap t {u : V | u.1 = 0}
    {u : U | u.1 ∈ S} hsingle
  let J := a3b4_neighborhoodPairMap U (S : Set E)
  let G := a3b4_supportPairMap
    (TopCat.ofHom ⟨fun u : U => g u.1, hg.domRestrict⟩)
    {u : U | u.1 ∈ S} ({0} : Set E) (fun u hu => (hS u.1 u.2).mp hu)
  refine ⟨relativeHomologyMap ℚ (2 * d) F v, ?_, ?_, ?_⟩
  · have heq : F ≫ (J ≫ supportInclusionPairMap (TopCat.of E)
        (Set.singleton_subset_iff.mpr x.2)) =
        neighborhoodPointComplementPairMap V 0 ≫ translationPointComplementPairMap E x.1 := by
      apply MorphismProperty.Arrow.Hom.ext <;> ext u <;> rfl
    change relativeHomologyMap ℚ (2 * d) (J ≫ _) (relativeHomologyMap ℚ (2 * d) F v) = _
    rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp, heq,
      relativeHomologyMap_comp, LinearMap.comp_apply, hv]
    rfl
  · intro y hyx
    let t' : TopCat.of V ⟶ TopCat.of E :=
      TopCat.ofHom ⟨fun u => u.1 + x.1, continuous_subtype_val.add continuous_const⟩
    have hmiss : ∀ u : V, t' u ∉ ({y.1} : Set E) := by
      intro u hu
      have huy : t' u = y.1 := hu
      have huS : (t u).1 ∈ S := by
        change u.1 + x.1 ∈ S
        change u.1 + x.1 = y.1 at huy
        exact huy.symm ▸ y.2
      have hu0 := hsingle u huS
      apply hyx
      apply Subtype.ext
      change y.1 = x.1
      calc
        y.1 = u.1 + x.1 := huy.symm
        _ = x.1 := by rw [hu0, zero_add]
    let H := a3b4_supportPairMap t' {u : V | u.1 = 0} ({y.1} : Set E)
      (fun u hu => (hmiss u hu).elim)
    have heq : F ≫ (J ≫ supportInclusionPairMap (TopCat.of E)
        (Set.singleton_subset_iff.mpr y.2)) = H := by
      apply MorphismProperty.Arrow.Hom.ext <;> ext u <;> rfl
    change relativeHomologyMap ℚ (2 * d) (J ≫ _) (relativeHomologyMap ℚ (2 * d) F v) = _
    rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp, heq]
    rw [show relativeHomologyMap ℚ (2 * d) H = 0 from
      a3b4a_gysin_homologyMap_zero_of_avoids_support t' {u : V | u.1 = 0}
        ({y.1} : Set E) (fun u hu => (hmiss u hu).elim) hmiss (2 * d)]
    rfl
  · have heq : F ≫ G = complexNeighborhoodPuncturedPairMapOf d V
        (fun z => g (z + x.1)) (hg₀.mono hVV₀) hne := by
      apply MorphismProperty.Arrow.Hom.ext <;> ext u <;> rfl
    change relativeHomologyMap ℚ (2 * d) G (relativeHomologyMap ℚ (2 * d) F v) = _
    rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp, heq]
    exact hmap v hv

theorem regular_fibre_degree_on_open
    (d : ℕ) (U : Set (Fin d → ℂ)) (hU : IsOpen U)
    (g : (Fin d → ℂ) → (Fin d → ℂ)) (hg : ContinuousOn g U)
    (S : Finset (Fin d → ℂ)) (hSU : (S : Set (Fin d → ℂ)) ⊆ U)
    (hS : ∀ x ∈ U, g x = 0 ↔ x ∈ S)
    (A : S → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ x, (A x).det ≠ 0)
    (hd : ∀ x : S, HasFDerivAt (fun z => g (z + x.1))
      ((A x).mulVecLin.toContinuousLinearMap : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) 0)
    (α : RelativeHomology ℚ (neighborhoodSupportComplementPair U (S : Set (Fin d → ℂ))) (2 * d))
    (hα : ∀ x : S, relativeHomologyMap ℚ (2 * d)
      (a3b4_neighborhoodPairMap U (S : Set (Fin d → ℂ)) ≫
        supportInclusionPairMap (TopCat.of (Fin d → ℂ)) (Set.singleton_subset_iff.mpr x.2)) α =
      HodgeLean.RealDefs.translatedStandardComplexLocalClass d x.1) :
    relativeHomologyMap ℚ (2 * d)
      (a3b4_supportPairMap
        (TopCat.ofHom ⟨fun u : U => g u.1, hg.domRestrict⟩)
        {u : U | u.1 ∈ S} ({0} : Set (Fin d → ℂ)) (fun u hu => (hS u.1 u.2).mp hu)) α =
      (S.card : ℚ) • standardComplexLocalClass ℚ d := by
  classical
  let E := Fin d → ℂ
  let J := a3b4_neighborhoodPairMap U (S : Set E)
  let G := a3b4_supportPairMap
    (TopCat.ofHom ⟨fun u : U => g u.1, hg.domRestrict⟩)
    {u : U | u.1 ∈ S} ({0} : Set E) (fun u hu => (hS u.1 u.2).mp hu)
  choose z hz hzother hzmap using fun x : S =>
    regular_fibre_point_class_on_open d U hU g hg S hSU hS x (A x) (hA x) (hd x)
  change ∀ x : S, relativeHomologyMap ℚ (2 * d) G (z x) =
    standardComplexLocalClass ℚ d at hzmap
  have hJ : Function.Injective (relativeHomologyMap ℚ (2 * d) J) := by
    exact (HodgeLean.RealDefs.j5c_excision hU S.finite_toSet.isClosed hSU (2 * d)).1
  have hn : Module.finrank ℝ E = 2 * d := by
    dsimp [E]
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  have hdet : Function.Injective (fun v : RelativeHomology ℚ
      (neighborhoodSupportComplementPair U (S : Set E)) (2 * d) =>
      fun x : S => relativeHomologyMap ℚ (2 * d)
        (J ≫ supportInclusionPairMap (TopCat.of E) (Set.singleton_subset_iff.mpr x.2)) v) := by
    intro a b hab
    apply hJ
    apply (a3b4a_gysin_finite_support_restrictions_bijective hn S).1
    funext x
    have h := congrFun hab x
    simpa only [relativeHomologyMap_comp, LinearMap.comp_apply] using h
  have hsum : α = ∑ x : S, z x := by
    apply hdet
    funext y
    change relativeHomologyMap ℚ (2 * d)
      (J ≫ supportInclusionPairMap (TopCat.of E) (Set.singleton_subset_iff.mpr y.2)) α =
      relativeHomologyMap ℚ (2 * d)
        (J ≫ supportInclusionPairMap (TopCat.of E) (Set.singleton_subset_iff.mpr y.2)) (∑ x : S, z x)
    rw [map_sum, Finset.sum_eq_single y]
    · exact (hα y).trans (hz y).symm
    · intro x _ hxy
      exact hzother x y hxy.symm
    · simp
  change relativeHomologyMap ℚ (2 * d) G α = _
  rw [hsum, map_sum]
  simp only [hzmap, Finset.sum_const, Finset.card_univ, Fintype.card_coe]
  exact (Nat.cast_smul_eq_nsmul ℚ S.card (standardComplexLocalClass ℚ d)).symm

theorem isolated_degree_on_open_of_regular_deformation
    (d : ℕ) (U : Set (Fin d → ℂ)) (hU : IsOpen U) (h0U : 0 ∈ U)
    (f : C(U, Fin d → ℂ)) (g : (Fin d → ℂ) → (Fin d → ℂ)) (hg : ContinuousOn g U)
    (H : ContinuousMap.Homotopy f ⟨fun u : U => g u.1, hg.domRestrict⟩)
    (K : Set (Fin d → ℂ)) (hK : IsCompact K) (hKU : K ⊆ U) (h0K : 0 ∈ K)
    (hf : ∀ u : U, f u = 0 → u.1 = 0)
    (hH : ∀ (t : unitInterval) (u : U), H (t, u) = 0 → u.1 ∈ K)
    (S : Finset (Fin d → ℂ)) (hSU : (S : Set (Fin d → ℂ)) ⊆ U)
    (hS : ∀ x ∈ U, g x = 0 ↔ x ∈ S)
    (A : S → Matrix (Fin d) (Fin d) ℂ) (hA : ∀ x, (A x).det ≠ 0)
    (hd : ∀ x : S, HasFDerivAt (fun z => g (z + x.1))
      ((A x).mulVecLin.toContinuousLinearMap : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) 0)
    (z : RelativeHomology ℚ (neighborhoodPointComplementPair U 0) (2 * d))
    (hz : relativeHomologyMap ℚ (2 * d) (neighborhoodPointComplementPairMap U 0) z =
      standardComplexLocalClass ℚ d) :
    relativeHomologyMap ℚ (2 * d)
      (a3b4_supportPairMap (TopCat.ofHom f) {u : U | u.1 = 0}
        ({0} : Set (Fin d → ℂ)) hf) z = (S.card : ℚ) • standardComplexLocalClass ℚ d := by
  classical
  let E := Fin d → ℂ
  let G : C(U, E) := ⟨fun u : U => g u.1, hg.domRestrict⟩
  have hgK : ∀ u : U, G u = 0 → u.1 ∈ K := by
    intro u hu
    apply hH 1 u
    exact (H.map_one_left u).trans hu
  have hfK : ∀ u : U, f u = 0 → u.1 ∈ K := fun u hu => hf u hu ▸ h0K
  have hSK : (S : Set E) ⊆ K := fun x hx =>
    hgK ⟨x, hSU hx⟩ ((hS x (hSU hx)).mpr hx)
  have hn : Module.finrank ℝ E = 2 * d := by
    dsimp [E]
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  obtain ⟨α, hα⟩ := HodgeLean.RealDefs.j5c_hasClassAlong_of_isCompact
    (M := E) (E := E) hn (HodgeLean.RealDefs.translatedStandardComplexLocalClass d)
    (HodgeLean.RealDefs.j5c_translatedStandardComplexLocalClass_locallyCoherent d) hK
  let J := a3b4_neighborhoodPairMap U K
  have hJ : Function.Bijective (relativeHomologyMap ℚ (2 * d) J) :=
    HodgeLean.RealDefs.j5c_excision hU hK.isClosed hKU (2 * d)
  obtain ⟨β, hβ⟩ := hJ.2 α
  let R := supportInclusionPairMap (TopCat.of U)
    (show {u : U | u.1 = 0} ⊆ {u : U | u.1 ∈ K} from by
      intro u hu
      change u.1 ∈ K
      rw [show u.1 = 0 from hu]
      exact h0K)
  have hres : relativeHomologyMap ℚ (2 * d) R β = z := by
    apply (neighborhoodPointComplement_relativeHomologyMap_bijective U 0 hU h0U (2 * d)).1
    have heq : R ≫ neighborhoodPointComplementPairMap U 0 =
        J ≫ supportInclusionPairMap (TopCat.of E) (Set.singleton_subset_iff.mpr h0K) := by
      apply MorphismProperty.Arrow.Hom.ext <;> ext u <;> rfl
    rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp, heq,
      relativeHomologyMap_comp, LinearMap.comp_apply, hβ, hα 0 h0K, hz]
    have htranslation : translationPointComplementPairMap E 0 =
        𝟙 (pointComplementPair (0 : E)) := by
      apply MorphismProperty.Arrow.Hom.ext
      · ext u
        apply Subtype.ext
        exact add_zero u.1
      · ext u
        exact @add_zero E _ u
    unfold HodgeLean.RealDefs.translatedStandardComplexLocalClass
    rw [htranslation, relativeHomologyMap_id]
    rfl
  let R₁ := supportInclusionPairMap (TopCat.of U)
    (show {u : U | u.1 ∈ S} ⊆ {u : U | u.1 ∈ K} from fun u hu => hSK hu)
  let β₁ := relativeHomologyMap ℚ (2 * d) R₁ β
  have hpoint : ∀ x : S, relativeHomologyMap ℚ (2 * d)
      (a3b4_neighborhoodPairMap U (S : Set E) ≫
        supportInclusionPairMap (TopCat.of E) (Set.singleton_subset_iff.mpr x.2)) β₁ =
      HodgeLean.RealDefs.translatedStandardComplexLocalClass d x.1 := by
    intro x
    have heq : R₁ ≫ (a3b4_neighborhoodPairMap U (S : Set E) ≫
        supportInclusionPairMap (TopCat.of E) (Set.singleton_subset_iff.mpr x.2)) =
        J ≫ supportInclusionPairMap (TopCat.of E) (Set.singleton_subset_iff.mpr (hSK x.2)) := by
      apply MorphismProperty.Arrow.Hom.ext <;> ext u <;> rfl
    change relativeHomologyMap ℚ (2 * d) _ (relativeHomologyMap ℚ (2 * d) R₁ β) = _
    rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp, heq,
      relativeHomologyMap_comp, LinearMap.comp_apply, hβ, hα x.1 (hSK x.2)]
  have heq₀ : a3b4_supportPairMap (TopCat.ofHom f) {u : U | u.1 ∈ K} {0} hfK =
      R ≫ a3b4_supportPairMap (TopCat.ofHom f) {u : U | u.1 = 0} {0} hf := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext u <;> rfl
  have heq₁ : a3b4_supportPairMap (TopCat.ofHom G) {u : U | u.1 ∈ K} {0} hgK =
      R₁ ≫ a3b4_supportPairMap (TopCat.ofHom G) {u : U | u.1 ∈ S} {0}
        (fun u hu => (hS u.1 u.2).mp hu) := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext u <;> rfl
  have hmove := congrArg (fun L => L β)
    (a3b4a_gysin_homologyMap_deformation H {u : U | u.1 ∈ K} {0} hfK hgK hH (2 * d))
  rw [heq₀, heq₁, relativeHomologyMap_comp, relativeHomologyMap_comp,
    LinearMap.comp_apply, LinearMap.comp_apply, hres] at hmove
  rw [hmove]
  exact regular_fibre_degree_on_open d U hU g hg S hSU hS A hA hd β₁ hpoint

theorem isolated_zero_translation_trapping_on_open
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (O : Set E) (f : E → E) (hf : ContinuousOn f O)
    (r ρ : ℝ) (hρ : 0 < ρ) (hO : Metric.closedBall (0 : E) r ⊆ O)
    (hiso : ∀ x ∈ Metric.closedBall (0 : E) r, f x = 0 → x = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a : E, ‖a‖ < ε →
      ∀ (t : unitInterval) (x : E), x ∈ Metric.closedBall (0 : E) r →
        f x - (t : ℝ) • a = 0 → x ∈ Metric.ball (0 : E) ρ := by
  let K := Metric.closedBall (0 : E) r \ Metric.ball (0 : E) ρ
  have hK : IsCompact K := (isCompact_closedBall (0 : E) r).diff Metric.isOpen_ball
  have hbound : ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K, ε ≤ ‖f x‖ := by
    apply hK.exists_forall_le' (hf.mono (fun x hx => hO hx.1)).norm
    intro x hx
    apply norm_pos_iff.mpr
    intro hz
    exact hx.2 (hiso x hx.1 hz ▸ Metric.mem_ball_self hρ)
  obtain ⟨ε, hε, hb⟩ := hbound
  refine ⟨ε, hε, ?_⟩
  intro a ha t x hx hz
  by_contra hxρ
  have heq : f x = (t : ℝ) • a := sub_eq_zero.mp hz
  have ht : ‖(t : ℝ) • a‖ ≤ ‖a‖ := by
    rw [norm_smul, Real.norm_of_nonneg t.2.1]
    exact mul_le_of_le_one_left (norm_nonneg a) t.2.2
  exact (not_le_of_gt ha) ((hb x ⟨hx, hxρ⟩).trans (heq ▸ ht))

end AlgebraicGeometry.SingularCycles
