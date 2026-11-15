import HodgeLean.Adapters.NormalConeB4aGysinTransverseSum
import HodgeLean.Adapters.NormalConeB4aGysinDegreeDeformation

/-! # Deforming an isolated disk intersection to transverse intersections

A compact set traps the intersection during the deformation. Its orientation
class restricts to the initial normal generator and to each final point class.
-/

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular

/-- A compactly trapped deformation expresses an isolated disk intersection
as the sum of the ambient normal cycles of its transverse endpoint. -/
theorem a3b4a_gysin_isolated_disk_normalCycle_sum
    {Z : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of ℂ)}
    [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q]
    {γ : AlgebraicCycle Z ℚ} {c : ℕ}
    (U : Set (Fin c → ℂ)) (hU : IsOpen U) (h0U : 0 ∈ U)
    {f : C(U, ComplexPoint (Over.mk q))}
    (g : (Fin c → ℂ) → ComplexPoint (Over.mk q)) (hgcont : ContinuousOn g U)
    (H : ContinuousMap.Homotopy f ⟨fun u : U => g u.1, hgcont.domRestrict⟩)
    (K : Set (Fin c → ℂ)) (hK : IsCompact K) (hKU : K ⊆ U) (h0K : 0 ∈ K)
    (hf : ∀ u : U, f u ∈ a3b4_cycleSupport q γ → u.1 = 0)
    (hH : ∀ (t : unitInterval) (u : U), H (t, u) ∈ a3b4_cycleSupport q γ → u.1 ∈ K)
    (S : Finset (Fin c → ℂ)) (hSU : (S : Set (Fin c → ℂ)) ⊆ U)
    (hS : ∀ v ∈ U, g v ∈ a3b4_cycleSupport q γ ↔ v ∈ S)
    (C : S → A3b4aGysinNormalChart q γ c) (hC : ∀ x : S, g x.1 = (C x).point)
    (A : S → Matrix (Fin c) (Fin c) ℂ) (hA : ∀ x, (A x).det ≠ 0)
    (hderiv : ∀ x : S, HasFDerivAt (fun v => ((C x).chart (g (v + x.1))).2)
      ((A x).mulVecLin.toContinuousLinearMap : (Fin c → ℂ) →L[ℂ] (Fin c → ℂ)) 0)
    (z : RelativeHomology ℚ (neighborhoodPointComplementPair U 0) (2 * c))
    (hz : relativeHomologyMap ℚ (2 * c) (neighborhoodPointComplementPairMap U 0) z =
      standardComplexLocalClass ℚ c) :
    relativeHomologyMap ℚ (2 * c)
      (a3b4_supportPairMap (TopCat.ofHom f) {u : U | u.1 = 0}
        (a3b4_cycleSupport q γ) hf) z =
      ∑ x : S, a3b4a_gysin_normalCycle (C x) := by
  classical
  let E := Fin c → ℂ
  let T := a3b4_cycleSupport q γ
  let G : C(U, ComplexPoint (Over.mk q)) := ⟨fun u => g u.1, hgcont.domRestrict⟩
  have hgK : ∀ u : U, G u ∈ T → u.1 ∈ K := by
    intro u hu
    apply hH 1 u
    have he : H (1, u) = G u := H.map_one_left u
    exact he.symm ▸ hu
  have hfK : ∀ u : U, f u ∈ T → u.1 ∈ K := fun u hu => hf u hu ▸ h0K
  have hSK : (S : Set E) ⊆ K := fun x hx =>
    hgK ⟨x, hSU hx⟩ ((hS x (hSU hx)).mpr hx)
  have hn : Module.finrank ℝ E = 2 * c := by
    dsimp [E]
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  obtain ⟨α, hα⟩ := HodgeLean.RealDefs.j5c_hasClassAlong_of_isCompact
    (M := E) (E := E) hn (HodgeLean.RealDefs.translatedStandardComplexLocalClass c)
    (HodgeLean.RealDefs.j5c_translatedStandardComplexLocalClass_locallyCoherent c) hK
  let J := a3b4_neighborhoodPairMap U K
  have hJ : Function.Bijective (relativeHomologyMap ℚ (2 * c) J) := by
    have heq : TopPair.ofSubsetHom (A := {u : U | u.1 ∉ K}) (B := Kᶜ)
        (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ : TopCat.of U ⟶ TopCat.of E)
        (fun _ h => h) = J := by
      apply MorphismProperty.Arrow.Hom.ext <;> ext u <;> rfl
    rw [← heq]
    exact HodgeLean.RealDefs.j5c_excision hU hK.isClosed hKU (2 * c)
  obtain ⟨β, hβ⟩ := hJ.2 α
  let R := supportInclusionPairMap (TopCat.of U)
    (show {u : U | u.1 = 0} ⊆ {u : U | u.1 ∈ K} from by
      intro u hu
      change u.1 ∈ K
      rw [show u.1 = 0 from hu]
      exact h0K)
  have hres : relativeHomologyMap ℚ (2 * c) R β = z := by
    apply (neighborhoodPointComplement_relativeHomologyMap_bijective U 0 hU h0U (2 * c)).1
    have heq : R ≫ neighborhoodPointComplementPairMap U 0 =
        J ≫ supportInclusionPairMap (TopCat.of E) (Set.singleton_subset_iff.mpr h0K) := by
      apply MorphismProperty.Arrow.Hom.ext <;> ext u <;> rfl
    rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp, heq,
      relativeHomologyMap_comp, LinearMap.comp_apply, hβ, hα 0 h0K, hz]
    have htranslation : translationPointComplementPairMap E 0 =
        𝟙 (pointComplementPair (0 : E)) := by
      apply MorphismProperty.Arrow.Hom.ext
      · ext x
        apply Subtype.ext
        exact add_zero x.1
      · ext x
        exact @add_zero E _ x
    unfold HodgeLean.RealDefs.translatedStandardComplexLocalClass
    rw [htranslation, relativeHomologyMap_id]
    rfl
  let R₁ := supportInclusionPairMap (TopCat.of U)
    (show {u : U | u.1 ∈ S} ⊆ {u : U | u.1 ∈ K} from fun u hu => hSK hu)
  let β₁ := relativeHomologyMap ℚ (2 * c) R₁ β
  have hpoint : ∀ x : S, relativeHomologyMap ℚ (2 * c)
      (supportInclusionPairMap (TopCat.of E) (Set.singleton_subset_iff.mpr x.2))
      (relativeHomologyMap ℚ (2 * c) (a3b4_neighborhoodPairMap U (S : Set E)) β₁) =
        (1 : ℚ) • HodgeLean.RealDefs.translatedStandardComplexLocalClass c x.1 := by
    intro x
    have heq : R₁ ≫ a3b4_neighborhoodPairMap U (S : Set E) ≫
        supportInclusionPairMap (TopCat.of E) (Set.singleton_subset_iff.mpr x.2) =
        J ≫ supportInclusionPairMap (TopCat.of E) (Set.singleton_subset_iff.mpr (hSK x.2)) := by
      apply MorphismProperty.Arrow.Hom.ext <;> ext u <;> rfl
    change relativeHomologyMap ℚ (2 * c) _
      (relativeHomologyMap ℚ (2 * c) _ (relativeHomologyMap ℚ (2 * c) R₁ β)) = _
    rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp,
      ← LinearMap.comp_apply, ← relativeHomologyMap_comp, heq,
      relativeHomologyMap_comp, LinearMap.comp_apply, hβ, hα x.1 (hSK x.2), one_smul]
  have heq₀ : a3b4_supportPairMap (TopCat.ofHom f) {u : U | u.1 ∈ K} T hfK =
      R ≫ a3b4_supportPairMap (TopCat.ofHom f) {u : U | u.1 = 0} T hf := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext u <;> rfl
  have heq₁ : a3b4_supportPairMap (TopCat.ofHom G) {u : U | u.1 ∈ K} T hgK =
      R₁ ≫ a3b4_supportPairMap (TopCat.ofHom G) {u : U | u.1 ∈ S} T
        (fun u hu => (hS u.1 u.2).mp hu) := by
    apply MorphismProperty.Arrow.Hom.ext <;> ext u <;> rfl
  have hmove := congrArg (fun L => L β)
    (a3b4a_gysin_homologyMap_deformation H {u : U | u.1 ∈ K} T hfK hgK hH (2 * c))
  rw [heq₀, heq₁, relativeHomologyMap_comp, relativeHomologyMap_comp,
    LinearMap.comp_apply, LinearMap.comp_apply, hres] at hmove
  rw [hmove]
  simpa only [one_smul] using a3b4a_gysin_transverse_normalCycle_sum
    U hU g hgcont S hSU hS C hC A hA hderiv (fun _ => 1) β₁ hpoint


/-- The evaluation on an isolated disk is the sum of exact ambient multiplicities
at a transverse endpoint of a compactly trapped deformation. -/
theorem a3b4a_gysin_isolated_disk_evaluation_of_deformation
    {Z : Scheme.{0}} {q : Z ⟶ Spec (CommRingCat.of ℂ)}
    [LocallyOfFiniteType q] [QuasiCompact q] [IsSeparated q]
    {γ : AlgebraicCycle Z ℚ} {c : ℕ}
    (U : Set (Fin c → ℂ)) (hU : IsOpen U) (h0U : 0 ∈ U)
    {f : C(U, ComplexPoint (Over.mk q))}
    (g : (Fin c → ℂ) → ComplexPoint (Over.mk q)) (hgcont : ContinuousOn g U)
    (H : ContinuousMap.Homotopy f ⟨fun u : U => g u.1, hgcont.domRestrict⟩)
    (K : Set (Fin c → ℂ)) (hK : IsCompact K) (hKU : K ⊆ U) (h0K : 0 ∈ K)
    (hf : ∀ u : U, f u ∈ a3b4_cycleSupport q γ → u.1 = 0)
    (hH : ∀ (t : unitInterval) (u : U), H (t, u) ∈ a3b4_cycleSupport q γ → u.1 ∈ K)
    (S : Finset (Fin c → ℂ)) (hSU : (S : Set (Fin c → ℂ)) ⊆ U)
    (hS : ∀ v ∈ U, g v ∈ a3b4_cycleSupport q γ ↔ v ∈ S)
    (C : S → A3b4aGysinNormalChart q γ c) (hC : ∀ x : S, g x.1 = (C x).point)
    (A : S → Matrix (Fin c) (Fin c) ℂ) (hA : ∀ x, (A x).det ≠ 0)
    (hderiv : ∀ x : S, HasFDerivAt (fun v => ((C x).chart (g (v + x.1))).2)
      ((A x).mulVecLin.toContinuousLinearMap : (Fin c → ℂ) →L[ℂ] (Fin c → ℂ)) 0)
    (z : RelativeHomology ℚ (neighborhoodPointComplementPair U 0) (2 * c))
    (hz : relativeHomologyMap ℚ (2 * c) (neighborhoodPointComplementPairMap U 0) z =
      standardComplexLocalClass ℚ c)
    (β : RelativeCohomology ℚ
      (TopPair.ofSubset (X := a3b4_an q) (a3b4_cycleSupport q γ)ᶜ) (2 * c))
    (hβ : a3b4_IsCycleClass q γ c β) :
    relativeCohomologyEquivDualHomology ℚ _ (2 * c)
      (relativeCohomologyMap ℚ (2 * c)
        (a3b4_supportPairMap (TopCat.ofHom f) {u : U | u.1 = 0}
          (a3b4_cycleSupport q γ) hf) β) z =
      ∑ x : S, a3b4_multiplicity q γ (g x.1) := by
  classical
  rw [relativeCohomologyEquivDualHomology_relativeCohomologyMap,
    a3b4a_gysin_isolated_disk_normalCycle_sum U hU h0U g hgcont H K hK hKU h0K
      hf hH S hSU hS C hC A hA hderiv z hz, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [a3b4a_gysin_normalCycle_pairing (C x) β hβ, hC x]

end HodgeLean.Adapters
