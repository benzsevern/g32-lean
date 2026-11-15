import HodgeLean.Adapters.NormalConeB4aGysinTransverseDisk

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicTopology.Singular

/-- A disk agreeing near its centre with the image of a transverse disk
represents the image of the flattened normal generator. -/
theorem a3b4a_gysin_disk_image_normalClass
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {r c : ℕ}
    (e : OpenPartialHomeomorph X ((Fin r → ℂ) × (Fin c → ℂ)))
    (S : Set X) (T : Set Y) (hS : ∀ x ∈ e.source, x ∈ S ↔ (e x).2 = 0)
    (y : X) (hy : y ∈ e.source) (hyS : y ∈ S)
    (f : C(X, Y)) (hf : ∀ x, f x ∈ T → x ∈ S)
    (g : (Fin c → ℂ) → X) (V : Set (Fin c → ℂ))
    (hV : IsOpen V) (h0V : 0 ∈ V) (hg : ContinuousOn g V) (hg0 : g 0 = y)
    (A : Matrix (Fin c) (Fin c) ℂ) (hA : A.det ≠ 0)
    (hd : HasFDerivAt (fun v => (e (g v)).2)
      (A.mulVecLin.toContinuousLinearMap : (Fin c → ℂ) →L[ℂ] (Fin c → ℂ)) 0)
    (F : C((Fin c → ℂ), Y)) (ρ : ℝ) (hρ : 0 < ρ)
    (hFg : ∀ v ∈ V ∩ Metric.ball 0 ρ, F v = f (g v))
    (hiso : ∀ v ∈ Metric.ball 0 ρ, F v ∈ T → v = 0) :
    ∃ z : RelativeHomology ℚ (neighborhoodPointComplementPair (Metric.ball (0 : Fin c → ℂ) ρ) 0)
        (2 * c),
      relativeHomologyMap ℚ (2 * c)
        (neighborhoodPointComplementPairMap (Metric.ball (0 : Fin c → ℂ) ρ) 0) z =
          standardComplexLocalClass ℚ c ∧
      relativeHomologyMap ℚ (2 * c)
        (a3b4_supportPairMap
          (TopCat.ofHom ⟨fun v : Metric.ball (0 : Fin c → ℂ) ρ => F v.1,
            F.continuous.comp continuous_subtype_val⟩)
          {v : Metric.ball (0 : Fin c → ℂ) ρ | v.1 = 0} T
          (fun v hv => hiso v.1 v.2 hv)) z =
        relativeHomologyMap ℚ (2 * c)
          (a3b4_supportPairMap (TopCat.ofHom f) S T hf)
          (relativeHomologyMap ℚ (2 * c)
            (a3b4_neighborhoodPairMap (flattenedSupportNeighborhood (Fin r → ℂ) c e y hy) S)
            (flattenedSupportNormalClass (Fin r → ℂ) c e y hy S hS ((hS y hy).mp hyS))) := by
  let B := Metric.ball (0 : Fin c → ℂ) ρ
  let D := V ∩ B
  have hD : IsOpen D := hV.inter Metric.isOpen_ball
  have h0D : (0 : Fin c → ℂ) ∈ D := ⟨h0V, Metric.mem_ball_self hρ⟩
  obtain ⟨W, hWD, hW, h0W, hWS, hnormal⟩ :=
    a3b4a_gysin_transverse_disk_normalClass e S hS y hy hyS D hD h0D g
      (hg.mono Set.inter_subset_left) hg0 A hA hd
  have hWB : W ⊆ B := hWD.trans Set.inter_subset_right
  let J := a3b4_supportPairMap
    (TopCat.ofHom ⟨fun w : W => (⟨w.1, hWB w.2⟩ : B),
      continuous_subtype_val.subtype_mk _⟩)
    {w : W | w.1 = 0} {v : B | v.1 = 0} (fun _ h => h)
  obtain ⟨zW, hzW⟩ :=
    (neighborhoodPointComplement_relativeHomologyMap_bijective W 0 hW h0W (2 * c)).2
      (standardComplexLocalClass ℚ c)
  let z := relativeHomologyMap ℚ (2 * c) J zW
  have hz : relativeHomologyMap ℚ (2 * c) (neighborhoodPointComplementPairMap B 0) z =
      standardComplexLocalClass ℚ c := by
    change relativeHomologyMap ℚ (2 * c) (neighborhoodPointComplementPairMap B 0)
      (relativeHomologyMap ℚ (2 * c) J zW) = _
    rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp]
    have heq : J ≫ neighborhoodPointComplementPairMap B 0 =
        neighborhoodPointComplementPairMap W 0 := by
      apply MorphismProperty.Arrow.Hom.ext <;> ext w <;> rfl
    rw [heq]
    exact hzW
  refine ⟨z, hz, ?_⟩
  let G := a3b4_supportPairMap
    (TopCat.ofHom ⟨fun w : W => g w.1, ((hg.mono Set.inter_subset_left).mono hWD).domRestrict⟩)
    {w : W | w.1 = 0} S hWS
  let H := a3b4_supportPairMap (TopCat.ofHom f) S T hf
  let Q := a3b4_supportPairMap
    (TopCat.ofHom ⟨fun v : B => F v.1, F.continuous.comp continuous_subtype_val⟩)
    {v : B | v.1 = 0} T (fun v hv => hiso v.1 v.2 hv)
  have heq : J ≫ Q = G ≫ H := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext w
      apply Subtype.ext
      exact hFg w.1.1 (hWD w.1.2)
    · ext w
      exact hFg w.1 (hWD w.2)
  change relativeHomologyMap ℚ (2 * c) Q
      (relativeHomologyMap ℚ (2 * c) J zW) = _
  rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp, heq,
    relativeHomologyMap_comp, LinearMap.comp_apply]
  exact congrArg (relativeHomologyMap ℚ (2 * c) H) (hnormal zW hzW)

end HodgeLean.Adapters
