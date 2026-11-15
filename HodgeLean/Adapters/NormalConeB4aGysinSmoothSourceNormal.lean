import HodgeLean.Adapters.NormalConeB4aGysinCoordinateEmbedding
import HodgeLean.Adapters.NormalConeB4aGysinSmoothCriticalParameters
import HodgeLean.Adapters.NormalConeB4aGysinEmbeddedSupportNormalOpen

noncomputable section
namespace HodgeLean.Adapters
open CategoryTheory AlgebraicGeometry
open HodgeLean.Foundations.Analytic

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- A regular parameter derivative on an actual smooth immersed source gives a
normal chart of the cycle whenever that source represents its local support. -/
theorem a3b4a_gysin_smooth_source_regular_normal_chart
    (X Y : Over (Spec (CommRingCat.of ℂ))) (n c : ℕ)
    [SmoothOfRelativeDimension n X.hom] [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsImmersion f.left] (γ : AlgebraicCycle Y.left ℚ)
    (Φ : OpenPartialHomeomorph (ComplexPoint Y) ((Fin n → ℂ) × (Fin c → ℂ)))
    (hΦ : a3b4_IsHolChart Y.hom Φ)
    (hS : ∀ y ∈ Φ.source, y ∈ a3b4_cycleSupport Y.hom γ ↔ y ∈ Set.range (Point.map f))
    (x j : ComplexPoint X) (hx : Point.map f x ∈ Φ.source)
    (hxj : x ∈ (chartAt (Fin n → ℂ) j).source)
    (hp : IsUnit (fderiv ℂ
      (fun a => (Φ (Point.map f ((chartAt (Fin n → ℂ) j).symm a))).1)
      ((chartAt (Fin n → ℂ) j) x))) :
    ∃ C : A3b4aGysinNormalChart Y.hom γ c, C.point = Point.map f x ∧
      HasFDerivAt (fun v' =>
        (C.chart (Φ.symm ((Φ (Point.map f x)).1, v' + (Φ (Point.map f x)).2))).2)
        (ContinuousLinearMap.id ℂ (Fin c → ℂ)) 0 := by
  let e := chartAt (Fin n → ℂ) j
  let V := Point.map f ⁻¹' Φ.source
  have hV : IsOpen V := Φ.open_source.preimage (Point.continuous_map f)
  let Ω := e.target ∩ e.symm ⁻¹' V
  have hΩ : IsOpen Ω := e.isOpen_inter_preimage_symm hV
  let η : (Fin n → ℂ) → ((Fin n → ℂ) × (Fin c → ℂ)) :=
    fun a => Φ (Point.map f (e.symm a))
  have hf := AnalytificationAn5_isEmbedding_map_of_immersion f
  have hη : Topology.IsEmbedding (fun a : Ω => η a) :=
    a3b4a_gysin_coordinate_embedding (Point.map f) hf e Φ
  obtain ⟨O, hO, himage⟩ := hf.isInducing.image_eq_isOpen_inter_range e.open_source
  have hxO : Point.map f x ∈ O := by
    have hm : Point.map f x ∈ Point.map f '' e.source := ⟨x, hxj, rfl⟩
    rw [himage] at hm
    exact hm.1
  let Ψ := Φ.restrOpen O hO
  have hxΨ : Point.map f x ∈ Ψ.source := ⟨hx, hxO⟩
  have hhol : a3b4_IsHolChart Y.hom Ψ := by
    constructor
    · intro k
      exact anrem_isHolFun_restrict (f4_analytification Y)
        (fun _ hz => hz.1) (hΦ.1 k)
    · intro k
      exact anrem_isHolFun_restrict (f4_analytification Y)
        (fun _ hz => hz.1) (hΦ.2 k)
  have hsupport : ∀ y ∈ Ψ.source,
      y ∈ a3b4_cycleSupport Y.hom γ ↔ Ψ y ∈ η '' Ω := by
    intro y hy
    constructor
    · intro hys
      have hyim : y ∈ Point.map f '' e.source := by
        rw [himage]
        exact ⟨hy.2, (hS y hy.1).mp hys⟩
      obtain ⟨z, hz, rfl⟩ := hyim
      refine ⟨e z, ⟨e.map_source hz, ?_⟩, ?_⟩
      · change e.symm (e z) ∈ V
        rw [e.left_inv hz]
        exact hy.1
      · change Φ (Point.map f (e.symm (e z))) = Φ (Point.map f z)
        rw [e.left_inv hz]
    · rintro ⟨a, ha, heq⟩
      have hyEq : Point.map f (e.symm a) = y := Φ.injOn ha.2 hy.1 heq
      exact (hS y hy.1).mpr ⟨e.symm a, hyEq⟩
  have hxΩ : e x ∈ Ω := by
    refine ⟨e.map_source hxj, ?_⟩
    change e.symm (e x) ∈ V
    rw [e.left_inv hxj]
    exact hx
  have hηx : η (e x) = Φ (Point.map f x) := by
    dsimp [η]
    rw [e.left_inv hxj]
  have htarget : η (e x) ∈ Ψ.target := by
    rw [hηx]
    exact Ψ.map_source hxΨ
  obtain ⟨C, hC, hd⟩ := a3b4a_gysin_open_embedded_support_normal_chart γ Ψ hhol
    η Ω hΩ hη (e x) hxΩ
    (a3b4a_gysin_smooth_source_coordinate_parametrization X Y n n c f Φ hΦ j _ hxΩ)
    hp htarget hsupport
  refine ⟨C, ?_, ?_⟩
  · change C.point = Φ.symm (η (e x)) at hC
    simpa only [hηx, Φ.left_inv hx] using hC
  · change HasFDerivAt (fun v' => (C.chart
      (Φ.symm ((η (e x)).1, v' + (η (e x)).2))).2) _ 0 at hd
    simpa only [hηx] using hd


/-- A smooth immersed presentation of the local cycle support has transverse
vertical slices at every point over parameters outside one null set. -/
theorem a3b4a_gysin_smooth_source_normal_parameters
    (X Y : Over (Spec (CommRingCat.of ℂ))) (n c : ℕ)
    [SmoothOfRelativeDimension n X.hom] [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X ⟶ Y) [IsImmersion f.left] (γ : AlgebraicCycle Y.left ℚ)
    (Φ : OpenPartialHomeomorph (ComplexPoint Y) ((Fin n → ℂ) × (Fin c → ℂ)))
    (hΦ : a3b4_IsHolChart Y.hom Φ)
    (hS : ∀ y ∈ Φ.source, y ∈ a3b4_cycleSupport Y.hom γ ↔ y ∈ Set.range (Point.map f)) :
    ∃ B : Set (Fin n → ℂ), MeasureTheory.volume B = 0 ∧
      ∀ x : ComplexPoint X, Point.map f x ∈ Φ.source → (Φ (Point.map f x)).1 ∉ B →
        ∃ C : A3b4aGysinNormalChart Y.hom γ c, C.point = Point.map f x ∧
          HasFDerivAt (fun v' =>
            (C.chart (Φ.symm ((Φ (Point.map f x)).1, v' + (Φ (Point.map f x)).2))).2)
            (ContinuousLinearMap.id ℂ (Fin c → ℂ)) 0 := by
  obtain ⟨B, hB, hregular⟩ :=
    a3b4a_gysin_smooth_source_regular_parameter_charts X Y n c f Φ hΦ
  refine ⟨B, hB, ?_⟩
  intro x hx hnot
  obtain ⟨j, hxj, hp⟩ := hregular x hx hnot
  exact a3b4a_gysin_smooth_source_regular_normal_chart X Y n c f γ Φ hΦ hS x j hx hxj hp

end HodgeLean.Adapters
