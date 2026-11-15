import HodgeLean.Foundations.ChowAbelianSurface2
import HodgeLean.Foundations.AnalyticGermCone
import HodgeLean.Foundations.ChowTheorem
import HodgeLean.Foundations.AnalyticGermRSAssembly

/-! # Cone closure and E² assembly proofs

Vertex extension is routed through the homogeneous-cone theorems.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace Set
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations.Curves
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
namespace HodgeLean.Foundations

theorem chowEE3_closure_eq_aux (n : ℕ) (A : Set (Fin (n + 1) → ℂ))
    (hzero : (0 : Fin (n + 1) → ℂ) ∉ A) (hne : A.Nonempty)
    (hclosed : IsClosed {z : {z : Fin (n + 1) → ℂ // z ≠ 0} | z.val ∈ A})
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ A, t • z ∈ A) :
    closure A = insert 0 A := by
  have himage : Subtype.val '' {z : {z : Fin (n + 1) → ℂ // z ≠ 0} |
      z.val ∈ A} = A := by
    ext z
    exact ⟨fun ⟨w, hw, he⟩ ↦ he ▸ hw,
      fun hz ↦ ⟨⟨z, fun he ↦ hzero (he ▸ hz)⟩, hz, rfl⟩⟩
  apply subset_antisymm
  · intro z hz
    by_cases hz0 : z = 0
    · exact Or.inl hz0
    · right
      apply (Topology.IsInducing.subtypeVal.isClosed_iff'.mp hclosed) ⟨z, hz0⟩
      change z ∈ closure (Subtype.val '' {w : {w : Fin (n + 1) → ℂ // w ≠ 0} | w.val ∈ A})
      rw [himage]
      exact hz
  · refine insert_subset ?_ subset_closure
    obtain ⟨x, hx⟩ := hne
    have hmem : (0 : ℂ) ∈ closure ({0}ᶜ : Set ℂ) := (dense_compl_singleton 0) 0
    have hcont : Continuous (fun t : ℂ ↦ t • x) := continuous_id.smul continuous_const
    have hm := mem_closure_image hcont.continuousAt hmem
    have hsub : (fun t : ℂ ↦ t • x) '' ({0}ᶜ : Set ℂ) ⊆ A := by
      rintro z ⟨t, ht, rfl⟩
      exact hscale t ht x hx
    simpa only [zero_smul] using closure_mono hsub hm

theorem chowEE3_vertex_extension_of_point_aux (n : ℕ) (A : Set (Fin (n + 1) → ℂ))
    (hzero : (0 : Fin (n + 1) → ℂ) ∉ A) (hne : A.Nonempty)
    (hclosed : IsClosed {z : {z : Fin (n + 1) → ℂ // z ≠ 0} | z.val ∈ A})
    (hscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ A, t • z ∈ A)
    (hloc : ∀ x ∈ A, ∃ U : Set (Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      U ⊆ {z | z ≠ 0} ∧ ∃ (m : ℕ) (f : Fin m → (Fin (n + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ A ↔ ∀ j, f j z = 0)) :
    IsClosedAnalytic (Fin (n + 1) → ℂ) (insert 0 A) := by
  obtain ⟨k, Cι, dι, hcover, hpiece⟩ :=
    adim9_cone_pure_cover n A hzero hne hclosed hscale hloc
  refine adim9_cone_vertex_extension_finite_union n k A Cι hcover (fun i ↦ ?_)
  obtain ⟨_, _, hz, hn, hc, hs, hl, hp⟩ := hpiece i
  obtain ⟨L, hsurj, honto, hproper, hfib, hcentral⟩ :=
    adim9_cone_pure_projection n (Cι i) hz hn hc hs hl (dι i) hp
  exact adim9_cone_vertex_extension n (Cι i) hz hn hc hs hl (dι i) L hp honto
    hsurj hproper hfib hcentral

theorem chowEE3_setLevel_aux :
    ∀ Z : Set (ComplexPoint (g3_power E 2)),
      IsClosedAnalytic (Fin (dim (g3_power E 2).left) → ℂ) Z →
        ∃ C : Set (g3_power E 2).left, IsClosed C ∧
          Z = (Point.underlying : ComplexPoint (g3_power E 2) →
            (g3_power E 2).left) ⁻¹' C := by
  classical
  intro Z hZ
  by_cases hne : Z.Nonempty
  swap
  · exact ⟨∅, isClosed_empty, by simp [not_nonempty_iff_eq_empty.mp hne]⟩
  let p := Classical.choice
    (inferInstance : IsProjective (g3_power E 2).hom).nonempty_presentation
  let K : Set (Fin (p.ambientDimension + 1) → ℂ) :=
    {z | ∃ hz : z ≠ 0, ∃ x ∈ Z, x.left ≫ p.immersion =
      ComplexProjectiveSpace.vectorToProjectiveSpace z hz}
  have hkzero : (0 : Fin (p.ambientDimension + 1) → ℂ) ∉ K :=
    fun ⟨hz, _⟩ ↦ hz rfl
  have hkne : K.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨z, hz⟩ := ComplexProjectiveSpace.surjective_vectorToComplexPoint
      (p.analyticImmersion x)
    exact ⟨z.val, z.property, x, hx, (congrArg (fun q ↦ q.left) hz).symm⟩
  have hkclosed : IsClosed {z : {z : Fin (p.ambientDimension + 1) → ℂ // z ≠ 0} |
      z.val ∈ K} := by
    convert chowEE2_punctured_closed p Z hZ.isClosed using 1
    ext z
    exact ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨z.property, h⟩⟩
  have hkscale : ∀ (t : ℂ), t ≠ 0 → ∀ z ∈ K, t • z ∈ K := by
    rintro t ht z ⟨hz, x, hx, he⟩
    exact ⟨smul_ne_zero ht hz, x, hx, he.trans
      (ComplexProjectiveSpace.vectorToProjectiveSpace_smul z hz t ht).symm⟩
  have hkloc : ∀ x ∈ K, ∃ U : Set (Fin (p.ambientDimension + 1) → ℂ),
      IsOpen U ∧ x ∈ U ∧ U ⊆ {z | z ≠ 0} ∧
      ∃ (m : ℕ) (f : Fin m → (Fin (p.ambientDimension + 1) → ℂ) → ℂ),
        (∀ j, AnalyticOnNhd ℂ (f j) U) ∧
        ∀ z ∈ U, (z ∈ K ↔ ∀ j, f j z = 0) := by
    intro x hx
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      exact hx.1 (funext fun i ↦ not_ne_iff.mp (not_exists.mp h i))
    obtain ⟨U, hU, hxU, hUi, hrest⟩ :=
      chow2_chart_cone p.ambientDimension K hkscale i
        (chowEE2_embedding_slices p Z hZ i) x hx hi
    refine ⟨U, hU, hxU, ?_, hrest⟩
    intro z hz he
    exact hUi hz (congrFun he i)
  have hD := chowEE3_vertex_extension_of_point_aux p.ambientDimension K
    hkzero hkne hkclosed hkscale hkloc
  have hDscale : ∀ (t : ℂ) (z : Fin (p.ambientDimension + 1) → ℂ),
      z ∈ insert 0 K → t • z ∈ insert 0 K := by
    intro t z hz
    by_cases ht : t = 0
    · simp only [ht, zero_smul, mem_insert_iff, true_or]
    rcases hz with rfl | hz
    · exact Or.inl (smul_zero t)
    · exact Or.inr (hkscale t ht z hz)
  obtain ⟨m, d, P, hP, hDP⟩ :=
    chow_cone_algebraic (p.ambientDimension + 1) (insert 0 K) hD hDscale
  let B := chowEE_projectiveCarrier p.ambientDimension m P
  refine ⟨p.immersion ⁻¹' B, isClosed_closure.preimage p.immersion.continuous, ?_⟩
  ext x
  obtain ⟨z, hz⟩ := ComplexProjectiveSpace.surjective_vectorToComplexPoint
    (p.analyticImmersion x)
  have hund : (ComplexProjectiveSpace.vectorToComplexPoint z.val z.property).underlying =
      p.immersion x.underlying :=
    (congrArg (fun q ↦ q.underlying) hz).trans
      (Point.underlying_map p.overImmersion x)
  change x ∈ Z ↔ p.immersion x.underlying ∈ B
  rw [← hund, chowEE_projectiveCarrier_mem p.ambientDimension m d P hP]
  change x ∈ Z ↔ z.val ∈ {z | ∀ j, MvPolynomial.eval z (P j) = 0}
  rw [← hDP]
  constructor
  · intro hx
    exact Or.inr ⟨z.property, x, hx, (congrArg (fun q ↦ q.left) hz).symm⟩
  · intro hzK
    rcases hzK with hz0 | ⟨_, y, hy, he⟩
    · exact (z.property hz0).elim
    · have hyx : p.analyticImmersion y = p.analyticImmersion x :=
        (Over.OverMorphism.ext he).trans hz
      exact p.analyticImmersion_isClosedEmbedding.injective hyx ▸ hy

end HodgeLean.Foundations
