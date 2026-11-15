import HodgeLean.Foundations.BundleResolution.ChernDefs
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.UnitInterval

/-! # Open radial restrictions of bundle neighbourhoods

The whole compact interval of scalar multiples is retained in the source.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open Bundle Topology TopologicalSpace
namespace HodgeLean.Foundations.TubularEuler

theorem isOpen_forall_compact_parameter {X T : Type*}
    [TopologicalSpace X] [TopologicalSpace T] [CompactSpace T]
    {Y : Type*} [TopologicalSpace Y] (f : T × X → Y) (hf : Continuous f)
    {U : Set Y} (hU : IsOpen U) :
    IsOpen {x : X | ∀ t : T, f (t, x) ∈ U} := by
  classical
  have hc : IsClosed (Prod.fst '' ((fun p : X × T => f (p.2, p.1)) ⁻¹' Uᶜ)) :=
    isClosedMap_fst_of_compactSpace _
      (hU.isClosed_compl.preimage (hf.comp continuous_swap))
  convert hc.isOpen_compl using 1
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_image, Set.mem_preimage,
    not_exists, not_and]
  constructor
  · intro h p hp he
    exact hp (he ▸ h p.2)
  · intro h t
    by_contra hn
    exact h (x, t) hn rfl

theorem bundle_real_smul_continuous {B : Type} [TopologicalSpace B] {k : ℕ}
    (E : B → Type) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
    [FiberBundle (Fin k → ℂ) E] [VectorBundle ℂ (Fin k → ℂ) E] :
    Continuous (fun p : ℝ × TotalSpace (Fin k → ℂ) E =>
      (⟨p.2.proj, (p.1 : ℂ) • p.2.2⟩ : TotalSpace (Fin k → ℂ) E)) := by
  have hb : Continuous (fun p : ℝ × TotalSpace (Fin k → ℂ) E => p.2.proj) :=
    (FiberBundle.continuous_proj (Fin k → ℂ) E).comp continuous_snd
  apply continuous_iff_continuousAt.mpr
  intro p
  let e := trivializationAt (Fin k → ℂ) E p.2.proj
  have hp : p.2.proj ∈ e.baseSet := mem_baseSet_trivializationAt _ _ _
  apply e.continuousAt_of_comp_left
    (f := fun y : ℝ × TotalSpace (Fin k → ℂ) E =>
      (⟨y.2.proj, (y.1 : ℂ) • y.2.2⟩ : TotalSpace (Fin k → ℂ) E))
    hb.continuousAt hp
  have he : ContinuousAt (fun y : ℝ × TotalSpace (Fin k → ℂ) E => e y.2) p :=
    (e.continuousAt (e.mem_source.mpr hp)).comp continuous_snd.continuousAt
  have hc := hb.continuousAt.prodMk
    (((Complex.continuous_ofReal.comp continuous_fst).continuousAt).smul he.snd)
  apply hc.congr_of_eventuallyEq
  filter_upwards [hb.continuousAt.eventually (e.open_baseSet.mem_nhds hp)] with y hy
  change e (⟨y.2.proj, (y.1 : ℂ) • y.2.2⟩ : TotalSpace (Fin k → ℂ) E) =
    (y.2.proj, (y.1 : ℂ) • (e y.2).2)
  rw [e.apply_eq_prod_continuousLinearEquivAt ℂ _ hy,
    e.apply_eq_prod_continuousLinearEquivAt ℂ _ hy, map_smul]

theorem bundle_radial_shrinking {B : Type} [TopologicalSpace B] {k : ℕ}
    (E : B → Type) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [∀ x, TopologicalSpace (E x)] [TopologicalSpace (TotalSpace (Fin k → ℂ) E)]
    [FiberBundle (Fin k → ℂ) E] [VectorBundle ℂ (Fin k → ℂ) E]
    (U : Opens (TotalSpace (Fin k → ℂ) E))
    (hU : ∀ x, zeroSection (Fin k → ℂ) E x ∈ U) :
    ∃ R : Opens (TotalSpace (Fin k → ℂ) E),
      (R : Set (TotalSpace (Fin k → ℂ) E)) ⊆
        (U : Set (TotalSpace (Fin k → ℂ) E)) ∧
      (∀ x, zeroSection (Fin k → ℂ) E x ∈ R) ∧
      ∀ z : R, ∀ a : ℝ, a ∈ Set.Icc 0 1 →
        (⟨z.val.proj, (a : ℂ) • z.val.2⟩ : TotalSpace (Fin k → ℂ) E) ∈ R := by
  let f : unitInterval × TotalSpace (Fin k → ℂ) E → TotalSpace (Fin k → ℂ) E :=
    fun p => ⟨p.2.proj, ((p.1 : ℝ) : ℂ) • p.2.2⟩
  have hf : Continuous f := (bundle_real_smul_continuous E).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  let R : Opens (TotalSpace (Fin k → ℂ) E) :=
    ⟨{z | ∀ a : unitInterval, f (a, z) ∈ U},
      isOpen_forall_compact_parameter f hf U.isOpen⟩
  refine ⟨R, ?_, ?_, ?_⟩
  · intro z hz
    change z ∈ U
    have h := hz (1 : unitInterval)
    change (⟨z.proj, (1 : ℂ) • z.2⟩ : TotalSpace (Fin k → ℂ) E) ∈ U at h
    simpa only [one_smul] using h
  · intro x a
    simpa only [f, zeroSection, smul_zero] using hU x
  · intro z a ha b
    let c : unitInterval := ⟨(b : ℝ) * a, by
      constructor
      · exact mul_nonneg b.property.1 ha.1
      · nlinarith [b.property.1, b.property.2, ha.1, ha.2]⟩
    have h := z.property c
    change (⟨z.val.proj, ((b : ℝ) : ℂ) • ((a : ℂ) • z.val.2)⟩ :
      TotalSpace (Fin k → ℂ) E) ∈ U
    simpa only [f, c, Complex.ofReal_mul, mul_smul] using h

#print axioms bundle_radial_shrinking
#print axioms bundle_real_smul_continuous
#print axioms isOpen_forall_compact_parameter

end HodgeLean.Foundations.TubularEuler
