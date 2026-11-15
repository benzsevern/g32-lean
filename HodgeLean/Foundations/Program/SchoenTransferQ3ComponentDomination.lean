import HodgeLean.Foundations.Program.SchoenTransferQ3SchemeOpen
import HodgeLean.Adapters.CycleClassFlatPullback

/-! Generic images of the unreduced inverse-image components. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
open scoped Classical
namespace HodgeLean.Foundations.Program

/-- An open scheme map sends every generic inverse-image component to the
specified target prime, retaining components before reduction. -/
theorem s4_q3_inverse_component_dominates
    {X W : Scheme} [IsNoetherian X] (q : X ⟶ W) (hq : IsOpenMap q)
    (x : W) (y : (ccm3_inverseIdeal q x).subscheme)
    (hy : closure ({y} : Set (ccm3_inverseIdeal q x).subscheme) ∈
      irreducibleComponents (ccm3_inverseIdeal q x).subscheme) :
    q ((ccm3_inverseIdeal q x).subschemeι y) = x := by
  let J := ccm3_inverseIdeal q x
  have hsupport : (J.support : Set X) = q ⁻¹' closure ({x} : Set W) := by
    dsimp only [J, ccm3_inverseIdeal]
    rw [Scheme.IdealSheafData.support_comap]
    change q ⁻¹' ((ccm3_primeIdeal W x).support : Set W) = _
    rw [ccm3_primeIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  obtain ⟨o, ho, ⟨t, ht⟩, hoc⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hy
  have hyo : y ∈ o :=
    (specializes_iff_mem_closure.mpr (hoc ht)).mem_open ho ht
  obtain ⟨V, hV, hVo⟩ := J.subschemeι.isClosedEmbedding.isInducing.isOpen_iff.mp ho
  have hyV : J.subschemeι y ∈ V := by
    change y ∈ J.subschemeι ⁻¹' V
    rwa [hVo]
  have hyS : J.subschemeι y ∈ (J.support : Set X) := by
    change J.subschemeι y ∈ (J.support : Set X)
    rw [← J.range_subschemeι]
    exact ⟨y, rfl⟩
  have hxy : Specializes x (q (J.subschemeι y)) :=
    specializes_iff_mem_closure.mpr (by
      rw [hsupport] at hyS
      exact hyS)
  have hxV : x ∈ q '' V := hxy.mem_open (hq V hV) ⟨_, hyV, rfl⟩
  obtain ⟨z, hzV, hzx⟩ := hxV
  have hzS : z ∈ (J.support : Set X) := by
    change z ∈ (J.support : Set X)
    rw [hsupport]
    change q z ∈ closure ({x} : Set W)
    rw [hzx]
    exact subset_closure (Set.mem_singleton x)
  obtain ⟨w, hwz⟩ := J.range_subschemeι.symm.subset hzS
  have hwo : w ∈ o := by
    rw [← hVo]
    change J.subschemeι w ∈ V
    rwa [hwz]
  have hyw : Specializes y w := specializes_iff_mem_closure.mpr (hoc hwo)
  have hyx : Specializes (q (J.subschemeι y)) x := by
    have hh := hyw.map (q.continuous.comp J.subschemeι.continuous)
    simpa only [Function.comp_apply, hwz, hzx] using hh
  exact (hyx.antisymm hxy).eq

end HodgeLean.Foundations.Program
