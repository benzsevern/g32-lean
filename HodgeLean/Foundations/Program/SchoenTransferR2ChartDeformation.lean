import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.Algebra.Module.Basic

/-! # Ambient deformations in flat normal charts

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open TopologicalSpace Topology
namespace HodgeLean.Foundations.Program

/-- A normal-star-shaped chart and a supported cutoff give an ambient homotopy
whose endpoint sends the cutoff plateau into the flat subset.
Source: Hatcher, Algebraic Topology, §0, coordinate deformations and homotopies.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_flat_chart_deformation
    {X E F : Type*} [TopologicalSpace X] [TopologicalSpace E] [TopologicalSpace F]
    [AddCommGroup F] [Module ℝ F] [ContinuousSMul ℝ F]
    (S : Set X) (e : OpenPartialHomeomorph X (E × F))
    (hflat : ∀ x ∈ e.source, x ∈ S ↔ (e x).2 = 0)
    (hstar : ∀ y ∈ e.target, ∀ s ∈ Set.Icc (0 : ℝ) 1, (y.1, s • y.2) ∈ e.target)
    (b : C(X, ℝ)) (hsupport : tsupport b ⊆ e.source)
    (hb : ∀ x, b x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ f : C(X, X), Nonempty (ContinuousMap.Homotopy (ContinuousMap.id X) f) ∧
      (∀ x ∈ S, f x = x) ∧ Set.MapsTo f {x | b x = 1} S := by
  classical
  let c (p : unitInterval × X) : E × F :=
    ((e p.2).1, (1 - (p.1 : ℝ) * b p.2) • (e p.2).2)
  let G (p : unitInterval × X) : X := if p.2 ∈ e.source then e.symm (c p) else p.2
  let A : Set (unitInterval × X) := Prod.snd ⁻¹' e.source
  let B : Set (unitInterval × X) := Prod.snd ⁻¹' (tsupport b)ᶜ
  have hc (p : unitInterval × X) (hp : p ∈ A) : c p ∈ e.target := by
    apply hstar (e p.2) (e.map_source hp)
    constructor
    · nlinarith [p.1.property.1, p.1.property.2, (hb p.2).1, (hb p.2).2]
    · nlinarith [p.1.property.1, p.1.property.2, (hb p.2).1, (hb p.2).2]
  have hxy : ContinuousOn (fun p : unitInterval × X => e p.2) A :=
    e.continuousOn.comp continuous_snd.continuousOn (fun _ h => h)
  have hscale : Continuous (fun p : unitInterval × X => 1 - (p.1 : ℝ) * b p.2) := by
    fun_prop
  have hcoords : ContinuousOn c A := hxy.fst.prodMk (hscale.continuousOn.smul hxy.snd)
  have hGA : ContinuousOn G A := by
    apply (e.symm.continuousOn.comp hcoords hc).congr
    intro p hp
    exact if_pos hp
  have hGBval (p : unitInterval × X) (hp : p ∈ B) : G p = p.2 := by
    have hb0 : b p.2 = 0 := image_eq_zero_of_notMem_tsupport hp
    dsimp only [G]
    split_ifs with hx
    · dsimp only [c]
      simpa only [hb0, mul_zero, sub_zero, one_smul, Prod.mk.eta] using e.left_inv hx
    · rfl
  have hGB : ContinuousOn G B :=
    continuous_snd.continuousOn.congr (fun p hp => hGBval p hp)
  have hG : Continuous G := by
    rw [continuous_iff_continuousAt]
    intro p
    by_cases hp : p.2 ∈ e.source
    · exact hGA.continuousAt ((e.open_source.preimage continuous_snd).mem_nhds hp)
    · have hb' : p.2 ∉ tsupport b := fun h => hp (hsupport h)
      exact hGB.continuousAt ((isClosed_tsupport b).isOpen_compl.preimage
        continuous_snd |>.mem_nhds hb')
  have hG0 (x : X) : G (0, x) = x := by
    dsimp only [G]
    split_ifs with hx
    · dsimp only [c]
      simpa using e.left_inv hx
    · rfl
  let f : C(X, X) := ⟨fun x => G (1, x), hG.comp (continuous_const.prodMk continuous_id)⟩
  have HH : ContinuousMap.Homotopy (ContinuousMap.id X) f :=
    { toContinuousMap := ⟨G, hG⟩
      map_zero_left := hG0
      map_one_left := fun _ => rfl }
  refine ⟨f, ⟨HH⟩, ?_, ?_⟩
  · intro x hxS
    change G (1, x) = x
    dsimp only [G]
    split_ifs with hx
    · have hn := (hflat x hx).mp hxS
      dsimp only [c]
      have heq : ((e x).1, (0 : F)) = e x := by
        exact Prod.ext rfl hn.symm
      rw [hn, smul_zero, heq]
      exact e.left_inv hx
    · rfl
  · intro x hx
    change b x = 1 at hx
    have hx' : x ∈ e.source := hsupport (subset_tsupport b (by simpa [hx]))
    have ht := hc (1, x) hx'
    change G (1, x) ∈ S
    rw [show G (1, x) = e.symm (c (1, x)) from if_pos hx']
    apply (hflat _ (e.map_target ht)).mpr
    rw [e.right_inv ht]
    dsimp only [c]
    simp [hx]

#print axioms s4_assembly_flat_chart_deformation
end HodgeLean.Foundations.Program
