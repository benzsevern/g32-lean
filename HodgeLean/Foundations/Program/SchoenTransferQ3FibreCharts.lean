import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.ContinuousOn

/-! Normal coordinates on an actual embedded level-set fibre. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Topology Function Set
namespace HodgeLean.Foundations.Program

/-- Restricting an ambient product chart to an embedded tangential level
set gives a chart with precisely the ambient normal coordinates. -/
theorem s4_q3_embedded_fibre_normal_chart
    {M N E F : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [TopologicalSpace E] [TopologicalSpace F]
    (j : N → M) (hj : IsEmbedding j) (e : OpenPartialHomeomorph M (E × F)) (a : E)
    (hlevel : ∀ m ∈ e.source, m ∈ Set.range j ↔ (e m).1 = a)
    (x : N) (hx : j x ∈ e.source) :
    ∃ es : OpenPartialHomeomorph N F,
      es.source = j ⁻¹' e.source ∧ x ∈ es.source ∧
        ∀ n, es n = (e (j n)).2 := by
  letI : Nonempty N := ⟨x⟩
  let S : Set N := j ⁻¹' e.source
  let V : Set F := (fun v => (a, v)) ⁻¹' e.target
  let f : N → F := fun n => (e (j n)).2
  let g : F → N := fun v => Function.invFun j (e.symm (a, v))
  have htan (n : N) (hn : n ∈ S) : (e (j n)).1 = a :=
    (hlevel (j n) hn).mp ⟨n, rfl⟩
  have hpair (n : N) (hn : n ∈ S) : (a, f n) = e (j n) :=
    Prod.ext (htan n hn).symm rfl
  have hinv (v : F) (hv : v ∈ V) : j (g v) = e.symm (a, v) := by
    apply Function.invFun_eq
    apply (hlevel _ (e.map_target hv)).mpr
    exact congrArg Prod.fst (e.right_inv hv)
  let es : OpenPartialHomeomorph N F :=
    { toFun := f
      invFun := g
      source := S
      target := V
      map_source' := by
        intro n hn
        change (a, f n) ∈ e.target
        rw [hpair n hn]
        exact e.map_source hn
      map_target' := by
        intro v hv
        change j (g v) ∈ e.source
        rw [hinv v hv]
        exact e.map_target hv
      left_inv' := by
        intro n hn
        change Function.invFun j (e.symm (a, f n)) = n
        rw [hpair n hn, e.left_inv hn]
        exact Function.leftInverse_invFun hj.injective n
      right_inv' := by
        intro v hv
        change (e (j (g v))).2 = v
        rw [hinv v hv]
        exact congrArg Prod.snd (e.right_inv hv)
      continuousOn_toFun :=
        (e.continuousOn.comp hj.continuous.continuousOn (fun _ h => h)).snd
      continuousOn_invFun := by
        apply hj.continuousOn_iff.mpr
        have hc : ContinuousOn (fun v => e.symm (a, v)) V :=
          e.symm.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
            (fun _ h => h)
        exact hc.congr hinv
      open_source := e.open_source.preimage hj.continuous
      open_target := e.open_target.preimage (continuous_const.prodMk continuous_id) }
  exact ⟨es, rfl, hx, fun _ => rfl⟩

end HodgeLean.Foundations.Program
