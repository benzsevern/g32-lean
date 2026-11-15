import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.AffineSpace.Centroid

/-! Passing a geometric subface to subtype indices preserves its actual centroid. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_centroid_subtype {E : Type*}
    [AddCommGroup E] [Module ℝ E] [DecidableEq E] (S T : Finset E) (hTS : T ⊆ S) :
    let I : Finset S := Finset.univ.filter (fun i => i.val ∈ T)
    (fun i : S => i.val) '' (↑I : Set S) = (↑T : Set E) ∧
      I.centroid ℝ (fun i : S => i.val) = T.centroid ℝ id := by
  classical
  intro I
  have hmap : I.map (Function.Embedding.subtype (fun x => x ∈ S)) = T := by
    ext x
    simp only [I, Finset.mem_map, Function.Embedding.coe_subtype, Subtype.exists,
      exists_prop, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨y, hyS, hyT, rfl⟩
      exact hyT
    · intro hx
      exact ⟨x, hTS hx, hx, rfl⟩
  refine ⟨?_, ?_⟩
  · have hh := congrArg (fun Q : Finset E => (↑Q : Set E)) hmap
    simpa only [Finset.coe_map, Function.Embedding.coe_subtype] using hh
  · have hc := I.centroid_map ℝ (Function.Embedding.subtype (fun x => x ∈ S)) (id : E → E)
    rw [hmap] at hc
    exact hc.symm

end HodgeLean.Foundations.Program
