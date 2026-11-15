import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCentroidChain
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbCentroidSubtype

/-! Independence of actual centroid chains inside a geometric base simplex. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_geometric_centroid_chain_independent {E : Type*}
    [AddCommGroup E] [Module ℝ E]
    (S : Finset E) (hS : AffineIndependent ℝ (fun i : S => i.val))
    (C : Finset (Finset E)) (hsub : ∀ T ∈ C, T ⊆ S)
    (hne : ∀ T ∈ C, T.Nonempty)
    (hchain : ∀ T ∈ C, ∀ U ∈ C, T ⊆ U ∨ U ⊆ T) :
    AffineIndepOn ℝ (fun T : Finset E => T.centroid ℝ id) (↑C : Set (Finset E)) := by
  classical
  let r : Finset E → Finset S := fun T => Finset.univ.filter (fun i => i.val ∈ T)
  let F := C.image r
  have hcoords (T : Finset E) (hT : T ∈ C) :
      (fun i : S => i.val) '' (↑(r T) : Set S) = (↑T : Set E) ∧
        (r T).centroid ℝ (fun i : S => i.val) = T.centroid ℝ id :=
    s2v_hardt6rb_centroid_subtype S T (hsub T hT)
  have hmono {T U : Finset E} (hTU : T ⊆ U) : r T ⊆ r U := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTU (Finset.mem_filter.mp hi).2⟩
  have hFne : ∀ T ∈ F, T.Nonempty := by
    intro T hT
    obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨x, hx⟩ := hne U hU
    exact ⟨⟨x, hsub U hU hx⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
  have hFchain : ∀ T ∈ F, ∀ U ∈ F, T ⊆ U ∨ U ⊆ T := by
    intro T hT U hU
    obtain ⟨T', hT', rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨U', hU', rfl⟩ := Finset.mem_image.mp hU
    rcases hchain T' hT' U' hU' with h | h
    · exact Or.inl (hmono h)
    · exact Or.inr (hmono h)
  let e : C ↪ F :=
    { toFun := fun T => ⟨r T.val, Finset.mem_image.mpr ⟨T.val, T.property, rfl⟩⟩
      inj' := by
        intro T U hTU
        have hr : r T.val = r U.val := congrArg Subtype.val hTU
        have he : (↑T.val : Set E) = (↑U.val : Set E) :=
          (hcoords T.val T.property).1.symm.trans
            ((congrArg (fun I : Finset S => (fun i : S => i.val) '' (↑I : Set S)) hr).trans
              (hcoords U.val U.property).1)
        exact Subtype.ext (Finset.coe_injective he) }
  have hi := (s2v_hardt6rb_centroid_chain_independent (fun i : S => i.val) hS F hFne hFchain).comp_embedding e
  change AffineIndependent ℝ (fun T : C => (r T.val).centroid ℝ (fun i : S => i.val)) at hi
  have he : (fun T : C => (r T.val).centroid ℝ (fun i : S => i.val)) =
      (fun T : C => T.val.centroid ℝ id) :=
    funext (fun T => (hcoords T.val T.property).2)
  rw [he] at hi
  exact hi

end HodgeLean.Foundations.Program
