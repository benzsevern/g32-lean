import HodgeLean.Foundations.Program.SchoenCycleS3CotangentBasis

/-! # Cotangent generators indexed by a specified subset -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program.G32Native

/-- The classes of the specified image generators span the cotangent
module, retaining the original ideal and its subset labels. -/
theorem paired_c3_cotangent_image_generators_span {A σ : Type*} [CommRing A]
    (f : σ → A) (S : Set σ) :
    let I := Ideal.span (f '' S)
    ⊤ ≤ Submodule.span (A ⧸ I)
      (Set.range (fun j : S => I.toCotangent
        ⟨f j.val, Ideal.subset_span ⟨j.val, j.property, rfl⟩⟩)) := by
  dsimp only
  let I := Ideal.span (f '' S)
  let N := Submodule.span (A ⧸ I)
    (Set.range (fun j : S => I.toCotangent
      ⟨f j.val, Ideal.subset_span ⟨j.val, j.property, rfl⟩⟩))
  intro z hz
  clear hz
  obtain ⟨⟨a, ha⟩, rfl⟩ := I.toCotangent_surjective z
  change I.toCotangent ⟨a, ha⟩ ∈ N
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨j, hj, rfl⟩ := ha
    exact Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
  | zero => exact N.zero_mem
  | add a b ha hb hia hib =>
    change I.toCotangent (⟨a, ha⟩ + ⟨b, hb⟩) ∈ N
    rw [map_add]
    exact N.add_mem hia hib
  | smul c a ha hi =>
    change I.toCotangent (c • ⟨a, ha⟩) ∈ N
    rw [map_smul]
    exact N.smul_mem (Ideal.Quotient.mk I c) hi

end HodgeLean.Foundations.Program.G32Native
