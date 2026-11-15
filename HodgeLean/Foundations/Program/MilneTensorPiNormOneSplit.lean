import HodgeLean.Foundations.Program.MilneTensorPiRepresentationSplit

noncomputable section
namespace HodgeLean.Foundations.Program
variable {ι : Type*} {R M : ι → Type*}
    [∀ i, Ring (R i)] [∀ i, Algebra ℂ (R i)]
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]

theorem m1b_pi_norm_one_split_image
    (ρ : (i : ι) → R i →ₐ[ℂ] Module.End ℂ (M i))
    (p : ι → Prop) [DecidablePred p]
    (τ : ((i : ι) → R i) ≃ₗ[ℂ] ((i : ι) → R i))
    (α : ((i : {i // p i}) → R i.val) ≃ₗ[ℂ] ((i : {i // p i}) → R i.val))
    (β : ((i : {i // ¬p i}) → R i.val) ≃ₗ[ℂ] ((i : {i // ¬p i}) → R i.val))
    (hparts : ∀ X, m1b_piSplitAlgEquiv R p (τ X) =
      (α (m1b_piSplitAlgEquiv R p X).1, β (m1b_piSplitAlgEquiv R p X).2)) :
    (m1b_piSplitModuleEquiv M p).conj '' (m1b_piRepresentation ρ '' {X | τ X * X = 1}) =
      Set.image2 (fun u v => u.prodMap v)
        (m1b_piRepresentation (fun i : {i // p i} => ρ i.val) '' {a | α a * a = 1})
        (m1b_piRepresentation (fun i : {i // ¬p i} => ρ i.val) '' {b | β b * b = 1}) := by
  let e := m1b_piSplitAlgEquiv R p
  let ρp := m1b_piRepresentation (fun i : {i // p i} => ρ i.val)
  let ρq := m1b_piRepresentation (fun i : {i // ¬p i} => ρ i.val)
  ext u
  constructor
  · rintro ⟨_, ⟨X, hX, rfl⟩, rfl⟩
    have h := congrArg e hX
    rw [map_mul, map_one, hparts] at h
    refine ⟨ρp (e X).1, ⟨(e X).1, congrArg Prod.fst h, rfl⟩,
      ρq (e X).2, ⟨(e X).2, congrArg Prod.snd h, rfl⟩, ?_⟩
    exact (m1b_piRepresentation_split_conj ρ p X).symm
  · rintro ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
    let X := e.symm (a, b)
    have hXE : e X = (a, b) := e.apply_symm_apply (a, b)
    have hX : τ X * X = 1 := by
      apply e.injective
      rw [map_mul, map_one, hparts, hXE]
      exact Prod.ext ha hb
    refine ⟨m1b_piRepresentation ρ X, ⟨X, hX, rfl⟩, ?_⟩
    rw [m1b_piRepresentation_split_conj]
    change (ρp (e X).1).prodMap (ρq (e X).2) = (ρp a).prodMap (ρq b)
    rw [hXE]

end HodgeLean.Foundations.Program
