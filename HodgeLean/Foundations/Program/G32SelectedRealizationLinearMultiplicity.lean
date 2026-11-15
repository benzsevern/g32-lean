import HodgeLean.Foundations.Program.G32SelectedRealizationHolomorphicMultiplicity

noncomputable section
open HodgeLean.Papers HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

theorem g32y_linear_character_multiplicity {G M : Type*} [Group G]
    [AddCommGroup M] [Module ℂ M] (χ : G →* ℂˣ)
    (act : G → M →ₗ[ℂ] M) (W : Submodule ℂ M) :
    Module.finrank ℂ (b4_HomG (papersLinRep χ).ρ act W) =
      Module.finrank ℂ ↥(W ⊓ ⨅ g, Module.End.eigenspace (act g) (χ g : ℂ)) := by
  let ρ : Representation ℂ G ℂ := (papersLinRep χ).ρ
  change Module.finrank ℂ (b4_HomG ρ act W) = _
  let E := W ⊓ ⨅ g, Module.End.eigenspace (act g) (χ g : ℂ)
  let ev : (b4_HomG ρ act W) →ₗ[ℂ] E := {
    toFun := fun p ↦ ⟨p.val 1, p.property.1 1, by
      apply (Submodule.mem_iInf _).mpr
      intro g
      apply Module.End.mem_eigenspace_iff.mpr
      have hh := p.property.2 g 1
      change p.val ((χ g : ℂ) * 1) = act g (p.val 1) at hh
      simpa only [mul_one, ← smul_eq_mul, map_smul] using hh.symm⟩
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  have hinj : Function.Injective ev := by
    intro p q h
    apply Subtype.ext
    apply LinearMap.ext
    intro a
    have hh := congrArg Subtype.val h
    change p.val 1 = q.val 1 at hh
    calc
      p.val a = a • p.val 1 := by rw [← map_smul]; simp
      _ = a • q.val 1 := congrArg (a • ·) hh
      _ = q.val a := by rw [← map_smul]; simp
  have hsurj : Function.Surjective ev := by
    intro x
    let p := LinearMap.toSpanSingleton ℂ M x.val
    have hp : p ∈ b4_HomG ρ act W := by
      refine ⟨fun a ↦ W.smul_mem a x.property.1, ?_⟩
      intro g a
      have hx := Module.End.mem_eigenspace_iff.mp ((Submodule.mem_iInf _).mp x.property.2 g)
      change ((χ g : ℂ) * a) • x.val = act g (a • x.val)
      rw [map_smul, hx, mul_smul, smul_comm]
    refine ⟨⟨p, hp⟩, ?_⟩
    apply Subtype.ext
    change (1 : ℂ) • x.val = x.val
    exact one_smul ℂ x.val
  exact (LinearEquiv.ofBijective ev ⟨hinj, hsurj⟩).finrank_eq

end HodgeLean.Foundations.Program
