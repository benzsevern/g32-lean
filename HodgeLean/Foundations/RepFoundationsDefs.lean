import Mathlib.RepresentationTheory.Character
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Analysis.Complex.Basic

/-! # Representation foundations: multiplicity spaces and form types (FROZEN DEFINITIONS)

General finite-group definitions over `ℂ`, not tied to a particular group: the multiplicity
space `Hom_G(σ, V)` of a simple representation in a representation `V`, the action of the
centralizer of `G` on it and its determinant, the evaluation map of the isotypic decomposition,
the Frobenius–Schur indicator and the space of invariant bilinear forms.
-/

noncomputable section

namespace HodgeLean.Foundations

open scoped TensorProduct

variable {G : Type} [Group G] [Fintype G] {V : Type} [AddCommGroup V] [Module ℂ V]

/-- The multiplicity space `M_σ = Hom_G(σ, V)` of `σ` in a representation `ρ` of `G` on `V`,
as the subspace of `G`-equivariant maps in `σ →ₗ V`.
Source: Serre, *Linear representations of finite groups*, §2.6 (the isotypic component of `V`
of type `σ` is the image of `σ ⊗ Hom_G(σ, V)`); G32 v0.16, Subsection 4.2. -/
def rfd_mult (σ : FDRep ℂ G) (ρ : Representation ℂ G V) : Submodule ℂ (σ →ₗ[ℂ] V) where
  carrier := {φ | ∀ g, φ ∘ₗ σ.ρ g = ρ g ∘ₗ φ}
  add_mem' {φ ψ} hφ hψ g := by
    rw [LinearMap.add_comp, hφ g, hψ g, LinearMap.comp_add]
  zero_mem' g := by rw [LinearMap.zero_comp, LinearMap.comp_zero]
  smul_mem' c φ hφ g := by
    rw [LinearMap.smul_comp, hφ g, LinearMap.comp_smul]

/-- The zero map is equivariant. -/
example (σ : FDRep ℂ G) (ρ : Representation ℂ G V) : (0 : σ →ₗ[ℂ] V) ∈ rfd_mult σ ρ :=
  Submodule.zero_mem _

/-- The action of an element `u` of the centralizer of `ρ(G)` on `M_σ` by composition,
`φ ↦ u ∘ φ`.
Source: Serre, *Linear representations of finite groups*, §2.6; G32 v0.16, Subsection 4.2
(`U(ℂ)` acts on `M_τ`). -/
def rfd_multAct (σ : FDRep ℂ G) (ρ : Representation ℂ G V) (u : Module.End ℂ V)
    (hu : u ∈ Subalgebra.centralizer ℂ (Set.range ρ)) : Module.End ℂ (rfd_mult σ ρ) :=
  (LinearMap.compRight ℂ u).restrict fun φ hφ g => by
    have hg := (Subalgebra.mem_centralizer_iff ℂ).1 hu (ρ g) ⟨g, rfl⟩
    change (u ∘ₗ φ) ∘ₗ σ.ρ g = ρ g ∘ₗ (u ∘ₗ φ)
    rw [LinearMap.comp_assoc, hφ g, ← LinearMap.comp_assoc, ← LinearMap.comp_assoc]
    exact congrArg (· ∘ₗ φ) hg.symm

/-- The identity of `V` acts as the identity on `M_σ`. -/
example (σ : FDRep ℂ G) (ρ : Representation ℂ G V) :
    rfd_multAct σ ρ 1 (Subalgebra.one_mem _) = 1 := by
  ext φ x
  rfl

/-- The determinant `e_σ(u) = det(u | M_σ)` of a centralizer element on the multiplicity space.
Source: G32 v0.16, Subsection 4.2 (the characters `e_τ` of `U`). -/
def rfd_det (σ : FDRep ℂ G) (ρ : Representation ℂ G V) (u : Module.End ℂ V)
    (hu : u ∈ Subalgebra.centralizer ℂ (Set.range ρ)) : ℂ :=
  LinearMap.det (rfd_multAct σ ρ u hu)

example (σ : FDRep ℂ G) (ρ : Representation ℂ G V) :
    rfd_det σ ρ 1 (Subalgebra.one_mem _) = 1 := by
  have h : rfd_multAct σ ρ 1 (Subalgebra.one_mem _) = 1 := by
    ext φ x
    rfl
  rw [rfd_det, h, map_one]

/-- The evaluation map of the isotypic decomposition, `⊕_i σ_i ⊗ M_{σ_i} → V`,
`x ⊗ φ ↦ φ x`, for a finite family `σ` of representations.
Source: Serre, *Linear representations of finite groups*, §2.6, Theorem 8;
Fulton–Harris, *Representation theory*, §1.2. -/
def rfd_eval {ι : Type} [Fintype ι] (σ : ι → FDRep ℂ G) (ρ : Representation ℂ G V) :
    (∀ i, σ i ⊗[ℂ] rfd_mult (σ i) ρ) →ₗ[ℂ] V :=
  ∑ i, TensorProduct.lift
      ((LinearMap.applyₗ (R := ℂ)).compl₂ (rfd_mult (σ i) ρ).subtype) ∘ₗ
    LinearMap.proj i

/-- On a pure tensor, the evaluation map evaluates. -/
example (σ : FDRep ℂ G) (ρ : Representation ℂ G V) (x : σ) (φ : rfd_mult σ ρ) :
    rfd_eval (fun _ : Unit => σ) ρ (fun _ => x ⊗ₜ φ) = (φ : σ →ₗ[ℂ] V) x := by
  simp [rfd_eval]

/-- The action of a centralizer element on `⊕_i σ_i ⊗ M_{σ_i}`: `1 ⊗ (u ∘ -)` on each summand.
Source: Serre, *Linear representations of finite groups*, §2.6; G32 v0.16, Subsection 4.2
(`u ∈ U` acts on `H¹(C, ℂ) = ⊕_τ τ ⊗ M_τ` through the factors `M_τ`). -/
def rfd_evalAct {ι : Type} [Fintype ι] (σ : ι → FDRep ℂ G) (ρ : Representation ℂ G V)
    (u : Module.End ℂ V) (hu : u ∈ Subalgebra.centralizer ℂ (Set.range ρ)) :
    Module.End ℂ (∀ i, σ i ⊗[ℂ] rfd_mult (σ i) ρ) :=
  LinearMap.pi fun i => TensorProduct.map LinearMap.id (rfd_multAct (σ i) ρ u hu) ∘ₗ
    LinearMap.proj i

/-- The evaluation map intertwines `1 ⊗ (u ∘ -)` with `u`. -/
example {ι : Type} [Fintype ι] (σ : ι → FDRep ℂ G) (ρ : Representation ℂ G V)
    (u : Module.End ℂ V) (hu : u ∈ Subalgebra.centralizer ℂ (Set.range ρ)) :
    rfd_eval σ ρ ∘ₗ rfd_evalAct σ ρ u hu = u ∘ₗ rfd_eval σ ρ := by
  classical
  refine LinearMap.pi_ext' fun i => TensorProduct.ext' fun x φ => ?_
  simp only [LinearMap.comp_apply, rfd_eval, rfd_evalAct, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : j = i
  · subst h; simp; rfl
  · simp [h]

/-- The `χ`-eigenspace `V^{H, χ} = {v | ρ(h) v = χ(h) v for all h ∈ H}` of a subgroup `H` with a
character `χ`.
Source: Serre, *Linear representations of finite groups*, §7.1 (restriction and Frobenius
reciprocity); G32 v0.16, Subsection 4.2 (`H¹(C, ℂ)^{H′, χ}`). -/
def rfd_eigen {W : Type} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W)
    (H : Subgroup G) (χ : H →* ℂˣ) : Submodule ℂ W where
  carrier := {v | ∀ h : H, ρ h v = ((χ h : ℂˣ) : ℂ) • v}
  add_mem' {v w} hv hw h := by rw [map_add, hv h, hw h, smul_add]
  zero_mem' h := by rw [map_zero, smul_zero]
  smul_mem' c v hv h := by rw [map_smul, hv h, smul_comm]

/-- For the trivial subgroup the eigenspace is everything. -/
example (ρ : Representation ℂ G V) : rfd_eigen ρ ⊥ 1 = ⊤ := by
  refine eq_top_iff.2 fun v _ h => ?_
  obtain ⟨h, hh⟩ := h
  rw [Subgroup.mem_bot] at hh
  subst hh
  simp

/-- The restriction of a centralizer element to `V^{H, χ}`.
Source: G32 v0.16, Subsection 4.2 and proof of Proposition 4.6 (`U` preserves the eigenspaces
of `H′`). -/
def rfd_eigenAct (ρ : Representation ℂ G V) (H : Subgroup G) (χ : H →* ℂˣ)
    (u : Module.End ℂ V) (hu : u ∈ Subalgebra.centralizer ℂ (Set.range ρ)) :
    Module.End ℂ (rfd_eigen ρ H χ) :=
  u.restrict fun v hv h => by
    have hg := (Subalgebra.mem_centralizer_iff ℂ).1 hu (ρ h) ⟨h, rfl⟩
    change ρ h (u v) = ((χ h : ℂˣ) : ℂ) • u v
    rw [← Module.End.mul_apply, hg, Module.End.mul_apply, hv h, map_smul]

example (ρ : Representation ℂ G V) (H : Subgroup G) (χ : H →* ℂˣ) :
    rfd_eigenAct ρ H χ 1 (Subalgebra.one_mem _) = 1 := by
  ext v
  rfl

/-- The Frobenius–Schur indicator `ν(σ) = |G|⁻¹ Σ_g χ_σ(g²)`.
Source: Serre, *Linear representations of finite groups*, §13.2, Proposition 39;
Isaacs, *Character theory of finite groups*, Chapter 4. -/
def rfd_indicator (σ : FDRep ℂ G) : ℂ :=
  (Fintype.card G : ℂ)⁻¹ * ∑ g, σ.character (g * g)

example (σ : FDRep ℂ G) :
    rfd_indicator σ = (Fintype.card G : ℂ)⁻¹ * ∑ g, σ.character (g * g) := rfl

/-- The space of `G`-invariant bilinear forms on `σ`.
Source: Serre, *Linear representations of finite groups*, §13.2;
Fulton–Harris, *Representation theory*, §3.5. -/
def rfd_invForms (σ : FDRep ℂ G) : Submodule ℂ (LinearMap.BilinForm ℂ σ) where
  carrier := {B | ∀ g x y, B (σ.ρ g x) (σ.ρ g y) = B x y}
  add_mem' {B C} hB hC g x y := by
    simp only [LinearMap.add_apply, hB g x y, hC g x y]
  zero_mem' g x y := rfl
  smul_mem' c B hB g x y := by
    simp only [LinearMap.smul_apply, hB g x y]

/-- The zero form is invariant. -/
example (σ : FDRep ℂ G) : (0 : LinearMap.BilinForm ℂ σ) ∈ rfd_invForms σ :=
  Submodule.zero_mem _

end HodgeLean.Foundations
