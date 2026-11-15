import HodgeLean.Blocks.HodgeStructure.Basic

/-!
# Track B2, families of complex tori and images of integral endomorphisms: definitions

The fibrewise object is linear algebra on a lattice `Λ` (a finite free `ℤ`-module): a complex
subspace `F ⊆ ℂ ⊗[ℤ] Λ` (the Hodge filtration `F¹`), the complex torus
`T = ((ℂ ⊗[ℤ] Λ) ⧸ F) ⧸ Λ`, constructed as an iterated quotient with its quotient group law, and a
Riemann form `Q : Λ × Λ → ℤ` satisfying the Hodge–Riemann relations for `F`. For a weight-one Hodge
structure `Λ ⊗ ℚ` with `H¹(·, ℤ) = Λ`, the torus `(H¹(ℂ) ⧸ F¹) ⧸ H¹(ℤ)` is the classical
`H^{0,1} ⧸ H¹(ℤ)` (Birkenhake–Lange, §1.1 and §2.4).

The family is a lattice local system on a complex manifold `B`, as a functor from Mathlib's
`FundamentalGroupoid B` to `ℤ`-modules with finite free fibres, with a holomorphic weight-one
filtration and a flat Riemann form. The holomorphy vocabulary (flat coordinates over simply
connected opens, holomorphic frames) follows the D1 drafts on `spec/d1vhs`, restated here over
`ℤ`; relating the two is left to a later stage. Griffiths transversality is vacuous in weight one
and is not recorded.

The image of a flat endomorphism `e` of the local system is constructed: its fibres are the
ranges `e_b(Λ_b)`, its filtration is the preimage of `F_b`, its form is the restriction of `Q_b`.
The kernel of an idempotent `e` is the image of `1 - e`.

Topology and complex structure: `ℂ ⊗[ℤ] Λ` carries Mathlib's module topology over `ℂ`, the
torus the quotient topology, and for a finite `Λ` with discrete image the torus is a complex
charted space modelled on `ℂ^g` with charts from local sections of the quotient map. The total
space of a family is the sigma type of the fibre tori, with the final topology for the flat
trivialisations over simply connected open sets.

Algebraicity of the tori (the Lefschetz embedding) is not in scope. HC no distance; AV milestone
no distance.
-/

noncomputable section

open CategoryTheory Manifold
open scoped TensorProduct ContDiff

namespace HodgeLean.Foundations.Program

/-! ## Fibrewise lattice algebra -/

section Fibre

variable (Λ : Type*) [AddCommGroup Λ]

/-- The lattice inside its complexification, `x ↦ 1 ⊗ x`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, §1.1;
Mathlib `TensorProduct.mk`. -/
def b2_incl : Λ →ₗ[ℤ] ℂ ⊗[ℤ] Λ :=
  TensorProduct.mk ℤ ℂ Λ 1

example (x : Λ) : b2_incl Λ x = (1 : ℂ) ⊗ₜ[ℤ] x := rfl

/-- Complex conjugation `c ⊗ x ↦ c̄ ⊗ x` on `ℂ ⊗[ℤ] Λ`, an additive (conjugate-linear) map.
Source: Birkenhake–Lange, §1.2 (the real structure of `Λ ⊗ ℂ`); Mathlib `LinearMap.rTensor`. -/
def b2_conj : (ℂ ⊗[ℤ] Λ) →ₗ[ℤ] (ℂ ⊗[ℤ] Λ) :=
  LinearMap.rTensor Λ (starRingEnd ℂ).toAddMonoidHom.toIntLinearMap

example (c : ℂ) (x : Λ) : b2_conj Λ (c ⊗ₜ[ℤ] x) = (starRingEnd ℂ c) ⊗ₜ[ℤ] x := rfl

/-- The conjugate `F̄` of a complex subspace, the complex span of `conj '' F`.
Source: Birkenhake–Lange, §1.2; Deligne, *Théorie de Hodge II*, Publ. Math. IHES 40, §1.2. -/
def b2_conjSubmodule (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) : Submodule ℂ (ℂ ⊗[ℤ] Λ) :=
  Submodule.span ℂ (b2_conj Λ '' F)

example : b2_conjSubmodule Λ ⊥ = ⊥ := by
  simp [b2_conjSubmodule]

/-- **A weight-one Hodge structure on the lattice**: `ℂ ⊗ Λ = F ⊕ F̄`, with `F = F¹ = H^{1,0}`.
Source: Deligne, *Théorie de Hodge II*, §1.2; Birkenhake–Lange, §1.2 and Proposition 1.1.3 (complex
structures on `Λ ⊗ ℝ`). -/
def b2_IsWeightOne (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) : Prop :=
  IsCompl F (b2_conjSubmodule Λ F)

example (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (h : b2_IsWeightOne Λ F) :
    F ⊓ b2_conjSubmodule Λ F = ⊥ :=
  h.inf_eq_bot

/-- The lattice in `(ℂ ⊗ Λ) ⧸ F`, `x ↦ [1 ⊗ x]`.
Source: Birkenhake–Lange, §1.1 and §2.4 (`X = V ⧸ Λ`). -/
def b2_latticeMap (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) : Λ →+ (ℂ ⊗[ℤ] Λ) ⧸ F :=
  F.mkQ.toAddMonoidHom.comp (b2_incl Λ).toAddMonoidHom

example (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (x : Λ) :
    b2_latticeMap Λ F x = Submodule.Quotient.mk ((1 : ℂ) ⊗ₜ[ℤ] x) := rfl

/-- **The complex torus `T = ((ℂ ⊗ Λ) ⧸ F) ⧸ Λ`**, with the quotient group law.
Source: Birkenhake–Lange, §1.1 and §2.4 (for `F = H^{1,0}`, `T = H^{0,1} ⧸ Λ`). -/
abbrev b2_torus (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) : Type _ :=
  ((ℂ ⊗[ℤ] Λ) ⧸ F) ⧸ (b2_latticeMap Λ F).range

example (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (x : Λ) :
    (QuotientAddGroup.mk (b2_latticeMap Λ F x) : b2_torus Λ F) = 0 :=
  (QuotientAddGroup.eq_zero_iff _).2 ⟨x, rfl⟩

/-- **A Riemann form for `F`** (a polarization of the weight-one Hodge structure): `Q` is
alternating, `F` is isotropic for `Q_ℂ`, and `Re (i · Q_ℂ(x, x̄)) > 0` for `0 ≠ x ∈ F`. These are
the two Hodge–Riemann relations in weight one, `(p, q) = (1, 0)`.
Source: Griffiths, *Periods of integrals on algebraic manifolds I*, Amer. J. Math. 90 (1968), §2;
Birkenhake–Lange, §4.2 (Riemann relations). -/
structure b2_IsRiemannForm (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (Q : LinearMap.BilinForm ℤ Λ) :
    Prop where
  alt : ∀ x, Q x x = 0
  isotropic : ∀ x ∈ F, ∀ y ∈ F, Q.baseChange ℂ x y = 0
  positive : ∀ x ∈ F, x ≠ 0 → 0 < (Complex.I * Q.baseChange ℂ x (b2_conj Λ x)).re

example (Q : LinearMap.BilinForm ℤ Λ) (h : ∀ x, Q x x = 0) : b2_IsRiemannForm Λ ⊥ Q :=
  ⟨h, fun x hx _ _ => by simp_all, fun x hx h0 => absurd ((Submodule.mem_bot ℂ).1 hx) h0⟩

end Fibre

/-! ## Morphisms of tori and images of endomorphisms -/

section Morphisms

variable {Λ Λ' : Type*} [AddCommGroup Λ] [AddCommGroup Λ']

/-- The complexification `g_ℂ = 1 ⊗ g : ℂ ⊗ Λ' → ℂ ⊗ Λ` of an additive map.
Source: Birkenhake–Lange, §1.2 (the rational and analytic representations); Mathlib
`LinearMap.baseChange`. -/
def b2_cplxMap (g : Λ' →+ Λ) : (ℂ ⊗[ℤ] Λ') →ₗ[ℂ] (ℂ ⊗[ℤ] Λ) :=
  g.toIntLinearMap.baseChange ℂ

example (g : Λ' →+ Λ) (c : ℂ) (x : Λ') : b2_cplxMap g (c ⊗ₜ[ℤ] x) = c ⊗ₜ[ℤ] g x := rfl

/-- The complexification of the identity is the identity. -/
@[simp] theorem b2_cplxMap_id : b2_cplxMap (AddMonoidHom.id Λ) = LinearMap.id := by
  refine LinearMap.ext fun v ↦ ?_
  induction v using TensorProduct.inductionOn with
  | tmul c x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- **The morphism of tori induced by `g : Λ' → Λ` with `g_ℂ(F') ⊆ F`**: the map
`[v] ↦ [g_ℂ v]` on `((ℂ ⊗ Λ') ⧸ F') ⧸ Λ'`.
Source: Birkenhake–Lange, §1.2 (analytic and rational representations of homomorphisms). -/
def b2_torusHom (F' : Submodule ℂ (ℂ ⊗[ℤ] Λ')) (F : Submodule ℂ (ℂ ⊗[ℤ] Λ))
    (g : Λ' →+ Λ) (hg : F' ≤ F.comap (b2_cplxMap g)) :
    b2_torus Λ' F' →+ b2_torus Λ F :=
  QuotientAddGroup.map _ _ (F'.mapQ F (b2_cplxMap g) hg).toAddMonoidHom (by
    rintro _ ⟨x, rfl⟩
    exact ⟨g x, rfl⟩)

example (F' : Submodule ℂ (ℂ ⊗[ℤ] Λ')) (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (g : Λ' →+ Λ)
    (hg : F' ≤ F.comap (b2_cplxMap g)) (v : ℂ ⊗[ℤ] Λ') :
    b2_torusHom F' F g hg (QuotientAddGroup.mk (Submodule.Quotient.mk v)) =
      QuotientAddGroup.mk (Submodule.Quotient.mk (b2_cplxMap g v)) := rfl

/-- **The image lattice's filtration**: the preimage of `F` in `ℂ ⊗ f(Λ)`.
Source: Birkenhake–Lange, §5.3 and §12.2 (abelian subvarieties as images of endomorphisms). -/
def b2_imageF (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (f : Λ →+ Λ) :
    Submodule ℂ (ℂ ⊗[ℤ] f.range) :=
  F.comap (b2_cplxMap f.range.subtype)

example (f : Λ →+ Λ) : b2_imageF (⊤ : Submodule ℂ (ℂ ⊗[ℤ] Λ)) f = ⊤ := by
  simp [b2_imageF]

/-- **The restricted form** on the image lattice `f(Λ)`.
Source: Birkenhake–Lange, §5.3 (the induced polarization on an abelian subvariety). -/
def b2_imageQ (Q : LinearMap.BilinForm ℤ Λ) (f : Λ →+ Λ) :
    LinearMap.BilinForm ℤ f.range :=
  Q.compl₁₂ f.range.subtype.toIntLinearMap f.range.subtype.toIntLinearMap

example (Q : LinearMap.BilinForm ℤ Λ) (f : Λ →+ Λ) (x y : f.range) :
    b2_imageQ Q f x y = Q x y := rfl

/-- **The sub-torus of an endomorphism**: the morphism `T(f(Λ), F_f) → T(Λ, F)` induced by the
inclusion `f(Λ) ⊆ Λ`.
Source: Birkenhake–Lange, §5.3 and §12.2. -/
def b2_subTorus (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (f : Λ →+ Λ) :
    b2_torus f.range (b2_imageF F f) →+ b2_torus Λ F :=
  b2_torusHom (b2_imageF F f) F f.range.subtype le_rfl

example (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (f : Λ →+ Λ) :
    b2_subTorus F f 0 = 0 := map_zero _

end Morphisms

/-! ## Holomorphy in flat coordinates -/

section Coordinates

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {B : Type*} [TopologicalSpace B] [ChartedSpace E B]
variable {H : Type*} [AddCommGroup H] [Module ℂ H] [Module.Finite ℂ H]

/-- Coordinates on a finite-dimensional complex vector space from Mathlib's chosen basis.
Source: Bourbaki, *Algèbre*, ch. II, §7 (finite bases); `Module.finBasis`. -/
def b2_coord (H : Type*) [AddCommGroup H] [Module ℂ H] [Module.Finite ℂ H] :
    H ≃ₗ[ℂ] (Fin (Module.finrank ℂ H) → ℂ) :=
  (Module.finBasis ℂ H).equivFun

example : (ℂ ≃ₗ[ℂ] (Fin (Module.finrank ℂ ℂ) → ℂ)) := b2_coord ℂ

/-- A map from a complex manifold to a finite-dimensional complex vector space is holomorphic
on `U` when its coordinates are `ω`-smooth (complex analytic in charts) on `U`.
Source: Huybrechts, *Complex Geometry*, §2.1; Mathlib `ContMDiffOn` with `n = ω`. -/
def b2_IsHolomorphicOn (f : B → H) (U : Set B) : Prop :=
  ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, Fin (Module.finrank ℂ H) → ℂ) ω (b2_coord H ∘ f) U

example (U : Set E) : b2_IsHolomorphicOn E (fun _ : E ↦ (0 : ℂ)) U :=
  contMDiffOn_const

end Coordinates

/-! ## Topology and complex structure of the torus -/

section Topology

variable (Λ : Type*) [AddCommGroup Λ]

/-- **The vector-space topology of `ℂ ⊗[ℤ] Λ`**: Mathlib's module topology over `ℂ`, the finest
topology making addition and scalar multiplication continuous. For finite `Λ` it is the unique
Hausdorff vector-space topology, that of `ℂⁿ`; the quotient `(ℂ ⊗ Λ) ⧸ F` then carries the
quotient topology, again the module topology (`IsModuleTopology.instQuot`).
Source: Bourbaki, *Espaces vectoriels topologiques*, ch. I, §2.3 (uniqueness of the Hausdorff
vector-space topology in finite dimension); Mathlib `moduleTopology`. -/
instance b2_cplxTopology : TopologicalSpace (ℂ ⊗[ℤ] Λ) :=
  moduleTopology ℂ _

/-- The topology of `ℂ ⊗[ℤ] Λ` is the module topology.
Source: Mathlib `IsModuleTopology`. -/
instance b2_cplx_isModuleTopology : IsModuleTopology ℂ (ℂ ⊗[ℤ] Λ) :=
  ⟨rfl⟩

/-- `ℂ ⊗[ℤ] Λ` is a topological additive group.
Source: Mathlib `IsModuleTopology.isTopologicalAddGroup`. -/
instance b2_cplx_isTopologicalAddGroup : IsTopologicalAddGroup (ℂ ⊗[ℤ] Λ) :=
  IsModuleTopology.isTopologicalAddGroup ℂ _

example (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) : IsModuleTopology ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F) := inferInstance

-- The torus is a topological group for the quotient topology.
example (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) : IsTopologicalAddGroup (b2_torus Λ F) := inferInstance

variable (F : Submodule ℂ (ℂ ⊗[ℤ] Λ))

/-- **Linear coordinates `(ℂ ⊗ Λ) ⧸ F ≃ₜ ℂ^g`**, `g = dim_ℂ ((ℂ ⊗ Λ) ⧸ F)`, from Mathlib's chosen
basis; a homeomorphism because both sides carry the module topology.
Source: Bourbaki, *Espaces vectoriels topologiques*, ch. I, §2.3; Mathlib
`IsModuleTopology.continuous_of_linearMap`. -/
def b2_coordHomeomorph [Module.Finite ℤ Λ] :
    ((ℂ ⊗[ℤ] Λ) ⧸ F) ≃ₜ (Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F)) → ℂ) where
  toEquiv := (b2_coord ((ℂ ⊗[ℤ] Λ) ⧸ F)).toEquiv
  continuous_toFun := IsModuleTopology.continuous_of_linearMap (b2_coord _).toLinearMap
  continuous_invFun := IsModuleTopology.continuous_of_linearMap (b2_coord _).symm.toLinearMap

example [Module.Finite ℤ Λ] (v : (ℂ ⊗[ℤ] Λ) ⧸ F) :
    b2_coordHomeomorph Λ F v = b2_coord _ v := rfl

/-- For a discrete lattice, the quotient map `(ℂ ⊗ Λ) ⧸ F → T` is a local homeomorphism (it is a
covering map).
Source: Mathlib `AddSubgroup.isAddQuotientCoveringMap_of_comm`,
`IsAddQuotientCoveringMap.isLocalHomeomorph`. -/
theorem b2_isLocalHomeomorph_mk [DiscreteTopology (b2_latticeMap Λ F).range] :
    IsLocalHomeomorph (QuotientAddGroup.mk : (ℂ ⊗[ℤ] Λ) ⧸ F → b2_torus Λ F) :=
  (AddSubgroup.isAddQuotientCoveringMap_of_comm _
    (SetLike.isDiscrete_iff_discreteTopology.2 inferInstance)).isLocalHomeomorph

/-- **The chart of the torus at `t`**: the local section of the quotient map through the
representative `t.out`, followed by linear coordinates.
Source: Birkenhake–Lange, §1.1 (`X = V ⧸ Λ` with charts from `V`); Mathlib
`IsLocalHomeomorph`. -/
def b2_torusChart [Module.Finite ℤ Λ] [DiscreteTopology (b2_latticeMap Λ F).range]
    (t : b2_torus Λ F) :
    OpenPartialHomeomorph (b2_torus Λ F) (Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F)) → ℂ) :=
  (Classical.choose (b2_isLocalHomeomorph_mk Λ F t.out)).symm.trans
    (b2_coordHomeomorph Λ F).toOpenPartialHomeomorph

/-- A point lies in the source of its own chart.
Source: Mathlib `OpenPartialHomeomorph.map_source`. -/
theorem b2_mem_torusChart_source [Module.Finite ℤ Λ]
    [DiscreteTopology (b2_latticeMap Λ F).range] (t : b2_torus Λ F) :
    t ∈ (b2_torusChart Λ F t).source := by
  obtain ⟨h₁, h₂⟩ := Classical.choose_spec (b2_isLocalHomeomorph_mk Λ F t.out)
  simp only [b2_torusChart, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.symm_source, Homeomorph.toOpenPartialHomeomorph_source,
    Set.preimage_univ, Set.inter_univ]
  have := (Classical.choose (b2_isLocalHomeomorph_mk Λ F t.out)).map_source h₁
  rwa [← h₂, QuotientAddGroup.out_eq'] at this

/-- **The complex charted space of the torus** `T = ((ℂ ⊗ Λ) ⧸ F) ⧸ Λ`, modelled on `ℂ^g`, for a
finite `Λ` whose image in `(ℂ ⊗ Λ) ⧸ F` is discrete. Its charts are local sections of the quotient
map in linear coordinates; their transition maps are translations by lattice vectors.
Source: Birkenhake–Lange, §1.1; Huybrechts, *Complex Geometry*, Example 1.1.3 (complex tori);
Mathlib `ChartedSpace`. -/
instance b2_torus_chartedSpace [Module.Finite ℤ Λ] [DiscreteTopology (b2_latticeMap Λ F).range] :
    ChartedSpace (Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F)) → ℂ) (b2_torus Λ F) where
  atlas := Set.range (b2_torusChart Λ F)
  chartAt := b2_torusChart Λ F
  mem_chart_source := b2_mem_torusChart_source Λ F
  chart_mem_atlas t := ⟨t, rfl⟩

example [Module.Finite ℤ Λ] [DiscreteTopology (b2_latticeMap Λ F).range] (t : b2_torus Λ F) :
    chartAt (Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F)) → ℂ) t = b2_torusChart Λ F t := rfl

/-- **The universal cover in coordinates** `ℂ^g → T`, `v ↦ [coord⁻¹ v]`.
Source: Birkenhake–Lange, §1.1. -/
def b2_torusCover [Module.Finite ℤ Λ] :
    (Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F)) → ℂ) → b2_torus Λ F :=
  fun v ↦ QuotientAddGroup.mk ((b2_coordHomeomorph Λ F).symm v)

example [Module.Finite ℤ Λ] : b2_torusCover Λ F 0 = 0 := by
  simp [b2_torusCover, b2_coordHomeomorph]

end Topology

/-! ## Lattice local systems -/

section LocalSystem

/-- **A lattice local system** on `B`: a representation of the fundamental groupoid on finite
free `ℤ`-modules.
Source: Deligne, *Équations différentielles à points singuliers réguliers*, LNM 163, I.1;
Voisin, *Hodge Theory and Complex Algebraic Geometry I*, ch. 9. -/
structure b2_LatticeLocalSystem (B : Type*) [TopologicalSpace B] where
  functor : FundamentalGroupoid B ⥤ AddCommGrpCat.{0}
  free : ∀ x, Module.Free ℤ (functor.obj x)
  finite : ∀ x, Module.Finite ℤ (functor.obj x)

/-- The constant lattice local system with fibre `W`.
Source: Voisin, *Hodge Theory I*, ch. 9 (constant local systems). -/
def b2_constLocalSystem (B : Type*) [TopologicalSpace B] (W : Type) [AddCommGroup W]
    [Module.Free ℤ W] [Module.Finite ℤ W] : b2_LatticeLocalSystem B where
  functor := (Functor.const _).obj (AddCommGrpCat.of W)
  free _ := inferInstanceAs (Module.Free ℤ W)
  finite _ := inferInstanceAs (Module.Finite ℤ W)

example (B : Type*) [TopologicalSpace B] : b2_LatticeLocalSystem B :=
  b2_constLocalSystem B (Fin 2 → ℤ)

/-- A constant filtration on the constant local system, typed as a family over its fibres.
Source: Voisin, *Hodge Theory I*, ch. 9 (constant variations). -/
def b2_constF (B : Type*) [TopologicalSpace B] (W : Type) [AddCommGroup W] [Module.Free ℤ W]
    [Module.Finite ℤ W] (F₀ : Submodule ℂ (ℂ ⊗[ℤ] W)) :
    ∀ b, Submodule ℂ (ℂ ⊗[ℤ] (b2_constLocalSystem B W).functor.obj (FundamentalGroupoid.mk b)) :=
  fun _ ↦ F₀

example (B : Type*) [TopologicalSpace B] (b : B) :
    b2_constF B (Fin 2 → ℤ) ⊥ b = ⊥ := rfl

namespace b2_LatticeLocalSystem

variable {B : Type*} [TopologicalSpace B] (L : b2_LatticeLocalSystem B)

/-- The fibre `Λ_b`.
Source: Voisin, *Hodge Theory I*, ch. 9. -/
abbrev fiber (b : B) : Type := L.functor.obj (FundamentalGroupoid.mk b)

instance (b : B) : Module.Free ℤ (L.fiber b) := L.free _

instance (b : B) : Module.Finite ℤ (L.fiber b) := L.finite _

/-- The fibre `ℂ ⊗ Λ_b` of the flat bundle `Λ ⊗ 𝒪_B`.
Source: Deligne, LNM 163, I.2; Voisin, *Hodge Theory I*, ch. 9. -/
abbrev cFiber (b : B) : Type := ℂ ⊗[ℤ] L.fiber b

example (b : B) : Module.Finite ℂ (L.cFiber b) := inferInstance

/-- Parallel transport along a homotopy class of paths.
Source: Voisin, *Hodge Theory I*, ch. 9. -/
def transport {b b' : B} (γ : Path.Homotopic.Quotient b b') : L.fiber b ≃+ L.fiber b' :=
  (L.functor.mapIso (asIso (show FundamentalGroupoid.mk b ⟶ FundamentalGroupoid.mk b' from γ))
    ).addCommGroupIsoToAddEquiv

example (b : B) (x : L.fiber b) : L.fiber b :=
  L.transport (Path.Homotopic.Quotient.mk (Path.refl b)) x

/-- The homotopy class in `B` of a path inside a simply connected subset `U`; every path in `U`
between the two points gives this class.
Source: Hatcher, *Algebraic Topology*, §1.1, Proposition 1.6. -/
def classIn (U : Set B) (hU : IsSimplyConnected U) (b b₀ : U) :
    Path.Homotopic.Quotient (b : B) b₀ :=
  haveI := hU.simplyConnectedSpace
  Path.Homotopic.Quotient.mk ((PathConnectedSpace.somePath b b₀).map continuous_subtype_val)

example (U : Set B) (hU : IsSimplyConnected U) (b : U) : Path.Homotopic.Quotient (b : B) b :=
  classIn U hU b b

/-- Complexified parallel transport inside a simply connected subset: the flat trivialisation
of `Λ ⊗ 𝒪` over `U`.
Source: Voisin, *Hodge Theory I*, ch. 9; Griffiths, Publ. Math. IHES 38, §1. -/
def flatTransport (U : Set B) (hU : IsSimplyConnected U) (b b₀ : U) :
    L.cFiber b ≃ₗ[ℂ] L.cFiber b₀ :=
  LinearEquiv.baseChange ℤ ℂ _ _ (L.transport (classIn U hU b b₀)).toIntLinearEquiv

example (U : Set B) (hU : IsSimplyConnected U) (b : U) : L.cFiber b ≃ₗ[ℂ] L.cFiber b :=
  L.flatTransport U hU b b

open scoped Classical in
/-- The flat coordinates of a section over `U`, valued in the reference fibre at `b₀`.
Source: Voisin, *Hodge Theory I*, ch. 9. -/
def flatCoord (U : Set B) (hU : IsSimplyConnected U) (b₀ : U) (s : ∀ b, L.cFiber b) :
    B → L.cFiber b₀ :=
  fun b ↦ if h : b ∈ U then L.flatTransport U hU ⟨b, h⟩ b₀ (s b) else 0

example (U : Set B) (hU : IsSimplyConnected U) (b₀ : U) : B → L.cFiber b₀ :=
  L.flatCoord U hU b₀ 0

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] [ChartedSpace E B]

/-- A section of `Λ ⊗ 𝒪_B` is holomorphic on the simply connected set `U` when its flat
coordinates are holomorphic there.
Source: Deligne, LNM 163, I.2.17; Voisin, *Hodge Theory I*, ch. 9. -/
def IsHolomorphicSectionOn (U : Set B) (hU : IsSimplyConnected U) (b₀ : U)
    (s : ∀ b, L.cFiber b) : Prop :=
  b2_IsHolomorphicOn E (L.flatCoord U hU b₀ s) U

/-- A family of subspaces `G_b ⊆ ℂ ⊗ Λ_b` is holomorphic when, near each point, it is generated
by finitely many holomorphic sections on a simply connected open neighbourhood. For a family of
constant rank (as every weight-one filtration of a lattice local system is, `dim F_b = rk Λ / 2`)
this is the usual holomorphic subbundle: `r` of the generators independent at `b₁` stay
independent nearby and span by dimension.
Source: Griffiths, Publ. Math. IHES 38, §1; Griffiths–Harris, *Principles of Algebraic
Geometry*, ch. 0, §5; Huybrechts, *Complex Geometry*, §2.2. -/
def IsHolomorphicSubbundle (G : ∀ b, Submodule ℂ (L.cFiber b)) : Prop :=
  ∀ b₁ : B, ∃ (U : Set B) (hU : IsSimplyConnected U) (h₁ : b₁ ∈ U), IsOpen U ∧
    ∃ (r : ℕ) (s : Fin r → ∀ b, L.cFiber b),
      (∀ i, L.IsHolomorphicSectionOn E U hU ⟨b₁, h₁⟩ (s i)) ∧
      ∀ b ∈ U, Submodule.span ℂ (Set.range fun i ↦ s i b) = G b

example : (b2_constLocalSystem E (Fin 2 → ℤ)).IsHolomorphicSubbundle E (fun _ ↦ ⊥) := by
  intro b₁
  refine ⟨Set.univ, ?_, Set.mem_univ _, isOpen_univ, 0, Fin.elim0, fun i ↦ Fin.elim0 i,
    fun _ _ ↦ by simp⟩
  have : ContractibleSpace (Set.univ : Set E) := (Homeomorph.Set.univ E).contractibleSpace
  exact (inferInstance : SimplyConnectedSpace (Set.univ : Set E))

/-- The image `e(Λ_x)` of a flat endomorphism `e` at an object of the groupoid.
Source: Deligne, LNM 163, I.1 (sub-local systems). -/
abbrev imageObj (e : L.functor ⟶ L.functor) (x : FundamentalGroupoid B) :
    AddSubgroup (L.functor.obj x) :=
  (e.app x).hom.range

/-- **The image local system** of a flat endomorphism `e : Λ → Λ`: fibres `e_b(Λ_b)`, with the
restricted transport (well defined because `e` commutes with transport).
Source: Deligne, LNM 163, I.1 (sub-local systems); Birkenhake–Lange, §5.3 and §12.2. -/
def imageFunctor (e : L.functor ⟶ L.functor) : FundamentalGroupoid B ⥤ AddCommGrpCat.{0} where
  obj x := AddCommGrpCat.of (L.imageObj e x)
  map {x y} γ := AddCommGrpCat.ofHom (((L.functor.map γ).hom.comp (L.imageObj e x).subtype
    ).codRestrict (L.imageObj e y) (by
      rintro ⟨_, v, rfl⟩
      refine ⟨(L.functor.map γ).hom v, ?_⟩
      have := congrArg (fun φ ↦ φ.hom v) (e.naturality γ)
      simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply] at this
      exact this))
  map_id x := by
    ext v
    simp
  map_comp γ δ := by
    ext v
    simp

/-- **The image local system** of a flat endomorphism `e : Λ → Λ`: fibres `e_b(Λ_b)`, with the
restricted transport (well defined because `e` commutes with transport).
Source: Deligne, LNM 163, I.1 (sub-local systems); Birkenhake–Lange, §5.3 and §12.2. -/
def image (e : L.functor ⟶ L.functor) : b2_LatticeLocalSystem B where
  functor := L.imageFunctor e
  free x := by
    have : Module.Free ℤ (L.functor.obj x) := L.free x
    have : Module.Finite ℤ (L.functor.obj x) := L.finite x
    exact inferInstanceAs (Module.Free ℤ (L.imageObj e x).toIntSubmodule)
  finite x := by
    have : Module.Finite ℤ (L.functor.obj x) := L.finite x
    exact inferInstanceAs (Module.Finite ℤ (L.imageObj e x).toIntSubmodule)

/-- The filtration of the image local system: the preimage of `F_b`.
Source: Birkenhake–Lange, §5.3 and §12.2. -/
def imageF (F : ∀ b, Submodule ℂ (L.cFiber b)) (e : L.functor ⟶ L.functor) (b : B) :
    Submodule ℂ ((L.image e).cFiber b) :=
  b2_imageF (F b) (e.app (FundamentalGroupoid.mk b)).hom

/-- The form of the image local system: the restriction of `Q_b`.
Source: Birkenhake–Lange, §5.3. -/
def imageQ (Q : ∀ b, LinearMap.BilinForm ℤ (L.fiber b)) (e : L.functor ⟶ L.functor) (b : B) :
    LinearMap.BilinForm ℤ ((L.image e).fiber b) :=
  b2_imageQ (Q b) (e.app (FundamentalGroupoid.mk b)).hom

example (e : L.functor ⟶ L.functor) (b : B) :
    (L.image e).fiber b = L.imageObj e (FundamentalGroupoid.mk b) := rfl

end b2_LatticeLocalSystem

end LocalSystem

/-! ## Polarized families of complex tori -/

section Family

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {B : Type*} [TopologicalSpace B] [ChartedSpace E B]

/-- **A polarized family of complex tori** (a polarized integral variation of Hodge structure of
weight one) on the lattice local system `L`: the filtration `F_b ⊆ ℂ ⊗ Λ_b` is a holomorphic
subbundle and a weight-one Hodge structure in each fibre, and the flat form `Q_b` is a Riemann
form for `F_b` in each fibre. Its fibres are the tori `b2_torus (L.fiber b) (F b)`.
Source: Griffiths, *Periods of integrals on algebraic manifolds III*, Publ. Math. IHES 38 (1970),
§§1–3; Deligne, *Théorie de Hodge II*, §4.4 (weight one and complex tori); Birkenhake–Lange,
§§1.1, 4.2. -/
structure b2_IsPolarizedTorusFamily (L : b2_LatticeLocalSystem B)
    (F : ∀ b, Submodule ℂ (L.cFiber b)) (Q : ∀ b, LinearMap.BilinForm ℤ (L.fiber b)) : Prop where
  holomorphic : L.IsHolomorphicSubbundle E F
  flat : ∀ (b b' : B) (γ : Path.Homotopic.Quotient b b') (x y : L.fiber b),
    Q b' (L.transport γ x) (L.transport γ y) = Q b x y
  hodge : ∀ b, b2_IsWeightOne (L.fiber b) (F b)
  polarized : ∀ b, b2_IsRiemannForm (L.fiber b) (F b) (Q b)

/-- **The fibre torus** `T_b = ((ℂ ⊗ Λ_b) ⧸ F_b) ⧸ Λ_b` of the family.
Source: Birkenhake–Lange, §1.1; Deligne, *Théorie de Hodge II*, §4.4. -/
abbrev b2_fiberTorus (L : b2_LatticeLocalSystem B) (F : ∀ b, Submodule ℂ (L.cFiber b)) (b : B) :
    Type :=
  b2_torus (L.fiber b) (F b)

example (L : b2_LatticeLocalSystem B) (F : ∀ b, Submodule ℂ (L.cFiber b)) (b : B) :
    AddCommGroup (b2_fiberTorus L F b) := inferInstance

end Family

/-! ## The total space of a family of tori -/

section TotalSpace

variable {B : Type*} [TopologicalSpace B]

/-- **The total space** `𝒯 = Σ_b T_b` of the family of tori `T_b = ((ℂ ⊗ Λ_b) ⧸ F_b) ⧸ Λ_b`.
Source: Griffiths, Publ. Math. IHES 38 (1970), §1; Deligne, *Théorie de Hodge II*, §4.4 (the
family of complex tori of a weight-one variation); Birkenhake–Lange, §1.1. -/
def b2_totalSpace (L : b2_LatticeLocalSystem B) (F : ∀ b, Submodule ℂ (L.cFiber b)) : Type _ :=
  Σ b : B, b2_fiberTorus L F b

/-- **The projection** `π : 𝒯 → B`.
Source: Griffiths, Publ. Math. IHES 38, §1. -/
def b2_proj (L : b2_LatticeLocalSystem B) (F : ∀ b, Submodule ℂ (L.cFiber b)) :
    b2_totalSpace L F → B :=
  Sigma.fst

/-- **The inclusion of the fibre** `T_b → 𝒯`.
Source: Griffiths, Publ. Math. IHES 38, §1. -/
def b2_fiberIncl (L : b2_LatticeLocalSystem B) (F : ∀ b, Submodule ℂ (L.cFiber b)) (b : B) :
    b2_fiberTorus L F b → b2_totalSpace L F :=
  Sigma.mk b

example (L : b2_LatticeLocalSystem B) (F : ∀ b, Submodule ℂ (L.cFiber b)) (b : B)
    (t : b2_fiberTorus L F b) : b2_proj L F (b2_fiberIncl L F b t) = b := rfl

/-- **The flat trivialisation over a simply connected `U`** with reference point `b₀`:
`(b, v) ↦ [flat transport of v ∈ ℂ ⊗ Λ_{b₀} to ℂ ⊗ Λ_b] ∈ T_b`. It is onto `π⁻¹(U)`; the torus
`T_b` is the quotient of `ℂ ⊗ Λ_{b₀}` by the transported `F_b + Λ_b`, so the filtration varies
with `b` while the lattice is constant.
Source: Voisin, *Hodge Theory I*, ch. 9 (flat trivialisation of `Λ ⊗ 𝒪`); Griffiths, Publ. Math.
IHES 38, §1. -/
def b2_flatTriv (L : b2_LatticeLocalSystem B) (F : ∀ b, Submodule ℂ (L.cFiber b))
    (U : Set B) (hU : IsSimplyConnected U) (b₀ : U) :
    U × L.cFiber b₀ → b2_totalSpace L F :=
  fun p ↦ ⟨p.1, QuotientAddGroup.mk (Submodule.Quotient.mk
    ((L.flatTransport U hU p.1 b₀).symm p.2))⟩

example (L : b2_LatticeLocalSystem B) (F : ∀ b, Submodule ℂ (L.cFiber b)) (U : Set B)
    (hU : IsSimplyConnected U) (b₀ : U) (p : U × L.cFiber b₀) :
    b2_proj L F (b2_flatTriv L F U hU b₀ p) = p.1 := rfl

/-- **The topology of the total space**: the finest topology for which every flat trivialisation
over a simply connected open set is continuous. When the trivialisations are open maps (frozen
in `RelativeTorusKernel.lean` for a holomorphic filtration) this is the topology in which
`π⁻¹(U) ≅ (U × ℂ ⊗ Λ_{b₀}) ⧸ ∼` for each such `U`.
Source: Bourbaki, *Topologie générale*, ch. I, §2.4 (final topologies); Griffiths, Publ. Math.
IHES 38, §1. -/
instance b2_totalSpace_topology (L : b2_LatticeLocalSystem B)
    (F : ∀ b, Submodule ℂ (L.cFiber b)) : TopologicalSpace (b2_totalSpace L F) :=
  ⨆ (U : Set B) (hU : IsSimplyConnected U) (_ : IsOpen U) (b₀ : U),
    TopologicalSpace.coinduced (b2_flatTriv L F U hU b₀) inferInstance

/-- Each flat trivialisation over a simply connected open set is continuous.
Source: Mathlib `continuous_iff_coinduced_le`. -/
theorem b2_flatTriv_continuous (L : b2_LatticeLocalSystem B)
    (F : ∀ b, Submodule ℂ (L.cFiber b)) (U : Set B) (hU : IsSimplyConnected U) (hUo : IsOpen U)
    (b₀ : U) : Continuous (b2_flatTriv L F U hU b₀) := by
  rw [continuous_iff_coinduced_le]
  exact le_iSup₂_of_le U hU (le_iSup₂_of_le hUo b₀ le_rfl)

example (L : b2_LatticeLocalSystem B) (F : ∀ b, Submodule ℂ (L.cFiber b)) (U : Set B)
    (hU : IsSimplyConnected U) (hUo : IsOpen U) (b₀ : U) :
    Continuous fun v : L.cFiber b₀ ↦ b2_flatTriv L F U hU b₀ (b₀, v) :=
  (b2_flatTriv_continuous L F U hU hUo b₀).comp (Continuous.prodMk_right b₀)

end TotalSpace

/-! ## Standard data: the lattice `ℤ²` -/

section Standard

/-- The Hodge line `F = ℂ · (e₀ + i e₁)` in `ℂ ⊗ ℤ²`.
Source: Birkenhake–Lange, §1.1 (the elliptic curve `ℂ ⧸ (ℤ + iℤ)`). -/
def b2_stdF : Submodule ℂ (ℂ ⊗[ℤ] (Fin 2 → ℤ)) :=
  ℂ ∙ ((1 : ℂ) ⊗ₜ[ℤ] (Pi.single 0 1 : Fin 2 → ℤ) + Complex.I ⊗ₜ[ℤ] (Pi.single 1 1 : Fin 2 → ℤ))

example : (1 : ℂ) ⊗ₜ[ℤ] (Pi.single 0 1 : Fin 2 → ℤ) +
    Complex.I ⊗ₜ[ℤ] (Pi.single 1 1 : Fin 2 → ℤ) ∈ b2_stdF :=
  Submodule.mem_span_singleton_self _

/-- The real line `ℂ · e₀`, equal to its own conjugate.
Source: Birkenhake–Lange, §1.2. -/
def b2_realF : Submodule ℂ (ℂ ⊗[ℤ] (Fin 2 → ℤ)) :=
  ℂ ∙ ((1 : ℂ) ⊗ₜ[ℤ] (Pi.single 0 1 : Fin 2 → ℤ))

example : (1 : ℂ) ⊗ₜ[ℤ] (Pi.single 0 1 : Fin 2 → ℤ) ∈ b2_realF :=
  Submodule.mem_span_singleton_self _

/-- The standard symplectic form `Q(x, y) = x₀ y₁ - x₁ y₀` on `ℤ²`.
Source: Birkenhake–Lange, §3.1 (the form `E` of type `(1)`). -/
def b2_stdForm : LinearMap.BilinForm ℤ (Fin 2 → ℤ) :=
  Matrix.toLinearMap₂' ℤ !![0, 1; -1, 0]

example : b2_stdForm (Pi.single 0 1) (Pi.single 1 1) = 1 := by
  simp [b2_stdForm, Matrix.toLinearMap₂'_apply']

/-- The idempotent `(x, y) ↦ (x + y, 0)` of `ℤ²`, not symmetric for `b2_stdForm`.
Source: elementary; Birkenhake–Lange, §5.3 (symmetric idempotents). -/
def b2_skewIdem : (Fin 2 → ℤ) →+ (Fin 2 → ℤ) :=
  (Matrix.toLin' !![1, 1; 0, 0]).toAddMonoidHom

example : b2_skewIdem (Pi.single 1 1) = Pi.single 0 1 := by
  ext i
  fin_cases i <;> simp [b2_skewIdem]

/-- The real line `ℂ · (√2 e₀ - e₁)`, equal to its own conjugate. In `(ℂ ⊗ ℤ²) ⧸ F ≅ ℂ`
(`e₀ ↦ 1`, `e₁ ↦ √2`) the lattice maps to `ℤ + √2 ℤ ⊂ ℝ`, which is dense.
Source: Birkenhake–Lange, §1.1 (a lattice must be discrete); Mathlib
`dense_addSubgroupClosure_pair_iff`. -/
def b2_irrF : Submodule ℂ (ℂ ⊗[ℤ] (Fin 2 → ℤ)) :=
  ℂ ∙ (((Real.sqrt 2 : ℝ) : ℂ) ⊗ₜ[ℤ] (Pi.single 0 1 : Fin 2 → ℤ) -
    (1 : ℂ) ⊗ₜ[ℤ] (Pi.single 1 1 : Fin 2 → ℤ))

example : ((Real.sqrt 2 : ℝ) : ℂ) ⊗ₜ[ℤ] (Pi.single 0 1 : Fin 2 → ℤ) -
    (1 : ℂ) ⊗ₜ[ℤ] (Pi.single 1 1 : Fin 2 → ℤ) ∈ b2_irrF :=
  Submodule.mem_span_singleton_self _

end Standard

end HodgeLean.Foundations.Program
