import HodgeLean.Foundations.Program.RelativeTorusKernelProofs
import HodgeLean.Foundations.Program.RelativeTorusIdempotent

/-! # Track B2, families of complex tori and images of integral endomorphisms (FROZEN SPEC)

Each theorem is the matching `_aux` theorem of `RelativeTorusKernelProofs.lean`. The objects are
constructed in `RelativeTorusKernelDefs.lean`:
* the fibre torus `b2_torus Λ F = ((ℂ ⊗[ℤ] Λ) ⧸ F) ⧸ Λ` of a lattice `Λ` with a complex subspace
  `F = F¹`, with its quotient group law; `ℂ ⊗[ℤ] Λ` carries its vector-space (module) topology,
  `(ℂ ⊗ Λ) ⧸ F` and `T` the quotient topologies, and for a finite `Λ` with discrete image `T`
  carries the complex charted space `b2_torus_chartedSpace` modelled on `ℂ^g`,
  `g = dim_ℂ ((ℂ ⊗ Λ) ⧸ F)`, whose charts are local sections of the quotient map in linear
  coordinates; `b2_torusCover : ℂ^g → T` is the quotient map in those coordinates;
* the morphism `b2_torusHom` of tori induced by an additive map of lattices whose
  complexification maps `F'` into `F`;
* for an additive endomorphism `f` of `Λ`, the image lattice `f(Λ)` with the preimage filtration
  `b2_imageF F f`, the restricted form `b2_imageQ Q f` and the sub-torus map `b2_subTorus F f`;
* over a complex manifold `B`, a lattice local system `L` (a functor from the fundamental
  groupoid), the image local system `L.image e` of a flat endomorphism `e` (a natural
  transformation `L.functor ⟶ L.functor`), and its filtration and form `L.imageF F e`,
  `L.imageQ Q e`;
* the total space `b2_totalSpace L F = Σ_b T_b` of a family, with the flat trivialisations
  `b2_flatTriv` over simply connected open sets, the final topology for them, the projection
  `b2_proj` and the fibre inclusions `b2_fiberIncl`.

**Claimed.** For a weight-one Hodge structure `ℂ ⊗ Λ = F ⊕ F̄` on a lattice: a `ℤ`-basis of `Λ`
maps to an `ℝ`-basis of `(ℂ ⊗ Λ) ⧸ F`, so the torus is `(ℝ ⧸ ℤ)^{rk Λ}` as a topological group
through that basis, `2 dim_ℂ ((ℂ ⊗ Λ) ⧸ F) = rk Λ`, the lattice is discrete and the torus is
compact; a Riemann form is nondegenerate. For a discrete lattice the torus is Hausdorff and a
complex manifold, the quotient map is a holomorphic covering, and the maps `b2_torusHom` (so the
sub-torus maps) are holomorphic. The image of an endomorphism preserving `F` carries the preimage
filtration as a weight-one Hodge structure, and the restricted form of a Riemann form is a Riemann
form (no symmetry needed); the sub-torus is the image of the induced endomorphism of the torus.
For an idempotent `e` preserving `F`: the sub-torus map is injective, the torus is the direct sum
of the sub-tori of `e` and `1 - e`, and `1 - e` preserves `F` (the kernel and orthogonality
statements are in `RelativeTorusIdempotent.lean`). In families: the image of a flat endomorphism
preserving `F` is again a polarized family of complex tori over `B`; for a holomorphic weight-one
filtration the flat trivialisations are open maps onto `π⁻¹(U)` and the fibre inclusions are
embeddings; for such a filtration of rank `2g` the total space is a complex manifold on which
`π` is a holomorphic submersion, the fibre inclusions and the flat trivialisations are
holomorphic. Witnesses: the constant family `ℤ²` with `F = ℂ (e₀ + i e₁)` over `ℂ` is a polarized
family of complex tori; a real line, a non-discrete lattice `ℤ + √2 ℤ` (non-Hausdorff quotient),
the zero form, a non-symmetric idempotent and `2 · id` are degenerate cases that the hypotheses
rule out.

**Not claimed.** No algebraicity: the Lefschetz embedding of a polarized complex torus into
projective space is not in scope. The comparison with the complex points of an abelian variety is
in `RelativeTorusAbelian.lean`. The charts of the total space are not constructed: their
existence is the frozen statement `b2_totalSpace_complexManifold` (stage B2.1 in
`docs/specs/RelativeTorusKernel.md`). No Jacobian of a curve family and no correspondence: the
endomorphism is an input. Of the fields of `g32h_PrymFamily` and `g34h_PrymFamily`, only the
lattice-derived parts of `dim_eq`, `nondegenerate` and `positive` are supplied, through the
adapters (see `docs/specs/RelativeTorusKernel.md`). HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory Manifold
open scoped TensorProduct ContDiff

namespace HodgeLean.Foundations.Program

section Fibre

variable {Λ : Type*} [AddCommGroup Λ]

/-- **The lattice is a full lattice in `(ℂ ⊗ Λ) ⧸ F`.** For a weight-one Hodge structure `F`
and a finite `ℤ`-basis `b` of `Λ`, the classes `[1 ⊗ bᵢ]` form an `ℝ`-basis of `(ℂ ⊗ Λ) ⧸ F`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Grundlehren 302, §1.1 and
Proposition 1.1.3; Deligne, *Théorie de Hodge II*, Publ. Math. IHES 40, §4.4. -/
theorem b2_latticeMap_basis {ι : Type*} [Fintype ι] (b : Module.Basis ι ℤ Λ)
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F) :
    ∃ c : Module.Basis ι ℝ ((ℂ ⊗[ℤ] Λ) ⧸ F), ∀ i, c i = b2_latticeMap Λ F (b i) :=
  b2_latticeMap_basis_aux b F hF

example (b : Module.Basis (Fin 2) ℤ (Fin 2 → ℤ)) :
    ∃ c : Module.Basis (Fin 2) ℝ ((ℂ ⊗[ℤ] (Fin 2 → ℤ)) ⧸ b2_stdF),
      ∀ i, c i = b2_latticeMap _ b2_stdF (b i) :=
  b2_latticeMap_basis b b2_stdF b2_std_isWeightOne_aux

/-- **The fibre identification.** For a weight-one Hodge structure `F` and a finite `ℤ`-basis
`b` of `Λ`, the torus is `(ℝ ⧸ ℤ)^ι` as a topological group, by
`[∑ tᵢ [1 ⊗ bᵢ]] ↦ (tᵢ mod 1)ᵢ`.
Source: Birkenhake–Lange, §1.1 (`X = V ⧸ Λ ≅ (ℝ ⧸ ℤ)^{2g}` as a real Lie group); Mathlib
`UnitAddCircle`, `ContinuousAddEquiv`. -/
theorem b2_torus_addEquiv {ι : Type*} [Fintype ι] (b : Module.Basis ι ℤ Λ)
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F) :
    ∃ φ : b2_torus Λ F ≃ₜ+ (ι → UnitAddCircle), ∀ t : ι → ℝ,
      φ (QuotientAddGroup.mk (∑ i, t i • b2_latticeMap Λ F (b i))) =
        fun i ↦ (t i : UnitAddCircle) :=
  b2_torus_addEquiv_aux b F hF

example (b : Module.Basis (Fin 2) ℤ (Fin 2 → ℤ)) :
    Nonempty (b2_torus _ b2_stdF ≃ₜ (Fin 2 → UnitAddCircle)) :=
  let ⟨φ, _⟩ := b2_torus_addEquiv b b2_stdF b2_std_isWeightOne_aux
  ⟨φ.toHomeomorph⟩

/-- **Dimension.** For a weight-one Hodge structure on a finite free lattice,
`2 · dim_ℂ ((ℂ ⊗ Λ) ⧸ F) = rk Λ`.
Source: Birkenhake–Lange, §1.1; Deligne, *Théorie de Hodge II*, §4.4. -/
theorem b2_two_mul_finrank [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F) :
    2 * Module.finrank ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F) = Module.finrank ℤ Λ :=
  b2_two_mul_finrank_aux F hF

example : 2 * Module.finrank ℂ ((ℂ ⊗[ℤ] (Fin 2 → ℤ)) ⧸ b2_stdF) = 2 := by
  rw [b2_two_mul_finrank b2_stdF b2_std_isWeightOne_aux]
  simp

/-- **A Riemann form is nondegenerate.** On a free lattice with a weight-one Hodge structure,
a Riemann form `Q` has trivial left kernel.
Source: Birkenhake–Lange, §4.1–4.2 (a polarization is a nondegenerate form);
Griffiths, Amer. J. Math. 90 (1968), §2. -/
theorem b2_riemannForm_nondegenerate [Module.Free ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ))
    (Q : LinearMap.BilinForm ℤ Λ) (hF : b2_IsWeightOne Λ F) (hQ : b2_IsRiemannForm Λ F Q)
    (x : Λ) (hx : ∀ y, Q x y = 0) : x = 0 :=
  b2_riemannForm_nondegenerate_aux F Q hF hQ x hx

example (x : Fin 2 → ℤ) (hx : ∀ y, b2_stdForm x y = 0) : x = 0 :=
  b2_riemannForm_nondegenerate b2_stdF b2_stdForm b2_std_isWeightOne_aux
    b2_std_isRiemannForm_aux x hx

/-- **The image of an endomorphism is a weight-one Hodge structure.** If `f : Λ → Λ` preserves
`F` (`f_ℂ(F) ⊆ F`), the preimage of `F` in `ℂ ⊗ f(Λ)` is a weight-one Hodge structure on the
lattice `f(Λ)`.
Source: Birkenhake–Lange, §5.3 and §12.2 (the image of an endomorphism is a sub-torus);
Deligne, *Théorie de Hodge II*, §1.2 (the category of Hodge structures is abelian). -/
theorem b2_image_isWeightOne (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F)
    (f : Λ →+ Λ) (hf : F ≤ F.comap (b2_cplxMap f)) :
    b2_IsWeightOne f.range (b2_imageF F f) :=
  b2_image_isWeightOne_aux F hF f hf

example (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F) :
    b2_IsWeightOne (AddMonoidHom.id Λ).range (b2_imageF F (AddMonoidHom.id Λ)) :=
  b2_image_isWeightOne F hF _ (fun x hx ↦ by simpa using hx)

/-- **The restricted form is a Riemann form.** For any endomorphism `f`, the restriction of a
Riemann form for `F` to `f(Λ)` is a Riemann form for the preimage filtration.
Source: Birkenhake–Lange, §5.3 (the induced polarization on an abelian subvariety). -/
theorem b2_image_isRiemannForm (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (Q : LinearMap.BilinForm ℤ Λ)
    (hQ : b2_IsRiemannForm Λ F Q) (f : Λ →+ Λ) :
    b2_IsRiemannForm f.range (b2_imageF F f) (b2_imageQ Q f) :=
  b2_image_isRiemannForm_aux F Q hQ f

example (f : (Fin 2 → ℤ) →+ (Fin 2 → ℤ)) :
    b2_IsRiemannForm f.range (b2_imageF b2_stdF f) (b2_imageQ b2_stdForm f) :=
  b2_image_isRiemannForm b2_stdF b2_stdForm b2_std_isRiemannForm_aux f

/-- **The sub-torus is the image of the induced endomorphism.** If `f` preserves `F`, the image
of `T(f(Λ)) → T(Λ)` is the image of the endomorphism of `T(Λ)` induced by `f`.
Source: Birkenhake–Lange, §1.2 and §5.3 (the image of a homomorphism of complex tori). -/
theorem b2_subTorus_range (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (f : Λ →+ Λ)
    (hf : F ≤ F.comap (b2_cplxMap f)) :
    (b2_subTorus F f).range = (b2_torusHom F F f hf).range :=
  b2_subTorus_range_aux F f hf

example (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (f : Λ →+ Λ) (hf : F ≤ F.comap (b2_cplxMap f))
    (x : b2_torus f.range (b2_imageF F f)) :
    b2_subTorus F f x ∈ (b2_torusHom F F f hf).range :=
  b2_subTorus_range F f hf ▸ ⟨x, rfl⟩

/-- **The sub-torus of an idempotent embeds.** If `e` is idempotent and preserves `F`, the map
`T(e(Λ)) → T(Λ)` is injective.
Source: Birkenhake–Lange, §5.3 (abelian subvarieties and symmetric idempotents) and §12.2. -/
theorem b2_subTorus_injective (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (e : Λ →+ Λ)
    (he : e.comp e = e) (hf : F ≤ F.comap (b2_cplxMap e)) :
    Function.Injective (b2_subTorus F e) :=
  b2_subTorus_injective_aux F e he hf

example (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) :
    Function.Injective (b2_subTorus F (AddMonoidHom.id Λ)) :=
  b2_subTorus_injective F _ rfl (fun x hx ↦ by simpa using hx)

/-- **The torus splits along an idempotent.** If `e` is idempotent and preserves `F`, the sum of
the sub-tori of `e` and of `1 - e` is an additive bijection `T(e(Λ)) × T((1 - e)(Λ)) → T(Λ)`.
Source: Birkenhake–Lange, §5.3 (the decomposition by a symmetric idempotent; the group-level
splitting needs only idempotence). -/
theorem b2_torus_split (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (e : Λ →+ Λ)
    (he : e.comp e = e) (hf : F ≤ F.comap (b2_cplxMap e)) :
    Function.Bijective (fun p : b2_torus e.range (b2_imageF F e) ×
        b2_torus (AddMonoidHom.id Λ - e).range (b2_imageF F (AddMonoidHom.id Λ - e)) ↦
      b2_subTorus F e p.1 + b2_subTorus F (AddMonoidHom.id Λ - e) p.2) :=
  b2_torus_split_aux F e he hf

example (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (e : Λ →+ Λ) (he : e.comp e = e)
    (hf : F ≤ F.comap (b2_cplxMap e)) (x : b2_torus Λ F) :
    ∃ p : b2_torus e.range (b2_imageF F e) ×
        b2_torus (AddMonoidHom.id Λ - e).range (b2_imageF F (AddMonoidHom.id Λ - e)),
      b2_subTorus F e p.1 + b2_subTorus F (AddMonoidHom.id Λ - e) p.2 = x :=
  (b2_torus_split F e he hf).2 x

/-- **`1 - e` preserves `F`** when `e` does, so the kernel `(1 - e)(Λ)` carries the
constructions of the image.
Source: elementary; Birkenhake–Lange, §5.3. -/
theorem b2_one_sub_le_comap (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (e : Λ →+ Λ)
    (hf : F ≤ F.comap (b2_cplxMap e)) :
    F ≤ F.comap (b2_cplxMap (AddMonoidHom.id Λ - e)) :=
  b2_one_sub_le_comap_aux F e hf

example (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F) (e : Λ →+ Λ)
    (hf : F ≤ F.comap (b2_cplxMap e)) :
    b2_IsWeightOne (AddMonoidHom.id Λ - e).range (b2_imageF F (AddMonoidHom.id Λ - e)) :=
  b2_image_isWeightOne F hF _ (b2_one_sub_le_comap F e hf)

/-- **The lattice is discrete.** For a weight-one Hodge structure on a finite free lattice, the
image of `Λ` in `(ℂ ⊗ Λ) ⧸ F` is a discrete subgroup.
Source: Birkenhake–Lange, §1.1 (a lattice of `ℂ^g` is a discrete subgroup of rank `2g`);
Deligne, *Théorie de Hodge II*, §4.4. -/
theorem b2_latticeMap_discrete [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F) :
    DiscreteTopology (b2_latticeMap Λ F).range :=
  b2_latticeMap_discrete_aux F hF

example : DiscreteTopology (b2_latticeMap (Fin 2 → ℤ) b2_stdF).range :=
  b2_latticeMap_discrete b2_stdF b2_std_isWeightOne_aux

/-- **The torus is Hausdorff** when the lattice is discrete: a discrete subgroup of the Hausdorff
group `(ℂ ⊗ Λ) ⧸ F` is closed.
Source: Bourbaki, *Topologie générale*, ch. III, §2.6 (quotients by closed subgroups) and §4
(discrete subgroups are closed); Mathlib `AddSubgroup.isClosed_of_discreteTopology`. -/
theorem b2_torus_t2Space [Module.Finite ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ))
    [DiscreteTopology (b2_latticeMap Λ F).range] :
    T2Space (b2_torus Λ F) :=
  b2_torus_t2Space_aux F

example : T2Space (b2_torus (Fin 2 → ℤ) b2_stdF) :=
  haveI := b2_latticeMap_discrete b2_stdF b2_std_isWeightOne_aux
  b2_torus_t2Space b2_stdF

/-- **The torus is compact** for a weight-one Hodge structure on a finite free lattice: the image
of the cube `[0, 1]^n` in the real basis of `b2_latticeMap_basis` covers it.
Source: Birkenhake–Lange, §1.1; Mathlib `IsZLattice.isCompact_range_of_periodic`. -/
theorem b2_torus_compactSpace [Module.Free ℤ Λ] [Module.Finite ℤ Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : b2_IsWeightOne Λ F) :
    CompactSpace (b2_torus Λ F) :=
  b2_torus_compactSpace_aux F hF

example : CompactSpace (b2_torus (Fin 2 → ℤ) b2_stdF) :=
  b2_torus_compactSpace b2_stdF b2_std_isWeightOne_aux

/-- **The torus is a complex manifold.** For a finite `Λ` whose image in `(ℂ ⊗ Λ) ⧸ F` is
discrete, the charts `b2_torusChart` (local sections of the quotient map in linear coordinates)
form a holomorphic atlas: each transition map is, near each point, a translation by a lattice
vector.
Source: Birkenhake–Lange, §1.1; Huybrechts, *Complex Geometry*, Example 1.1.3. -/
theorem b2_torus_isManifold [Module.Finite ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ))
    [DiscreteTopology (b2_latticeMap Λ F).range] :
    IsManifold 𝓘(ℂ, Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F)) → ℂ) ω (b2_torus Λ F) :=
  b2_torus_isManifold_aux F

example :
    haveI := b2_latticeMap_discrete b2_stdF b2_std_isWeightOne_aux
    IsManifold 𝓘(ℂ, Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] (Fin 2 → ℤ)) ⧸ b2_stdF)) → ℂ) ω
      (b2_torus (Fin 2 → ℤ) b2_stdF) :=
  haveI := b2_latticeMap_discrete b2_stdF b2_std_isWeightOne_aux
  b2_torus_isManifold b2_stdF

/-- **The quotient map is a covering.** In linear coordinates, `ℂ^g → T` is a covering map.
Source: Hatcher, *Algebraic Topology*, §1.3 (quotients by properly discontinuous actions);
Mathlib `AddSubgroup.isAddQuotientCoveringMap_of_comm`. -/
theorem b2_torusCover_isCoveringMap [Module.Finite ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ))
    [DiscreteTopology (b2_latticeMap Λ F).range] :
    IsCoveringMap (b2_torusCover Λ F) :=
  b2_torusCover_isCoveringMap_aux F

example : IsCoveringMap (b2_torusCover (Fin 2 → ℤ) b2_stdF) :=
  haveI := b2_latticeMap_discrete b2_stdF b2_std_isWeightOne_aux
  b2_torusCover_isCoveringMap b2_stdF

/-- **The quotient map is holomorphic.** In linear coordinates, `ℂ^g → T` is holomorphic for the
charted space `b2_torus_chartedSpace`.
Source: Birkenhake–Lange, §1.1; Huybrechts, *Complex Geometry*, Example 1.1.3. -/
theorem b2_torusCover_contMDiff [Module.Finite ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ))
    [DiscreteTopology (b2_latticeMap Λ F).range] :
    ContMDiff 𝓘(ℂ, Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F)) → ℂ)
      𝓘(ℂ, Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F)) → ℂ) ω (b2_torusCover Λ F) :=
  b2_torusCover_contMDiff_aux F

example [Module.Finite ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ))
    [DiscreteTopology (b2_latticeMap Λ F).range] : Continuous (b2_torusCover Λ F) :=
  (b2_torusCover_contMDiff F).continuous

end Fibre

section Holomorphic

variable {Λ Λ' : Type*} [AddCommGroup Λ] [AddCommGroup Λ']

/-- **The induced maps of tori are holomorphic.** For discrete lattices, the group homomorphism
`b2_torusHom F' F g hg`, induced by the complex-linear `g_ℂ`, is holomorphic; in charts it is
`g_ℂ` up to translations by lattice vectors. In particular every sub-torus map `b2_subTorus` is
holomorphic.
Source: Birkenhake–Lange, §1.2 (homomorphisms of complex tori and their analytic
representation). -/
theorem b2_torusHom_contMDiff [Module.Finite ℤ Λ'] [Module.Finite ℤ Λ]
    (F' : Submodule ℂ (ℂ ⊗[ℤ] Λ')) (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (g : Λ' →+ Λ)
    (hg : F' ≤ F.comap (b2_cplxMap g)) [DiscreteTopology (b2_latticeMap Λ' F').range]
    [DiscreteTopology (b2_latticeMap Λ F).range] :
    ContMDiff 𝓘(ℂ, Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ') ⧸ F')) → ℂ)
      𝓘(ℂ, Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F)) → ℂ) ω (b2_torusHom F' F g hg) :=
  b2_torusHom_contMDiff_aux F' F g hg

example [Module.Finite ℤ Λ] (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (f : Λ →+ Λ)
    [Module.Finite ℤ f.range] [DiscreteTopology (b2_latticeMap f.range (b2_imageF F f)).range]
    [DiscreteTopology (b2_latticeMap Λ F).range] :
    ContMDiff 𝓘(ℂ, Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] f.range) ⧸ b2_imageF F f)) → ℂ)
      𝓘(ℂ, Fin (Module.finrank ℂ ((ℂ ⊗[ℤ] Λ) ⧸ F)) → ℂ) ω (b2_subTorus F f) :=
  b2_torusHom_contMDiff _ _ _ _

end Holomorphic

section Family

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {B : Type*} [TopologicalSpace B] [ChartedSpace E B]

/-- **The restricted form is flat.** For a flat form `Q` and a flat endomorphism `e`, the
restricted forms on the image local system are preserved by its transport.
Source: Deligne, LNM 163, I.1 (sub-local systems); Birkenhake–Lange, §5.3. -/
theorem b2_image_flat (L : b2_LatticeLocalSystem B)
    (Q : ∀ b, LinearMap.BilinForm ℤ (L.fiber b))
    (hQ : ∀ (b b' : B) (γ : Path.Homotopic.Quotient b b') (x y : L.fiber b),
      Q b' (L.transport γ x) (L.transport γ y) = Q b x y)
    (e : L.functor ⟶ L.functor) :
    ∀ (b b' : B) (γ : Path.Homotopic.Quotient b b') (x y : (L.image e).fiber b),
      L.imageQ Q e b' ((L.image e).transport γ x) ((L.image e).transport γ y) =
        L.imageQ Q e b x y :=
  b2_image_flat_aux L Q hQ e

example (L : b2_LatticeLocalSystem B) (F : ∀ b, Submodule ℂ (L.cFiber b))
    (Q : ∀ b, LinearMap.BilinForm ℤ (L.fiber b)) (hT : b2_IsPolarizedTorusFamily E L F Q)
    (e : L.functor ⟶ L.functor) (b : B) (x y : (L.image e).fiber b) :
    L.imageQ Q e b ((L.image e).transport (Path.Homotopic.Quotient.mk (Path.refl b)) x)
      ((L.image e).transport (Path.Homotopic.Quotient.mk (Path.refl b)) y) =
        L.imageQ Q e b x y :=
  b2_image_flat L Q hT.flat e b b _ x y

/-- **The image filtration is holomorphic.** In a polarized family of complex tori, for a flat
endomorphism `e` preserving `F`, the preimage filtration on the image local system is locally
generated by holomorphic sections.
Source: Griffiths, Publ. Math. IHES 38 (1970), §1; Deligne, *Théorie de Hodge II*, §4.4
(variations of Hodge structure of weight one form an abelian category). -/
theorem b2_image_holomorphic (L : b2_LatticeLocalSystem B)
    (F : ∀ b, Submodule ℂ (L.cFiber b)) (Q : ∀ b, LinearMap.BilinForm ℤ (L.fiber b))
    (hT : b2_IsPolarizedTorusFamily E L F Q) (e : L.functor ⟶ L.functor)
    (hf : ∀ b, F b ≤ (F b).comap (b2_cplxMap (e.app (FundamentalGroupoid.mk b)).hom)) :
    (L.image e).IsHolomorphicSubbundle E (L.imageF F e) :=
  b2_image_holomorphic_aux L F Q hT e hf

example (L : b2_LatticeLocalSystem B) (F : ∀ b, Submodule ℂ (L.cFiber b))
    (Q : ∀ b, LinearMap.BilinForm ℤ (L.fiber b)) (hT : b2_IsPolarizedTorusFamily E L F Q) :
    (L.image (𝟙 L.functor)).IsHolomorphicSubbundle E (L.imageF F (𝟙 L.functor)) :=
  b2_image_holomorphic L F Q hT _ (fun _ x hx ↦ by simpa using hx)

/-- **The image of a flat endomorphism is a polarized family of complex tori.** In a polarized
family of complex tori, for a flat endomorphism `e` preserving `F`, the image local system with
the preimage filtration and the restricted form is again a polarized family of complex tori;
fibrewise it is `b2_image_isWeightOne` and `b2_image_isRiemannForm`, with `b2_image_flat` and
`b2_image_holomorphic`.
Source: Birkenhake–Lange, §5.3 and §12.2; Deligne, *Théorie de Hodge II*, §4.4. -/
theorem b2_image_isPolarizedTorusFamily (L : b2_LatticeLocalSystem B)
    (F : ∀ b, Submodule ℂ (L.cFiber b)) (Q : ∀ b, LinearMap.BilinForm ℤ (L.fiber b))
    (hT : b2_IsPolarizedTorusFamily E L F Q) (e : L.functor ⟶ L.functor)
    (hf : ∀ b, F b ≤ (F b).comap (b2_cplxMap (e.app (FundamentalGroupoid.mk b)).hom)) :
    b2_IsPolarizedTorusFamily E (L.image e) (L.imageF F e) (L.imageQ Q e) :=
  b2_image_isPolarizedTorusFamily_aux L F Q hT e hf

example (L : b2_LatticeLocalSystem B) (F : ∀ b, Submodule ℂ (L.cFiber b))
    (Q : ∀ b, LinearMap.BilinForm ℤ (L.fiber b)) (hT : b2_IsPolarizedTorusFamily E L F Q)
    (e : L.functor ⟶ L.functor)
    (hf : ∀ b, F b ≤ (F b).comap (b2_cplxMap (e.app (FundamentalGroupoid.mk b)).hom))
    (b : B) :
    b2_IsWeightOne ((L.image e).fiber b) (L.imageF F e b) :=
  (b2_image_isPolarizedTorusFamily L F Q hT e hf).hodge b

/-- **The flat trivialisations are open.** For a filtration of weight one at each point, locally
generated by holomorphic sections, each flat trivialisation over a simply connected open `U` is an open map onto
`π⁻¹(U)`; so `π⁻¹(U)` is the quotient of `U × (ℂ ⊗ Λ_{b₀})` by the transported `F_b + Λ_{b₀}`.
Source: Griffiths, Publ. Math. IHES 38 (1970), §1; Bourbaki, *Topologie générale*, ch. I, §5
(open quotient maps). -/
theorem b2_flatTriv_isOpenMap (L : b2_LatticeLocalSystem B)
    (F : ∀ b, Submodule ℂ (L.cFiber b)) (hhol : L.IsHolomorphicSubbundle E F)
    (hw : ∀ b, b2_IsWeightOne (L.fiber b) (F b)) (U : Set B) (hU : IsSimplyConnected U)
    (hUo : IsOpen U) (b₀ : U) :
    IsOpenMap (b2_flatTriv L F U hU b₀) ∧
      Set.range (b2_flatTriv L F U hU b₀) = b2_proj L F ⁻¹' U :=
  b2_flatTriv_isOpenMap_aux L F hhol hw U hU hUo b₀

example (L : b2_LatticeLocalSystem B) (F : ∀ b, Submodule ℂ (L.cFiber b))
    (Q : ∀ b, LinearMap.BilinForm ℤ (L.fiber b)) (hT : b2_IsPolarizedTorusFamily E L F Q)
    (U : Set B) (hU : IsSimplyConnected U) (hUo : IsOpen U) (b₀ : U) :
    IsOpen (b2_proj L F ⁻¹' U) := by
  rw [← (b2_flatTriv_isOpenMap L F hT.holomorphic hT.hodge U hU hUo b₀).2]
  exact (b2_flatTriv_isOpenMap L F hT.holomorphic hT.hodge U hU hUo b₀).1.isOpen_range

/-- **The fibres are the tori.** For a filtration of weight one at each point, locally generated
by holomorphic sections, the inclusion `T_b → 𝒯` of the fibre over `b` is a topological
embedding, so the fibre `π⁻¹(b)` with the subspace topology is the torus `b2_torus (Λ_b) (F_b)`.
Source: Griffiths, Publ. Math. IHES 38, §1; Deligne, *Théorie de Hodge II*, §4.4. -/
theorem b2_fiberIncl_isEmbedding (L : b2_LatticeLocalSystem B)
    (F : ∀ b, Submodule ℂ (L.cFiber b)) (hhol : L.IsHolomorphicSubbundle E F)
    (hw : ∀ b, b2_IsWeightOne (L.fiber b) (F b)) (b : B) :
    Topology.IsEmbedding (b2_fiberIncl L F b) :=
  b2_fiberIncl_isEmbedding_aux L F hhol hw b

example (L : b2_LatticeLocalSystem B) (F : ∀ b, Submodule ℂ (L.cFiber b))
    (Q : ∀ b, LinearMap.BilinForm ℤ (L.fiber b)) (hT : b2_IsPolarizedTorusFamily E L F Q)
    (b : B) : Function.Injective (b2_fiberIncl L F b) :=
  (b2_fiberIncl_isEmbedding L F hT.holomorphic hT.hodge b).injective

/-- **The total space is a complex manifold and the projection a holomorphic submersion.** Over a
complex manifold `B`, for a filtration of weight one at each point, locally generated by
holomorphic sections, with `rk Λ_b = 2g`: the topological total space `𝒯` carries a complex
charted space modelled on `E × ℂ^g` for which
* `𝒯` is a complex manifold;
* `π : 𝒯 → B` is holomorphic with surjective differential at every point (a submersion);
* each fibre inclusion `T_b → 𝒯` is holomorphic for the complex structure
  `b2_torus_chartedSpace` of `T_b`;
* each flat trivialisation `U × ℂ ⊗ Λ_{b₀} → 𝒯` over a simply connected open `U` is holomorphic
  in linear coordinates.
The last clause determines the complex structure: the trivialisations are surjective
submersions onto the open sets `π⁻¹(U)`. The charts are not constructed in this file (see
`docs/specs/RelativeTorusKernel.md`, stage B2.1).
Source: Griffiths, Publ. Math. IHES 38 (1970), §1 (the family of intermediate Jacobians of a
variation; in weight one, of complex tori); Deligne, *Théorie de Hodge II*, §4.4; Huybrechts,
*Complex Geometry*, §2.3 (quotients of holomorphic vector bundles). -/
theorem b2_totalSpace_complexManifold [IsManifold 𝓘(ℂ, E) ω B]
    (L : b2_LatticeLocalSystem B) (F : ∀ b, Submodule ℂ (L.cFiber b))
    (hhol : L.IsHolomorphicSubbundle E F) (hw : ∀ b, b2_IsWeightOne (L.fiber b) (F b))
    (g : ℕ) (hg : ∀ b, Module.finrank ℤ (L.fiber b) = 2 * g) :
    ∃ cs : ChartedSpace (E × (Fin g → ℂ)) (b2_totalSpace L F),
      letI := cs
      IsManifold 𝓘(ℂ, E × (Fin g → ℂ)) ω (b2_totalSpace L F) ∧
      ContMDiff 𝓘(ℂ, E × (Fin g → ℂ)) 𝓘(ℂ, E) ω (b2_proj L F) ∧
      (∀ p, Function.Surjective (mfderiv 𝓘(ℂ, E × (Fin g → ℂ)) 𝓘(ℂ, E) (b2_proj L F) p)) ∧
      (∀ b, letI := b2_latticeMap_discrete (F b) (hw b)
        ContMDiff 𝓘(ℂ, Fin (Module.finrank ℂ ((L.cFiber b) ⧸ F b)) → ℂ)
          𝓘(ℂ, E × (Fin g → ℂ)) ω (b2_fiberIncl L F b)) ∧
      ∀ (U : TopologicalSpace.Opens B) (hU : IsSimplyConnected (U : Set B)) (b₀ : U),
        ContMDiff (𝓘(ℂ, E).prod 𝓘(ℂ, Fin (Module.finrank ℂ (L.cFiber b₀)) → ℂ))
          𝓘(ℂ, E × (Fin g → ℂ)) ω
          (fun p : U × (Fin (Module.finrank ℂ (L.cFiber b₀)) → ℂ) ↦
            b2_flatTriv L F U hU b₀ (p.1, (b2_coord (L.cFiber b₀)).symm p.2)) :=
  b2_totalSpace_complexManifold_aux L F hhol hw g hg

example [IsManifold 𝓘(ℂ, E) ω B] (L : b2_LatticeLocalSystem B)
    (F : ∀ b, Submodule ℂ (L.cFiber b)) (Q : ∀ b, LinearMap.BilinForm ℤ (L.fiber b))
    (hT : b2_IsPolarizedTorusFamily E L F Q) (g : ℕ)
    (hg : ∀ b, Module.finrank ℤ (L.fiber b) = 2 * g) :
    ∃ cs : ChartedSpace (E × (Fin g → ℂ)) (b2_totalSpace L F),
      letI := cs
      ContMDiff 𝓘(ℂ, E × (Fin g → ℂ)) 𝓘(ℂ, E) ω (b2_proj L F) :=
  let ⟨cs, h⟩ := b2_totalSpace_complexManifold L F hT.holomorphic hT.hodge g hg
  ⟨cs, h.2.1⟩

end Family

section Standard

/-- **Witness: `F = ℂ (e₀ + i e₁)` is a weight-one Hodge structure on `ℤ²`.**
Source: Birkenhake–Lange, §1.1 (the elliptic curve `ℂ ⧸ (ℤ + iℤ)`). -/
theorem b2_std_isWeightOne : b2_IsWeightOne (Fin 2 → ℤ) b2_stdF :=
  b2_std_isWeightOne_aux

example : b2_stdF ⊓ b2_conjSubmodule _ b2_stdF = ⊥ :=
  b2_std_isWeightOne.inf_eq_bot

/-- **Witness: the standard symplectic form is a Riemann form for `F = ℂ (e₀ + i e₁)`.**
Source: Birkenhake–Lange, §3.1 and §4.2 (the principal polarization of `ℂ ⧸ (ℤ + iℤ)`). -/
theorem b2_std_isRiemannForm : b2_IsRiemannForm (Fin 2 → ℤ) b2_stdF b2_stdForm :=
  b2_std_isRiemannForm_aux

example (x : Fin 2 → ℤ) : b2_stdForm x x = 0 :=
  b2_std_isRiemannForm.alt x

/-- **Witness: the constant family.** The constant lattice local system `ℤ²` over `ℂ`, with the
constant filtration `ℂ (e₀ + i e₁)` and the standard symplectic form, is a polarized family of
complex tori.
Source: Birkenhake–Lange, §1.1 and §4.2; Deligne, *Théorie de Hodge II*, §4.4. -/
theorem b2_const_isPolarizedTorusFamily :
    b2_IsPolarizedTorusFamily ℂ (b2_constLocalSystem ℂ (Fin 2 → ℤ)) (fun _ ↦ b2_stdF)
      (fun _ ↦ b2_stdForm) :=
  b2_const_isPolarizedTorusFamily_aux

example : b2_IsPolarizedTorusFamily ℂ
    ((b2_constLocalSystem ℂ (Fin 2 → ℤ)).image (𝟙 _))
    ((b2_constLocalSystem ℂ (Fin 2 → ℤ)).imageF (fun _ ↦ b2_stdF) (𝟙 _))
    ((b2_constLocalSystem ℂ (Fin 2 → ℤ)).imageQ (fun _ ↦ b2_stdForm) (𝟙 _)) :=
  b2_image_isPolarizedTorusFamily _ _ _ b2_const_isPolarizedTorusFamily _
    (fun _ x hx ↦ by
      simp only [NatTrans.id_app, AddCommGrpCat.hom_id, b2_cplxMap_id]
      exact hx)

-- The constant family `ℤ²` over `ℂ` satisfies the hypotheses of
-- `b2_totalSpace_complexManifold` with `g = 1`: its total space is `ℂ × ℂ ⧸ (ℤ + iℤ)`.
example : ∃ cs : ChartedSpace (ℂ × (Fin 1 → ℂ))
      (b2_totalSpace (b2_constLocalSystem ℂ (Fin 2 → ℤ))
        (b2_constF ℂ (Fin 2 → ℤ) b2_stdF)),
    letI := cs
    ContMDiff 𝓘(ℂ, ℂ × (Fin 1 → ℂ)) 𝓘(ℂ, ℂ) ω
      (b2_proj (b2_constLocalSystem ℂ (Fin 2 → ℤ))
        (b2_constF ℂ (Fin 2 → ℤ) b2_stdF)) :=
  let ⟨cs, h⟩ := b2_totalSpace_complexManifold _ _ b2_const_isPolarizedTorusFamily.holomorphic
    b2_const_isPolarizedTorusFamily.hodge 1 (fun _ ↦ by
      change Module.finrank ℤ (Fin 2 → ℤ) = 2 * 1
      simp)
  ⟨cs, h.2.1⟩

/-- **Degenerate case: a real line is not a weight-one Hodge structure.** `ℂ e₀ ⊆ ℂ ⊗ ℤ²` is
its own conjugate.
Source: Birkenhake–Lange, §1.2. -/
theorem b2_realF_not_isWeightOne : ¬ b2_IsWeightOne (Fin 2 → ℤ) b2_realF :=
  b2_realF_not_isWeightOne_aux

example : b2_realF ≠ b2_stdF := fun h ↦
  b2_realF_not_isWeightOne (h ▸ b2_std_isWeightOne)

/-- **Degenerate case: the zero form is not a Riemann form** for a nonzero `F`.
Source: Birkenhake–Lange, §4.2 (positivity). -/
theorem b2_zero_not_isRiemannForm {Λ : Type*} [AddCommGroup Λ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (hF : F ≠ ⊥) : ¬ b2_IsRiemannForm Λ F 0 :=
  b2_zero_not_isRiemannForm_aux F hF

example (F : Submodule ℂ (ℂ ⊗[ℤ] (Fin 2 → ℤ))) (hF : F ≠ ⊥)
    (Q : LinearMap.BilinForm ℤ (Fin 2 → ℤ)) (hQ : b2_IsRiemannForm _ F Q) : Q ≠ 0 :=
  fun h ↦ b2_zero_not_isRiemannForm F hF (h ▸ hQ)

/-- **Degenerate case: orthogonality needs symmetry.** The idempotent `(x, y) ↦ (x + y, 0)` of
`ℤ²` has `Q(e(Λ), (1 - e)(Λ)) ≠ 0` for the standard form.
Source: Birkenhake–Lange, §5.3. -/
theorem b2_skewIdem_not_orthogonal :
    b2_skewIdem.comp b2_skewIdem = b2_skewIdem ∧
      ∃ x ∈ b2_skewIdem.range, ∃ y ∈ (AddMonoidHom.id (Fin 2 → ℤ) - b2_skewIdem).range,
        b2_stdForm x y ≠ 0 :=
  b2_skewIdem_not_orthogonal_aux

example : ¬ ∀ x y, b2_stdForm (b2_skewIdem x) y = b2_stdForm x (b2_skewIdem y) := fun h ↦
  let ⟨x, hx, y, hy, hne⟩ := b2_skewIdem_not_orthogonal.2
  hne (b2_orthogonal_of_symm _ _ b2_skewIdem_not_orthogonal.1 h x hx y hy)

/-- **Degenerate case: injectivity needs idempotence.** For `2 · id` on `ℤ²` the sub-torus map
`T(2ℤ²) → T(ℤ²)` has kernel `ℤ² ⧸ 2ℤ²`, so it is not injective.
Source: Birkenhake–Lange, §1.2 (isogenies; multiplication by `n`). -/
theorem b2_two_subTorus_not_injective :
    ¬ Function.Injective (b2_subTorus b2_stdF (2 • AddMonoidHom.id (Fin 2 → ℤ))) :=
  b2_two_subTorus_not_injective_aux

example : ∃ x y : b2_torus (2 • AddMonoidHom.id (Fin 2 → ℤ)).range
      (b2_imageF b2_stdF (2 • AddMonoidHom.id (Fin 2 → ℤ))),
    x ≠ y ∧ b2_subTorus b2_stdF (2 • AddMonoidHom.id _) x =
      b2_subTorus b2_stdF (2 • AddMonoidHom.id _) y := by
  have h := b2_two_subTorus_not_injective
  simp only [Function.Injective, not_forall] at h
  obtain ⟨x, y, hxy, hne⟩ := h
  exact ⟨x, y, hne, hxy⟩

/-- **Degenerate case: a non-discrete lattice.** For the real line `F = ℂ (√2 e₀ - e₁)` the image
of `ℤ²` in `(ℂ ⊗ ℤ²) ⧸ F ≅ ℂ` is `ℤ + √2 ℤ ⊂ ℝ`, which is not discrete.
Source: Birkenhake–Lange, §1.1; Mathlib `dense_addSubgroupClosure_pair_iff`. -/
theorem b2_irrF_not_discrete :
    ¬ DiscreteTopology (b2_latticeMap (Fin 2 → ℤ) b2_irrF).range :=
  b2_irrF_not_discrete_aux

example : ¬ b2_IsWeightOne (Fin 2 → ℤ) b2_irrF := fun h ↦
  b2_irrF_not_discrete (b2_latticeMap_discrete b2_irrF h)

/-- **Degenerate case: the quotient by a non-discrete subgroup is not Hausdorff.** For
`F = ℂ (√2 e₀ - e₁)` the closure of the image of `ℤ²` is the real line, so the class of `0` is not
closed in the torus.
Source: Bourbaki, *Topologie générale*, ch. III, §2.6 (a quotient group is Hausdorff iff the
subgroup is closed). -/
theorem b2_irrF_not_t2Space : ¬ T2Space (b2_torus (Fin 2 → ℤ) b2_irrF) :=
  b2_irrF_not_t2Space_aux

example : ¬ T2Space (b2_torus (Fin 2 → ℤ) b2_irrF) ∧ T2Space (b2_torus (Fin 2 → ℤ) b2_stdF) :=
  ⟨b2_irrF_not_t2Space,
    haveI := b2_latticeMap_discrete b2_stdF b2_std_isWeightOne_aux
    b2_torus_t2Space b2_stdF⟩

end Standard

end HodgeLean.Foundations.Program
