import HodgeLean.Foundations.DolbeaultCurve3Proofs

/-! # The Dolbeault sequence on `X(ℂ)`, stage 3: acyclicity of the soft Dolbeault sheaves (FROZEN SPEC)

Scope. dolb2 (`DolbeaultCurve2.lean`) proves `H^2(X(ℂ), 𝒪) = 0` and `CycleClassIsHodge X` for an
integral smooth projective curve as an implication from two binders, `ℍ^2(𝒜^{0,0}[0]) = 0` (`hA`)
and `ℍ^1(𝒜^{0,1}[0]) = 0` (`hB`). This stage discharges both, through soft sheaves.

* Soft sheaves on a compact Hausdorff space (statements 1–6), for the predicate `IsSoft` of
  `DolbeaultCurve3Defs.lean`: flasque sheaves are soft; in a short exact sequence
  `0 → A → B → C → 0` with `A` soft, sections of `C` lift near closed sets (a gluing step for two
  closed sets on a normal space, then compactness), so `Γ(B) → Γ(C)` is onto and, if `B` is soft
  too, `C` is soft; soft sheaves have vanishing Mathlib sheaf cohomology `Sheaf.H F (n + 1)`.
* Comparison (statements 7, 8): the repository's hypercohomology `ℍ^n(X; F[0])` of a single sheaf
  is in bijection with Mathlib's `Sheaf.H F n`, so soft sheaves on a compact Hausdorff `X(ℂ)` have
  `ℍ^(n+1)(X; F[0]) = 0`.
* The Dolbeault sheaves are soft (statements 9, 10): smooth bump functions multiply sections of
  `𝒜^{0,0}` and `𝒜^{0,1}` (dolb2 statement 9), on `X(ℂ)` Hausdorff and σ-compact.
* Corollaries (statements 11–14): `ℍ^(n+1)(𝒜^{0,0}[0]) = 0` and `ℍ^(n+1)(𝒜^{0,1}[0]) = 0` for projective
  `X` (in particular `hA` and `hB`), hence `H^2(X(ℂ), 𝒪) = 0` and `CycleClassIsHodge X` for every
  integral smooth projective curve, with no binder beyond the instances.

Claimed: statements 1–6 for every compact Hausdorff space (statement 2 for every normal space);
statements 7, 8 for every `X`; statements 9, 10 in every relative dimension for `X(ℂ)` Hausdorff and
σ-compact; statements 11, 12 for projective `X`; statements 13, 14 for integral smooth projective
curves, unconditionally.

Not claimed: soft-sheaf acyclicity on paracompact non-compact spaces (only compact Hausdorff is
needed here); fine sheaves as a notion, or sheaves of modules over `𝒜^{0,0}` (softness of the two
Dolbeault sheaves is proved directly); a Dolbeault isomorphism `H^q(X, 𝒪) ≅ H^{0,q}_{∂̄}(X)` as a
statement about global forms; any statement in relative dimension `≥ 2` beyond softness. No new
`@[hodge_hypothesis]`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory Limits TopologicalSpace AlgebraicGeometry ComplexPoint Opposite
open scoped ContDiff Manifold
open HodgeLean.RealDefs HodgeLean.Adapters

universe u

namespace HodgeLean.Foundations

/-- **Flasque sheaves are soft.** A section over an open `U ⊇ K` is the restriction of a global
section, since `F(⊤) → F(U)` is onto; take `V = U`.
Source: Godement, *Topologie algébrique et théorie des faisceaux*, Hermann (1958), II.3.1
(un faisceau flasque est mou); Bredon, *Sheaf Theory*, 2nd ed., GTM 170 (1997), II.9.2. -/
theorem spec_isSoft_of_isFlasque {T : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} T)
    [F.IsFlasque] : IsSoft F :=
  spec_isSoft_of_isFlasque_aux F

/-- Injective sheaves are soft. -/
example {T : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} T) [Injective F] : IsSoft F :=
  haveI := TopCat.Sheaf.injective_isFlasque T F
  spec_isSoft_of_isFlasque F

/-- **The gluing step: lifts near two closed sets glue.** Let `0 → A → B → C → 0` be short exact
with `A` soft, on a normal space. If a section `c` of `C` lifts near the closed sets `K₁` and `K₂`,
by `b₁` and `b₂`, it lifts near `K₁ ∪ K₂`: `b₁ − b₂` comes from `A` on the overlap; by softness it
agrees near `K₁ ∩ K₂` with a global section `a` of `A`; then `b₁` and `b₂ + a` agree near `K₁ ∩ K₂`,
and separating the disjoint closed sets `K₁ ∖ W`, `K₂ ∖ W` shrinks the two domains until they meet
only where the lifts agree, so they glue.
Source: Godement, *Topologie algébrique et théorie des faisceaux*, proof of Théorème II.3.5.2;
Bredon, *Sheaf Theory*, 2nd ed., proof of Theorem II.9.9. -/
theorem spec_liftsNear_union {T : TopCat.{u}} [NormalSpace T]
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} T)} (hS : S.ShortExact)
    (hA : IsSoft S.X₁) {K₁ K₂ : Set T} (hK₁ : IsClosed K₁) (hK₂ : IsClosed K₂) {U : Opens T}
    (c : S.X₃.obj.obj (op U)) (h₁ : LiftsNear S.g K₁ c) (h₂ : LiftsNear S.g K₂ c) :
    LiftsNear S.g (K₁ ∪ K₂) c :=
  spec_liftsNear_union_aux hS hA hK₁ hK₂ c h₁ h₂

/-- Three closed sets, by applying the gluing step twice. -/
example {T : TopCat.{u}} [NormalSpace T]
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} T)} (hS : S.ShortExact)
    (hA : IsSoft S.X₁) {K₁ K₂ K₃ : Set T} (hK₁ : IsClosed K₁) (hK₂ : IsClosed K₂)
    (hK₃ : IsClosed K₃) {U : Opens T} (c : S.X₃.obj.obj (op U)) (h₁ : LiftsNear S.g K₁ c)
    (h₂ : LiftsNear S.g K₂ c) (h₃ : LiftsNear S.g K₃ c) :
    LiftsNear S.g (K₁ ∪ K₂ ∪ K₃) c :=
  spec_liftsNear_union hS hA (hK₁.union hK₂) hK₃ c (spec_liftsNear_union hS hA hK₁ hK₂ c h₁ h₂) h₃

/-- **Lifting near closed sets.** Let `0 → A → B → C → 0` be short exact with `A` soft, on a compact
Hausdorff space. Every section `c` of `C` over an open `U` lifts through `B → C` near every closed
`K ⊆ U`: `B → C` is locally surjective, so each point of `K` has a closed neighbourhood near which
`c` lifts; finitely many cover the compact `K`, and statement 2 glues them.
Source: Godement, *Topologie algébrique et théorie des faisceaux*, Théorème II.3.5.2 and its proof;
Bredon, *Sheaf Theory*, 2nd ed., Theorem II.9.9. -/
theorem spec_liftsNear_of_isClosed {T : TopCat.{u}} [CompactSpace T] [T2Space T]
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} T)} (hS : S.ShortExact)
    (hA : IsSoft S.X₁) {K : Set T} (hK : IsClosed K) {U : Opens T} (hKU : K ⊆ U)
    (c : S.X₃.obj.obj (op U)) :
    LiftsNear S.g K c :=
  spec_liftsNear_of_isClosed_aux hS hA hK hKU c

/-- In particular every section lifts near each of its points. -/
example {T : TopCat.{u}} [CompactSpace T] [T2Space T]
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} T)} (hS : S.ShortExact)
    (hA : IsSoft S.X₁) {U : Opens T} (c : S.X₃.obj.obj (op U)) (x : T) (hx : x ∈ U) :
    LiftsNear S.g {x} c :=
  spec_liftsNear_of_isClosed hS hA isClosed_singleton (Set.singleton_subset_iff.2 hx) c

/-- **Global sections are exact on the right when the kernel is soft.** For `0 → A → B → C → 0`
short exact with `A` soft, on a compact Hausdorff space, `Γ(B) → Γ(C)` is onto: statement 3 with
`K = T`.
Source: Godement, *Topologie algébrique et théorie des faisceaux*, Théorème II.3.5.2; Bredon,
*Sheaf Theory*, 2nd ed., Theorem II.9.9. -/
theorem spec_surjective_globalSections_of_isSoft {T : TopCat.{u}} [CompactSpace T]
    [T2Space T] {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} T)} (hS : S.ShortExact)
    (hA : IsSoft S.X₁) :
    Function.Surjective (S.g.hom.app (op ⊤)) :=
  spec_surjective_globalSections_of_isSoft_aux hS hA

/-- With a flasque kernel this is Mathlib's `IsFlasque.epi_of_shortExact` on `⊤`. -/
example {T : TopCat.{u}} [CompactSpace T] [T2Space T]
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} T)} (hS : S.ShortExact)
    [S.X₁.IsFlasque] :
    Function.Surjective (S.g.hom.app (op ⊤)) :=
  spec_surjective_globalSections_of_isSoft hS (spec_isSoft_of_isFlasque S.X₁)

/-- **Quotients of soft sheaves by soft sheaves are soft.** For `0 → A → B → C → 0` short exact with
`A` and `B` soft, on a compact Hausdorff space, `C` is soft: a section of `C` near a closed `K` lifts
to `B` near `K` (statement 3), extends from there to a global section of `B` (softness of `B`), and
its image is the required global section of `C`.
Source: Godement, *Topologie algébrique et théorie des faisceaux*, Théorème II.3.5.3; Bredon,
*Sheaf Theory*, 2nd ed., Theorem II.9.10. -/
theorem spec_isSoft_of_shortExact {T : TopCat.{u}} [CompactSpace T] [T2Space T]
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} T)} (hS : S.ShortExact)
    (h₁ : IsSoft S.X₁) (h₂ : IsSoft S.X₂) :
    IsSoft S.X₃ :=
  spec_isSoft_of_shortExact_aux hS h₁ h₂

/-- The cokernel of the injective hull of a soft sheaf is soft: the dimension shift used in
statement 6. -/
example {T : TopCat.{u}} [CompactSpace T] [T2Space T] (F : TopCat.Sheaf AddCommGrpCat.{u} T)
    (hF : IsSoft F) : IsSoft (cokernel (Injective.ι F)) := by
  let S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} T) :=
    ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
      (cokernel.condition (Injective.ι F))
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel (Injective.ι F) }
  have := TopCat.Sheaf.injective_isFlasque T (Injective.under F)
  exact spec_isSoft_of_shortExact hS hF (spec_isSoft_of_isFlasque (Injective.under F))

/-- **Soft sheaves are acyclic.** On a compact Hausdorff space a soft sheaf of abelian groups has
vanishing sheaf cohomology `Sheaf.H F (n + 1)` (Mathlib's `Ext` from the constant sheaf `ℤ`) in every
positive degree: embed `F` into an injective, hence flasque and soft, sheaf; the cokernel is soft
(statement 5) and `Γ` is onto (statement 4); shift dimension, as in the flasque case
`TopCat.Sheaf.IsFlasque.cohomology_succ_eq_zero`.
Source: Godement, *Topologie algébrique et théorie des faisceaux*, Théorème II.4.4.3; Bredon,
*Sheaf Theory*, 2nd ed., Theorem II.9.11. -/
theorem spec_subsingleton_cohomology_succ_of_isSoft {T : TopCat.{u}} [CompactSpace T]
    [T2Space T] (F : TopCat.Sheaf AddCommGrpCat.{u} T) (hF : IsSoft F) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H F (n + 1)) :=
  spec_subsingleton_cohomology_succ_of_isSoft_aux F hF n

/-- On a compact Hausdorff space this recovers the flasque case. -/
example {T : TopCat.{u}} [CompactSpace T] [T2Space T] (F : TopCat.Sheaf AddCommGrpCat.{u} T)
    [F.IsFlasque] (n : ℕ) : Subsingleton (CategoryTheory.Sheaf.H F (n + 1)) :=
  spec_subsingleton_cohomology_succ_of_isSoft F (spec_isSoft_of_isFlasque F) n

/-- **Hypercohomology of a single sheaf is sheaf cohomology.** For a sheaf `F` of abelian groups on
`X(ℂ)`, the repository's `ℍ^n(X; F[0]) = Hom_D(ℤ[0], F[n])` is in bijection with Mathlib's
`Sheaf.H F n = Ext^n(ℤ, F)`: both are shifted morphisms in the localization at quasi-isomorphisms,
and the integer constant sheaf complex is isomorphic to the constant sheaf `ULift ℤ` in degree `0`
(upstream `constantIntegerSheafComplexIntIsoSingleULift`), exactly as in upstream's
`hypercohomologyAddEquivConstantCohomology`, which is the case of a constant `F`.
Source: upstream `hypercohomologyAddEquivConstantCohomology`
(`Definitions/AlgebraicGeometry/Hodge/Filtration.lean`); Mathlib's
`Localization.SmallShiftedHom.precompEquiv` and `Localization.SmallShiftedHom.chgUniv`. -/
theorem spec_nonempty_hypercohomology_single_equiv (X : Over (Spec ↧ℂ))
    (F : AnalyticAdditiveSheaf X) (n : ℕ) :
    Nonempty (ℍ^(n : ℤ)(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj F) ≃ CategoryTheory.Sheaf.H F n) :=
  spec_nonempty_hypercohomology_single_equiv_aux X F n

/-- So vanishing can be read on either side. -/
example (X : Over (Spec ↧ℂ)) (F : AnalyticAdditiveSheaf X) (n : ℕ)
    [h : Subsingleton (CategoryTheory.Sheaf.H F n)] :
    Subsingleton ℍ^(n : ℤ)(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj F) :=
  (spec_nonempty_hypercohomology_single_equiv X F n).some.subsingleton

/-- **Soft sheaves on `X(ℂ)` have vanishing hypercohomology in positive degrees.** If `X(ℂ)` is
compact Hausdorff and `F` is soft, `ℍ^(n+1)(X; F[0]) = 0`: statements 6 and 7.
Source: Godement, *Topologie algébrique et théorie des faisceaux*, Théorème II.4.4.3; upstream
`hypercohomologyAddEquivConstantCohomology` for the comparison. -/
theorem spec_subsingleton_hypercohomology_succ_of_isSoft (X : Over (Spec ↧ℂ))
    [CompactSpace (ComplexPoint X)] [T2Space (ComplexPoint X)]
    (F : AnalyticAdditiveSheaf X) (hF : IsSoft F) (n : ℕ) :
    Subsingleton ℍ^((n + 1 : ℕ) : ℤ)(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj F) :=
  spec_subsingleton_hypercohomology_succ_of_isSoft_aux X F hF n

/-- The topological hypotheses hold for projective `X` (upstream's `CompactSpace` and `T2Space`). -/
example (X : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom]
    (F : AnalyticAdditiveSheaf X) (hF : IsSoft F) :
    Subsingleton ℍ^2(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj F) :=
  spec_subsingleton_hypercohomology_succ_of_isSoft X F hF 1

/-- **`𝒜^{0,0}` is soft.** On `X(ℂ)` Hausdorff and σ-compact (so paracompact and normal), let `f` be
smooth on an open `U ⊇ K`, `K` closed. Choose opens `K ⊆ V₁ ⊆ cl V₁ ⊆ V₂ ⊆ cl V₂ ⊆ U` and a smooth
`φ : X(ℂ) → ℝ` equal to `1` on `cl V₁` and to `0` off `V₂` (Mathlib's
`exists_contMDiff_zero_iff_one_iff_of_isClosed`); `φ f`, extended by zero, is a global smooth
function equal to `f` on `V₁`.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §3 (the sheaves `𝒜^{p,q}` are
fine); Godement, *Topologie algébrique et théorie des faisceaux*, II.3.7 (fine sheaves are soft);
Mathlib's `exists_contMDiff_zero_iff_one_iff_of_isClosed`. -/
theorem spec_isSoft_smoothFunctionSheaf (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] [T2Space (ComplexPoint X)]
    [SigmaCompactSpace (ComplexPoint X)] :
    IsSoft (smoothFunctionSheaf X d) :=
  spec_isSoft_smoothFunctionSheaf_aux X d

/-- For projective `X` (upstream's `T2Space` and `CompactSpace`). -/
example (X : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom] :
    IsSoft (smoothFunctionSheaf X 1) :=
  spec_isSoft_smoothFunctionSheaf X 1

/-- **`𝒜^{0,1}` is soft.** As for statement 9: for a smooth `(0,1)`-form `σ` near `K`, the form
`φ σ`, extended by zero, is a global smooth `(0,1)`-form (dolb2's `spec_isZeroOneFormAt_smul` on
`U`, and zero near every point outside `cl V₂`) equal to `σ` on `V₁`.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §3 (the sheaves `𝒜^{p,q}` are
fine); Godement, *Topologie algébrique et théorie des faisceaux*, II.3.7; dolb2's
`spec_isZeroOneFormAt_smul`. -/
theorem spec_isSoft_zeroOneFormSheaf (X : Over (Spec ↧ℂ)) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] [T2Space (ComplexPoint X)]
    [SigmaCompactSpace (ComplexPoint X)] :
    IsSoft (zeroOneFormSheaf X d) :=
  spec_isSoft_zeroOneFormSheaf_aux X d

/-- For projective `X`. -/
example (X : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom] :
    IsSoft (zeroOneFormSheaf X 1) :=
  spec_isSoft_zeroOneFormSheaf X 1

/-- **`H^{n+1}(X(ℂ), 𝒜^{0,0}) = 0` for projective `X`.** Statements 8 and 9, with upstream's
`CompactSpace` and `T2Space` for projective `X`.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §3 (fine sheaves are acyclic);
Godement, *Topologie algébrique et théorie des faisceaux*, Théorème II.4.4.3. -/
theorem spec_subsingleton_hypercohomology_succ_smoothFunctionSheaf (X : Over (Spec ↧ℂ))
    (d : ℕ) [SmoothOfRelativeDimension d X.hom] [IsProjective X.hom] (n : ℕ) :
    Subsingleton ℍ^((n + 1 : ℕ) : ℤ)(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj (smoothFunctionSheaf X d)) :=
  spec_subsingleton_hypercohomology_succ_smoothFunctionSheaf_aux X d n

/-- The binder `hA` of dolb2's assemblies, for an integral smooth projective `X`. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    Subsingleton ℍ^2(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj (smoothFunctionSheaf X (dim X.left))) :=
  spec_subsingleton_hypercohomology_succ_smoothFunctionSheaf X (dim X.left) 1

/-- **`H^{n+1}(X(ℂ), 𝒜^{0,1}) = 0` for projective `X`.** Statements 8 and 10.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §3 (fine sheaves are acyclic);
Godement, *Topologie algébrique et théorie des faisceaux*, Théorème II.4.4.3. -/
theorem spec_subsingleton_hypercohomology_succ_zeroOneFormSheaf (X : Over (Spec ↧ℂ))
    (d : ℕ) [SmoothOfRelativeDimension d X.hom] [IsProjective X.hom] (n : ℕ) :
    Subsingleton ℍ^((n + 1 : ℕ) : ℤ)(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj (zeroOneFormSheaf X d)) :=
  spec_subsingleton_hypercohomology_succ_zeroOneFormSheaf_aux X d n

/-- The binder `hB` of dolb2's assemblies, for an integral smooth projective `X`. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    Subsingleton ℍ^1(X; (HomologicalComplex.single (AnalyticAdditiveSheaf X)
      (ComplexShape.up ℤ) 0).obj (zeroOneFormSheaf X (dim X.left))) :=
  spec_subsingleton_hypercohomology_succ_zeroOneFormSheaf X (dim X.left) 0

/-- **`H^2(X(ℂ), 𝒪) = 0` for every integral smooth projective curve.** dolb2's
`spec_subsingleton_hypercohomology_two_of_acyclic` with `hA` and `hB` supplied by statements 11
and 12.
Source: Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §3 (Dolbeault's theorem) and
Ch. 2 §1 (on a compact Riemann surface `H^q(X, 𝒪) = 0` for `q ≥ 2`); Voisin, *Hodge Theory and
Complex Algebraic Geometry I*, §8.1.2. -/
theorem spec_subsingleton_hypercohomology_two_of_curve (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [SmoothOfRelativeDimension 1 X.hom]
    [IsProjective X.hom] :
    Subsingleton ℍ^2(X; holomorphicFormsShifted X 0) :=
  spec_subsingleton_hypercohomology_two_of_curve_aux X

/-- With the cch spec, `F^1 H_dR^2(X) = F^0 H_dR^2(X)` for every integral smooth projective curve. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom] :
    F^(0 + 1) H_dR^2(X) = F^0 H_dR^2(X) :=
  spec_hodgeFiltration_succ_eq_of_subsingleton X 0 2
    (spec_subsingleton_hypercohomology_two_of_curve X)

/-- **`CycleClassIsHodge` for every integral smooth projective curve.** dolb2's
`spec_cycleClassIsHodge_of_curve_of_acyclic` with `hA` and `hB` supplied by statements 11 and 12.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §§11.1.2–11.1.3 (cycle classes are
of type `(p, p)`); Griffiths–Harris, *Principles of Algebraic Geometry*, Ch. 0 §3. -/
theorem spec_cycleClassIsHodge_of_curve_of_projective (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [SmoothOfRelativeDimension 1 X.hom]
    [IsProjective X.hom] :
    CycleClassIsHodge X :=
  spec_cycleClassIsHodge_of_curve_of_projective_aux X

/-- The codimension-one part. -/
example (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [SmoothOfRelativeDimension 1 X.hom] [IsProjective X.hom] :
    algebraicCycleClassSpan X 1 ≤ Hdg^1(X; ℚ) :=
  (spec_cycleClassIsHodge_of_curve_of_projective X).le 1

end HodgeLean.Foundations
