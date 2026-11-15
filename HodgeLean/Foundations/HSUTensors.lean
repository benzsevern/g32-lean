import HodgeLean.Foundations.HSUTensorsProofs

/-!
# Bounded mixed tensors and the 12-dimensional `hSU` candidate (FROZEN SPEC)

Stage 2 of the `hSU` lane. It claims: the stabilizer `mixedTensorStabilizer` of a finite list
of rational mixed tensors `T^{a,b}(V) = V^{⊗a} ⊗ (V^∨)^{⊗b}` of possibly different types agrees
with `HSUFinite`'s `finiteTensorStabilizer` (one type, a direct sum, and vectors); the
complexified action is by derivations; the Hodge Lie algebra fixes any such list of Hodge
tensors, and the implication from a computed stabilizer plus explicit generators to equality
holds for mixed lists. For the explicit 12-dimensional block model of the F-1569 datum
`⟨1, 1, 1, -1, -1, -2⟩` over `ℚ(√-3)`, it states the defining identities of `J` and `E`, the
dimension `35` of `complexSU`, and two falsification checks: the polarization alone has
stabilizer `sp₁₂` (dimension `78`), and `J` with `E` has stabilizer `gl₆` (dimension `36`), both
strictly larger than `complexSU`.

It does not claim: that any list of Hodge tensors of the candidate has stabilizer
`complexSU` (stage 3); any Hodge decomposition or period point for the candidate; genericity in
the F-1575 family; realization by an abelian variety; any geometric cohomology or algebraicity.
HC no distance; AV milestone no distance.
-/

noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] HodgeLean.Foundations.SchurWeyl.dualAddCommGroup

namespace HodgeLean.Foundations

open WeilPower SchurWeyl
open scoped TensorProduct

section Mixed

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- On a list of tensors of one type `(a, b)`, the mixed stabilizer is `HSUFinite`'s
`finiteTensorStabilizer` for the Lie module `T^{a,b}(V)`.
Source: the definitions `mixedTensorStabilizer` and `finiteTensorStabilizer`; Deligne,
*Hodge cycles on abelian varieties*, LNM 900 (1982), §2. -/
theorem spec_mixedTensorStabilizer_const {a b n : ℕ}
    (t : Fin n → MixedTensorOfType V (a, b)) :
    mixedTensorStabilizer (fun i => (⟨(a, b), t i⟩ : BoundedTensor V)) =
      finiteTensorStabilizer t :=
  spec_mixedTensorStabilizer_const_aux t

example {a b n : ℕ}
    (t : Fin n → MixedTensorOfType V (a, b)) :
    mixedTensorStabilizer (fun i => (⟨(a, b), t i⟩ : BoundedTensor V)) =
      finiteTensorStabilizer t :=
  spec_mixedTensorStabilizer_const t

/-- A mixed list has the stabilizer of the single family `ι_i (t_i)` in the direct sum
`⨁ᵢ T^{aᵢ,bᵢ}(V)`, so `HSUFinite`'s `finiteTensorStabilizer` computes it.
Source: Bourbaki, *Groupes et algèbres de Lie*, ch. I, §3 (direct sums of Lie modules; the
inclusions `ι_i` are injective and equivariant). -/
theorem spec_mixedTensorStabilizer_eq_directSum {n : ℕ} (t : Fin n → BoundedTensor V) :
    mixedTensorStabilizer t =
      finiteTensorStabilizer (N := DirectSum (Fin n) fun i => MixedTensorOfType V (t i).1)
        (fun i => DirectSum.of (fun i => MixedTensorOfType V (t i).1) i (t i).2) :=
  spec_mixedTensorStabilizer_eq_directSum_aux t

example {n : ℕ} (t : Fin n → BoundedTensor V) :
    mixedTensorStabilizer t =
      finiteTensorStabilizer (N := DirectSum (Fin n) fun i => MixedTensorOfType V (t i).1)
        (fun i => DirectSum.of (fun i => MixedTensorOfType V (t i).1) i (t i).2) :=
  spec_mixedTensorStabilizer_eq_directSum t

/-- On vectors, `HSUFinite`'s stabilizer for the Lie module `V` agrees with the mixed
stabilizer of the same vectors as type `(1, 0)` tensors.
Source: the equivariant isomorphism `V ≅ V^{⊗1} ⊗ (V^∨)^{⊗0}`, Goodman–Wallach, *Symmetry,
Representations, and Invariants*, GTM 255, Ch. 5. -/
theorem spec_finiteTensorStabilizer_vec {n : ℕ} (t : Fin n → V) :
    finiteTensorStabilizer (N := V) t =
      mixedTensorStabilizer (fun i => (⟨(1, 0), vecTensor (t i)⟩ : BoundedTensor V)) :=
  spec_finiteTensorStabilizer_vec_aux t

example {n : ℕ} (t : Fin n → V) :
    finiteTensorStabilizer (N := V) t =
      mixedTensorStabilizer (fun i => (⟨(1, 0), vecTensor (t i)⟩ : BoundedTensor V)) :=
  spec_finiteTensorStabilizer_vec t

/-- The complexified action of `End_ℂ (ℂ ⊗ V)` on `ℂ ⊗ T^{a,b}(V)` is a morphism of Lie
algebras (it acts by derivations).
Source: Bourbaki, *Groupes et algèbres de Lie*, ch. I, §1 (extension of scalars of a Lie
algebra representation); `SchurWeyl.mixedLie` for the rational action. -/
theorem spec_complexAction_mixed_lie [FiniteDimensional ℚ V] (ab : ℕ × ℕ)
    (X Y : Module.End ℂ (ℂ ⊗[ℚ] V)) :
    complexAction (MixedTensorOfType V ab) (X * Y - Y * X) =
      complexAction (MixedTensorOfType V ab) X * complexAction (MixedTensorOfType V ab) Y -
        complexAction (MixedTensorOfType V ab) Y * complexAction (MixedTensorOfType V ab) X :=
  spec_complexAction_mixed_lie_aux ab X Y

example [FiniteDimensional ℚ V] (ab : ℕ × ℕ)
    (X Y : Module.End ℂ (ℂ ⊗[ℚ] V)) :
    complexAction (MixedTensorOfType V ab) (X * Y - Y * X) =
      complexAction (MixedTensorOfType V ab) X * complexAction (MixedTensorOfType V ab) Y -
        complexAction (MixedTensorOfType V ab) Y * complexAction (MixedTensorOfType V ab) X :=
  spec_complexAction_mixed_lie ab X Y

variable [FiniteDimensional ℚ V]
  {H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)} {hH : DirectSum.IsInternal H}

/-- Every finite list of rational Hodge tensors of mixed types is fixed by the Hodge Lie
algebra.
Source: Deligne, *Hodge cycles on abelian varieties*, LNM 900 (1982), §2; Moonen,
*An introduction to Mumford–Tate groups* (2004), §2. -/
theorem spec_hodgeLieAlgebra_le_mixedTensorStabilizer {n : ℕ}
    (t : Fin n → BoundedTensor V)
    (ht : ∀ i, (t i).2 ∈
      LieModule.maxTrivSubmodule ℚ (hodgeLieAlgebra H hH) (MixedTensorOfType V (t i).1)) :
    complexSpan (hodgeLieAlgebra H hH).toSubmodule ≤ mixedTensorStabilizer t :=
  spec_hodgeLieAlgebra_le_mixedTensorStabilizer_aux t ht

example {n : ℕ}
    (t : Fin n → BoundedTensor V)
    (ht : ∀ i, (t i).2 ∈
      LieModule.maxTrivSubmodule ℚ (hodgeLieAlgebra H hH) (MixedTensorOfType V (t i).1)) :
    complexSpan (hodgeLieAlgebra H hH).toSubmodule ≤ mixedTensorStabilizer t :=
  spec_hodgeLieAlgebra_le_mixedTensorStabilizer t ht

/-- If the stabilizer of an explicit mixed list of Hodge tensors is `L`, and explicit elements
of the Hodge Lie algebra span `L`, then the complexified Hodge Lie algebra is `L`.
Source: Bourbaki, *Groupes et algèbres de Lie*, ch. I, §2; van Geemen, *An introduction to the
Hodge conjecture for abelian varieties*, §5. -/
theorem spec_hSU_of_mixedTensorStabilizer_and_generators {n m : ℕ}
    (t : Fin n → BoundedTensor V)
    (L : LieSubalgebra ℂ (Module.End ℂ (ℂ ⊗[ℚ] V)))
    (g : Fin m → Module.End ℂ (ℂ ⊗[ℚ] V))
    (ht : ∀ i, (t i).2 ∈
      LieModule.maxTrivSubmodule ℚ (hodgeLieAlgebra H hH) (MixedTensorOfType V (t i).1))
    (hstabilizer : mixedTensorStabilizer t = L.toSubmodule)
    (hgenerate : L.toSubmodule ≤ Submodule.span ℂ (Set.range g))
    (hg : ∀ i, g i ∈ complexSpan (hodgeLieAlgebra H hH).toSubmodule) :
    complexSpan (hodgeLieAlgebra H hH).toSubmodule = L.toSubmodule :=
  spec_hSU_of_mixedTensorStabilizer_and_generators_aux t L g ht hstabilizer hgenerate hg

example {n m : ℕ}
    (t : Fin n → BoundedTensor V)
    (L : LieSubalgebra ℂ (Module.End ℂ (ℂ ⊗[ℚ] V)))
    (g : Fin m → Module.End ℂ (ℂ ⊗[ℚ] V))
    (ht : ∀ i, (t i).2 ∈
      LieModule.maxTrivSubmodule ℚ (hodgeLieAlgebra H hH) (MixedTensorOfType V (t i).1))
    (hstabilizer : mixedTensorStabilizer t = L.toSubmodule)
    (hgenerate : L.toSubmodule ≤ Submodule.span ℂ (Set.range g))
    (hg : ∀ i, g i ∈ complexSpan (hodgeLieAlgebra H hH).toSubmodule) :
    complexSpan (hodgeLieAlgebra H hH).toSubmodule = L.toSubmodule :=
  spec_hSU_of_mixedTensorStabilizer_and_generators t L g ht hstabilizer hgenerate hg

end Mixed

section Candidate

/-- The candidate Weil operator satisfies `J² = -3`.
Source: van Geemen, *An introduction to the Hodge conjecture for abelian varieties*, §5 (a Weil
operator for `ℚ(√-3)`); checked blockwise as for `WeilHermitian.exJ₄`. -/
theorem spec_hsuJ_sq : hsuJ.comp hsuJ = (-3 : ℚ) • LinearMap.id :=
  spec_hsuJ_sq_aux

example : hsuJ.comp hsuJ = (-3 : ℚ) • LinearMap.id :=
  spec_hsuJ_sq

/-- The candidate polarization is alternating.
Source: van Geemen, *An introduction to the Hodge conjecture for abelian varieties*, §5. -/
theorem spec_hsuE_isAlt : hsuE.IsAlt :=
  spec_hsuE_isAlt_aux

example : hsuE.IsAlt :=
  spec_hsuE_isAlt

/-- The candidate Weil operator is skew for the polarization: `E(Jx, y) = -E(x, Jy)`.
Source: van Geemen, *An introduction to the Hodge conjecture for abelian varieties*, §5;
`WeilHermitian.isSkew_iff`. -/
theorem spec_hsuE_skew : ∀ x y, hsuE (hsuJ x) y = -hsuE x (hsuJ y) :=
  spec_hsuE_skew_aux

example : ∀ x y, hsuE (hsuJ x) y = -hsuE x (hsuJ y) :=
  spec_hsuE_skew

/-- The Rosati form of the compatibility: `E(Jx, Jy) = 3 E(x, y)`.
Source: `WeilHermitian.isSkew_iff` (with `d = 3`); van Geemen, §5. -/
theorem spec_hsuE_rosati : ∀ x y, hsuE (hsuJ x) (hsuJ y) = 3 * hsuE x y :=
  spec_hsuE_rosati_aux

example : ∀ x y, hsuE (hsuJ x) (hsuJ y) = 3 * hsuE x y :=
  spec_hsuE_rosati

/-- The candidate polarization is nondegenerate.
Source: its Gram determinant is `∏ₖ hsuWeights k ^ 2 = 4 ≠ 0`; Bourbaki, *Algèbre*, ch. IX. -/
theorem spec_hsuE_nondegenerate : hsuE.Nondegenerate :=
  spec_hsuE_nondegenerate_aux

example : hsuE.Nondegenerate :=
  spec_hsuE_nondegenerate

/-- In the `ℚ(√-3)`-basis `e₀, e₂, …, e₁₀`, the Hermitian form `h(x, y) = E(x, Jy) + √-3 E(x, y)`
of the candidate is the F-1569 diagonal form `⟨1, 1, 1, -1, -1, -2⟩`.
Source: `WeilHermitian.weilHermitian`; `HermitianForm.hermSignature_diag_F1569`. -/
theorem spec_hsuE_hermitian_diag (k l : Fin 6) :
    hsuE (Pi.single ⟨2 * k.val, by omega⟩ 1) (hsuJ (Pi.single ⟨2 * l.val, by omega⟩ 1)) =
        (if k = l then hsuWeights k else 0) ∧
      hsuE (Pi.single ⟨2 * k.val, by omega⟩ 1) (Pi.single ⟨2 * l.val, by omega⟩ 1) = 0 :=
  spec_hsuE_hermitian_diag_aux k l

example (k l : Fin 6) :
    hsuE (Pi.single ⟨2 * k.val, by omega⟩ 1) (hsuJ (Pi.single ⟨2 * l.val, by omega⟩ 1)) =
        (if k = l then hsuWeights k else 0) ∧
      hsuE (Pi.single ⟨2 * k.val, by omega⟩ 1) (Pi.single ⟨2 * l.val, by omega⟩ 1) = 0 :=
  spec_hsuE_hermitian_diag k l

/-- The complex special unitary Lie algebra of the candidate has dimension `35 = 6² - 1`.
Source: `WeilPower.complexSUEquiv` (it is `sl(W)` for the 6-dimensional eigenspace `W`);
Bourbaki, *Groupes et algèbres de Lie*, ch. I, §6. -/
theorem spec_finrank_hsu_complexSU :
    Module.finrank ℂ (complexSU hsuE spec_hsuE_nondegenerate hsuJ spec_hsuJ_sq
      spec_hsuE_skew).toSubmodule = 35 :=
  spec_finrank_hsu_complexSU_aux

example :
    Module.finrank ℂ (complexSU hsuE spec_hsuE_nondegenerate hsuJ spec_hsuJ_sq
      spec_hsuE_skew).toSubmodule = 35 :=
  spec_finrank_hsu_complexSU

/-- The stabilizer of the Weil operator and the polarization has dimension `36`: it is the
complexified unitary Lie algebra `gl₆`, one dimension more than `complexSU`.
Source: Moonen, *An introduction to Mumford–Tate groups* (2004), §2; van Geemen, §5–6 (the
unitary group of a Hermitian space and its special part). -/
theorem spec_finrank_hsuWeilPair :
    Module.finrank ℂ (mixedTensorStabilizer hsuWeilPair) = 36 :=
  spec_finrank_hsuWeilPair_aux

example :
    Module.finrank ℂ (mixedTensorStabilizer hsuWeilPair) = 36 :=
  spec_finrank_hsuWeilPair

/-- Falsification check: `complexSU` is strictly contained in the stabilizer of `J` and `E`;
these two tensors alone do not cut out `complexSU`.
Source: van Geemen, *An introduction to the Hodge conjecture for abelian varieties*, §6 (the
Weil classes cut the unitary group down to the special unitary group). -/
theorem spec_hsu_complexSU_lt_weilPair :
    (complexSU hsuE spec_hsuE_nondegenerate hsuJ spec_hsuJ_sq
      spec_hsuE_skew).toSubmodule < mixedTensorStabilizer hsuWeilPair :=
  spec_hsu_complexSU_lt_weilPair_aux

example :
    (complexSU hsuE spec_hsuE_nondegenerate hsuJ spec_hsuJ_sq
      spec_hsuE_skew).toSubmodule < mixedTensorStabilizer hsuWeilPair :=
  spec_hsu_complexSU_lt_weilPair

/-- The stabilizer of the polarization alone is the symplectic Lie algebra `sp₁₂`, of
dimension `78 = 6 · 13`.
Source: Bourbaki, *Groupes et algèbres de Lie*, ch. VIII, §13 (type `C₆`). -/
theorem spec_finrank_hsuPolarizationOnly :
    Module.finrank ℂ (mixedTensorStabilizer hsuPolarizationOnly) = 78 :=
  spec_finrank_hsuPolarizationOnly_aux

example :
    Module.finrank ℂ (mixedTensorStabilizer hsuPolarizationOnly) = 78 :=
  spec_finrank_hsuPolarizationOnly

/-- Falsification check: `complexSU` is strictly contained in the stabilizer of the polarization
alone, so equality with `complexSU` fails for that list.
Source: Bourbaki, *Groupes et algèbres de Lie*, ch. VIII, §13; van Geemen, §5. -/
theorem spec_hsu_complexSU_lt_polarizationOnly :
    (complexSU hsuE spec_hsuE_nondegenerate hsuJ spec_hsuJ_sq
      spec_hsuE_skew).toSubmodule < mixedTensorStabilizer hsuPolarizationOnly :=
  spec_hsu_complexSU_lt_polarizationOnly_aux

example :
    (complexSU hsuE spec_hsuE_nondegenerate hsuJ spec_hsuJ_sq
      spec_hsuE_skew).toSubmodule < mixedTensorStabilizer hsuPolarizationOnly :=
  spec_hsu_complexSU_lt_polarizationOnly

end Candidate

end HodgeLean.Foundations
