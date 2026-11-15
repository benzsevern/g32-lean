import HodgeLean.RealDefs.Filtration
import HodgeLean.Blocks.HodgeStructure.DirectSum
import HodgeLean.Blocks.Weil.WeilClasses

/-! # The rational Hodge structure on `H^n(X(ℂ); ℚ)`

Roadmap `docs/roadmap/layer3.md` §3 C5. Over three hypotheses,

* `FiniteBetti` (C1): each `H^n(X(ℂ); ℚ)` is finite-dimensional;
* `BettiDeRhamIso` (C2): `ℂ ⊗[ℚ] H^n(X(ℂ); ℚ) → H_dR^n(X)` is bijective;
* `HodgeDecomposition` (C4): the pieces `hodgePiece X p q n`, `p + q = n`, form an internal
  direct sum of `H_dR^n(X)`;

`cohomologyHodgeStructure` is a Blocks `QHodgeStructure n (HQ X n)` whose `(p, q)` piece is the
pullback of upstream's `hodgePiece X p q n` when `p + q = n`, and `⊥` off that line. Its conjugation symmetry is C3/U2
(`deRhamConj_fieldToDeRhamCohomology`, through `bettiDeRhamHQ_sigmaQ`), with no further hypothesis.
`isHodgeClass_iff_mem_hodgeClasses` identifies its Hodge classes with upstream's `Hdg^p(X; ℚ)`.

The roadmap states C2 for `bettiDeRham`, whose domain is `ℂ ⊗[ℚ] H^n(X; ℚ)`. Here it is stated for
`bettiDeRhamHQ`, the same map on `ℂ ⊗[ℚ] HQ X n` (`bettiDeRhamHQ_tmul`), because the structures of
this repository are stated over `HQ X n` for the kernel-time reason recorded in `Operations`.
`bettiDeRhamHQ_eq` writes it as `bettiDeRham` after the base change of `HQ.linearEquiv`, so
`bijective_bettiDeRhamHQ_iff` turns a proof of C2 for `bettiDeRham` into `BettiDeRhamIso`. -/

open CategoryTheory AlgebraicGeometry ComplexPoint
open scoped TensorProduct

namespace HodgeLean.RealDefs

variable (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]

/-- Upstream's Betti-to-de Rham map `fieldToDeRhamCohomology ℚ X n`, on `HQ X n`. -/
noncomputable def fieldToDeRhamHQ (n : ℕ) : HQ X n →ₗ[ℚ] H_dR^(n : ℤ)(X) where
  toFun v := fieldToDeRhamCohomology ℚ X n v
  map_add' := (fieldToDeRhamCohomology ℚ X n).map_add
  map_smul' := fieldToDeRhamCohomology_smul ℚ X n

/-- The `ℂ`-linear extension `ℂ ⊗[ℚ] HQ X n → H_dR^n(X)`: `bettiDeRham` on `HQ X n`. -/
noncomputable def bettiDeRhamHQ (n : ℕ) : ℂ ⊗[ℚ] HQ X n →ₗ[ℂ] H_dR^(n : ℤ)(X) :=
  (fieldToDeRhamHQ X n).liftBaseChange ℂ

/-- `bettiDeRhamHQ` sends `z ⊗ v` to `z` times the de Rham image of `v`. -/
theorem bettiDeRhamHQ_tmul (n : ℕ) (z : ℂ) (v : HQ X n) :
    bettiDeRhamHQ X n (z ⊗ₜ v) = z • fieldToDeRhamCohomology ℚ X n v := by
  rw [bettiDeRhamHQ, LinearMap.liftBaseChange_tmul]
  rfl

/-- `HQ X n` is `H^n(X; ℚ)` as a `ℚ`-vector space: the identity, which is linear because the
instances on `HQ X n` are upstream's. -/
noncomputable def HQ.linearEquiv (n : ℕ) : HQ X n ≃ₗ[ℚ] H^n(X; ℚ) where
  toFun v := v
  invFun v := v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- `bettiDeRhamHQ` is `bettiDeRham` precomposed with the base change of `HQ.linearEquiv`. -/
theorem bettiDeRhamHQ_eq (n : ℕ) :
    bettiDeRhamHQ X n =
      bettiDeRham X n ∘ₗ LinearMap.baseChange ℂ (HQ.linearEquiv X n).toLinearMap := by
  refine TensorProduct.AlgebraTensorModule.ext fun z v => ?_
  rw [LinearMap.comp_apply, LinearMap.baseChange_tmul, bettiDeRham,
    LinearMap.liftBaseChange_tmul, bettiDeRhamHQ_tmul]
  rfl

/-- `bettiDeRhamHQ` is bijective exactly when `bettiDeRham` is, so C2 for `bettiDeRham`
discharges `BettiDeRhamIso`. -/
theorem bijective_bettiDeRhamHQ_iff (n : ℕ) :
    Function.Bijective (bettiDeRhamHQ X n) ↔ Function.Bijective (bettiDeRham X n) := by
  rw [bettiDeRhamHQ_eq, LinearMap.coe_comp]
  exact Function.Bijective.of_comp_iff _
    ((HQ.linearEquiv X n).baseChange ℚ ℂ (HQ X n) (H^n(X; ℚ))).bijective

/-- `bettiDeRhamHQ` intertwines rational conjugation `sigmaQ` with `deRhamConj` (C3/U2). -/
theorem bettiDeRhamHQ_sigmaQ (n : ℕ) (x : ℂ ⊗[ℚ] HQ X n) :
    bettiDeRhamHQ X n (HodgeBlocks.sigmaQ (HQ X n) x) = deRhamConj X n (bettiDeRhamHQ X n x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z v =>
    change bettiDeRhamHQ X n (HodgeBlocks.sigmaQR (HQ X n) (z ⊗ₜ v)) = _
    rw [HodgeBlocks.sigmaQ_tmul, bettiDeRhamHQ_tmul, bettiDeRhamHQ_tmul, deRhamConj_smul]
    exact congrArg _ (deRhamConj_fieldToDeRhamCohomology X n v).symm
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Membership in the conjugate filtration: `conj α ∈ F^q`. -/
theorem mem_conjHodgeFiltrationComplexSubmodule {q n : ℤ} (α : H_dR^n(X)) :
    α ∈ conjHodgeFiltrationComplexSubmodule X q n ↔ deRhamConj X n α ∈ F^q H_dR^n(X) :=
  Iff.rfl

/-- The candidate `(p, q)` piece of `ℂ ⊗[ℚ] H^n(X(ℂ); ℚ)`: the pullback of `hodgePiece X p q n`
along `bettiDeRhamHQ` when `p + q = n`, and `⊥` otherwise. -/
noncomputable def cohomologyHodgePiece (n : ℕ) (pq : ℤ × ℤ) :
    Submodule ℂ (ℂ ⊗[ℚ] HQ X n) :=
  if pq.1 + pq.2 = n then (hodgePiece X pq.1 pq.2 n).comap (bettiDeRhamHQ X n) else ⊥

/-- Rational conjugation swaps the candidate pieces `(p, q)` and `(q, p)`, with no hypothesis. -/
theorem cohomologyHodgePiece_map_sigmaQ (n : ℕ) (p q : ℤ) :
    (cohomologyHodgePiece X n (p, q)).map (HodgeBlocks.sigmaQ (HQ X n)) =
      cohomologyHodgePiece X n (q, p) := by
  unfold cohomologyHodgePiece
  by_cases h : p + q = n
  · have h' : q + p = n := by lia
    simp only [h, h', ↓reduceIte]
    ext y
    have key : y ∈ ((hodgePiece X p q n).comap (bettiDeRhamHQ X n)).map
        (HodgeBlocks.sigmaQ (HQ X n)) ↔
        HodgeBlocks.sigmaQ (HQ X n) y ∈ (hodgePiece X p q n).comap (bettiDeRhamHQ X n) :=
      ⟨by rintro ⟨x, hx, rfl⟩; simpa using hx, fun hy => ⟨_, hy, by simp⟩⟩
    rw [key]
    simp only [Submodule.mem_comap, hodgePiece, Submodule.mem_inf,
      mem_conjHodgeFiltrationComplexSubmodule, bettiDeRhamHQ_sigmaQ, deRhamConj_deRhamConj]
    exact and_comm
  · have h' : ¬ q + p = n := by lia
    simp only [h, h', ↓reduceIte, Submodule.map_bot]

/-- Upstream's `hodgePiece`s in degree `n`, extended by `⊥` off the line `p + q = n`. -/
noncomputable def deRhamHodgePiece (n : ℕ) (pq : ℤ × ℤ) : Submodule ℂ H_dR^(n : ℤ)(X) :=
  if pq.1 + pq.2 = n then hodgePiece X pq.1 pq.2 n else ⊥

/-- In degree `0`, the pieces `deRhamHodgePiece X 0` (upstream's `hodgePiece` on the line `p + q = 0`,
`⊥` off it) are `⊤` at `(0, 0)` and `⊥` elsewhere. Off the line upstream's raw intersection need
not be `⊥`: for `X = Spec ℂ`, `hodgePiece X (-1) 0 0 = ⊤`. -/
theorem deRhamHodgePiece_zero (pq : ℤ × ℤ) :
    deRhamHodgePiece X 0 pq = if pq = (0, 0) then ⊤ else ⊥ := by
  obtain ⟨p, q⟩ := pq
  unfold deRhamHodgePiece
  by_cases h : p + q = ((0 : ℕ) : ℤ)
  · by_cases hp : p = 0
    · have hq : q = 0 := by lia
      subst hp hq
      simp only [Nat.cast_zero, add_zero, ↓reduceIte, hodgePiece]
      refine eq_top_iff.mpr fun α _ => ⟨?_, ?_⟩
      · rw [hodgeFiltration_eq_top_of_nonpos X le_rfl]
        exact Submodule.mem_top
      · refine (mem_conjHodgeFiltrationComplexSubmodule X α).mpr ?_
        rw [hodgeFiltration_eq_top_of_nonpos X le_rfl]
        exact Submodule.mem_top
    · have hne : (p, q) ≠ ((0 : ℤ), (0 : ℤ)) := fun he => hp (Prod.mk.inj he).1
      simp only [h, hne, ↓reduceIte]
      exact hodgePiece_eq_bot_of_lt X (by lia)
  · have hne : (p, q) ≠ ((0 : ℤ), (0 : ℤ)) := fun he => by
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      exact h (by simp)
    simp only [h, hne, ↓reduceIte]

/-- In degree `0`, the pieces `deRhamHodgePiece X 0` (restricted to `p + q = 0`) form an internal direct sum, with no hypothesis: C4 holds in
degree `0` for every `X`.

Checks: F-1665 -/
theorem deRhamHodgePiece_isInternal_zero : DirectSum.IsInternal (deRhamHodgePiece X 0) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨fun i => ?_, ?_⟩
  · by_cases hi : i = (0, 0)
    · refine Disjoint.symm (disjoint_bot_left.mono_left (le_of_eq ?_))
      refine le_bot_iff.mp (iSup₂_le fun j hj => ?_)
      rw [deRhamHodgePiece_zero, ite_eq_right_of_eq_false _ _ (eq_false (hi ▸ hj))]
    · rw [deRhamHodgePiece_zero, ite_eq_right_of_eq_false _ _ (eq_false hi)]
      exact disjoint_bot_left
  · refine eq_top_iff.mpr (le_iSup_of_le (0, 0) ?_)
    rw [deRhamHodgePiece_zero, ite_eq_left_of_eq_true _ _ (eq_true rfl)]

/-- Finite Betti numbers: each `H^n(X(ℂ); ℚ)` is a finite-dimensional `ℚ`-vector space.

Source: Bott–Tu, *Differential Forms in Algebraic Topology*, GTM 82, §5 (a compact manifold has a finite good cover, and the Mayer–Vietoris argument over it gives finite-dimensional cohomology), with Bredon, *Sheaf Theory*, 2nd ed., GTM 170, Ch. III (sheaf cohomology with constant coefficients on a manifold is singular cohomology); sections only.

`X(ℂ)` is a compact manifold because `X` is smooth and projective. Bott–Tu run the Mayer–Vietoris
argument for de Rham cohomology; the same induction over a finite good cover applies to sheaf
cohomology with coefficients in the constant sheaf `ℚ`, since `ℚ` has no higher cohomology on a
contractible open set. No theorem numbers are pinned.

**Consistency.** For `X = Spec ℂ` (as `𝟙 : Spec ℂ ⟶ Spec ℂ`), `X(ℂ)` is one point, so
`H^0(X; ℚ) = ℚ` and `H^n = 0` for `n > 0`, because global sections are exact on a point; each is
finite-dimensional. This is not proved here for upstream's `Sheaf.H`. -/
@[hodge_hypothesis]
structure FiniteBetti [IsProjective X.hom] : Prop where
  finite : ∀ n : ℕ, Module.Finite ℚ (HQ X n)

/-- Betti–de Rham comparison: the `ℂ`-linear extension `ℂ ⊗[ℚ] H^n(X(ℂ); ℚ) → H_dR^n(X)` of
upstream's coefficient map is bijective.

Source: Hatcher, *Algebraic Topology*, §3.1 (the universal coefficient theorem for cohomology), with Bredon, *Sheaf Theory*, 2nd ed., GTM 170, Ch. III (sheaf cohomology with constant coefficients on a manifold is singular cohomology); sections only.

Upstream already proves the holomorphic Poincaré lemma (`complexConstantCohomologyDeRhamEquiv`), so
the content is the change of coefficients `ℂ ⊗[ℚ] H^n(X(ℂ); ℚ) ≅ H^n(X(ℂ); ℂ)`. For the compact
manifold `X(ℂ)` the integral homology is finitely generated, and the universal coefficient theorem
with `Ext(-, ℂ) = 0` gives the isomorphism. The structure also takes as given that the map is the
one induced by `ℚ → ℂ` on constant sheaves, which is how upstream defines it.

**Consistency.** For `X = Spec ℂ`, in degree `0` both sides are `ℂ` and `z ⊗ 1 ↦ z · 1`; in degree
`n > 0` both sides are `0`. This is expected, not proved here.

**Non-degeneracy.** At `n = 0`, the source contains `1 ⊗ [X]` with `[X] ≠ 0`
(`cycleComponentSheafClass_genericPoint_ne_zero`), and `ℂ ⊗[ℚ] -` is faithful over a field, so a
bijection forces `H_dR^0(X) ≠ 0`. -/
@[hodge_hypothesis]
structure BettiDeRhamIso [IsProjective X.hom] : Prop where
  bijective : ∀ n : ℕ, Function.Bijective (bettiDeRhamHQ X n)

/-- Hodge decomposition: in each degree `n`, the pieces `hodgePiece X p q n = F^p ∩ conj F^q`
with `p + q = n` form an internal direct sum of `H_dR^n(X)`.

Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, Cambridge Stud. Adv. Math. 76, Ch. 6 §6.1 (the Hodge decomposition of a compact Kähler manifold) and Ch. 8 (degeneration of the Frölicher spectral sequence); sections only.

A smooth projective `X` is Kähler. Upstream's `F^p` is the image of the hypercohomology of the
stupid truncation `σ_{≥p} Ω•`, which is the Hodge filtration on any complex manifold. Degeneration
at `E₁` makes `ℍ^n(σ_{≥p} Ω•) → H^n` injective, and the Kähler Hodge decomposition identifies
`H^{p,q}` with `F^p ∩ conj F^q` for `p + q = n`; upstream's `deRhamConj` is conjugation of
`ℂ`-coefficients. The structure takes these identifications as part of the hypothesis. No theorem numbers are pinned.

**Consistency.** In degree `0` the statement holds for every `X`, without hypothesis
(`deRhamHodgePiece_isInternal_zero`): `F^0 = ⊤`, so `hodgePiece X 0 0 0 = ⊤`, and every other
piece on the line `p + q = 0` has `p > 0` or `q > 0`, so it is `⊥` (`hodgePiece_eq_bot_of_lt`). For
`X = Spec ℂ` the higher degrees are expected to vanish, which makes the statement hold there. -/
@[hodge_hypothesis]
structure HodgeDecomposition [IsProjective X.hom] : Prop where
  isInternal : ∀ n : ℕ, DirectSum.IsInternal (deRhamHodgePiece X n)

variable {X} [IsProjective X.hom]

/-- Under C2, each candidate piece is the image of upstream's piece under the inverse of the
Betti–de Rham isomorphism. -/
theorem cohomologyHodgePiece_eq_map (hB : BettiDeRhamIso X) (n : ℕ) :
    cohomologyHodgePiece X n = fun pq => (deRhamHodgePiece X n pq).map
      (LinearEquiv.ofBijective (bettiDeRhamHQ X n) (hB.bijective n)).symm.toLinearMap := by
  funext pq
  unfold cohomologyHodgePiece deRhamHodgePiece
  split_ifs
  · exact Submodule.comap_equiv_eq_map_symm
      (LinearEquiv.ofBijective (bettiDeRhamHQ X n) (hB.bijective n)) _
  · exact (Submodule.map_bot _).symm

/-- The rational Hodge structure of weight `n` on `H^n(X(ℂ); ℚ)` (roadmap C5): its `(p, q)` piece
is the pullback of `hodgePiece X p q n` along the Betti–de Rham isomorphism when `p + q = n`, and `⊥`
otherwise.

Checks: F-1666 -/
noncomputable def cohomologyHodgeStructure (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (n : ℕ) :
    letI := hF.finite n
    HodgeBlocks.QHodgeStructure (n : ℤ) (HQ X n) :=
  letI := hF.finite n
  { H := cohomologyHodgePiece X n
    supported := fun pq h => by simp only [cohomologyHodgePiece, h, ↓reduceIte]
    isInternal := by
      rw [cohomologyHodgePiece_eq_map hB n]
      exact (hD.isInternal n).mapEquiv _
    conj_symm := cohomologyHodgePiece_map_sigmaQ X n }

/-- The `(p, q)` piece of `cohomologyHodgeStructure` is `cohomologyHodgePiece`. -/
theorem cohomologyHodgeStructure_H (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (n : ℕ) :
    letI := hF.finite n
    (cohomologyHodgeStructure hF hB hD n).H = cohomologyHodgePiece X n :=
  rfl

/-- Under C1, C2 and C4, a rational class `v ∈ H^(2p)(X(ℂ); ℚ)` is a Hodge class of
`cohomologyHodgeStructure` exactly when it lies in upstream's `Hdg^p(X; ℚ)`.

Checks: F-1666 -/
theorem isHodgeClass_iff_mem_hodgeClasses (hF : FiniteBetti X) (hB : BettiDeRhamIso X)
    (hD : HodgeDecomposition X) (p : ℕ) (v : HQ X (2 * p)) :
    letI := hF.finite (2 * p)
    HodgeBlocks.IsHodgeClass (p := (p : ℤ))
      (HodgeBlocks.WeilAction.weightCast (by push_cast; ring)
        (cohomologyHodgeStructure hF hB hD (2 * p))) v ↔
      (v : H^(2 * p)(X; ℚ)) ∈ Hdg^p(X; ℚ) := by
  let := hF.finite (2 * p)
  have h : ((p : ℤ), (p : ℤ)).1 + ((p : ℤ), (p : ℤ)).2 = ((2 * p : ℕ) : ℤ) := by push_cast; ring
  rw [HodgeBlocks.IsHodgeClass, HodgeBlocks.WeilAction.weightCast_H, cohomologyHodgeStructure_H,
    cohomologyHodgePiece, ite_eq_left_of_eq_true _ _ (eq_true h), Submodule.mem_comap,
    HodgeBlocks.complexify_apply, bettiDeRhamHQ_tmul, one_smul]
  rfl

end HodgeLean.RealDefs
