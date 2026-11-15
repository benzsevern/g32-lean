import HodgeLean.Adapters.AbelianPowerHodgeProofs

/-! # Powers, from the exterior model to `HQ(Y)`, stage G2 of the Powers flagship (FROZEN)

Stage G2 of the Powers flagship plan (`docs/roadmap/pw-flagship-plan.md`, §4.2, row G2), towards
PW v0.3, Theorem 4.2 (`thm:gen`). For abelian `A` and `Y` (group objects over `ℂ` that are
integral, smooth and projective, `Y` commutative) with power data `P : AbelianPowerData A Y r`
(stage G4: homomorphisms `p_i : Y ⟶ A`, `s_i : A ⟶ Y` with the biproduct identities), and the
maps `Φ = P.h1Map : HQ A 1 ⊗ ℚ^r → HQ Y 1`, `P.h1Inv` and `P.cohomologyMap k = cupWedgeEquiv k ∘
⋀^k Φ` of `AbelianPowerHodgeDefs`.

Claimed:
* **degree one:** `Φ` and `P.h1Inv` are inverse to each other, and `dim Y = r · dim A`;
* **Hodge compatibility:** `Φ_ℂ` carries the piece `H^{p,q}(A) ⊗ ℂ^r` onto
  `cohomologyHodgePiece Y 1 (p, q)`, for every `(p, q)`;
* **all degrees:** `P.cohomologyMap k` is bijective and carries the exterior Hodge piece
  `exteriorHodge (cohomologyHodgePiece A 1) r k (p, q)` onto `cohomologyHodgePiece Y k (p, q)`;
  so a class `v ∈ ⋀^{2p} (HQ A 1 ⊗ ℚ^r)` lies in `rationalExteriorHodge` of the weight-one
  structure of `A` exactly when `P.cohomologyMap (2p) v ∈ Hdg^p(Y; ℚ)`, and the image of the
  former is the latter;
* **pullback of `f_a`:** for `a ∈ 𝒪^r`, `f_a^* = Φ ∘ pwPowerPullback A θ a` on `HQ · 1`, and in
  degree `k` `f_a^* ∘ cupWedgeEquiv_A k = P.cohomologyMap k ∘ ⋀^k (pwPowerPullback A θ a)`;
* **`r = 1`:** for `AbelianPowerData.one A`, `Φ` is the canonical `powerOneFlatten A`;
* **degenerate checks:** in degree `k = 0`, `P.cohomologyMap 0` sends `1` to the unit class;
  `Hdg^p(Y; ℚ) = 0` for `p > r · dim A` (at `r = 0`, for every `p > 0`); and a constant map to a
  point other than the identity is not a homomorphism, so it is never a projection of power data.

Every hypothesis on `A` and `Y` is a Mathlib instance; `FiniteBetti`, `HodgeDecomposition`,
`CupFiltered` and the torus theorem enter only through theorems already proved for abelian
varieties (`finiteBetti_abelian`, `hodgeDecomposition_of_abelian`,
`cupFiltered_cupProductOf_of_abelian`, `torusCohomology_cupProductOf`). The weight-one structure
is `abelianWeightOneHodgeStructure A`; its pieces are definitionally those of the package
`abelianVarietyCohomologyOf … (torusCohomology_cupProductOf A)` (see the `example` after
`spec_g2_rationalExteriorHodge_map_eq`).

Not claimed: that a power `A^r` exists as a scheme (power data is a binder); any statement about
generation of `Hdg^p(Y; ℚ)` (that is F1, from PW-0's model statement transported here); any
algebraicity; a pullback formula for `f_a` with `a ∈ L^r ∖ 𝒪^r` (no morphism exists there).
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower

namespace HodgeLean.Adapters

section Power

variable {A Y : Over (Spec ↧ℂ)} [GrpObj A] [IsIntegral A.left] [Smooth A.hom]
  [IsProjective A.hom] [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom]
  [IsProjective Y.hom] {r : ℕ}

/-- **`s^* ∘ Φ = id`.** On `x ⊗ c`, `Σ_j s_j^* (Σ_i c_i p_i^* x) ⊗ e_j = Σ_{i,j} c_i (s_j ≫ p_i)^* x
⊗ e_j`, and `s_j ≫ p_i` is `𝟙 A` for `i = j` and the constant map `1` otherwise, which pulls back
to `0` on `HQ · 1`.
Source: Mac Lane, *Categories for the Working Mathematician*, §VIII.2 (biproducts);
`AbelianPowerData.incl_proj`, `spec_homPullback_comp`, `spec_homPullback_id`,
`spec_homPullback_one`. -/
theorem spec_g2_h1Inv_comp_h1Map (P : AbelianPowerData A Y r) :
    P.h1Inv ∘ₗ P.h1Map = LinearMap.id :=
  spec_g2_h1Inv_comp_h1Map_aux P

example (P : AbelianPowerData A Y r) : Function.Injective P.h1Map :=
  Function.LeftInverse.injective (g := P.h1Inv) fun x => by
    rw [← LinearMap.comp_apply, spec_g2_h1Inv_comp_h1Map, LinearMap.id_apply]

/-- **`Φ ∘ s^* = id`.** `Σ_i p_i^* s_i^* = Σ_i (p_i ≫ s_i)^*`, which is the pullback of the
product `Π_i (p_i ≫ s_i) = 𝟙 Y` by additivity on `HQ · 1` (the empty product is `1`, pulling
back to `0`); and `(𝟙 Y)^* = id`.
Source: Mac Lane, *Categories for the Working Mathematician*, §VIII.2;
`AbelianPowerData.sum_proj_incl`, `spec_homPullback_mul`, `spec_homPullback_one`,
`spec_homPullback_comp`, `spec_homPullback_id`. -/
theorem spec_g2_h1Map_comp_h1Inv (P : AbelianPowerData A Y r) :
    P.h1Map ∘ₗ P.h1Inv = LinearMap.id :=
  spec_g2_h1Map_comp_h1Inv_aux P

/-- So `Φ` is a linear equivalence. -/
example (P : AbelianPowerData A Y r) : HQ A 1 ⊗[ℚ] (Fin r → ℚ) ≃ₗ[ℚ] HQ Y 1 :=
  LinearEquiv.ofLinearMap P.h1Map P.h1Inv (spec_g2_h1Map_comp_h1Inv P) (spec_g2_h1Inv_comp_h1Map P)

/-- **`dim Y = r · dim A`.** `Φ` is an isomorphism, so `2 · dim Y = rank HQ Y 1 =
r · rank HQ A 1 = r · 2 · dim A` (the torus theorem gives `rank HQ · 1 = 2 · dim`).
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 (`H¹` of a `g`-dimensional
complex torus has rank `2g`); `spec_g2_h1Inv_comp_h1Map`, `spec_g2_h1Map_comp_h1Inv`,
`TorusCohomology.finrank_eq`. -/
theorem spec_g2_dim_eq (P : AbelianPowerData A Y r) : dim Y.left = r * dim A.left :=
  spec_g2_dim_eq_aux P

/-- At `r = 0`, `Y` is zero-dimensional, matching G4's `spec_g4_eq_zero_of_powerData_zero`. -/
example (P : AbelianPowerData A Y 0) : dim Y.left = 0 := by
  rw [spec_g2_dim_eq P, zero_mul]

/-- **`Φ` is Hodge-compatible in weight one.** `Φ_ℂ` carries `H^{p,q}(A) ⊗ ℂ^r` onto
`cohomologyHodgePiece Y 1 (p, q)`, for every `(p, q)`. Each `p_i` is a homomorphism, so `p_i^*`
maps the pieces of `A` into those of `Y` (≤); each `s_i` is a homomorphism, so `Φ⁻¹_ℂ y =
Σ_i s_i^* y ⊗ e_i` lies in `H^{p,q}(A) ⊗ ℂ^r` for `y` of type `(p, q)` (≥).
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.2 and Theorem 1.4.1;
`spec_homPullback_hodgePiece_one` (stage G1b), `spec_g2_h1Map_comp_h1Inv`. -/
theorem spec_g2_h1Map_hodgePiece (P : AbelianPowerData A Y r) (pq : ℤ × ℤ) :
    (powerWeightOnePiece (cohomologyHodgePiece A 1) r pq).map (P.h1Map.baseChange ℂ) =
      cohomologyHodgePiece Y 1 pq :=
  spec_g2_h1Map_hodgePiece_aux P pq

/-- Off the line `p + q = 1` both sides are `0`. -/
example (P : AbelianPowerData A Y r) :
    (powerWeightOnePiece (cohomologyHodgePiece A 1) r (1, 1)).map (P.h1Map.baseChange ℂ) = ⊥ := by
  rw [spec_g2_h1Map_hodgePiece]
  simp [cohomologyHodgePiece]

/-- **The model map is bijective in every degree**: `⋀^k Φ` is an isomorphism with inverse
`⋀^k (P.h1Inv)`, and `cupWedgeEquiv k` is one.
Source: `spec_g2_h1Inv_comp_h1Map`, `spec_g2_h1Map_comp_h1Inv`; Mathlib `exteriorPower.map_comp`;
`TorusCohomology.cupWedgeEquiv`. -/
theorem spec_g2_cohomologyMap_bijective (P : AbelianPowerData A Y r) (k : ℕ) :
    Function.Bijective (P.cohomologyMap k) :=
  spec_g2_cohomologyMap_bijective_aux P k

/-- **The model map is Hodge-compatible in every degree.** The complexification of
`P.cohomologyMap k`, read through `exteriorBaseChange k`, carries the exterior Hodge piece
`exteriorHodge (cohomologyHodgePiece A 1) r k (p, q)` onto `cohomologyHodgePiece Y k (p, q)`.
`⋀^k Φ_ℂ` carries wedges of vectors of `H^{p_i,q_i}(A) ⊗ ℂ^r` to wedges of vectors of
`H^{p_i,q_i}(Y)` (`spec_g2_h1Map_hodgePiece`), whose cup products span the `(p, q)` piece of
`HQ Y k` (`CupFiltered Y` and `HodgeDecomposition Y`, both theorems for abelian `Y`).
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 1.3.1 and Theorem 1.4.1;
`spec_g2_h1Map_hodgePiece`, `comap_cohomologyHodgePiece_eq_exteriorPowerH`,
`cupFiltered_cupProductOf_of_abelian`, `hodgeDecomposition_of_abelian`. -/
theorem spec_g2_cohomologyMap_hodgePiece (P : AbelianPowerData A Y r) (k : ℕ) (pq : ℤ × ℤ) :
    letI := (finiteBetti_abelian A).finite 1
    (exteriorHodge (cohomologyHodgePiece A 1) r k pq).map
        ((P.cohomologyMap k).baseChange ℂ ∘ₗ (exteriorBaseChange k).symm.toLinearMap) =
      cohomologyHodgePiece Y k pq :=
  spec_g2_cohomologyMap_hodgePiece_aux P k pq

/-- **Rational Hodge classes, pointwise.** A class `v ∈ ⋀^{2p} (HQ A 1 ⊗ ℚ^r)` is a rational
exterior Hodge class of the weight-one structure of `A` exactly when its image in `HQ Y (2p)` is
a Hodge class of `Y`. Both are "the complexification lies in the `(p, p)` piece"
(`mem_rationalExteriorHodge_iff`, `mem_hodgeClasses_iff_tmul_mem`), and the pieces correspond by
`spec_g2_cohomologyMap_hodgePiece`, with `P.cohomologyMap` injective.
Source: van Geemen, *An introduction to the Hodge conjecture for abelian varieties*, §5–6;
`spec_g2_cohomologyMap_hodgePiece`, `spec_g2_cohomologyMap_bijective`,
`isHodgeClass_exteriorPower_add_iff`. -/
theorem spec_g2_mem_rationalExteriorHodge_iff (P : AbelianPowerData A Y r) (p : ℕ)
    (v : ⋀[ℚ]^(2 * p) (HQ A 1 ⊗[ℚ] (Fin r → ℚ))) :
    letI := (finiteBetti_abelian A).finite 1
    v ∈ rationalExteriorHodge (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal r (2 * p) ↔
      (P.cohomologyMap (2 * p) v : H^(2 * p)(Y; ℚ)) ∈ Hdg^p(Y; ℚ) :=
  spec_g2_mem_rationalExteriorHodge_iff_aux P p v

/-- **`⋀^{2p} Φ` followed by `cupWedgeEquiv Y` carries the model's rational Hodge classes onto
`Hdg^p(Y; ℚ)`.** From the pointwise statement and surjectivity.
Source: `spec_g2_mem_rationalExteriorHodge_iff`, `spec_g2_cohomologyMap_bijective`; at `r = 1`
compare `powerOne_rationalExteriorHodge_map_eq`. -/
theorem spec_g2_rationalExteriorHodge_map_eq (P : AbelianPowerData A Y r) (p : ℕ) :
    letI := (finiteBetti_abelian A).finite 1
    (rationalExteriorHodge (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal r (2 * p)).map (P.cohomologyMap (2 * p)) =
      Hdg^p(Y; ℚ) :=
  spec_g2_rationalExteriorHodge_map_eq_aux P p

/-- The weight-one structure used here and the package `S A = abelianVarietyCohomologyOf …` built
from `torusCohomology_cupProductOf A` give the same model classes, definitionally: both have the
pieces `cohomologyHodgePiece A 1`, and the finiteness instances are propositions. -/
example (p : ℕ) :
    letI := (finiteBetti_abelian A).finite 1
    rationalExteriorHodge (abelianWeightOneHodgeStructure A).H
        (abelianWeightOneHodgeStructure A).isInternal r (2 * p) =
      letI := (torusCohomology_cupProductOf A).finite
      rationalExteriorHodge
        (abelianVarietyCohomologyOf (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)).weight1.H
        (abelianVarietyCohomologyOf (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
          (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A)).weight1.isInternal
        r (2 * p) :=
  rfl

/-- **Degenerate check `k = 0`**: the model map sends the unit `1 ∈ ⋀^0` to the unit class of
`Y`. `⋀^0 Φ` fixes the empty wedge, and `cupWedgeMap 0` sends it to the unit.
Source: `CupProduct.cupWedgeMap_zero`; Mathlib `exteriorPower.map_apply_ιMulti`. -/
theorem spec_g2_cohomologyMap_zero (P : AbelianPowerData A Y r) :
    P.cohomologyMap 0 (exteriorPower.ιMulti ℚ 0 Fin.elim0) = cupUnit Y :=
  spec_g2_cohomologyMap_zero_aux P

/-- So, in degree zero, the model map is not zero (the unit class is nonzero), even at `r = 0`. -/
example (P : AbelianPowerData A Y r) : P.cohomologyMap 0 ≠ 0 := fun h => by
  have := spec_g2_cohomologyMap_zero P
  rw [h, LinearMap.zero_apply] at this
  exact (cupProductOf Y).unitClass_ne_zero this.symm

/-- **Degenerate check, `p` out of range**: `Hdg^p(Y; ℚ) = 0` for `p > r · dim A`. Then
`2p > 2 · dim Y` (`spec_g2_dim_eq`), and `HQ Y (2p) ≅ ⋀^{2p} HQ Y 1 = 0` since `HQ Y 1` has
rank `2 · dim Y`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 1.3.1; `spec_g2_dim_eq`,
`torusCohomology_cupProductOf`. -/
theorem spec_g2_hodgeClasses_eq_bot_of_lt (P : AbelianPowerData A Y r) (p : ℕ)
    (hp : r * dim A.left < p) : Hdg^p(Y; ℚ) = ⊥ :=
  spec_g2_hodgeClasses_eq_bot_of_lt_aux P p hp

/-- **Degenerate check `r = 0`**: every `Hdg^p(Y; ℚ)` with `p > 0` vanishes (`Y` has trivial
`H¹`, G4's `spec_g4_eq_zero_of_powerData_zero`). The bound `p > 0` is needed: `Hdg^0(Y; ℚ)`
contains the nonzero unit class. -/
example (P : AbelianPowerData A Y 0) (p : ℕ) (hp : 0 < p) : Hdg^p(Y; ℚ) = ⊥ :=
  spec_g2_hodgeClasses_eq_bot_of_lt P p (by rwa [zero_mul])

variable [IsCommMonObj A] {L : Type*} [Field L] [Algebra ℚ L]

/-- **The pullback of `f_a` on `H¹` is the model pullback under `Φ`.** For `a ∈ 𝒪^r`,
`f_a^* = Φ ∘ pwPowerPullback A θ a`: G4 gives `f_a^* = Σ_i p_i^* ∘ θ(a_i)^*`, and
`Φ (Σ_i θ(a_i)^* x ⊗ e_i) = Σ_i p_i^* θ(a_i)^* x`.
Source: PW v0.3, proof of Theorem 4.2, paragraph "Weil classes"; `spec_g4_homPullback_sumMap`,
`spec_g4_abelianEndAction_pwOrderEnd`, `pwPowerPullback`. -/
theorem spec_g2_homPullback_pwSumMap (P : AbelianPowerData A Y r) (θ : L →ₐ[ℚ] AbelianEnd0 A)
    (a : Fin r → pwOrder A θ) :
    homPullback (P.pwSumMap θ a) 1 = P.h1Map ∘ₗ pwPowerPullback A θ (fun i => (a i : L)) :=
  spec_g2_homPullback_pwSumMap_aux P θ a

/-- At `a_i = p_i + s_i u` with rational `p_i`, `s_i` and `u ∈ 𝒪`, this is PW-0's Weil pullback
`weilPowerPullback` under `Φ` (G4's `spec_g4_pwPowerPullback_eq_weilPowerPullback`). -/
example (P : AbelianPowerData A Y r) (θ : L →ₐ[ℚ] AbelianEnd0 A) (u : L) (p s : Fin r → ℚ)
    (a : Fin r → pwOrder A θ) (ha : ∀ i, (a i : L) = algebraMap ℚ L (p i) + algebraMap ℚ L (s i) * u) :
    homPullback (P.pwSumMap θ a) 1 = P.h1Map ∘ₗ weilPowerPullback (pwAction A θ u) p s := by
  rw [spec_g2_homPullback_pwSumMap, ← spec_g4_pwPowerPullback_eq_weilPowerPullback]
  simp_rw [ha]

/-- **The pullback of `f_a` in every degree is `⋀ cmPowerPullback` under the model map.** In
degree `k`, `f_a^* ∘ cupWedgeEquiv_A k = P.cohomologyMap k ∘ ⋀^k (pwPowerPullback A θ a)`. By
G1b (`f^*` in degree `k` is `⋀^k` of `f^*` in degree one, through the torus isomorphisms) and the
degree-one statement.
Source: PW v0.3, proof of Theorem 4.2, paragraph "Weil classes" (`f_a^* W_k(A)`);
`spec_homPullback_eq_cupWedgeEquiv` (stage G1b), `spec_g2_homPullback_pwSumMap`. -/
theorem spec_g2_homPullback_pwSumMap_degree (P : AbelianPowerData A Y r)
    (θ : L →ₐ[ℚ] AbelianEnd0 A) (a : Fin r → pwOrder A θ) (k : ℕ) :
    homPullback (P.pwSumMap θ a) k ∘ₗ
        ((torusCohomology_cupProductOf A).cupWedgeEquiv k).toLinearMap =
      P.cohomologyMap k ∘ₗ exteriorPower.map k (pwPowerPullback A θ (fun i => (a i : L))) :=
  spec_g2_homPullback_pwSumMap_degree_aux P θ a k

/-- So the image in `HQ Y n` of the model class `⋀^n (pwPowerPullback A θ a) w` is the pullback
`f_a^*` of the class of `w` in `HQ A n`. -/
example (P : AbelianPowerData A Y r) (θ : L →ₐ[ℚ] AbelianEnd0 A) (a : Fin r → pwOrder A θ)
    (n : ℕ) (w : ⋀[ℚ]^n (HQ A 1)) :
    P.cohomologyMap n (exteriorPower.map n (pwPowerPullback A θ (fun i => (a i : L))) w) =
      homPullback (P.pwSumMap θ a) n ((cupProductOf A).cupWedgeMap n w) := by
  have h := LinearMap.congr_fun (spec_g2_homPullback_pwSumMap_degree P θ a n) w
  simpa using h.symm

end Power

variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom]
  [IsProjective A.hom]

/-- **The `r = 1` example**: for `Y = A`, `p = s = 𝟙 A`, `Φ` is the canonical identification
`powerOneFlatten A : x ⊗ c ↦ c_0 • x`, since `(𝟙 A)^* = id`.
Source: `spec_homPullback_id` (stage G1a); `powerOneFlatten`. -/
theorem spec_g2_h1Map_one : (AbelianPowerData.one A).h1Map = powerOneFlatten A :=
  spec_g2_h1Map_one_aux A

/-- So at `r = 1` the model map is the one of `powerOne_rationalExteriorHodge_map_eq`. -/
example (k : ℕ) :
    (AbelianPowerData.one A).cohomologyMap k =
      ((torusCohomology_cupProductOf A).cupWedgeEquiv k).toLinearMap ∘ₗ
        exteriorPower.map k (powerOneFlatten A) := by
  rw [AbelianPowerData.cohomologyMap, spec_g2_h1Map_one]

omit [IsCommMonObj A] [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] in
/-- **Falsification: a non-homomorphism is not admissible as a projection.** The constant map
`Y → pt → A` at a point `x` other than the identity `η[A]` is not a homomorphism: a homomorphism
sends `η[Y]` to `η[A]`, and the constant map sends it to `x`. Constant maps also pull back to `0`
on `HQ · 1`, so without the field `proj_isMonHom` the shape of power data would not exclude them.
Source: Mathlib `IsMonHom.one_hom`, `CartesianMonoidalCategory.toUnit_unique`. -/
theorem spec_g2_not_isMonHom_const (Y : Over (Spec ↧ℂ)) [GrpObj Y]
    (x : 𝟙_ (Over (Spec ↧ℂ)) ⟶ A) (hx : x ≠ η[A]) : ¬ IsMonHom (toUnit Y ≫ x) :=
  spec_g2_not_isMonHom_const_aux A Y x hx

omit [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom] in
/-- So no power data has such a constant map as a projection. -/
example {Y : Over (Spec ↧ℂ)} [GrpObj Y] [IsCommMonObj Y] {r : ℕ} (P : AbelianPowerData A Y r)
    (i : Fin r) (x : 𝟙_ (Over (Spec ↧ℂ)) ⟶ A) (hx : x ≠ η[A]) : P.proj i ≠ toUnit Y ≫ x :=
  fun h => spec_g2_not_isMonHom_const A Y x hx (h ▸ P.proj_isMonHom i)

end HodgeLean.Adapters
