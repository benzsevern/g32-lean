import HodgeLean.Adapters.AbelianHomPullbackDegreesProofs

/-! # Pullback along morphisms of abelian varieties in all degrees (FROZEN)

Stage G1b of the Powers flagship plan (`docs/roadmap/pw-flagship-plan.md`, §4.2): the pullback
`homPullback f n : HQ X n →ₗ[ℚ] HQ Y n` of stage G1a (`AbelianHomPullbackDefs`), along a morphism
`f : Y ⟶ X`, in every degree.

Claimed, for smooth projective integral `X`, `Y` over `ℂ` and any morphism `f : Y ⟶ X`:
* naturality of the instantiated cup product `cupProductOf`: `f^*(a ∪ b) = f^* a ∪ f^* b`, with no
  normalization scalar (both cup products are transported along the comparisons `homPullback` is
  conjugated by);
* naturality of the wedge map: `f^* ∘ cupWedgeMap m = cupWedgeMap m ∘ ⋀^m (f^* on HQ · 1)`.

Claimed, for abelian `X` and `Y` (group objects that are integral, smooth and projective):
* for any morphism `f`, the pullback in degree `m` is the exterior power of the pullback in degree
  one, read through the torus isomorphisms `cupWedgeEquiv m` of `X` and `Y`;
* for any morphism `f` and `n ∈ ℤ`, `(f ^ n)^* = n ^ m • f^*` on `HQ · m`; in particular the
  constant map to the identity kills `HQ · m` for `m ≥ 1`;
* for a homomorphism `f` (`IsMonHom f`): the complexified pullback maps each candidate Hodge piece
  `cohomologyHodgePiece X m (p, q)` into that of `Y`, in degree one and in every degree; so `f^*`
  maps `Hdg^p(X; ℚ)` into `Hdg^p(Y; ℚ)`, and the pullback of every rational Weil class of `X` (for
  any Weil-type action on `H¹(X(ℂ); ℚ)`) lies in `Hdg^k(Y; ℚ)`.

Not claimed: any comparison of `homPullback` with a pullback of sheaf or de Rham cohomology; Hodge
compatibility for morphisms that are not homomorphisms; a formula for the pullback of a Weil class
in terms of the Weil classes of `Y` (that needs a Weil action on `Y` and `K`-linearity of `f`, and is
recorded for G2); anything about products or powers of abelian varieties; algebraicity of pulled
back classes.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Foundations

namespace HodgeLean.Adapters

section Cup

variable {X Y : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]

/-- Naturality of the instantiated cup product: for any morphism `f : Y ⟶ X`,
`f^*(a ∪ b) = f^* a ∪ f^* b`. `cupProductOf` is the singular Alexander–Whitney product transported
along `cupComparison` (`cupComparison_cup`), `homPullback` is singular pullback conjugated by the
same comparisons, and singular pullback preserves the cup product
(`Foundations.Singular.cohomologyMap_cup`). No normalization scalar enters.
Source: Hatcher, *Algebraic Topology*, §3.2 (naturality of the cup product, `f^*(a ⌣ b) =
f^* a ⌣ f^* b`); `cupComparison_cup`, `Foundations.Singular.cohomologyMap_cup`. -/
theorem spec_homPullback_cup (f : Y ⟶ X) {i j k : ℕ} (h : i + j = k) (a : HQ X i)
    (b : HQ X j) :
    homPullback f k ((cupProductOf X).cup h a b) =
      (cupProductOf Y).cup h (homPullback f i a) (homPullback f j b) :=
  spec_homPullback_cup_aux f h a b

/-- Degree-zero check: with `spec_homPullback_unit`, the pullback of `1 ∪ b` is `1 ∪ f^* b`. -/
example (f : Y ⟶ X) (k : ℕ) (b : HQ X k) :
    homPullback f k ((cupProductOf X).cup (zero_add k) (cupUnit X) b) =
      (cupProductOf Y).cup (zero_add k) (cupUnit Y) (homPullback f k b) := by
  rw [spec_homPullback_cup, spec_homPullback_unit]

/-- Naturality of the wedge map: `f^*` on `HQ · m` after `cupWedgeMap m` of `X` is `cupWedgeMap m`
of `Y` after the `m`-th exterior power of `f^*` on `HQ · 1`. The empty wedge (`m = 0`) is the unit
on both sides.
Source: Hatcher, *Algebraic Topology*, §3.2 (naturality of the cup product);
`spec_homPullback_cup`, `spec_homPullback_unit`, `CupProduct.cupWedgeMap_ιMulti`. -/
theorem spec_homPullback_cupWedgeMap (f : Y ⟶ X) (m : ℕ) :
    homPullback f m ∘ₗ (cupProductOf X).cupWedgeMap m =
      (cupProductOf Y).cupWedgeMap m ∘ₗ exteriorPower.map m (homPullback f 1) :=
  spec_homPullback_cupWedgeMap_aux f m

example (f : Y ⟶ X) (m : ℕ) (v : Fin m → HQ X 1) :
    homPullback f m ((cupProductOf X).cupMulti m v) =
      (cupProductOf Y).cupMulti m (fun i => homPullback f 1 (v i)) := by
  have h := LinearMap.congr_fun (spec_homPullback_cupWedgeMap f m) (exteriorPower.ιMulti ℚ m v)
  simpa only [LinearMap.comp_apply, CupProduct.cupWedgeMap_ιMulti,
    exteriorPower.map_apply_ιMulti, Function.comp_def] using h

end Cup

section Abelian

variable {X Y : Over (Spec ↧ℂ)} [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
  [IsProjective X.hom] [GrpObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]

/-- For abelian `X` and `Y` and any morphism `f : Y ⟶ X`, the pullback in degree `m` is the
`m`-th exterior power of the pullback in degree one, read through the torus isomorphisms
`⋀^m HQ · 1 ≃ HQ · m` of `X` and `Y` (`torusCohomology_cupProductOf`).
Source: Hatcher, *Algebraic Topology*, §3.2 (naturality of the cup product); Birkenhake–Lange,
*Complex Abelian Varieties*, 2nd ed., Lemma 1.3.1 (`H^m = ⋀^m H¹`);
`spec_homPullback_cupWedgeMap`, `torusCohomology_cupProductOf`. -/
theorem spec_homPullback_eq_cupWedgeEquiv (f : Y ⟶ X) (m : ℕ) :
    homPullback f m =
      ((torusCohomology_cupProductOf Y).cupWedgeEquiv m).toLinearMap ∘ₗ
        exteriorPower.map m (homPullback f 1) ∘ₗ
          ((torusCohomology_cupProductOf X).cupWedgeEquiv m).symm.toLinearMap :=
  spec_homPullback_eq_cupWedgeEquiv_aux f m

/-- So the pullback in every degree is determined by the pullback in degree one. -/
example (f g : Y ⟶ X) (h : homPullback f 1 = homPullback g 1) (m : ℕ) :
    homPullback f m = homPullback g m := by
  rw [spec_homPullback_eq_cupWedgeEquiv f m, spec_homPullback_eq_cupWedgeEquiv g m, h]

/-- Degree check: for any morphism `f : Y ⟶ X` and `n ∈ ℤ`, the pointwise power `f ^ n` (through
the group law of `X`) pulls back to `n ^ m • f^*` on `HQ · m`. In degree one this is
`spec_homPullback_zpow`; in degree `m` the factor is `n ^ m` because `⋀^m (n • φ) = n ^ m • ⋀^m φ`.
At `m = 0` both sides send the unit to the unit.
Source: Mumford, *Abelian Varieties*, §4 (`[n]^*` acts on `H^m` by `n^m`); Birkenhake–Lange,
*Complex Abelian Varieties*, 2nd ed., §1.2 and Lemma 1.3.1; `spec_homPullback_zpow`,
`spec_homPullback_eq_cupWedgeEquiv`. -/
theorem spec_homPullback_zpow_degree (f : Y ⟶ X) (n : ℤ) (m : ℕ) :
    homPullback (f ^ n) m = ((n : ℚ) ^ m) • homPullback f m :=
  spec_homPullback_zpow_degree_aux f n m

/-- Falsification check (degree zero): the factor is `n ^ 0 = 1`, so `f ^ n` and `f` pull back to
the same map on `HQ · 0`; a factor `n` would contradict `spec_homPullback_unit` at `n = 0`. -/
example (f : Y ⟶ X) (n : ℤ) : homPullback (f ^ n) 0 = homPullback f 0 := by
  rw [spec_homPullback_zpow_degree, pow_zero, one_smul]

/-- Sanity check: the constant map to the identity kills `HQ · m` for every `m ≥ 1` (it is
`f ^ 0` for any `f`). At `m = 0` it does not (`spec_homPullback_unit`). -/
example (m : ℕ) (hm : 1 ≤ m) : homPullback (1 : Y ⟶ X) m = 0 := by
  have h := spec_homPullback_zpow_degree (1 : Y ⟶ X) 0 m
  rw [zpow_zero, Int.cast_zero, zero_pow (by omega), zero_smul] at h
  exact h

/-- Sanity check: multiplication by `n` (the power `𝟙 X ^ n`) acts on `HQ X m` by `n ^ m`. -/
example (n : ℤ) (m : ℕ) (x : HQ X m) :
    homPullback (𝟙 X ^ n) m x = ((n : ℚ) ^ m) • x := by
  rw [spec_homPullback_zpow_degree, spec_homPullback_id, LinearMap.smul_apply,
    LinearMap.id_apply]

/-- For a homomorphism `f : Y ⟶ X`, the complexified pullback on `HQ · 1` maps each candidate Hodge
piece `cohomologyHodgePiece X 1 (p, q)` into that of `Y`. The `(1, 0)` piece is `F^1_B`
(`spec_homPullback_hodgeFiltration`), the `(0, 1)` piece is its rational conjugate
(`cohomologyHodgePiece_map_sigmaQ`, and the pullback is rational), and the other pieces are `⊥`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.2 and Theorem 1.4.1;
`spec_homPullback_hodgeFiltration`, `cohomologyHodgePiece_map_sigmaQ`. -/
theorem spec_homPullback_hodgePiece_one (f : Y ⟶ X) [IsMonHom f] (pq : ℤ × ℤ) :
    (cohomologyHodgePiece X 1 pq).map ((homPullback f 1).baseChange ℂ) ≤
      cohomologyHodgePiece Y 1 pq :=
  spec_homPullback_hodgePiece_one_aux f pq

/-- For a homomorphism `f : Y ⟶ X`, the complexified pullback on `HQ · m` maps each candidate Hodge
piece of `X` into that of `Y`: `f^*` is a morphism of the Hodge structures of every degree. The
pieces of `ℂ ⊗ HQ · m` are spanned by cup products of degree-one pieces
(`comap_cohomologyHodgePiece_eq_exteriorPowerH`, with `CupFiltered` and `HodgeDecomposition` for
abelian varieties), and `f^*` commutes with cup products (`spec_homPullback_cup`) and preserves the
degree-one pieces (`spec_homPullback_hodgePiece_one`). At `m = 0` the only nonzero piece is
`(0, 0)`, which is everything.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §7.3.2 (pullback is a morphism of
Hodge structures); Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 1.3.1 and
Theorem 1.4.1; `spec_homPullback_cup`, `spec_homPullback_hodgePiece_one`. -/
theorem spec_homPullback_hodgePiece (f : Y ⟶ X) [IsMonHom f] (m : ℕ) (pq : ℤ × ℤ) :
    (cohomologyHodgePiece X m pq).map ((homPullback f m).baseChange ℂ) ≤
      cohomologyHodgePiece Y m pq :=
  spec_homPullback_hodgePiece_aux f m pq

/-- For a homomorphism `f : Y ⟶ X`, the pullback maps `Hdg^p(X; ℚ)` into `Hdg^p(Y; ℚ)`.
Source: Voisin, *Hodge Theory and Complex Algebraic Geometry I*, §7.3.2; Birkenhake–Lange,
*Complex Abelian Varieties*, 2nd ed., Theorem 1.4.1; `spec_homPullback_hodgePiece`,
`mem_hodgeClasses_iff_tmul_mem`. -/
theorem spec_homPullback_hodgeClasses (f : Y ⟶ X) [IsMonHom f] (p : ℕ) (x : HQ X (2 * p))
    (hx : (x : H^(2 * p)(X; ℚ)) ∈ Hdg^p(X; ℚ)) :
    (homPullback f (2 * p) x : H^(2 * p)(Y; ℚ)) ∈ Hdg^p(Y; ℚ) :=
  spec_homPullback_hodgeClasses_aux f p x hx

/-- The Hodge-class statement follows from the degree-`2p` piece statement. -/
example (f : Y ⟶ X) [IsMonHom f] (p : ℕ) (x : HQ X (2 * p))
    (hx : (x : H^(2 * p)(X; ℚ)) ∈ Hdg^p(X; ℚ)) :
    (homPullback f (2 * p) x : H^(2 * p)(Y; ℚ)) ∈ Hdg^p(Y; ℚ) := by
  rw [mem_hodgeClasses_iff_tmul_mem] at hx ⊢
  have h := spec_homPullback_hodgePiece f (2 * p) ((p : ℤ), (p : ℤ))
    (Submodule.mem_map_of_mem hx)
  rwa [LinearMap.baseChange_tmul] at h

/-- For a homomorphism `f : Y ⟶ X` and a Weil-type action `A` on `H¹(X(ℂ); ℚ)`, the pullback of
every rational Weil class of `X` lies in `Hdg^k(Y; ℚ)`, `k = dim_ℂ (Vs ⊓ H^{1,0})`. These are the
generators `f_a^* W_k(A)` of PW v0.3 Theorem 4.2, so they are Hodge classes on the power.
`hF`, `hB`, `hD` only fix the Blocks package of `X`; each is a theorem for abelian `X` (see the
`example` below), and since they are propositions any proofs give the same package.
Source: Weil, "Abelian varieties and the Hodge ring" (1977); PW v0.3 Theorem 4.2, proof,
"Conclusion" (`𝓑` consists of Hodge classes); `weilClassOf_le_hdg`,
`spec_homPullback_hodgeClasses`. -/
theorem spec_homPullback_weilClassOf (f : Y ⟶ X) [IsMonHom f] (hF : FiniteBetti X)
    (hB : BettiDeRhamIso X) (hD : HodgeDecomposition X) {d : ℚ}
    (A : letI := (torusCohomology_cupProductOf X).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf hF hB hD (torusCohomology_cupProductOf X)).weight1 d)
    (hW : letI := (torusCohomology_cupProductOf X).finite; A.IsWeilType) :
    letI := (torusCohomology_cupProductOf X).finite
    (weilClassOf hF hB hD (torusCohomology_cupProductOf X) A hW).map (homPullback f _) ≤
      Hdg^(Module.finrank ℂ ↥(A.Vs ⊓
        (abelianVarietyCohomologyOf hF hB hD (torusCohomology_cupProductOf X)).weight1.H
          (1, 0)))(Y; ℚ) :=
  spec_homPullback_weilClassOf_aux f hF hB hD A hW

/-- The package inputs are theorems for abelian `X`: no open input remains. -/
example (f : Y ⟶ X) [IsMonHom f] {d : ℚ}
    (A : letI := (torusCohomology_cupProductOf X).finite
      HodgeBlocks.WeilAction
        (abelianVarietyCohomologyOf (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
          (spec_hodgeDecomposition_of_cupLeft_alone X (torusCohomology_cupProductOf X)
            (spec_cupLeft_cupProductOf X)) (torusCohomology_cupProductOf X)).weight1 d)
    (hW : letI := (torusCohomology_cupProductOf X).finite; A.IsWeilType) :
    letI := (torusCohomology_cupProductOf X).finite
    (weilClassOf (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
        (spec_hodgeDecomposition_of_cupLeft_alone X (torusCohomology_cupProductOf X)
          (spec_cupLeft_cupProductOf X)) (torusCohomology_cupProductOf X) A hW).map
        (homPullback f _) ≤
      Hdg^(Module.finrank ℂ ↥(A.Vs ⊓
        (abelianVarietyCohomologyOf (finiteBetti_abelian X) (spec_bettiDeRhamIso_abelian X)
          (spec_hodgeDecomposition_of_cupLeft_alone X (torusCohomology_cupProductOf X)
            (spec_cupLeft_cupProductOf X)) (torusCohomology_cupProductOf X)).weight1.H
          (1, 0)))(Y; ℚ) :=
  spec_homPullback_weilClassOf f _ _ _ A hW

end Abelian

end HodgeLean.Adapters
