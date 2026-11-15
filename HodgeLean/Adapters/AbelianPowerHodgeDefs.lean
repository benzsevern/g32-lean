import HodgeLean.Adapters.AbelianCMDataDefs
import HodgeLean.Adapters.F1575PowersOneDefs

/-! # Powers, from the exterior model to `HQ(Y)`, stage G2 of the Powers flagship: definitions

Definitions for `AbelianPowerHodge`, stage G2 of formalizing PW v0.3, Theorem 4.2 (`thm:gen`).
For abelian `A` and `Y` with power data `P : AbelianPowerData A Y r` (stage G4):

* `P.h1Map : HQ A 1 ⊗ ℚ^r → HQ Y 1`, `x ⊗ c ↦ Σ_i c_i • p_i^* x`, the map `Φ` built from the
  pullbacks along the projections `p_i : Y ⟶ A`;
* `P.h1Inv : HQ Y 1 → HQ A 1 ⊗ ℚ^r`, `y ↦ Σ_i s_i^* y ⊗ e_i`, built from the pullbacks along the
  inclusions `s_i : A ⟶ Y`;
* `P.cohomologyMap k : ⋀^k (HQ A 1 ⊗ ℚ^r) → HQ Y k`, the `k`-th exterior power of `Φ` followed by
  the torus isomorphism `cupWedgeEquiv k` of `Y` (`torusCohomology_cupProductOf Y`);
* `powerWeightOnePiece H r pq`: the `(p, q)` piece `H^{p,q} ⊗ ℂ^r` of `ℂ ⊗ (V ⊗ ℚ^r)`, for a
  family of pieces `H` of `ℂ ⊗ V`;
* `AbelianPowerData.one A`: the first power `Y = A`, `p = s = 𝟙 A`.

No definition asserts that `Φ` is invertible, Hodge-compatible or compatible with any pullback;
those are the statements of `AbelianPowerHodge`. HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.WeilPower

namespace HodgeLean.Adapters

/-- **The weight-one pieces of a power**: for pieces `H` of `ℂ ⊗[ℚ] V`, the `(p, q)` piece of
`ℂ ⊗[ℚ] (V ⊗[ℚ] ℚ^r)` is `H (p, q) ⊗ ℂ^r`, the span of the vectors `x ⊗ u` with `x ∈ H (p, q)`,
read through `powerBaseChange r : ℂ ⊗ (V ⊗ ℚ^r) ≃ (ℂ ⊗ V) ⊗[ℂ] ℂ^r`. It is `exteriorHodge`'s
generator shape at exterior degree one, without the exterior power.
Source: van Geemen, *An introduction to the Hodge conjecture for abelian varieties*, §5–6 (the Hodge
structure on `H¹(A^r) = H¹(A)^r`); `powerBaseChange`, `exteriorHodge`. -/
def powerWeightOnePiece {V : Type*} [AddCommGroup V] [Module ℚ V]
    (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) (r : ℕ) (pq : ℤ × ℤ) :
    Submodule ℂ (ℂ ⊗[ℚ] (V ⊗[ℚ] (Fin r → ℚ))) :=
  Submodule.span ℂ {z | ∃ x ∈ H pq, ∃ u : Fin r → ℂ,
    z = (powerBaseChange r).symm (x ⊗ₜ[ℂ] u)}

example {V : Type*} [AddCommGroup V] [Module ℚ V] (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V))
    (r : ℕ) (pq : ℤ × ℤ) (x : ℂ ⊗[ℚ] V) (hx : x ∈ H pq) (u : Fin r → ℂ) :
    (powerBaseChange r).symm (x ⊗ₜ[ℂ] u) ∈ powerWeightOnePiece H r pq :=
  Submodule.subset_span ⟨x, hx, u, rfl⟩

/-- **The first power**: `Y = A`, with `p_0 = s_0 = 𝟙 A`. Stage G4's `example` of power data at
`r = 1`, as a definition.
Source: PW v0.3, Theorem 4.2 (`r = 1`: `A^1 = A`); Mac Lane, *Categories for the Working
Mathematician*, §VIII.2. -/
def AbelianPowerData.one (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] :
    AbelianPowerData A A 1 where
  proj _ := 𝟙 A
  incl _ := 𝟙 A
  proj_isMonHom _ := inferInstance
  incl_isMonHom _ := inferInstance
  incl_proj i j := by
    rw [Subsingleton.elim i j, ite_eq_left_iff.2 fun h => (h rfl).elim, Category.comp_id]
  sum_proj_incl := by rw [Fin.prod_univ_one, Category.comp_id]

example (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A] (i : Fin 1) :
    (AbelianPowerData.one A).proj i = 𝟙 A := rfl

namespace AbelianPowerData

variable {A Y : Over (Spec ↧ℂ)} [GrpObj A] [IsIntegral A.left] [Smooth A.hom]
  [IsProjective A.hom] [GrpObj Y] [IsCommMonObj Y] [IsIntegral Y.left] [Smooth Y.hom]
  [IsProjective Y.hom] {r : ℕ}

/-- **The map `Φ : H¹(A) ⊗ ℚ^r → H¹(Y)`**, `x ⊗ c ↦ Σ_i c_i • p_i^* x`: the sum over `i` of the
pullback along the projection `p_i : Y ⟶ A` after the `i`-th coordinate `x ⊗ c ↦ c_i • x`.
Source: PW v0.3, Theorem 4.2 and its proof (`H¹(A^r) = H¹(A) ⊗ ℚ^r`); Birkenhake–Lange, *Complex
Abelian Varieties*, 2nd ed., §1.3; `homPullback` (stage G1a). -/
def h1Map (P : AbelianPowerData A Y r) : HQ A 1 ⊗[ℚ] (Fin r → ℚ) →ₗ[ℚ] HQ Y 1 :=
  ∑ i, homPullback (P.proj i) 1 ∘ₗ (TensorProduct.rid ℚ (HQ A 1)).toLinearMap ∘ₗ
    LinearMap.lTensor (HQ A 1) (LinearMap.proj i)

example (P : AbelianPowerData A Y r) (x : HQ A 1) (c : Fin r → ℚ) :
    P.h1Map (x ⊗ₜ[ℚ] c) = ∑ i, c i • homPullback (P.proj i) 1 x := by
  simp [h1Map]

/-- **The candidate inverse of `Φ`**, `y ↦ Σ_i s_i^* y ⊗ e_i`, from the pullbacks along the
inclusions `s_i : A ⟶ Y`. The same shape as `cmPowerPullback`.
Source: PW v0.3, Theorem 4.2 (`H¹(A^r) = H¹(A) ⊗ ℚ^r`); `homPullback` (stage G1a),
`cmPowerPullback`. -/
def h1Inv (P : AbelianPowerData A Y r) : HQ Y 1 →ₗ[ℚ] HQ A 1 ⊗[ℚ] (Fin r → ℚ) :=
  ∑ i, ((TensorProduct.mk ℚ (HQ A 1) (Fin r → ℚ)).flip (Pi.single i 1)).comp
    (homPullback (P.incl i) 1)

example (P : AbelianPowerData A Y r) (y : HQ Y 1) :
    P.h1Inv y = ∑ i, homPullback (P.incl i) 1 y ⊗ₜ[ℚ] (Pi.single i 1 : Fin r → ℚ) := by
  simp [h1Inv]

/-- **The model of `HQ Y k`**: `⋀^k Φ` followed by the torus isomorphism
`cupWedgeEquiv k : ⋀^k HQ Y 1 ≃ HQ Y k` of the instantiated cup product of `Y`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., Lemma 1.3.1 (`H^k = ⋀^k H¹`);
`torusCohomology_cupProductOf`, `TorusCohomology.cupWedgeEquiv`. -/
def cohomologyMap (P : AbelianPowerData A Y r) (k : ℕ) :
    ⋀[ℚ]^k (HQ A 1 ⊗[ℚ] (Fin r → ℚ)) →ₗ[ℚ] HQ Y k :=
  ((torusCohomology_cupProductOf Y).cupWedgeEquiv k).toLinearMap ∘ₗ exteriorPower.map k P.h1Map

example (P : AbelianPowerData A Y r) (k : ℕ) (v : ⋀[ℚ]^k (HQ A 1 ⊗[ℚ] (Fin r → ℚ))) :
    P.cohomologyMap k v = (cupProductOf Y).cupWedgeMap k (exteriorPower.map k P.h1Map v) := by
  simp [cohomologyMap]

end AbelianPowerData

end HodgeLean.Adapters
