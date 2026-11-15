import HodgeLean.Foundations.Program.HurwitzPrym
import HodgeLean.Foundations.Program.RelativeFrameAssembly

/-! # Finite-group quotients of compact Riemann surfaces: definitions

The orbit space `X ⧸ H` is Mathlib's `MulAction.orbitRel.Quotient H X` with the quotient
topology, and `rsq_proj` is the quotient map. For a normal subgroup `K ⊴ H`, `rsq_quotAction`
is the induced action of `H ⧸ K` on `X ⧸ K`, and `rsq_tower` is the comparison map
`(X ⧸ K) ⧸ (H ⧸ K) → X ⧸ H`. No complex structure on a quotient is constructed here.

Compactness, connectedness and the Hausdorff property of `X ⧸ H` are Mathlib instances
(`Quotient.compactSpace`, the connected quotient instance and
`t2Space_of_properlyDiscontinuousSMul_of_t2Space` with `Finite.to_properlyDiscontinuousSMul`);
the example after `rsq_proj` derives them and nothing about them is restated.

HC no distance; AV milestone no distance.
-/

noncomputable section

open Manifold
open scoped ContDiff

namespace HodgeLean.Foundations.Program

section Quotient

variable (H : Type) [Group H] (X : Type) [MulAction H X]

/-- **The orbit space** `X ⧸ H`, with the quotient topology when `X` is a space.
Source: Forster, *Lectures on Riemann Surfaces*, GTM 81, §4 (quotient constructions);
Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. III §3; Mathlib
`MulAction.orbitRel.Quotient`. -/
abbrev rsq_Quot : Type := MulAction.orbitRel.Quotient H X

/-- **The quotient map** `X → X ⧸ H`.
Source: Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. III §3 (the quotient map
`π : X → X ⧸ G`). -/
def rsq_proj : X → rsq_Quot H X := Quotient.mk (MulAction.orbitRel H X)

example (g : H) (x : X) : rsq_proj H X (g • x) = rsq_proj H X x :=
  MulAction.orbitRel.Quotient.quotient_smul_eq

/-- The fibres of the quotient map are the orbits: it is a Galois cover in the sense of
`b4_IsGaloisCover`, independent of any complex structure on the quotient. -/
theorem rsq_proj_isGaloisCover : b4_IsGaloisCover H (rsq_proj H X) := by
  refine ⟨fun g x ↦ MulAction.orbitRel.Quotient.quotient_smul_eq, fun x x' h ↦ ?_⟩
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 (Quotient.exact h.symm)
  exact ⟨g, hg⟩

/-- Item (1) of the lane is Mathlib: for a continuous action of a finite group on a compact
connected locally compact Hausdorff space, the orbit space is compact, connected and Hausdorff. -/
example [TopologicalSpace X] [Finite H] [CompactSpace X] [ConnectedSpace X] [T2Space X]
    [LocallyCompactSpace X] [ContinuousConstSMul H X] :
    CompactSpace (rsq_Quot H X) ∧ ConnectedSpace (rsq_Quot H X) ∧ T2Space (rsq_Quot H X) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

variable {H X} in
/-- The orbit space of a Hausdorff surface by a finite group of homeomorphisms is Hausdorff:
Mathlib's `t2Space_of_properlyDiscontinuousSMul_of_t2Space`, with local compactness from the
charts into the complex line `E`. -/
theorem rsq_t2Space {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace X]
    [ChartedSpace E X] [T2Space X] (hE : Module.finrank ℂ E = 1) [Finite H]
    (hc : ∀ g : H, Continuous (fun x : X ↦ g • x)) : T2Space (rsq_Quot H X) := by
  have : ContinuousConstSMul H X := ⟨hc⟩
  have : FiniteDimensional ℂ E := Module.finite_of_finrank_eq_succ hE
  have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace E X
  infer_instance

variable {H X} in
/-- The map `X ⧸ H → Y` induced by an `H`-invariant map `f : X → Y`.
Source: Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. III §3 (maps that factor through
the quotient); Mathlib `Quotient.lift`. -/
def rsq_lift {Y : Type*} (f : X → Y) (hf : ∀ (g : H) (x : X), f (g • x) = f x) :
    rsq_Quot H X → Y :=
  Quotient.lift f fun x y hxy ↦ by
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.1 hxy
    exact hf g y

variable {H X} in
theorem rsq_lift_comp {Y : Type*} (f : X → Y) (hf : ∀ (g : H) (x : X), f (g • x) = f x) :
    rsq_lift f hf ∘ rsq_proj H X = f := rfl

/-- The quotient map is continuous and surjective. -/
example [TopologicalSpace X] : Continuous (rsq_proj H X) ∧ Function.Surjective (rsq_proj H X) :=
  ⟨continuous_quotient_mk', Quotient.mk_surjective⟩

variable {H X}
variable (K : Subgroup H) [K.Normal]

/-- Translation by `h` on `X ⧸ K`, well defined because `K` is normal:
`h k x = (h k h⁻¹) h x`.
Source: Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. III §3 (quotients in stages);
Mathlib `Quotient.map'`. -/
def rsq_quotSMul (h : H) : rsq_Quot K X → rsq_Quot K X :=
  Quotient.map' (h • ·) fun x y hxy ↦ by
    obtain ⟨k, hk⟩ := MulAction.mem_orbit_iff.1 hxy
    refine MulAction.mem_orbit_iff.2 ⟨⟨h * k * h⁻¹, ‹K.Normal›.conj_mem _ k.2 h⟩, ?_⟩
    rw [Subgroup.mk_smul, ← hk, Subgroup.smul_def, smul_smul, smul_smul, inv_mul_cancel_right]

theorem rsq_quotSMul_mk (h : H) (x : X) :
    rsq_quotSMul K h (rsq_proj K X x) = rsq_proj K X (h • x) := rfl

example (h : H) (x : X) :
    rsq_quotSMul K h (rsq_proj K X x) = rsq_proj K X (h • x) := rfl

theorem rsq_quotSMul_mul_mem (h : H) {k : H} (hk : k ∈ K) :
    rsq_quotSMul K (h * k) = rsq_quotSMul (X := X) K h := by
  funext q
  induction q using Quotient.inductionOn' with
  | h x =>
    change rsq_proj K X ((h * k) • x) = rsq_proj K X (h • x)
    refine Quotient.sound (MulAction.mem_orbit_iff.2
      ⟨⟨h * k * h⁻¹, ‹K.Normal›.conj_mem _ hk h⟩, ?_⟩)
    rw [Subgroup.mk_smul, smul_smul, inv_mul_cancel_right]

/-- **The induced action of `H ⧸ K` on `X ⧸ K`**, `(hK) · [x] = [h x]`, for `K ⊴ H`.
Source: Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. III §3 (quotients in stages);
Forster, *Lectures on Riemann Surfaces*, §4. -/
instance rsq_quotAction : MulAction (H ⧸ K) (rsq_Quot K X) where
  smul a q := Quotient.liftOn' a (fun h ↦ rsq_quotSMul K h q) fun h h' hh ↦ by
    rw [QuotientGroup.leftRel_apply] at hh
    rw [show h' = h * (h⁻¹ * h') by group, rsq_quotSMul_mul_mem K h hh]
  one_smul q := by
    induction q using Quotient.inductionOn' with
    | h x => exact congrArg (rsq_proj K X) (one_smul H x)
  mul_smul a b q := by
    induction a using QuotientGroup.induction_on with
    | H h =>
      induction b using QuotientGroup.induction_on with
      | H h' =>
        induction q using Quotient.inductionOn' with
        | h x => exact congrArg (rsq_proj K X) (mul_smul h h' x)

theorem rsq_quotAction_mk (h : H) (x : X) :
    (h : H ⧸ K) • rsq_proj K X x = rsq_proj K X (h • x) := rfl

/-- Elements of `K` act trivially on `X ⧸ K`. -/
example (k : K) (q : rsq_Quot K X) : ((k : H) : H ⧸ K) • q = q := by
  rw [(QuotientGroup.eq_one_iff (k : H)).2 k.2, one_smul]

omit [K.Normal] in
/-- The map `X ⧸ K → X ⧸ H` sending a `K`-orbit to the `H`-orbit containing it.
Source: Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. III §3 (quotients in stages);
Mathlib `MulAction.orbitRel.quotient_eq_of_quotient_subgroup_eq`. -/
def rsq_coarsen : rsq_Quot K X → rsq_Quot H X :=
  Quotient.lift (rsq_proj H X) fun _ _ hxy ↦
    MulAction.orbitRel.quotient_eq_of_quotient_subgroup_eq (Quotient.sound hxy)

omit [K.Normal] in
theorem rsq_coarsen_mk (x : X) : rsq_coarsen K (rsq_proj K X x) = rsq_proj H X x := rfl

omit [K.Normal] in
example (x : X) : rsq_coarsen K (rsq_proj K X x) = rsq_proj H X x := rfl

/-- **The tower map** `(X ⧸ K) ⧸ (H ⧸ K) → X ⧸ H`, `[[x]] ↦ [x]`.
Source: Miranda, *Algebraic Curves and Riemann Surfaces*, Ch. III §3 (if `K ⊴ G`, then
`X ⧸ G ≅ (X ⧸ K) ⧸ (G ⧸ K)`). -/
def rsq_tower : rsq_Quot (H ⧸ K) (rsq_Quot K X) → rsq_Quot H X :=
  Quotient.lift (rsq_coarsen K) fun q q' hq ↦ by
    obtain ⟨a, rfl⟩ := MulAction.mem_orbit_iff.1 hq
    induction a using QuotientGroup.induction_on with
    | H h =>
      induction q' using Quotient.inductionOn' with
      | h x => exact MulAction.orbitRel.Quotient.quotient_smul_eq

theorem rsq_tower_mk (x : X) :
    rsq_tower K (rsq_proj (H ⧸ K) (rsq_Quot K X) (rsq_proj K X x)) = rsq_proj H X x := rfl

/-- The tower map is surjective (the open part is that it is a homeomorphism). -/
example : Function.Surjective (rsq_tower (X := X) K) := fun q ↦ by
  induction q using Quotient.inductionOn' with
  | h x => exact ⟨_, rsq_tower_mk K x⟩

end Quotient

/-! ## A nondegenerate instance: `μ₄` acting on `ℂ ⧸ (ℤ + iℤ)` -/

/-- The subgroup `{1, σ²}` of `μ₄ = Multiplicative (ZMod 4)`, generated by `z ↦ -z`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, §1.1; Miranda, Ch. III §3 (the
elliptic involution). -/
def rsq_mu2 : Subgroup (Multiplicative (ZMod 4)) :=
  Subgroup.zpowers (Multiplicative.ofAdd 2)

instance rsq_mu2_normal : rsq_mu2.Normal := Subgroup.normal_of_isMulCommutative _

/-- `{1, σ²}` has order two: neither trivial nor all of `μ₄`. -/
theorem rsq_mu2_card : Nat.card rsq_mu2 = 2 := by
  rw [rsq_mu2, Nat.card_zpowers, orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 ↦ ?_⟩
  interval_cases m
  decide

/-- Every element of `μ₄` fixes `0`: the stabilizer of `0` is the whole group, of order four. -/
theorem rsq_mu4_stabilizer_zero : MulAction.stabilizer (Multiplicative (ZMod 4)) (0 : b3_Elliptic) = ⊤ := by
  ext g
  simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_top, iff_true]
  exact map_zero (b4_ellipticScale (Multiplicative.toAdd g).val)

example : Nat.card (Multiplicative (ZMod 4)) = 4 := by
  rw [Nat.card_eq_fintype_card]
  rfl

end HodgeLean.Foundations.Program
