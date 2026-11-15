import HodgeLean.Adapters.AbelianHomPullbackProofs

/-! # Pullback along homomorphisms of abelian varieties, degree one (FROZEN)

Stage G1a of the Powers flagship plan (`docs/roadmap/pw-flagship-plan.md`, §4.2): the pullback
`homPullback f n : HQ X n →ₗ[ℚ] HQ Y n` along a morphism `f : Y ⟶ X` between two different
varieties (defined in `AbelianHomPullbackDefs`; for `Y = X` it is `complexPointPullback`), and
its first properties.

Claimed, for smooth projective integral `X`, `Y`, `Z` over `ℂ`:
* functoriality: `(𝟙 X)^* = id` and `(g ≫ f)^* = g^* ∘ f^*` in every degree, hence
  `s^* ∘ p^* = id` whenever `s ≫ p = 𝟙 X` (a section);
* in degree zero every pullback sends the unit class to the unit class.

Claimed, for abelian `X` and `Y` (group objects that are integral, smooth and projective):
* additivity on `HQ · 1`: for any `f g : Y ⟶ X`, `(f * g)^* = f^* + g^*`, where `f * g` is the
  pointwise product through the group law of `X`; the constant map `1` pulls back to `0`, and
  `(f ^ n)^* = n • f^*` for `n ∈ ℤ`;
* for a homomorphism `f` (`IsMonHom f`): a complex-linear analytic representation
  `A : ℂ^{dim Y} → ℂ^{dim X}` intertwining the S12 exponentials, and a lattice map
  `Λ_Y → Λ_X` dual to `f^*` through the S12 periods;
* compatibility with the degree-one Hodge decomposition: `f^*` maps the lattice-side summands
  `Hol`, `Anti` of `X` into those of `Y` (as an implication from an analytic representation, and
  unconditionally for homomorphisms), and maps `F^1` of `X` into `F^1` of `Y`, where `F^1` is the
  pullback of upstream's `F^1 H_dR^1` along the Betti–de Rham map.

Not claimed: any comparison of `homPullback` with a pullback of sheaf or de Rham cohomology,
additivity outside degree one (it fails in degree two), Hodge compatibility in higher degrees or
for morphisms that are not homomorphisms, compatibility with cup product, and anything about
products or powers of abelian varieties.
HC no distance; AV milestone no distance.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Foundations

namespace HodgeLean.Adapters

section Functoriality

variable {X Y Z : Over (Spec ↧ℂ)} [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
  [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
  [IsIntegral Z.left] [Smooth Z.hom] [IsProjective Z.hom]

/-- The identity pulls back to the identity, in every degree.
Source: Hatcher, *Algebraic Topology*, §3.1 (functoriality: `id^* = id`). -/
theorem spec_homPullback_id (n : ℕ) : homPullback (𝟙 X) n = LinearMap.id :=
  spec_homPullback_id_aux n

example (n : ℕ) (x : HQ X n) : homPullback (𝟙 X) n x = x := by
  rw [spec_homPullback_id, LinearMap.id_apply]

/-- Pullback is contravariant: for `g : Z ⟶ Y` and `f : Y ⟶ X`, `(g ≫ f)^* = g^* ∘ f^*`.
Source: Hatcher, *Algebraic Topology*, §3.1 (functoriality: `(f g)^* = g^* f^*`). -/
theorem spec_homPullback_comp (g : Z ⟶ Y) (f : Y ⟶ X) (n : ℕ) :
    homPullback (g ≫ f) n = homPullback g n ∘ₗ homPullback f n :=
  spec_homPullback_comp_aux g f n

example (g : Z ⟶ Y) (f : Y ⟶ X) (n : ℕ) (x : HQ X n) :
    homPullback (g ≫ f) n x = homPullback g n (homPullback f n x) := by
  rw [spec_homPullback_comp, LinearMap.comp_apply]

/-- Sections: if `p ∘ s = 𝟙 X`, then `s^* ∘ p^* = id` on `HQ X n`. In particular `p^*` is
injective. Only this order holds in general: `p^* ∘ s^*` is the pullback along `p ≫ s`, which is
not the identity unless `p` is an isomorphism.
Source: Hatcher, *Algebraic Topology*, §3.1 (functoriality); `spec_homPullback_id`,
`spec_homPullback_comp`. -/
theorem spec_homPullback_section (p : Y ⟶ X) (s : X ⟶ Y) (hps : s ≫ p = 𝟙 X) (n : ℕ) :
    homPullback s n ∘ₗ homPullback p n = LinearMap.id :=
  spec_homPullback_section_aux p s hps n

example (p : Y ⟶ X) (s : X ⟶ Y) (hps : s ≫ p = 𝟙 X) (n : ℕ) :
    Function.Injective (homPullback p n) :=
  Function.LeftInverse.injective (g := homPullback s n) fun x => by
    rw [← LinearMap.comp_apply, spec_homPullback_section p s hps n, LinearMap.id_apply]

/-- In degree zero every pullback sends the unit class of `X` to the unit class of `Y`: the
comparisons send the sheaf units to the singular units, which singular pullback preserves.
Source: Hatcher, *Algebraic Topology*, §3.1 and §3.2 (`f^* 1 = 1`); `cupComparison_unit`,
`Foundations.Singular.cohomologyMap_unit`. -/
theorem spec_homPullback_unit (f : Y ⟶ X) :
    homPullback f 0 (cupUnit X) = cupUnit Y :=
  spec_homPullback_unit_aux f

/-- Falsification check: in degree zero no pullback is zero, since the unit class of `Y` is
nonzero. Compare `spec_homPullback_one`: the constant map pulls back to `0` in degree one. -/
example (f : Y ⟶ X) : homPullback f 0 ≠ 0 := by
  intro h
  have := spec_homPullback_unit f
  rw [h, LinearMap.zero_apply] at this
  exact unitClass_ne_zero' Y (this.symm.trans rfl)

end Functoriality

section Abelian

variable {X Y : Over (Spec ↧ℂ)} [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
  [IsProjective X.hom] [GrpObj Y] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]

/-- Additivity on `HQ · 1`: for `f g : Y ⟶ X`, the pullback along the pointwise product
`f * g = lift f g ≫ μ` is the sum of the pullbacks. Degree-one classes of the connected
topological group `X(ℂ)` are primitive; through the S12 periods, the pointwise product of the
image loops has the sum of the periods. No homomorphism condition is needed.
Source: Hatcher, *Algebraic Topology*, §3.C (H-spaces, primitive classes); Birkenhake–Lange,
*Complex Abelian Varieties*, 2nd ed., §1.2 (the rational representation is additive). -/
theorem spec_homPullback_mul (f g : Y ⟶ X) :
    homPullback (f * g) 1 = homPullback f 1 + homPullback g 1 :=
  spec_homPullback_mul_aux f g

/-- The constant map to the identity point pulls back to zero on `HQ · 1`: it factors through a
point, whose degree-one cohomology vanishes.
Source: Hatcher, *Algebraic Topology*, §3.1 (cohomology of a point). -/
theorem spec_homPullback_one : homPullback (1 : Y ⟶ X) 1 = 0 :=
  spec_homPullback_one_aux

/-- Sign check: the pointwise inverse pulls back to the negative, from `spec_homPullback_mul`
and `spec_homPullback_one`. -/
example (f : Y ⟶ X) : homPullback f⁻¹ 1 = -homPullback f 1 := by
  have h := spec_homPullback_mul f f⁻¹
  rw [mul_inv_cancel, spec_homPullback_one] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

/-- Degree check: `f ^ n` (the pointwise `n`-th power through the group law of `X`) pulls back to
`n • f^*` on `HQ · 1`. For `f = 𝟙 X` this is `spec_complexPointPullback_zpow`. In degree two the
factor would be `n²` on `f^*` of a product of two degree-one classes, so the degree matters.
Source: Mumford, *Abelian Varieties*, §4; Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed.,
§1.2; `spec_homPullback_mul`, `spec_homPullback_one`. -/
theorem spec_homPullback_zpow (f : Y ⟶ X) (n : ℤ) :
    homPullback (f ^ n) 1 = (n : ℚ) • homPullback f 1 :=
  spec_homPullback_zpow_aux f n

example (f : Y ⟶ X) (x : HQ X 1) : homPullback (f ^ (-1 : ℤ)) 1 x = -homPullback f 1 x := by
  rw [spec_homPullback_zpow]
  simp

/-- The analytic representation of a homomorphism `f : Y ⟶ X`: a complex-linear
`A : ℂ^{dim Y} → ℂ^{dim X}` with `exp_X ∘ A = f ∘ exp_Y`. The map of complex points is a
holomorphic group homomorphism (upstream `analyticAt_localChart_symm_map`), and a one-parameter
subgroup is determined by its velocity at the identity, so `A` is the derivative of `f` at the
identity in the identity charts.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.2 (analytic representation
`ρ_a` of a homomorphism); Mumford, *Abelian Varieties*, §1; upstream
`Lemmas/AlgebraicGeometry/ComplexPoint/AnalyticMap.lean` at `2ead713`. -/
theorem spec_abelianHom_analyticRepresentation (f : Y ⟶ X) [IsMonHom f] :
    ∃ A : (Fin (dim Y.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ), ∀ v,
      Additive.toMul (complexExponential X (dim X.left) (A v)) =
        Point.map f (Additive.toMul (complexExponential Y (dim Y.left) v)) :=
  spec_abelianHom_analyticRepresentation_aux f

/-- Complex linearity of the analytic representation, which statement
`spec_homPullback_hodge_of_analyticRepresentation` uses: an `ℝ`-linear `A` would not do. -/
example (f : Y ⟶ X) [IsMonHom f] :
    ∃ A : (Fin (dim Y.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ),
      ∀ v, A (Complex.I • v) = Complex.I • A v := by
  obtain ⟨A, -⟩ := spec_abelianHom_analyticRepresentation f
  exact ⟨A, fun v => A.map_smul _ _⟩

/-- The rational representation: through the S12 periods, `f^*` on `HQ · 1` is dual to an
additive map of period lattices `Λ_Y → Λ_X` (the restriction of the analytic representation).
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.2 (`ρ_r` of a homomorphism);
`spec_abelianHom_analyticRepresentation`, `loopPeriod_comp`. -/
theorem spec_homPullback_period (f : Y ⟶ X) [IsMonHom f] :
    ∃ φ : abelianPeriodLattice Y →+ abelianPeriodLattice X, ∀ x l,
      abelianPeriod Y (homPullback f 1 x) l = abelianPeriod X x (φ l) :=
  spec_homPullback_period_aux f

/-- Falsification check for the duality: if the lattice map is zero, then `f^* = 0` on `HQ · 1`,
since the periods of `Y` separate classes (`spec_abelianPeriod_equiv`). So the statement with
`φ` forced to be `0` fails for `f = 𝟙 X` when `dim X ≥ 1`. -/
example (f : Y ⟶ X) [IsMonHom f] (φ : abelianPeriodLattice Y →+ abelianPeriodLattice X)
    (hφ : ∀ x l, abelianPeriod Y (homPullback f 1 x) l = abelianPeriod X x (φ l))
    (h0 : φ = 0) : homPullback f 1 = 0 := by
  obtain ⟨e, he⟩ := spec_abelianPeriod_equiv Y
  obtain ⟨e', he'⟩ := spec_abelianPeriod_equiv X
  refine LinearMap.ext fun x => e.injective ?_
  refine DFunLike.ext _ _ fun l => ?_
  rw [he, hφ, h0, AddMonoidHom.zero_apply, LinearMap.zero_apply, map_zero,
    AddMonoidHom.zero_apply, ← he', map_zero]

/-- Implication from a complex-linear analytic representation: `(f^*)_ℂ` maps the lattice-side
holomorphic summand of `X` into that of `Y`, and the antiholomorphic summand into that of `Y`.
If `ω` has the periods of a complex-linear (or conjugate-linear) functional `F` on `ℂ^{dim X}`,
then `(f^*)_ℂ ω` has the periods of `F ∘ A`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.2 (`ρ_r ⊗ ℂ ≅ ρ_a ⊕ ρ̄_a`) and
Theorem 1.4.1. -/
theorem spec_homPullback_hodge_of_analyticRepresentation (f : Y ⟶ X)
    (A : (Fin (dim Y.left) → ℂ) →ₗ[ℂ] (Fin (dim X.left) → ℂ))
    (hA : ∀ v, Additive.toMul (complexExponential X (dim X.left) (A v)) =
      Point.map f (Additive.toMul (complexExponential Y (dim Y.left) v))) :
    (complexHolomorphicH1 X).map ((homPullback f 1).baseChange ℂ) ≤ complexHolomorphicH1 Y ∧
      (complexAntiholomorphicH1 X).map ((homPullback f 1).baseChange ℂ) ≤
        complexAntiholomorphicH1 Y :=
  spec_homPullback_hodge_of_analyticRepresentation_aux f A hA

/-- For a homomorphism `f : Y ⟶ X`, `(f^*)_ℂ` maps the lattice-side summands `Hol`, `Anti` of
`X` into those of `Y`. It generalizes `spec_abelianEndAction_hodge` from endomorphisms.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.2 and Theorem 1.4.1;
`spec_abelianHom_analyticRepresentation`, `spec_homPullback_hodge_of_analyticRepresentation`. -/
theorem spec_homPullback_hodge (f : Y ⟶ X) [IsMonHom f] :
    (complexHolomorphicH1 X).map ((homPullback f 1).baseChange ℂ) ≤ complexHolomorphicH1 Y ∧
      (complexAntiholomorphicH1 X).map ((homPullback f 1).baseChange ℂ) ≤
        complexAntiholomorphicH1 Y :=
  spec_homPullback_hodge_aux f

example (f : Y ⟶ X) [IsMonHom f] (ω : ℂ ⊗[ℚ] HQ X 1) (hω : ω ∈ complexAntiholomorphicH1 X) :
    (homPullback f 1).baseChange ℂ ω ∈ complexAntiholomorphicH1 Y :=
  (spec_homPullback_hodge f).2 (Submodule.mem_map_of_mem hω)

/-- For a homomorphism `f : Y ⟶ X`, `(f^*)_ℂ` maps `F^1` of `X` into `F^1` of `Y`, where `F^1`
is the pullback of upstream's `F^1 H_dR^1` along the Betti–de Rham map `bettiDeRhamHQ`. This is
the de Rham form of `spec_homPullback_hodge`, through `spec_comap_hodgeFiltration_one_eq` on both
sides; no pullback on de Rham cohomology is involved.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.2 and Theorem 1.4.1
(`H^{1,0} = H^0(Ω^1)`); `spec_homPullback_hodge`, `spec_comap_hodgeFiltration_one_eq`. -/
theorem spec_homPullback_hodgeFiltration (f : Y ⟶ X) [IsMonHom f] :
    ((F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1)).map
        ((homPullback f 1).baseChange ℂ) ≤
      (F^1 H_dR^((1 : ℕ) : ℤ)(Y)).comap (bettiDeRhamHQ Y 1) :=
  spec_homPullback_hodgeFiltration_aux f

/-- The de Rham form follows from the lattice-side form and the identification of `F^1` with the
holomorphic summand on both sides. -/
example (f : Y ⟶ X) [IsMonHom f] :
    ((F^1 H_dR^((1 : ℕ) : ℤ)(X)).comap (bettiDeRhamHQ X 1)).map
        ((homPullback f 1).baseChange ℂ) ≤
      (F^1 H_dR^((1 : ℕ) : ℤ)(Y)).comap (bettiDeRhamHQ Y 1) := by
  rw [spec_comap_hodgeFiltration_one_eq X, spec_comap_hodgeFiltration_one_eq Y]
  exact (spec_homPullback_hodge f).1

end Abelian

end HodgeLean.Adapters
