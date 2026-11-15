import HodgeLean.Adapters.IntersectionProductCycle

/-! # Intersection with a cycle rationally equivalent to zero: reductions

Stage A3.3 of track A3. The independence statement `a3i_intersect_ratEquiv` (if `α − α'` is
rationally equivalent to zero and both meet `β` properly, then so is `α·β − α'·β`) reduces, by
linearity of `a3i_intersect` in the first variable, to the case `α' = 0`: a cycle rationally
equivalent to zero that meets `β` properly has intersection product with `β` rationally
equivalent to zero (`a3e_intersect_ratEquiv_of_zero`).

## Route for the case `α' = 0`, and where it stands

Write `γ = Σ r_i [div φ_i]` with `φ_i` a rational function on `W_i`. The route (Fulton §2.3 and
Proposition 2.3, with Serre's multiplicity) intersects each `[div φ_i]` with `β` through
`W_i ∩ β`, which needs the `W_i` in proper position. The local algebra at a point `T` of
`div φ|_W ∩ V`, `A = 𝒪_{X,T}` regular, has these checked parts:
* `a3e_euler_tor` (`IntersectionProductHerbrand`): the Euler characteristic of `Tor(-, N)` along
  a nonzerodivisor is the alternating sum of Herbrand differences;
* `a3e_isZero_tor_regular` (`IntersectionProductTorDim`): `Tor_n` vanishes above `dim A`;
* `a3e_herbrand_eq_sum` (`IntersectionProductHerbrandDim`): Herbrand differences of a module of
  dimension at most one split along its one-dimensional primes;
* `a3e_principal_local` (`IntersectionProductPrincipalLocal`): with `a ∉ 𝔭_W` and the primes over
  `𝔭_W + 𝔭_V` the maximal ideal and the components `Z` of `W ∩ V` through `T`,
  `Σ (-1)^i ℓ Tor_i(A ⧸ (𝔭_W + a), A ⧸ 𝔭_V)` equals
  `Σ_Z (Σ (-1)^i ℓ Tor_i(A ⧸ 𝔭_W, A ⧸ 𝔭_V)_Z) e_a(A ⧸ Z)`.

Further checked local parts:
* `a3q_length_torModule` (`IntersectionProductTorLocal`): the inner sums of
  `a3e_principal_local` are the lengths in `a3i_serreMult X Z w v`, read at `T`;
* `a3w_vanishing_stalk` (`IntersectionProductSerreLocal`): Serre's vanishing theorem in the local
  rings of a smooth variety over `ℂ`: `Σ (-1)^i ℓ Tor_i(M, N) = 0` when the supports of `M` and `N`
  meet only at the closed point and `dim M + dim N < dim A` (Serre, *Algèbre locale,
  multiplicités*, Chapitre V, B.3, Théorème 1), by reduction to the diagonal
  (`a3d_tor_diag`, `a3v_xs_isWeaklyRegular`, `a3w_vanishing_affine`);
* `a3w_principal_stalk` (`IntersectionProductDivisorLocal`): the local form of Fulton,
  Theorem 2.4, for Serre's multiplicities:
  `Σ_D ord_D(a|_W) · i(T; D · V) = Σ_Z i(Z; W · V) · ord_T(a|_Z)` over the components `D` of
  `div(a|_W)` and `Z` of `W ∩ V` through `T`.

* `a3z_principal_intersect` (`IntersectionProductDivisorGlue`): the cycle form of Fulton,
  Theorem 2.4, for Serre's product: if `W` meets `V` properly, `φ ≠ 0` is a rational function on
  `W` whose divisor meets `V` properly and which is a unit at every component `Z` of `W ∩ V`
  (`a3z_UnitAt`), with restrictions `φ|_Z` (`a3z_IsRestriction`), then
  `[div φ] · [V] = Σ_Z i(Z; W · V) [div (φ|_Z)]`; so `[div φ] · [V]` is rationally equivalent
  to zero (`a3z_principal_intersect_mem`). It glues `a3y_principal_at` over the points `T` of
  `W ∩ V` of the next codimension, with `φ = a / b` for `a`, `b ∈ 𝒪_{X,T}` outside the primes of
  the components through `T` (prime avoidance, `a3z_exists_num_den`).

The global step, checked except for one input:
* `X × ℙ¹` (`IntersectionProductFamilyLine`, `IntersectionProductFamily`): `ℙ¹_ℂ` is smooth and
  integral (`a3n_P1`); `T = X × ℙ¹` is smooth, integral and Noetherian, with the sections
  `σ_c : X → T` over `t₁ = c` and the generic point `b_v` of `V × ℙ¹` (`a3n_b`); the fibres of `T`
  over `t₁ = 0` and `t₁ = 1` are `σ₀(X)` and `σ₁(X)` (`a3n_eq_σ0`, `a3n_eq_σ1`), and
  `codim σ_c(x) = codim x + 1` (`a3n_coheight_σ`);
* local rings along the sections (`IntersectionProductFibreTor`,
  `IntersectionProductFamilyStalk`): base change of `Tor` in one argument along a flat map with a
  retraction (`a3f_tor_restrict`, `a3f_length_tor`), the prime of `V × ℙ¹` at `σ_c(x)` is
  `𝔭_V 𝒪_{T,σ_c(x)}` (`a3n_stalkIdeal_b`), so Serre's multiplicities along `σ_c` are those of
  `X` (`a3n_serreMult_σ`, `a3n_intersectPrime_σ`);
* specialization (`IntersectionProductSpecialize`): for a subvariety `Y` of `T` dominating `ℙ¹`
  whose intersection with `V × ℙ¹` is proper over `ℙ¹ ∖ {∞}` and whose fibres over `t₁ = 0, 1`
  meet `V` properly, `([Y(0)] − [Y(1)]) · [V]` is rationally equivalent to zero
  (`a3o_specialize`), through the cycle form of Fulton, Theorem 2.4, on `T` (`a3o_identity`),
  the projection formula along the sections (`a3o_push_intersect`) and Fulton, Theorem 1.4
  (`a3o_pushforward_ratAll`);
* the reduction (`IntersectionProductRatEquivMoving`): `a3i_intersect_ratEquiv` follows from
  `a3o_MovingRatEquiv` (`a3o_intersect_ratEquiv_of_moving`) by bilinearity of `a3i_intersect`.

The input `a3o_MovingRatEquiv` (a cycle rationally equivalent to zero that meets `β` properly is
a rational combination of cycles `[Y(0)] − [Y(1)]` with `Y` in the position of `a3o_specialize`
with respect to every component of `β`, `a3o_Good`) is the degree-one case of Bloch's moving
lemma (S. Bloch, *The moving lemma for higher Chow groups*, J. Algebraic Geom. 3 (1994), 537–568,
main theorem), read on `X × Δ¹ ⊆ X × ℙ¹`. It is derived (`a3k_movingRatEquiv_of_step`) from
* Fulton's Proposition 1.6 (`IntersectionProductBlochGraph`): every cycle rationally equivalent to
  zero is the boundary `q_*[div t|_Z]` of a chain `Z` on `X × ℙ¹` whose members dominate `ℙ¹`
  (`a3k_ratAll_bd`);
* an induction on the excess (`IntersectionProductBlochExcess`): excess `0` against `V × ℙ¹`,
  `V × {0}` and `V × {1}` is the position `a3o_Good` (`a3k_good_of_excessLE_zero`).

The relative moving step `a3k_Step` follows (`a3k_step_of_homotopy`,
`IntersectionProductBlochHomotopy`) from Bloch's homotopy on `X × ℙ¹ × ℙ¹` and `∂∂ = 0` for
two-parameter chains in square position (`a3k_bd_bd`, `IntersectionProductBlochSquare`). The
homotopy follows from Bloch's homotopy operators by linearity (`a3k_homotopy_of_operators`).
What remains open is the existence of the operators, `a3k_HomotopyOperators` (Roberts'
construction read over `ℙ¹`, with a family of translates over a second `ℙ¹`), stated as
`a3k_homotopyOperators_aux` in `IntersectionProductProofs`.

Source: Fulton, *Intersection Theory*, second edition, §8.2 and §8.3 (the product is
bilinear); Serre, *Algèbre locale, multiplicités*, Chapitre V (bilinear extension of `V · W`).
HC no distance; AV milestone no distance.
-/

open CategoryTheory AlgebraicGeometry

noncomputable section
namespace HodgeLean.Adapters
universe u

/-- The intersection product is subtractive in the first variable. -/
theorem a3e_intersect_sub_left (X : Scheme.{u}) [IsNoetherian X]
    (c c' d : AlgebraicCycle X ℚ) :
    a3i_intersect X (c - c') d = a3i_intersect X c d - a3i_intersect X c' d := by
  classical
  let s := ((a3c_support_finite c).union (a3c_support_finite c')).toFinset
  let t := (a3c_support_finite d).toFinset
  have hs : ∀ u ∉ s, c u = 0 := fun u hu => by
    simp only [s, Set.Finite.mem_toFinset, Set.mem_union, Function.mem_support, not_or,
      not_not] at hu
    exact hu.1
  have hs' : ∀ u ∉ s, c' u = 0 := fun u hu => by
    simp only [s, Set.Finite.mem_toFinset, Set.mem_union, Function.mem_support, not_or,
      not_not] at hu
    exact hu.2
  have hs'' : ∀ u ∉ s, (c - c') u = 0 := fun u hu => by
    rw [Function.locallyFinsuppWithin.coe_sub, Pi.sub_apply, hs u hu, hs' u hu, sub_zero]
  have ht : ∀ v ∉ t, d v = 0 := fun v hv => by simpa [t] using hv
  rw [a3c_intersect_eq_sum X _ d s t hs'' ht, a3c_intersect_eq_sum X c d s t hs ht,
    a3c_intersect_eq_sum X c' d s t hs' ht, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  ext x
  simp only [Function.locallyFinsuppWithin.mapRange_apply, Function.locallyFinsuppWithin.coe_sub,
    Pi.sub_apply]
  ring

example (X : Scheme.{u}) [IsNoetherian X] (c d : AlgebraicCycle X ℚ) :
    a3i_intersect X (c - c) d = 0 := by
  rw [a3e_intersect_sub_left, sub_self]

/-- If `α` and `α'` both meet `β` properly, so does `α − α'`: every component of `α − α'` is a
component of `α` or of `α'`. -/
theorem a3e_cyclesMeetProperly_sub (X : Scheme.{u}) (α α' β : AlgebraicCycle X ℚ)
    (h : a3i_CyclesMeetProperly X α β) (h' : a3i_CyclesMeetProperly X α' β) :
    a3i_CyclesMeetProperly X (α - α') β := by
  intro u v hu hv
  by_cases hα : α u = 0
  · refine h' u v (fun h0 => hu ?_) hv
    rw [Function.locallyFinsuppWithin.coe_sub, Pi.sub_apply, hα, h0, sub_zero]
  · exact h u v hα hv

/-- The reduction of `a3i_intersect_ratEquiv` to cycles rationally equivalent to zero. -/
theorem a3e_intersect_ratEquiv_of_zero (X : Scheme.{u}) [IsNoetherian X]
    (H : ∀ γ β : AlgebraicCycle X ℚ, γ ∈ a3i_ratAll X → a3i_CyclesMeetProperly X γ β →
      a3i_intersect X γ β ∈ a3i_ratAll X)
    (α α' β : AlgebraicCycle X ℚ) (hα : α - α' ∈ a3i_ratAll X)
    (h : a3i_CyclesMeetProperly X α β) (h' : a3i_CyclesMeetProperly X α' β) :
    a3i_intersect X α β - a3i_intersect X α' β ∈ a3i_ratAll X := by
  rw [← a3e_intersect_sub_left]
  exact H _ β hα (a3e_cyclesMeetProperly_sub X α α' β h h')

end HodgeLean.Adapters
