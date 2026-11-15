import HodgeLean.Foundations.Program.CodifferentialComparisonProofs

/-! # B6-6 stage 6e at the G32 centre: the codifferential comparison

Implication, for a family `D : b65z_SharedFamily (b65z_centre p) g` at the G32 centre with a
Nielsen tuple, a compatible rational marking `m` at `b65z_s₀ (b65z_centre p)`, a 5c record
`O : b65p_Outputs p`, full kernels near `θ = 0` and a cover-dictionary comparison of the 5d array
with the residue array of eigen-direction frames, to the premise `codiff` of the G32-centre
Theorem A wrappers for the certified array `b65e_numerator p O.residue` along `b65p_curve p`:
eventually near `0`, `J θ = L * D(b65z_period D s₀ m)(b65p_curve p θ) * T` with `L`, `T` units.
Since `L` and `T` are arbitrary units at each `θ`, this is pointwise rank equivalence of `J θ`
with the period derivative, not an analytic comparison; the routes use it only to transfer rank
nine to the period map.

Four statements (prefix `b66f_`):
* `b66f_multiplication_transport`: changing the two primitive three-frames by `P`, `R` changes
  the residue array by `b66e_productChange P R` (the 6e preparation, at an arbitrary centre);
* `b66f_polarized_matrix`: period-normalized frames in the two eigen-directions exist at every
  parameter, and their residue array is the marked period derivative after the explicit output
  unit `b66m_leftMatrix` (stage 6d, at an arbitrary centre and Nielsen tuple);
* `b66f_direction_change`: two independent triples in the same eigen-direction differ by a unit;
* `b66f_numerator_codiff`: the assembly. Its conclusion is the body of the wrappers' `codiff`
  binder with `jet := b65e_numerator p O.residue` and the supplier marking `m₀` replaced by any
  compatible marking `m` (a consumer check below instantiates it at a chosen marking).

Not claimed here: full kernels (`hker`) and the dictionary comparison (`hdict`) are explicit
binders. Their planned suppliers are the geometric 5d statements on `spec/b65dg`, whose
auxiliaries are open (`b65g_cover_solutions_aux`, `b65g_dictionary_aux`, `b65g_full_kernels_aux`,
…), followed by a later stage: realizing the dictionary forms as primitive chart forms,
eigen-direction compatibility and the residue normalization. No statement removes `codiff` from
the wrappers, and none constructs the supplier marking. HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Filter Topology Manifold HodgeLean.Papers
open scoped TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] Classical.propDecidable
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.totalChart
  b65z_SharedFamily.totalMan b65z_SharedFamily.fibreChart b65z_SharedFamily.fibreMan
  b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact b65z_SharedFamily.fibreConnected
  b65z_SharedFamily.fibreFaithful

/-- **Frame change of the residue array.** Changing the two primitive three-frames by the
columns of `P` and `R` changes the residue multiplication array by the ordered product change
`K(P, R)`, on a family about any centre.
Source: Forster, Lectures on Riemann Surfaces, §17, bilinearity of residue duality;
`b66e_multiplication_transport` (the same statement at `mr_base`). -/
theorem b66f_multiplication_transport {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (q r : Fin 3 → b66f_primitiveForms D t)
    (P R : Matrix (Fin 3) (Fin 3) ℂ)
    (S : Fin 10 → Finset D.C) (v : Fin 10 → b66f_Index D → ℂ → ℂ)
    (hmero : ∀ j a z, z ∈ b66f_domain D t a → MeromorphicAt (v j a) z) :
    b66f_multiplicationMatrix D t (b66f_reframe D t q P) (b66f_reframe D t r R) S v =
      b66e_productChange P R * b66f_multiplicationMatrix D t q r S v :=
  b66f_multiplication_transport_aux D t q r P R S v hmero

example := @b66f_multiplication_transport

/-- **Polarized residue array at an arbitrary centre.** For a compatible rational marking at
`s`, every fibre carries six period-normalized primitive forms, three in each eigen-direction,
spanning the primitive forms; for every meromorphic splitting of the ten standard branch
velocities, their residue array is the marked period derivative after the explicit output unit
`b66m_leftMatrix (period t) κ`, `κ = ±(2πi)⁻¹`, with input change `1`.
Source: Griffiths, Periods II, §1; Forster, §17; van Geemen, LNM 1594, §5.10;
`b66m_polarized_matrix` (the same statement at `mr_base` for the retained tuple);
`b65z_period_analytic` (the period function about `c` for a Nielsen tuple). -/
theorem b66f_polarized_matrix {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i))) (D : b65z_SharedFamily c g)
    (s t : b6t_polydisc c)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) s) ≃ₗ[ℚ]
      (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((D.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ c D.C D.hC (b6t_polydisc c) (Subset.refl _)
        s (D.P s) (D.Q s)).baseChange ℚ x y) :
    ∃ (q r : Fin 3 → b66f_primitiveForms D t)
      (ω η : Fin 3 → b3_HolForm ℂ (b65z_fibre c D.C t)) (κ : ℂ),
      (κ = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ ∨
        κ = -(2 * (Real.pi : ℂ) * Complex.I)⁻¹) ∧
      (∀ i, (ω i).val = b66f_chartForm D t (q i).val ∧
        (η i).val = b66f_chartForm D t (r i).val) ∧
      LinearIndependent ℂ (fun ij : Fin 2 × Fin 3 => if ij.1 = 0 then q ij.2 else r ij.2) ∧
      Submodule.span ℂ (Set.range (fun ij : Fin 2 × Fin 3 =>
        if ij.1 = 0 then q ij.2 else r ij.2)) = ⊤ ∧
      (∀ (i : Fin 3) (x : b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) s),
        (b63e_transportMap c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.P s t x).val (ω i) =
            b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x))
              (b60_frame (b65z_period D s m t.val) (0, i)) ∧
        (b63e_transportMap c D.C D.hC (b6t_polydisc c) (Subset.refl _) D.P s t x).val (η i) =
            b60_E.baseChange ℂ (b64b_complexMarking _ m (1 ⊗ₜ[ℤ] x))
              (b60_frame (b65z_period D s m t.val) (1, i))) ∧
      IsUnit (b66m_leftMatrix (b65z_period D s m t.val) κ) ∧
      ∀ (S : Fin 10 → Finset D.C) (v : Fin 10 → b66f_Index D → ℂ → ℂ)
      (_hmero : ∀ j a z, z ∈ b66f_domain D t a → MeromorphicAt (v j a) z)
      (_hreg : ∀ j a z, z ∈ b66f_domain D t a →
        ((D.atlas.A a).symm (t.val, z)).2 ∉ S j → AnalyticAt ℂ (v j a) z)
      (_hv : ∀ j a b x, x ∉ S j → (t, x) ∈ (D.atlas.A a).source →
        (t, x) ∈ (D.atlas.A b).source →
        b66f_cocycle D t (Pi.single j 1) a b x = b66f_boundary D t (v j) a b x),
        b66f_multiplicationMatrix D t q r S v =
          b66m_leftMatrix (b65z_period D s m t.val) κ *
            LinearMap.toMatrix' (fderiv ℂ (b65z_period D s m) t.val).toLinearMap *
              (1 : Matrix (Fin 10) (Fin 10) ℂ) :=
  b66f_polarized_matrix_aux hg D s t m hJ hpol

example := @b66f_polarized_matrix

/-- **Change within an eigen-direction.** For a compatible marking, two linearly independent
triples of primitive forms in the same eigen-direction differ by an invertible coordinate change:
the primitive forms in a direction are the span of the three normalized forms of
`b66f_polarized_matrix`, since periods determine primitive forms and the six functionals
`x ↦ E(m x, b60_frame (period t) (k, i))` are independent.
Source: Riemann bilinear relations (Griffiths–Harris, Principles of Algebraic Geometry, §2.2);
`b66f_polarized_matrix`; Mathlib `LinearIndependent` and `Module.Basis`. -/
theorem b66f_direction_change {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i))) (D : b65z_SharedFamily c g)
    (s t : b6t_polydisc c)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice c D.C D.hC (b6t_polydisc c) (Subset.refl _) s) ≃ₗ[ℚ]
      (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((D.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ c D.C D.hC (b6t_polydisc c) (Subset.refl _)
        s (D.P s) (D.Q s)).baseChange ℚ x y)
    (k : Fin 2) (q q' : Fin 3 → b66f_primitiveForms D t)
    (hq : ∀ i, (q i).val ∈ b66f_direction D s t m k)
    (hq' : ∀ i, (q' i).val ∈ b66f_direction D s t m k)
    (hli : LinearIndependent ℂ q) (hli' : LinearIndependent ℂ q') :
    ∃ P : Matrix (Fin 3) (Fin 3) ℂ, IsUnit P ∧ q' = b66f_reframe D t q P :=
  b66f_direction_change_aux hg D s t m hJ hpol k q q' hq hq' hli hli'

example := @b66f_direction_change

/-- **The codifferential comparison at the G32 centre.** For a family at the G32 centre with a
Nielsen tuple and a compatible marking `m` at the centre: if near `θ = 0` the 5d frames solve the
full systems (`hker`) and the 5d array is, up to units, the residue array of independent
eigen-direction frames on the fibre over `b65p_curve p θ` (`hdict`), then near `0` the certified
array `b65e_numerator p O.residue` is the derivative of `b65z_period D s₀ m` at `b65p_curve p θ`
up to units on both sides. The conclusion is the body of the wrappers' `codiff` binder with
`jet := b65e_numerator p O.residue` and `m` in place of the supplier marking.
Source: G32 v0.16, Lemma 5.1 (Codifferential), Lemma 5.8 and Proposition 5.9;
Frediani–Ghigi–Penegini, IMRN 2015, §§2–3; `b65e_certified_numMatrix`;
`b66f_polarized_matrix`, `b66f_direction_change`, `b66f_multiplication_transport`;
`b66e_productChange_unit`. -/
theorem b66f_numerator_codiff (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    {g : Fin 13 → b4b_Group} (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i)))
    (D : b65z_SharedFamily (b65z_centre p) g)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice (b65z_centre p) D.C D.hC
      (b6t_polydisc (b65z_centre p)) (Subset.refl _) (b65z_s₀ (b65z_centre p))) ≃ₗ[ℚ]
        (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ y, m ((D.A (b65z_s₀ (b65z_centre p))).baseChange ℚ y) =
      b60_omega.baseChange ℚ (m y))
    (hpair : ∀ y z, b60_E.baseChange ℚ (m y) (m z) =
      (b63e_singularQ (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _)
        (b65z_s₀ (b65z_centre p)) (D.P (b65z_s₀ (b65z_centre p)))
        (D.Q (b65z_s₀ (b65z_centre p)))).baseChange ℚ y z)
    (hker : ∀ᶠ θ in 𝓝 (0 : ℂ),
      b65q_rFamily p O.residue θ * b65q_rFrame p O.residue θ = 0 ∧
        b65q_qFamily p O.residue θ * b65q_qFrame p O.residue θ = 0)
    (hdict : ∀ᶠ θ in 𝓝 (0 : ℂ), ∃ ht : b65p_curve p θ ∈ b6t_polydisc (b65z_centre p),
      ∃ (q r : Fin 3 → b66f_primitiveForms D ⟨b65p_curve p θ, ht⟩)
        (S : Fin 10 → Finset D.C) (v : Fin 10 → b66f_Index D → ℂ → ℂ)
        (A : Matrix (Fin 9) (Fin 9) ℂ) (B : Matrix (Fin 10) (Fin 10) ℂ),
        (∀ i, (q i).val ∈
          b66f_direction D (b65z_s₀ (b65z_centre p)) ⟨b65p_curve p θ, ht⟩ m 0) ∧
        (∀ i, (r i).val ∈
          b66f_direction D (b65z_s₀ (b65z_centre p)) ⟨b65p_curve p θ, ht⟩ m 1) ∧
        LinearIndependent ℂ q ∧ LinearIndependent ℂ r ∧
        (∀ j a z, z ∈ b66f_domain D ⟨b65p_curve p θ, ht⟩ a → MeromorphicAt (v j a) z) ∧
        (∀ j a z, z ∈ b66f_domain D ⟨b65p_curve p θ, ht⟩ a →
          ((D.atlas.A a).symm (b65p_curve p θ, z)).2 ∉ S j → AnalyticAt ℂ (v j a) z) ∧
        (∀ j a b x, x ∉ S j → (⟨b65p_curve p θ, ht⟩, x) ∈ (D.atlas.A a).source →
          (⟨b65p_curve p θ, ht⟩, x) ∈ (D.atlas.A b).source →
          b66f_cocycle D ⟨b65p_curve p θ, ht⟩ (Pi.single j 1) a b x =
            b66f_boundary D ⟨b65p_curve p θ, ht⟩ (v j) a b x) ∧
        IsUnit A ∧ IsUnit B ∧
        b65q_numMatrix p O.residue θ =
          A * b66f_multiplicationMatrix D ⟨b65p_curve p θ, ht⟩ q r S v * B) :
    ∀ᶠ θ in 𝓝 (0 : ℂ),
      ∃ L : Matrix (Fin 9) (Fin 9) ℂ,
      ∃ T : Matrix (Fin 10) (Fin 10) ℂ,
        IsUnit L ∧ IsUnit T ∧
        b65e_numerator p O.residue θ = L * LinearMap.toMatrix'
          (fderiv ℂ
            (b65z_period D (b65z_s₀ (b65z_centre p)) m)
            (b65p_curve p θ) :
              (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) * T :=
  b66f_numerator_codiff_aux p O hg D m hJ hpair hker hdict

example := @b66f_numerator_codiff

/-- **Consumer check: the wrappers' binder shape.** For any proof `hm` of the existence of a
compatible marking (the shape of the conclusion of the supplier `b65z_marking_u`), the
assembly at `m₀ := Classical.choose hm` gives the `codiff` binder of the G32-centre wrappers,
`let` included, with `jet := b65e_numerator p O.residue`. This checks the shape only; it takes
the premises `hker` and `hdict` at `m₀` as hypotheses and selects no geometric witness. -/
example (p : Fin 12 → ℂ) (O : b65p_Outputs p)
    {g : Fin 13 → b4b_Group} (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i)))
    (D : b65z_SharedFamily (b65z_centre p) g)
    (hm : ∃ m : (ℚ ⊗[ℤ] b63l_parameterLattice (b65z_centre p) D.C D.hC
        (b6t_polydisc (b65z_centre p)) (Subset.refl _) (b65z_s₀ (b65z_centre p))) ≃ₗ[ℚ]
          (ℚ ⊗[ℤ] b60_Lattice),
      (∀ y, m ((D.A (b65z_s₀ (b65z_centre p))).baseChange ℚ y) =
        b60_omega.baseChange ℚ (m y)) ∧
      ∀ y z, b60_E.baseChange ℚ (m y) (m z) =
        (b63e_singularQ (b65z_centre p) D.C D.hC (b6t_polydisc (b65z_centre p)) (Subset.refl _)
          (b65z_s₀ (b65z_centre p)) (D.P (b65z_s₀ (b65z_centre p)))
          (D.Q (b65z_s₀ (b65z_centre p)))).baseChange ℚ y z)
    (hker : ∀ᶠ θ in 𝓝 (0 : ℂ),
      b65q_rFamily p O.residue θ * b65q_rFrame p O.residue θ = 0 ∧
        b65q_qFamily p O.residue θ * b65q_qFrame p O.residue θ = 0)
    (hdict : ∀ᶠ θ in 𝓝 (0 : ℂ), ∃ ht : b65p_curve p θ ∈ b6t_polydisc (b65z_centre p),
      ∃ (q r : Fin 3 → b66f_primitiveForms D ⟨b65p_curve p θ, ht⟩)
        (S : Fin 10 → Finset D.C) (v : Fin 10 → b66f_Index D → ℂ → ℂ)
        (A : Matrix (Fin 9) (Fin 9) ℂ) (B : Matrix (Fin 10) (Fin 10) ℂ),
        (∀ i, (q i).val ∈ b66f_direction D (b65z_s₀ (b65z_centre p)) ⟨b65p_curve p θ, ht⟩
          (Classical.choose hm) 0) ∧
        (∀ i, (r i).val ∈ b66f_direction D (b65z_s₀ (b65z_centre p)) ⟨b65p_curve p θ, ht⟩
          (Classical.choose hm) 1) ∧
        LinearIndependent ℂ q ∧ LinearIndependent ℂ r ∧
        (∀ j a z, z ∈ b66f_domain D ⟨b65p_curve p θ, ht⟩ a → MeromorphicAt (v j a) z) ∧
        (∀ j a z, z ∈ b66f_domain D ⟨b65p_curve p θ, ht⟩ a →
          ((D.atlas.A a).symm (b65p_curve p θ, z)).2 ∉ S j → AnalyticAt ℂ (v j a) z) ∧
        (∀ j a b x, x ∉ S j → (⟨b65p_curve p θ, ht⟩, x) ∈ (D.atlas.A a).source →
          (⟨b65p_curve p θ, ht⟩, x) ∈ (D.atlas.A b).source →
          b66f_cocycle D ⟨b65p_curve p θ, ht⟩ (Pi.single j 1) a b x =
            b66f_boundary D ⟨b65p_curve p θ, ht⟩ (v j) a b x) ∧
        IsUnit A ∧ IsUnit B ∧
        b65q_numMatrix p O.residue θ =
          A * b66f_multiplicationMatrix D ⟨b65p_curve p θ, ht⟩ q r S v * B) :
    let m₀ := Classical.choose hm
    ∀ᶠ θ in 𝓝 (0 : ℂ),
      ∃ L : Matrix (Fin 9) (Fin 9) ℂ,
      ∃ T : Matrix (Fin 10) (Fin 10) ℂ,
        IsUnit L ∧ IsUnit T ∧
        b65e_numerator p O.residue θ = L * LinearMap.toMatrix'
          (fderiv ℂ
            (b65z_period D (b65z_s₀ (b65z_centre p)) m₀)
            (b65p_curve p θ) :
              (Fin 10 → ℂ) →ₗ[ℂ] Fin 9 → ℂ) * T :=
  b66f_numerator_codiff p O hg D (Classical.choose hm) (Classical.choose_spec hm).1
    (Classical.choose_spec hm).2 hker hdict

/-- **The jet slot is certified.** The array placed in the `jet` slot of the wrappers is a
certified jet, so the wrappers' `jet_certified` premise holds for it (`b65e_certified`). -/
example (p : Fin 12 → ℂ) (O : b65p_Outputs p) :
    HodgeLean.Papers.g32r_CertifiedJet (b65e_numerator p O.residue) := b65e_certified p O

/-- **Non-degeneracy of the comparison factors.** The ordered product change of two units is a
unit (`b66e_productChange_unit`), and the doubled identity frame change gives the entry `4` on
the diagonal, so `K(P, R)` is not the identity for every pair of units. -/
example : IsUnit (b66e_productChange (2 : Matrix (Fin 3) (Fin 3) ℂ) 2) ∧
    b66e_productChange (2 : Matrix (Fin 3) (Fin 3) ℂ) 2 0 0 = 4 := by
  have h2 : IsUnit (2 : Matrix (Fin 3) (Fin 3) ℂ) := by
    have h : (2 : Matrix (Fin 3) (Fin 3) ℂ) = Matrix.scalar (Fin 3) (2 : ℂ) := by
      ext i j; simp [Matrix.ofNat_apply, Matrix.diagonal_apply]
    rw [h]
    exact (IsUnit.mk0 (2 : ℂ) two_ne_zero).map (Matrix.scalar (Fin 3))
  refine ⟨b66e_productChange_unit _ _ h2 h2, ?_⟩
  simp only [b66e_productChange, Matrix.ofNat_apply]
  norm_num

/-- **A nonzero residue sum.** On every family, fibre and point `x`, the residue sum over `{x}`
of the splitting `z ↦ (z - z₀)⁻¹` in the chart centred at `x` (`z₀` the coordinate of `x`)
against the constant coefficient `1` is `1` (the residue of a simple pole, by `simp`). So the
residue sum of these definitions, and with it the residue array, is not identically zero. -/
example {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group} (D : b65z_SharedFamily c g)
    (t : b6t_polydisc c) (x : D.C) :
    b66f_residueSum D t {x} (fun _ z => (z - (D.atlas.A (t, x) (t, x)).2)⁻¹) 1 = 1 := by
  simp [b66f_residueSum]

section retained
attribute [local instance] rf8_SharedFamily.topC rf8_SharedFamily.chartC
  rf8_SharedFamily.manC rf8_SharedFamily.t2C rf8_SharedFamily.compactC
  rf8_SharedFamily.connectedC rf8_SharedFamily.actionC rf8_SharedFamily.totalChart
  rf8_SharedFamily.totalMan rf8_SharedFamily.fibreChart rf8_SharedFamily.fibreMan
  rf8_SharedFamily.fibreT2 rf8_SharedFamily.fibreCompact rf8_SharedFamily.fibreConnected
  rf8_SharedFamily.fibreFaithful

/-- **Independent forms in opposite directions on a retained family.** For a retained family and
a compatible marking at `s`, the normalized triples of stage 6d (`b66m_polarized_matrix`, with
body) are primitive forms of `b65z_ofRetained R` lying in directions `0` and `1` of
`b66f_direction` (coefficients `Pi.single i 1`), each triple independent and the six forms
jointly independent. No open statement is used. -/
example (R : rf8_SharedFamily) (s t : b6t_polydisc mr_base)
    (m : (ℚ ⊗[ℤ] b63l_parameterLattice mr_base R.C R.hC (b6t_polydisc mr_base)
      (Subset.refl _) s) ≃ₗ[ℚ] (ℚ ⊗[ℤ] b60_Lattice))
    (hJ : ∀ x, m ((R.A s).baseChange ℚ x) = b60_omega.baseChange ℚ (m x))
    (hpol : ∀ x y, b60_E.baseChange ℚ (m x) (m y) =
      (b63e_singularQ mr_base R.C R.hC (b6t_polydisc mr_base) (Subset.refl _)
        s (R.P s) (R.Q s)).baseChange ℚ x y) :
    ∃ q r : Fin 3 → b66f_primitiveForms (b65z_ofRetained R) t,
      (∀ i, (q i).val ∈ b66f_direction (b65z_ofRetained R) s t m 0) ∧
      (∀ i, (r i).val ∈ b66f_direction (b65z_ofRetained R) s t m 1) ∧
      LinearIndependent ℂ q ∧ LinearIndependent ℂ r ∧
      LinearIndependent ℂ (fun ij : Fin 2 × Fin 3 => if ij.1 = 0 then q ij.2 else r ij.2) := by
  obtain ⟨q, r, ω, η, -, -, hω, hli, -, hper, -⟩ := b66m_polarized_matrix R s t m hJ hpol
  have hsum : ∀ (i : Fin 3) (F : Fin 3 → ℂ), ∑ a, (Pi.single i (1 : ℂ) : Fin 3 → ℂ) a * F a = F i := by
    intro i F
    simp [Pi.single_apply]
  refine ⟨q, r, fun i => ⟨ω i, (hω i).1, Pi.single i (1 : ℂ), fun x => ?_⟩,
    fun i => ⟨η i, (hω i).2, Pi.single i (1 : ℂ), fun x => ?_⟩, ?_, ?_, hli⟩
  · rw [hsum i]
    exact (hper i x).1
  · rw [hsum i]
    exact (hper i x).2
  · have h := hli.comp (fun i : Fin 3 => ((0 : Fin 2), i)) (fun a b hab => by simpa using hab)
    have he : ((fun ij : Fin 2 × Fin 3 => if ij.1 = 0 then q ij.2 else r ij.2) ∘
        fun i : Fin 3 => ((0 : Fin 2), i)) = q := by
      funext i
      simp
    rw [he] at h
    exact h
  · have h := hli.comp (fun i : Fin 3 => ((1 : Fin 2), i)) (fun a b hab => by simpa using hab)
    have he : ((fun ij : Fin 2 × Fin 3 => if ij.1 = 0 then q ij.2 else r ij.2) ∘
        fun i : Fin 3 => ((1 : Fin 2), i)) = r := by
      funext i
      simp
    rw [he] at h
    exact h

end retained

end HodgeLean.Foundations.Program
