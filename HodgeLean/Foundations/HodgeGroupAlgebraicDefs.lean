import HodgeLean.Foundations.MatrixAlgGroupLieDefs
import HodgeLean.Foundations.HodgeLieAlgebra

/-! # The Hodge group and `G_k` as algebraic `ℚ`-groups (Track G2): definitions (FROZEN)

A rational vector space `V` with a basis `b : Fin n → V` is identified with `ℚⁿ`. A
**`ℚ`-algebraic subgroup** of `GL(V)` is recorded by its complex points: a subgroup of
`GL_n(ℂ)` that is the common zero set of a set of polynomials **with rational coefficients** in
the matrix entries (`g2_ratZeroSet`, `g2_IsRatAlgSubgroup`). This is the `ℚ`-closed subgroup of
Borel's AG.11–12 in characteristic zero. The Lie algebra and connectedness are Track G1's
`g1_lieOfSet` (differentials at `1` of the complex vanishing ideal of the point set) and
`g1_zariski`, applied to the point set.

* `g2_circleAction H hH z`: the action `z ↦ z^(p - q)` of `z ∈ U(1)` on `H (p, q)`, the circle
  part of Deligne's `h`; `g2_circleImage H hH b` its set of matrices in the basis `1 ⊗ b`.
* `g2_hodgeGroup H hH b`: the intersection of all `ℚ`-algebraic subgroups whose complex points
  contain `h(U(1))`. It is computed from `H`; that it is itself a `ℚ`-algebraic subgroup, and
  connected, are statements of the spec, not fields.
* `g2_ratClosure S`: the `ℚ`-Zariski closure of a set of complex points, the zero set of all
  rational polynomials vanishing on it; `g2_galoisOrbit S` the union of its conjugates under all
  field automorphisms of `ℂ`.
* `g2_kCharPoly b J`, `g2_kDetTrace b J d`: `det (x + s + t J)` and the rational polynomial
  `2^(1-m) Σ_j (-d)^(-j) [s^(m-2j) t^(2j)] det (x + s + t J)` (`n = 2m`), which for `x` commuting
  with `J`, `J² = -d`, is `det(x|V₊) + det(x|V₋)`, the trace over `ℚ` of the `k`-determinant.
* `g2_gkEquations b E R J d` and `g2_gkGroup b E R J d`: the explicit rational equations of
  `G_k = Lef ∩ SL_k` (commuting with `R` and `J`, preserving `E`, `det = 1`, trace of the
  `k`-determinant `= 2`) and their complex zero set.
* `g2_HodgeGroupEqGk H hH E R J d`: the group form of the paper's hypothesis (P3), the equality
  of the two point sets in the basis `Module.finBasis ℚ V`.

No definition asserts a group, Lie-algebra, connectedness or Hodge property. HC no distance; AV
milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000

namespace HodgeLean.Foundations

open MvPolynomial
open scoped TensorProduct

variable {n : ℕ}

/-- The complex zero set, inside `GL_n(ℂ)`, of a set of polynomials with **rational**
coefficients in the matrix entries.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.11.1–11.3 (`k`-closed sets of `K`-points,
`k ⊆ K` with `K` algebraically closed) and §1.6 (`GL_n`). -/
def g2_ratZeroSet (S : Set (MvPolynomial (Fin n × Fin n) ℚ)) :
    Set (Matrix.GeneralLinearGroup (Fin n) ℂ) :=
  {g | ∀ f ∈ S, aeval (g1_coords g) f = 0}

example : g2_ratZeroSet (∅ : Set (MvPolynomial (Fin n × Fin n) ℚ)) = Set.univ := by
  simp [g2_ratZeroSet]

/-- A set of complex points of `GL_n` is a **`ℚ`-algebraic subgroup** when it is the zero set of
some rational polynomials and a subgroup.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.12.1 and §1.1 (closed subgroups defined over
`k`; in characteristic zero `k`-closed and defined over `k` agree, AG.14.4). -/
def g2_IsRatAlgSubgroup (G : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)) : Prop :=
  (∃ S : Set (MvPolynomial (Fin n × Fin n) ℚ), G = g2_ratZeroSet S) ∧ (1 : _) ∈ G ∧
    (∀ x ∈ G, ∀ y ∈ G, x * y ∈ G) ∧ ∀ x ∈ G, x⁻¹ ∈ G

example : g2_IsRatAlgSubgroup (Set.univ : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)) :=
  ⟨⟨∅, by simp [g2_ratZeroSet]⟩, trivial, fun _ _ _ _ => trivial, fun _ _ => trivial⟩

/-- The `ℚ`-Zariski closure of a set of complex points: the zero set of all rational polynomials
vanishing on it.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.11.3 (the `k`-closure); Moonen, *An
introduction to Mumford–Tate groups* (2004), §1 (the Hodge group as a `ℚ`-Zariski closure). -/
def g2_ratClosure (S : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)) :
    Set (Matrix.GeneralLinearGroup (Fin n) ℂ) :=
  g2_ratZeroSet {f | ∀ g ∈ S, aeval (g1_coords g) f = 0}

example (S : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)) : S ⊆ g2_ratClosure S :=
  fun g hg _ hf => hf g hg

/-- The union of the conjugates of a set of complex points under all field automorphisms of
`ℂ`, acting on matrix entries.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., AG.14.1–14.4 (the Galois criterion for
rationality of closed sets). -/
def g2_galoisOrbit (S : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)) :
    Set (Matrix.GeneralLinearGroup (Fin n) ℂ) :=
  ⋃ σ : ℂ ≃+* ℂ, Matrix.GeneralLinearGroup.map (σ : ℂ →+* ℂ) '' S

example (S : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)) : S ⊆ g2_galoisOrbit S := by
  intro g hg
  refine Set.mem_iUnion.mpr ⟨RingEquiv.refl ℂ, g, hg, ?_⟩
  ext i j
  simp

section Circle

variable {V : Type*} [AddCommGroup V] [Module ℚ V]
  (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V)) (hH : DirectSum.IsInternal H)

/-- The action of `z ∈ U(1)` on `ℂ ⊗ V`: multiplication by `z^(p - q)` on `H (p, q)`. This is
Deligne's `h` restricted to the unit circle (`z^p z̄^q = z^(p - q)` for `|z| = 1`); its derivative
at `1` along `e^{iθ}` is `gradingOperator H hH`.
Source: Deligne, *Théorie de Hodge II*, Publ. Math. IHÉS 40 (1971), §2.1 (`h : 𝕊 → GL(V_ℝ)`);
Moonen, *An introduction to Mumford–Tate groups* (2004), §1–2 (`h` on `U(1)`). -/
def g2_circleAction (z : Circle) : Module.End ℂ (ℂ ⊗[ℚ] V) :=
  DirectSum.toModule ℂ (ℤ × ℤ) _
      (fun pq => ((z : ℂ) ^ (pq.1 - pq.2)) • (H pq).subtype) ∘ₗ
    (LinearEquiv.ofBijective (DirectSum.coeLinearMap H) hH).symm.toLinearMap

theorem g2_circleAction_apply_of_mem (z : Circle) {p q : ℤ} {x : ℂ ⊗[ℚ] V} (hx : x ∈ H (p, q)) :
    g2_circleAction H hH z x = ((z : ℂ) ^ (p - q)) • x := by
  have h : (LinearEquiv.ofBijective (DirectSum.coeLinearMap H) hH).symm x =
      DirectSum.lof ℂ (ℤ × ℤ) (fun i => H i) (p, q) ⟨x, hx⟩ := by
    rw [LinearEquiv.symm_apply_eq]
    exact (DirectSum.coeLinearMap_of H (p, q) ⟨x, hx⟩).symm
  simp only [g2_circleAction, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, h,
    DirectSum.toModule_lof, LinearMap.smul_apply, Submodule.subtype_apply]

example : g2_circleAction H hH 1 = LinearMap.id :=
  linearMap_ext_of_isInternal hH fun _ _ hx => by
    rw [g2_circleAction_apply_of_mem H hH 1 hx]
    simp

/-- The image `h(U(1))` as matrices in the basis `1 ⊗ b` of `ℂ ⊗ V`: the invertible complex
matrices equal to the matrix of `g2_circleAction H hH z` for some `z ∈ U(1)`.
Source: Moonen, *An introduction to Mumford–Tate groups* (2004), §1–2; Bourbaki, *Algèbre*,
ch. II (matrix of an endomorphism in the base-changed basis). -/
def g2_circleImage (b : Module.Basis (Fin n) ℚ V) : Set (Matrix.GeneralLinearGroup (Fin n) ℂ) :=
  {g | ∃ z : Circle, (g : Matrix (Fin n) (Fin n) ℂ) =
    LinearMap.toMatrix (Algebra.TensorProduct.basis ℂ b) (Algebra.TensorProduct.basis ℂ b)
      (g2_circleAction H hH z)}

example (b : Module.Basis (Fin n) ℚ V) : (1 : Matrix.GeneralLinearGroup (Fin n) ℂ) ∈
    g2_circleImage H hH b := by
  refine ⟨1, ?_⟩
  have h1 : g2_circleAction H hH 1 = LinearMap.id :=
    linearMap_ext_of_isInternal hH fun _ _ hx => by
      rw [g2_circleAction_apply_of_mem H hH 1 hx]
      simp
  rw [h1, LinearMap.toMatrix_id]
  rfl

/-- **The Hodge group, constructed.** The intersection of all `ℚ`-algebraic subgroups of
`GL(V)` whose complex points contain `h(U(1))`, as a set of complex points in the basis `1 ⊗ b`.
This is the smallest `ℚ`-algebraic subgroup through which `h|U(1)` factors.
Source: Mumford, *Families of abelian varieties*, Proc. Sympos. Pure Math. 9 (1966), §1 (the
Hodge group); Moonen, *An introduction to Mumford–Tate groups* (2004), §1–2 (`Hg(V)`, the
smallest algebraic `ℚ`-subgroup whose real points contain `h(U(1))`). -/
def g2_hodgeGroup (b : Module.Basis (Fin n) ℚ V) : Set (Matrix.GeneralLinearGroup (Fin n) ℂ) :=
  ⋂₀ {G | g2_IsRatAlgSubgroup G ∧ g2_circleImage H hH b ⊆ G}

example (b : Module.Basis (Fin n) ℚ V) {G : Set (Matrix.GeneralLinearGroup (Fin n) ℂ)}
    (hG : g2_IsRatAlgSubgroup G) (hc : g2_circleImage H hH b ⊆ G) : g2_hodgeGroup H hH b ⊆ G :=
  Set.sInter_subset_of_mem ⟨hG, hc⟩

end Circle

section Gk

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- The entries of `x M - M x`, rational polynomials whose zero set is the centralizer of the
rational matrix `M`.
Source: Borel, *Linear Algebraic Groups*, 2nd ed., §1.7 (centralizers are closed and defined by
linear equations). -/
def g2_commEquations (M : Matrix (Fin n) (Fin n) ℚ) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) ℚ) :=
  g1_varMatrix ℚ n * M.map C - M.map C * g1_varMatrix ℚ n

example (M : Matrix (Fin n) (Fin n) ℚ) :
    g2_commEquations M = g1_varMatrix ℚ n * M.map C - M.map C * g1_varMatrix ℚ n := rfl

/-- `det (x + s · 1 + t · J)`, with `x = (x_ij)` the matrix of variables, as a polynomial in `t`
whose coefficients are polynomials in `s` over the polynomial ring in the `x_ij`.
Source: Bourbaki, *Algèbre*, ch. III, §8 (determinants over a commutative ring); the two-variable
characteristic polynomial separating the eigenspaces of `J`. -/
def g2_kCharPoly (b : Module.Basis (Fin n) ℚ V) (J : Module.End ℚ V) :
    Polynomial (Polynomial (MvPolynomial (Fin n × Fin n) ℚ)) :=
  ((g1_varMatrix ℚ n).map (fun f => (Polynomial.C (Polynomial.C f) :
      Polynomial (Polynomial (MvPolynomial (Fin n × Fin n) ℚ)))) +
    (Polynomial.C Polynomial.X : Polynomial (Polynomial (MvPolynomial (Fin n × Fin n) ℚ))) •
      (1 : Matrix (Fin n) (Fin n) (Polynomial (Polynomial (MvPolynomial (Fin n × Fin n) ℚ)))) +
    (Polynomial.X : Polynomial (Polynomial (MvPolynomial (Fin n × Fin n) ℚ))) •
      (LinearMap.toMatrix b b J).map
        (algebraMap ℚ (Polynomial (Polynomial (MvPolynomial (Fin n × Fin n) ℚ))))).det

example (b : Module.Basis (Fin 0) ℚ V) (J : Module.End ℚ V) : g2_kCharPoly b J = 1 := by
  simp [g2_kCharPoly]

/-- **The trace of the `k`-determinant, as a rational polynomial.** With `n = 2m` and
`c_{a,b}` the coefficient of `s^a t^b` in `det (x + s + t J)`, it is
`2^(1-m) Σ_{2j ≤ m} (-d)^(-j) c_{m-2j, 2j}`. For `J² = -d`, `d > 0`, and `x` commuting with `J`,
writing `V_ℂ = V₊ ⊕ V₋` for the `±i√d`-eigenspaces (each of dimension `m`),
`det (x + s + t J) = det(x₊ + w) det(x₋ + w̄)` with `w = s + i√d t`, `w̄ = s - i√d t`; the
coefficients of `w^m` and `w̄^m` are `det x₋` and `det x₊`, and their sum is this polynomial.
Source: Bourbaki, *Algèbre*, ch. III, §9 (the norm and trace of a determinant over an étale
algebra); Shimura, *Arithmetic of unitary groups*, Ann. of Math. 79 (1964), §1 (`SU(h)` inside
`U(h)` over an imaginary quadratic field, `k`-determinant 1). -/
def g2_kDetTrace (b : Module.Basis (Fin n) ℚ V) (J : Module.End ℚ V) (d : ℚ) :
    MvPolynomial (Fin n × Fin n) ℚ :=
  ∑ j ∈ Finset.range (n / 2 / 2 + 1),
    C (2 / 2 ^ (n / 2) / (-d) ^ j) * ((g2_kCharPoly b J).coeff (2 * j)).coeff (n / 2 - 2 * j)

example (b : Module.Basis (Fin 2) ℚ V) (J : Module.End ℚ V) (d : ℚ) :
    g2_kDetTrace b J d = C 1 * ((g2_kCharPoly b J).coeff 0).coeff 1 := by
  simp [g2_kDetTrace]

/-- **The equations of `G_k = Lef ∩ SL_k`.** In the basis `b`: the entries of `x [r] - [r] x`
for every `r ∈ R` and of `x [J] - [J] x` (the centralizer of `R` and `J`), the entries of
`xᵀ [E] x - [E]` (isometries of `E`), `det x - 1`, and `g2_kDetTrace b J d - 2`. With
`det x = det x₊ · det x₋` the last two say `det x₊ = det x₋ = 1`, i.e. `k`-determinant `1`.
Source: PW v0.3, Subsection 2.3 (`G_k(A) = Lef(A) ∩ SL_k(V)`, `Lef(A)` the centralizer of `L` in
`Sp(V, E)`); Murty, *Hodge and Weil classes on abelian varieties*, §3 (the Lefschetz group);
Borel, *Linear Algebraic Groups*, 2nd ed., §1.6 (classical groups by equations). -/
def g2_gkEquations (b : Module.Basis (Fin n) ℚ V) (E : LinearMap.BilinForm ℚ V)
    (R : Subalgebra ℚ (Module.End ℚ V)) (J : Module.End ℚ V) (d : ℚ) :
    Set (MvPolynomial (Fin n × Fin n) ℚ) :=
  {f | ∃ r ∈ R, ∃ i j, f = g2_commEquations (LinearMap.toMatrix b b r) i j} ∪
    {f | ∃ i j, f = g2_commEquations (LinearMap.toMatrix b b J) i j} ∪
    {f | ∃ i j, f = g1_isometryEquations (LinearMap.BilinForm.toMatrix b E) i j} ∪
    {(g1_varMatrix ℚ n).det - 1, g2_kDetTrace b J d - 2}

example (b : Module.Basis (Fin n) ℚ V) (E : LinearMap.BilinForm ℚ V)
    (R : Subalgebra ℚ (Module.End ℚ V)) (J : Module.End ℚ V) (d : ℚ) :
    (g1_varMatrix ℚ n).det - 1 ∈ g2_gkEquations b E R J d :=
  Or.inr (Or.inl rfl)

/-- **`G_k`, constructed by equations**: the complex zero set of `g2_gkEquations`.
Source: PW v0.3, Subsection 2.3 (`G_k(A) = Lef(A) ∩ SL_k(V)`); Borel, *Linear Algebraic
Groups*, 2nd ed., AG.11.3 (the `K`-points of a `k`-closed set). -/
def g2_gkGroup (b : Module.Basis (Fin n) ℚ V) (E : LinearMap.BilinForm ℚ V)
    (R : Subalgebra ℚ (Module.End ℚ V)) (J : Module.End ℚ V) (d : ℚ) :
    Set (Matrix.GeneralLinearGroup (Fin n) ℂ) :=
  g2_ratZeroSet (g2_gkEquations b E R J d)

example (b : Module.Basis (Fin n) ℚ V) (E : LinearMap.BilinForm ℚ V)
    (R : Subalgebra ℚ (Module.End ℚ V)) (J : Module.End ℚ V) (d : ℚ)
    (g : Matrix.GeneralLinearGroup (Fin n) ℂ) (hg : g ∈ g2_gkGroup b E R J d) :
    aeval (g1_coords g) ((g1_varMatrix ℚ n).det - 1) = 0 :=
  hg _ (Or.inr (Or.inl rfl))

/-- **The group form of the paper's hypothesis (P3), `Hg(A) = G_k(A)`**: equality of the point
sets of the constructed Hodge group and of `G_k`, in the basis `Module.finBasis ℚ V`. It states
no conclusion of Theorem 4.2 and is not tagged.
Source: PW v0.3, Theorem 4.2, hypothesis `Hg(A) = G_k(A)`; Moonen, *An introduction to
Mumford–Tate groups* (2004), §1–2. -/
def g2_HodgeGroupEqGk [FiniteDimensional ℚ V] (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V))
    (hH : DirectSum.IsInternal H) (E : LinearMap.BilinForm ℚ V)
    (R : Subalgebra ℚ (Module.End ℚ V)) (J : Module.End ℚ V) (d : ℚ) : Prop :=
  g2_hodgeGroup H hH (Module.finBasis ℚ V) = g2_gkGroup (Module.finBasis ℚ V) E R J d

example [FiniteDimensional ℚ V] (H : ℤ × ℤ → Submodule ℂ (ℂ ⊗[ℚ] V))
    (hH : DirectSum.IsInternal H) (E : LinearMap.BilinForm ℚ V)
    (R : Subalgebra ℚ (Module.End ℚ V)) (J : Module.End ℚ V) (d : ℚ) :
    g2_HodgeGroupEqGk H hH E R J d ↔
      g2_hodgeGroup H hH (Module.finBasis ℚ V) = g2_gkGroup (Module.finBasis ℚ V) E R J d :=
  Iff.rfl

end Gk

end HodgeLean.Foundations
