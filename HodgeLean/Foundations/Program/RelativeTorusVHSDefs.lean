import HodgeLean.Foundations.Program.GaussManinToriB2

/-!
# The cohomology variation of a B2 torus family: definitions

B2's torus of a lattice `Λ` with filtration `F` is `((ℂ ⊗ Λ) ⧸ F) ⧸ Λ`, so `Λ` plays the role of
`H₁(X, ℤ)` and `(ℂ ⊗ Λ) ⧸ F` that of the tangent space `T₀X`.  The cohomology of the fibre is
the rational dual `H¹(X, ℚ) = Hom(Λ, ℚ)`, its Hodge line `F¹ = H^{1,0}` is the annihilator of `F`
(the forms on `ℂ ⊗ Λ` that factor through `T₀X`), and its polarization is the form dual to the
Riemann form.

These definitions construct, from B2's data:
* the fibrewise objects: the dual `Hom(Λ, ℚ)`, the complexified evaluation pairing, the
  annihilator line `b2b_hodgeOne`, the weight-one filtration `b2b_filtration`, the dual form
  `b2b_dualForm`;
* the contragredient local system `b2b_dualLocalSystem L` of a lattice local system;
* the constructor `b2b_mkVHS`, which assembles a `d1_PolarizedVHS` from the three properties of
  the data; the frozen `b2b_vhs` supplies them;
* the derivative of the Hodge filtration in flat coordinates over a simply connected set, read
  as a map `T_b B → Hom(F¹_b, H¹_b ⧸ F¹_b)`: the Kodaira--Spencer map `b2b_kodairaSpencer`;
* the marked identification `Hom(ℤ^{2g}, ℚ) ≃ ℚ^{2g}` and the isomorphism predicate
  `b2b_IsVHSIso` used to compare with D2.
-/

noncomputable section

open CategoryTheory Manifold
open scoped TensorProduct ContDiff Matrix

namespace HodgeLean.Foundations.Program

open HodgeBlocks

/-! ## Fibrewise cohomology of a lattice -/

section Fibre

variable (Λ : Type) [AddCommGroup Λ]

/-- The rational cohomology `H¹ = Hom(Λ, ℚ)` of the torus whose first homology is `Λ`.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §1.1 and §1.3; Hatcher,
*Algebraic Topology*, §3.1 (universal coefficients). -/
abbrev b2b_dual : Type := Λ →ₗ[ℤ] ℚ

example (φ : b2b_dual Λ) (x : Λ) : ℚ := φ x

/-- A rational form on `Λ`, extended to a `ℂ`-linear form on `ℂ ⊗[ℤ] Λ`.
Source: Bourbaki, *Algèbre*, ch. II, §5 (extension of scalars); Mathlib
`LinearMap.liftBaseChange`. -/
def b2b_cplxForm : b2b_dual Λ →ₗ[ℚ] Module.Dual ℂ (ℂ ⊗[ℤ] Λ) where
  toFun φ := LinearMap.liftBaseChange ℂ ((Algebra.linearMap ℚ ℂ).restrictScalars ℤ ∘ₗ φ)
  map_add' φ ψ := by
    ext x
    simp
  map_smul' c φ := by
    ext x
    simp [Algebra.smul_def, mul_comm]

example (φ : b2b_dual Λ) (c : ℂ) (x : Λ) :
    b2b_cplxForm Λ φ (c ⊗ₜ x) = c * (φ x : ℂ) := by
  simp [b2b_cplxForm]

/-- The evaluation pairing of complex cohomology `ℂ ⊗[ℚ] Hom(Λ, ℚ)` with complex homology
`ℂ ⊗[ℤ] Λ`.
Source: Hatcher, *Algebraic Topology*, §3.1 (the evaluation pairing); Birkenhake--Lange, §1.4. -/
def b2b_pairing : ℂ ⊗[ℚ] b2b_dual Λ →ₗ[ℂ] Module.Dual ℂ (ℂ ⊗[ℤ] Λ) :=
  LinearMap.liftBaseChange ℂ (b2b_cplxForm Λ)

example (φ : b2b_dual Λ) (x : Λ) :
    b2b_pairing Λ ((1 : ℂ) ⊗ₜ φ) ((1 : ℂ) ⊗ₜ x) = (φ x : ℂ) := by
  simp [b2b_pairing, b2b_cplxForm]

/-- **The Hodge line** `F¹ = H^{1,0}` of the torus `((ℂ ⊗ Λ) ⧸ F) ⧸ Λ`: the annihilator of `F`
under the evaluation pairing, the forms that factor through `(ℂ ⊗ Λ) ⧸ F`.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §1.4; Griffiths, *Periods of
integrals on algebraic manifolds I*, Amer. J. Math. 90 (1968), §2. -/
def b2b_hodgeOne (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) : Submodule ℂ (ℂ ⊗[ℚ] b2b_dual Λ) :=
  F.dualAnnihilator.comap (b2b_pairing Λ)

example (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (c : ℂ ⊗[ℚ] b2b_dual Λ) :
    c ∈ b2b_hodgeOne Λ F ↔ ∀ x ∈ F, b2b_pairing Λ c x = 0 :=
  Submodule.mem_dualAnnihilator _

variable {Λ} in
open scoped Classical in
/-- The weight-one filtration `F⁰ = H¹`, `F¹ = G`, `F² = 0` with a prescribed line `G`.
Source: Deligne, *Théorie de Hodge II*, Publ. Math. IHES 40 (1971), §1.2; Griffiths, Amer. J.
Math. 90 (1968), §2. -/
def b2b_weightOne {H : Type*} [AddCommGroup H] [Module ℂ H] (G : Submodule ℂ H) :
    ℤ → Submodule ℂ H :=
  fun p ↦ if p ≤ 0 then ⊤ else if p = 1 then G else ⊥

example {H : Type*} [AddCommGroup H] [Module ℂ H] (G : Submodule ℂ H) :
    b2b_weightOne G 1 = G := by
  simp [b2b_weightOne]

/-- The Hodge filtration of `H¹` of the torus: `b2b_weightOne` of the annihilator line.
Source: Birkenhake--Lange, §1.4; Deligne, *Théorie de Hodge II*, §4.4 (weight one and complex
tori). -/
def b2b_filtration (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) : ℤ → Submodule ℂ (ℂ ⊗[ℚ] b2b_dual Λ) :=
  b2b_weightOne (b2b_hodgeOne Λ F)

example (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) : b2b_filtration Λ F 2 = ⊥ := by
  simp [b2b_filtration, b2b_weightOne]

/-- The map `ℚ ⊗ Λ → Hom(Λ, ℚ)`, `u ↦ Q(u, ·)`, of an integral bilinear form.
Source: Birkenhake--Lange, §1.2 and §4.1; Bourbaki, *Algèbre*, ch. IX, §1. -/
def b2b_flat (Q : LinearMap.BilinForm ℤ Λ) : ℚ ⊗[ℤ] Λ →ₗ[ℚ] b2b_dual Λ :=
  LinearMap.liftBaseChange ℚ (Q.compr₂ (Algebra.linearMap ℤ ℚ))

example (Q : LinearMap.BilinForm ℤ Λ) (u v : Λ) :
    b2b_flat Λ Q ((1 : ℚ) ⊗ₜ u) v = (Q u v : ℚ) := by
  simp [b2b_flat]

open scoped Classical in
/-- **The polarization of `H¹` dual to an integral form** `Q`: when `u ↦ Q(u, ·)` is an
isomorphism `ℚ ⊗ Λ ≃ Hom(Λ, ℚ)`, the form `Q^∨(φ, ψ) = Q_ℚ(u_φ, u_ψ)` with `φ = Q(u_φ, ·)`, so
that `Q^∨(Q(u, ·), Q(v, ·)) = Q(u, v)`; otherwise `0`.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, 2nd ed., §4.1--§4.2 (the dual
polarization); Griffiths--Harris, *Principles of Algebraic Geometry*, ch. 2, §6. -/
def b2b_dualForm (Q : LinearMap.BilinForm ℤ Λ) : LinearMap.BilinForm ℚ (b2b_dual Λ) :=
  if h : Function.Bijective (b2b_flat Λ Q) then
    (Q.baseChange ℚ).compl₁₂ (LinearEquiv.ofBijective _ h).symm.toLinearMap
      (LinearEquiv.ofBijective _ h).symm.toLinearMap
  else 0

example (Q : LinearMap.BilinForm ℤ Λ) (h : ¬ Function.Bijective (b2b_flat Λ Q)) :
    b2b_dualForm Λ Q = 0 := by
  simp [b2b_dualForm, h]

end Fibre

/-! ## The contragredient local system -/

section LocalSystem

variable {B : Type*} [TopologicalSpace B]

/-- **The rational dual local system** `b ↦ Hom(Λ_b, ℚ)` of a lattice local system, with the
contragredient transport `φ ↦ φ ∘ γ⁻¹`.
Source: Deligne, *Équations différentielles à points singuliers réguliers*, LNM 163, I.1 (dual
local systems); Voisin, *Hodge Theory and Complex Algebraic Geometry I*, ch. 9 (the local system
`R¹f_*ℚ` is dual to `R₁f_*ℚ`). -/
def b2b_dualLocalSystem (L : b2_LatticeLocalSystem B) : d1_LocalSystem B where
  functor :=
    { obj := fun x ↦ ModuleCat.of ℚ (L.functor.obj x →ₗ[ℤ] ℚ)
      map := fun {x y} γ ↦ ModuleCat.ofHom
        (LinearMap.lcomp ℚ ℚ (L.functor.map (Groupoid.inv γ)).hom.toIntLinearMap)
      map_id := fun x ↦ by
        ext φ v
        simp
      map_comp := fun γ δ ↦ by
        ext φ v
        simp }
  finite x := by
    have : Module.Free ℤ (L.functor.obj x) := L.free x
    have : Module.Finite ℤ (L.functor.obj x) := L.finite x
    exact inferInstanceAs (Module.Finite ℚ (L.functor.obj x →ₗ[ℤ] ℚ))

example (L : b2_LatticeLocalSystem B) (b : B) :
    (b2b_dualLocalSystem L).fiber b = b2b_dual (L.fiber b) := rfl

end LocalSystem

/-! ## The polarized variation -/

section VHS

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {B : Type*} [TopologicalSpace B] [ChartedSpace E B]

/-- The cohomology VHS of a B2 family, assembled from the three properties of its data.  The
frozen `b2b_vhs` supplies them; this constructor only fixes the data: the dual local system, weight
one, the annihilator filtration and the dual forms.
Source: Griffiths, Publ. Math. IHES 38 (1970), §§1--3; Deligne, *Théorie de Hodge II*, §4.4. -/
def b2b_mkVHS [IsManifold 𝓘(ℂ, E) ω B] (L : b2_LatticeLocalSystem B)
    (F : ∀ b, Submodule ℂ (L.cFiber b)) (Q : ∀ b, LinearMap.BilinForm ℤ (L.fiber b))
    (hhol : ∀ p, (b2b_dualLocalSystem L).IsHolomorphicSubbundle E
      (fun b ↦ b2b_filtration (L.fiber b) (F b) p))
    (htr : (b2b_dualLocalSystem L).IsTransversal E
      (fun p b ↦ b2b_filtration (L.fiber b) (F b) p))
    (hflat : ∀ (b b' : B) (γ : Path.Homotopic.Quotient b b')
      (x y : (b2b_dualLocalSystem L).fiber b),
      b2b_dualForm (L.fiber b') (Q b') ((b2b_dualLocalSystem L).transport γ x)
        ((b2b_dualLocalSystem L).transport γ y) = b2b_dualForm (L.fiber b) (Q b) x y)
    (hpol : ∀ b, d1_IsPolarizedFiltration 1 (b2b_dualForm (L.fiber b) (Q b))
      (b2b_filtration (L.fiber b) (F b))) :
    d1_PolarizedVHS E B where
  L := b2b_dualLocalSystem L
  weight := 1
  F p b := b2b_filtration (L.fiber b) (F b) p
  Q b := b2b_dualForm (L.fiber b) (Q b)
  holomorphic := hhol
  transversal := htr
  flat := hflat
  polarized := hpol

/-- Two variations over the same base are isomorphic through the fibrewise rational
isomorphisms `e`: the weights agree, `e` commutes with transport, carries the filtration to the
filtration and the form to the form.
Source: Schmid, Invent. Math. 22 (1973), §3; Carlson--Müller-Stach--Peters, *Period Mappings and
Period Domains*, ch. 4 (morphisms of variations). -/
structure b2b_IsVHSIso [IsManifold 𝓘(ℂ, E) ω B] (V W : d1_PolarizedVHS E B)
    (e : ∀ b, V.L.fiber b ≃ₗ[ℚ] W.L.fiber b) : Prop where
  weight : V.weight = W.weight
  transport : ∀ (b b' : B) (γ : Path.Homotopic.Quotient b b') (x : V.L.fiber b),
    e b' (V.L.transport γ x) = W.L.transport γ (e b x)
  filtration : ∀ (p : ℤ) (b : B),
    (V.F p b).map (LinearEquiv.baseChange ℚ ℂ _ _ (e b)).toLinearMap = W.F p b
  form : ∀ (b : B) (x y : V.L.fiber b), W.Q b (e b x) (e b y) = V.Q b x y

example [IsManifold 𝓘(ℂ, E) ω B] (V : d1_PolarizedVHS E B) :
    b2b_IsVHSIso E V V (fun _ ↦ LinearEquiv.refl ℚ _) where
  weight := rfl
  transport _ _ _ _ := rfl
  filtration p b := by
    have : LinearEquiv.baseChange ℚ ℂ _ _ (LinearEquiv.refl ℚ (V.L.fiber b)) =
        LinearEquiv.refl ℂ _ := by
      ext x
      induction x using TensorProduct.inductionOn with
      | tmul c w => rfl
      | add x y hx hy => simp_all
    rw [this]
    exact Submodule.map_id _
  form _ _ _ := rfl

end VHS

/-! ## The derivative of the Hodge filtration -/

section KodairaSpencer

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {B : Type*} [TopologicalSpace B] [ChartedSpace E B]
variable (L : b2_LatticeLocalSystem B) (F : ∀ b, Submodule ℂ (L.cFiber b))

open scoped Classical in
/-- The Hodge line at `c`, transported flatly into the fibre at `b₀` inside the simply connected
set `U`, and the line at `b₀` off `U`: the period map of the family into the Grassmannian of
`H¹_{b₀}`.
Source: Griffiths, Publ. Math. IHES 38 (1970), §1; Carlson--Müller-Stach--Peters, ch. 4. -/
def b2b_periodLine (U : Set B) (hU : IsSimplyConnected U) (b₀ : U) (c : B) :
    Submodule ℂ ((b2b_dualLocalSystem L).cFiber b₀) :=
  if h : c ∈ U then
    (b2b_hodgeOne (L.fiber c) (F c)).map
      ((b2b_dualLocalSystem L).flatTransport U hU ⟨c, h⟩ b₀).toLinearMap
  else b2b_hodgeOne (L.fiber b₀) (F b₀)

example (U : Set B) (hU : IsSimplyConnected U) (b₀ : U) (c : B) (hc : c ∉ U) :
    b2b_periodLine L F U hU b₀ c = b2b_hodgeOne (L.fiber b₀) (F b₀) := by
  exact dite_eq_right_of_eq_false (eq_false hc)

/-- The matrix, in Mathlib's chosen basis of `H¹_{b₀}`, of the projection onto the transported
line at `c` along the conjugate of the line at `b₀`: the affine Grassmannian chart centred at
`F¹_{b₀}`, as in `d1_graphProjection`.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, ch. 1, §5 (Grassmannian charts);
Carlson--Müller-Stach--Peters, ch. 4. -/
def b2b_projMatrix (U : Set B) (hU : IsSimplyConnected U) (b₀ : U) (c : B) :
    Fin (Module.finrank ℂ ((b2b_dualLocalSystem L).cFiber b₀)) →
      Fin (Module.finrank ℂ ((b2b_dualLocalSystem L).cFiber b₀)) → ℂ :=
  LinearMap.toMatrix (Module.finBasis ℂ _) (Module.finBasis ℂ _)
    (d1_graphProjection 1 (b2b_weightOne (b2b_hodgeOne (L.fiber b₀) (F b₀)))
      (b2b_weightOne (b2b_periodLine L F U hU b₀ c)) 1)

example (U : Set B) (hU : IsSimplyConnected U) (b₀ : U) (c : B) :
    Fin (Module.finrank ℂ ((b2b_dualLocalSystem L).cFiber b₀)) →
      Fin (Module.finrank ℂ ((b2b_dualLocalSystem L).cFiber b₀)) → ℂ :=
  b2b_projMatrix L F U hU b₀ c

/-- The derivative at `b₀` of the chart projection, as an endomorphism of `H¹_{b₀}` for each
tangent vector.
Source: Griffiths, Amer. J. Math. 90 (1968), §1; Carlson--Müller-Stach--Peters, ch. 4. -/
def b2b_projDeriv (U : Set B) (hU : IsSimplyConnected U) (b₀ : U) :
    E →ₗ[ℂ] Module.End ℂ ((b2b_dualLocalSystem L).cFiber b₀) :=
  (Matrix.toLin (Module.finBasis ℂ _) (Module.finBasis ℂ _)).toLinearMap ∘ₗ
    (show E →L[ℂ] Matrix (Fin (Module.finrank ℂ ((b2b_dualLocalSystem L).cFiber b₀)))
        (Fin (Module.finrank ℂ ((b2b_dualLocalSystem L).cFiber b₀))) ℂ from
      mfderiv 𝓘(ℂ, E) 𝓘(ℂ, Fin (Module.finrank ℂ ((b2b_dualLocalSystem L).cFiber b₀)) →
        Fin (Module.finrank ℂ ((b2b_dualLocalSystem L).cFiber b₀)) → ℂ)
        (b2b_projMatrix L F U hU b₀) b₀).toLinearMap

example (U : Set B) (hU : IsSimplyConnected U) (b₀ : U) :
    b2b_projDeriv E L F U hU b₀ 0 = 0 := map_zero _

/-- **The Kodaira--Spencer map** `T_{b₀} B → Hom(F¹_{b₀}, H¹_{b₀} ⧸ F¹_{b₀})` of a B2 family: the
derivative of the Hodge filtration (Griffiths).  A vector `φ ∈ F¹_{b₀}` extends to the section
`c ↦ π_c φ` of `F¹`, where `π_c` projects onto `F¹_c` along `\bar F¹_{b₀}` in flat coordinates;
its derivative along `v`, read modulo `F¹_{b₀}`, is the value.
Source: Griffiths, *Periods of integrals on algebraic manifolds I*, Amer. J. Math. 90 (1968),
§1 and Proposition 1.20; Voisin, *Hodge Theory I*, Theorem 10.21; Kodaira, *Complex Manifolds
and Deformation of Complex Structures*, §4.1. -/
def b2b_kodairaSpencer (U : Set B) (hU : IsSimplyConnected U) (b₀ : U) :
    E →ₗ[ℂ] b2b_hodgeOne (L.fiber b₀) (F b₀) →ₗ[ℂ]
      (b2b_dualLocalSystem L).cFiber b₀ ⧸ b2b_hodgeOne (L.fiber b₀) (F b₀) :=
  LinearMap.lcomp ℂ _ (b2b_hodgeOne (L.fiber b₀) (F b₀)).subtype ∘ₗ
    LinearMap.llcomp ℂ _ _ _ (b2b_hodgeOne (L.fiber b₀) (F b₀)).mkQ ∘ₗ
      b2b_projDeriv E L F U hU b₀

example (U : Set B) (hU : IsSimplyConnected U) (b₀ : U) (v : E)
    (φ : b2b_hodgeOne (L.fiber b₀) (F b₀)) :
    b2b_kodairaSpencer E L F U hU b₀ v φ =
      (b2b_hodgeOne (L.fiber b₀) (F b₀)).mkQ (b2b_projDeriv E L F U hU b₀ v
        ((b2b_hodgeOne (L.fiber b₀) (F b₀)).subtype φ)) := rfl

end KodairaSpencer

/-! ## Marked coordinates -/

section Marked

variable (g : ℕ)

/-- The marked identification `Hom(ℤ^{2g}, ℚ) ≃ ℚ^{2g}`, `φ ↦ (φ(e_k))_k`.
Source: Bourbaki, *Algèbre*, ch. II, §2.6 (dual bases); Birkenhake--Lange, §1.1. -/
def b2b_markedEquiv : b2b_dual (Fin (2 * g) → ℤ) ≃ₗ[ℚ] (Fin (2 * g) → ℚ) :=
  ((Pi.basisFun ℤ (Fin (2 * g))).constr ℚ).symm

example (φ : b2b_dual (Fin (2 * g) → ℤ)) (k : Fin (2 * g)) :
    b2b_markedEquiv g φ k = φ (Pi.single k 1) := by
  simp [b2b_markedEquiv, Module.Basis.constr_symm_apply]

end Marked

end HodgeLean.Foundations.Program
