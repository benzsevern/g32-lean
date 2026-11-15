import HodgeLean.Foundations.HodgeLieAlgebra
import HodgeLean.Foundations.WeilHermitian
import HodgeLean.Foundations.InvariantsExteriorBlocks

/-!
# Weil powers: transport towards Hodge classes

This develops F-1575's step from (1) to the Hodge classes of `Aᵐ`, at the level of
`⋀ H¹`. The intended Hodge-class conclusion is conditional on an explicit `hSU`,
the Hodge-group input. This file does not identify `⋀ H¹(A)` with `H^*(Aᵐ)`;
that is C7. It does not prove the generating classes algebraic: that needs
F-1569, Lefschetz (1,1), and closure under pullback and products.

Relation to the goal: HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped TensorProduct

namespace HodgeLean.Foundations.WeilPower

/-- The chosen embedding of `√-3` in `ℂ`.
Source: constructed here for the two embeddings of the Weil field. -/
def root : ℂ := Complex.I * (Real.sqrt 3 : ℂ)

theorem root_sq : root ^ 2 = -3 := by
  rw [root, mul_pow, Complex.I_sq, ← Complex.ofReal_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

theorem root_ne_zero : root ≠ 0 := by
  intro h
  have := root_sq
  rw [h] at this
  norm_num at this

@[simp] theorem conj_root : starRingEnd ℂ root = -root := by
  simp [root]

example : root * root = -3 := by simpa [pow_two] using root_sq

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- A square relation with two distinct roots gives the eigenspace splitting.
Source: constructed here by the two spectral projections. -/
theorem isCompl_eigenspaces {J : Module.End ℂ M} {μ : ℂ} (hμ : μ ≠ 0)
    (hJ : ∀ x, J (J x) = μ ^ 2 • x) :
    IsCompl (Module.End.eigenspace J μ) (Module.End.eigenspace J (-μ)) := by
  constructor
  · rw [disjoint_iff]
    apply ((Module.End.eigenspaces_iSupIndep J).pairwiseDisjoint _).eq_bot
    intro h
    apply hμ
    linear_combination h / 2
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    refine Submodule.mem_sup.mpr
      ⟨(1 / (2 * μ)) • (μ • x + J x), ?_,
        (1 / (2 * μ)) • (μ • x - J x), ?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      simp only [map_smul, map_add, hJ, smul_add, smul_smul]
      module
    · rw [Module.End.mem_eigenspace_iff]
      simp only [map_smul, map_sub, hJ, smul_sub, smul_smul]
      module
    · have hs : 1 / (2 * μ) * μ + 1 / (2 * μ) * μ = 1 := by field_simp; ring
      calc
        _ = (1 / (2 * μ) * μ + 1 / (2 * μ) * μ) • x := by module
        _ = x := by rw [hs, one_smul]

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- The two eigenspaces of the rational Weil operator are complementary after base change.
Source: van Geemen, *An introduction to the Hodge conjecture for abelian varieties*, §5–6. -/
theorem isCompl_weilEigenspaces (J : Module.End ℚ V)
    (hJ : J.comp J = (-3 : ℚ) • LinearMap.id) :
    IsCompl (Module.End.eigenspace (J.baseChange ℂ) root)
      (Module.End.eigenspace (J.baseChange ℂ) (-root)) := by
  apply isCompl_eigenspaces root_ne_zero
  intro x
  rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hJ,
    LinearMap.baseChange_smul, LinearMap.baseChange_id, root_sq]
  simpa only [LinearMap.smul_apply, LinearMap.id_apply, map_neg, map_ofNat] using
    (IsScalarTower.algebraMap_smul (R := ℚ) (A := ℂ) (-3 : ℚ) x).symm

/-- Addition identifies the two Weil eigenspaces with the complexification.
Source: constructed here for F-1575's transport, using the spectral splitting. -/
def splitting (J : Module.End ℚ V) (hJ : J.comp J = (-3 : ℚ) • LinearMap.id) :
    (Module.End.eigenspace (J.baseChange ℂ) root ×
      Module.End.eigenspace (J.baseChange ℂ) (-root)) ≃ₗ[ℂ] ℂ ⊗[ℚ] V :=
  Submodule.prodEquivOfIsCompl _ _ (isCompl_weilEigenspaces J hJ)

example (J : Module.End ℚ V) (hJ : J.comp J = (-3 : ℚ) • LinearMap.id)
    (x : Module.End.eigenspace (J.baseChange ℂ) root)
    (y : Module.End.eigenspace (J.baseChange ℂ) (-root)) :
    splitting J hJ (x, y) = (x : ℂ ⊗[ℚ] V) + y := rfl

/-- Conjugation exchanges the positive and negative Weil eigenspaces. -/
theorem conjugation_swaps (J : Module.End ℚ V) {x : ℂ ⊗[ℚ] V}
    (hx : x ∈ Module.End.eigenspace (J.baseChange ℂ) root) :
    complexConj V x ∈ Module.End.eigenspace (J.baseChange ℂ) (-root) := by
  simpa using complexConj_mem_eigenspace hx

/-- Conjugation also exchanges them in the reverse direction. -/
theorem conjugation_swaps_reverse (J : Module.End ℚ V) {x : ℂ ⊗[ℚ] V}
    (hx : x ∈ Module.End.eigenspace (J.baseChange ℂ) (-root)) :
    complexConj V x ∈ Module.End.eigenspace (J.baseChange ℂ) root := by
  simpa using complexConj_mem_eigenspace hx

@[simp] theorem conjugation_involutive (x : ℂ ⊗[ℚ] V) :
    complexConj V (complexConj V x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul z v => simp
  | add x y hx hy => simp [hx, hy]

/-- Conjugation exchanges the two eigenspaces bijectively. -/
theorem conjugation_swaps_iff (J : Module.End ℚ V) (x : ℂ ⊗[ℚ] V) :
    complexConj V x ∈ Module.End.eigenspace (J.baseChange ℂ) (-root) ↔
      x ∈ Module.End.eigenspace (J.baseChange ℂ) root := by
  constructor
  · intro h
    simpa using conjugation_swaps_reverse J h
  · exact conjugation_swaps J

end HodgeLean.Foundations.WeilPower


noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.WeilPower
variable {M : Type*} [AddCommGroup M] [Module ℂ M]

/-- Eigenspaces with eigenvalues whose sum is nonzero are orthogonal for a skew operator. -/
theorem eigenspaces_orthogonal (E : LinearMap.BilinForm ℂ M) (J : Module.End ℂ M)
    (hskew : ∀ x y, E (J x) y = -E x (J y)) {a b : ℂ} (hab : a + b ≠ 0)
    {x y : M} (hx : x ∈ Module.End.eigenspace J a)
    (hy : y ∈ Module.End.eigenspace J b) : E x y = 0 := by
  have h := hskew x y
  rw [Module.End.mem_eigenspace_iff] at hx hy
  rw [hx, hy, map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul] at h
  apply (mul_eq_zero.mp (show (a + b) * E x y = 0 by linear_combination h)).resolve_left hab

/-- Pairing with the first summand, restricted to the second summand.
Source: constructed here for the polarization duality of the Weil eigenspaces. -/
def crossPairing (E : LinearMap.BilinForm ℂ M) (P Q : Submodule ℂ M) :
    Q →ₗ[ℂ] Module.Dual ℂ P :=
  P.subtype.dualMap ∘ₗ E.flip ∘ₗ Q.subtype

example (E : LinearMap.BilinForm ℂ M) (P Q : Submodule ℂ M) (x : P) (y : Q) :
    crossPairing E P Q y x = E x y := rfl

theorem crossPairing_bijective [FiniteDimensional ℂ M]
    (E : LinearMap.BilinForm ℂ M) (hE : E.Nondegenerate)
    (P Q : Submodule ℂ M) (hPQ : IsCompl P Q)
    (hP : ∀ x ∈ P, ∀ y ∈ P, E x y = 0)
    (hQ : ∀ x ∈ Q, ∀ y ∈ Q, E x y = 0) :
    Function.Bijective (crossPairing E P Q) := by
  let e := Submodule.prodEquivOfIsCompl P Q hPQ
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro y hy
    apply Subtype.ext
    apply hE.2
    intro x
    obtain ⟨⟨p, q⟩, rfl⟩ := e.surjective x
    change E ((p : M) + q) y = 0
    rw [map_add, LinearMap.add_apply, hQ q q.property y y.property, add_zero]
    exact LinearMap.congr_fun (LinearMap.mem_ker.mp hy) p
  · intro f
    let F : Module.Dual ℂ M := f ∘ₗ LinearMap.fst ℂ P Q ∘ₗ e.symm.toLinearMap
    let z := (E.flip.toDual hE.flip).symm F
    refine ⟨(e.symm z).2, ?_⟩
    ext p
    have hz : E p z = F p := by
      exact congrArg (fun g : Module.Dual ℂ M => g p)
        ((E.flip.toDual hE.flip).apply_symm_apply F)
    have he : (e.symm (p : M)).1 = p := by
      rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
    have hsum : (↑(e.symm z).1 : M) + ↑(e.symm z).2 = z := e.apply_symm_apply z
    change E p (e.symm z).2 = f p
    rw [← hsum, map_add, hP p p.property _ (e.symm z).1.property, zero_add] at hz
    simpa [F, he] using hz

/-- Perfect pairing of complementary isotropic summands.
Source: constructed here for the polarization duality of the Weil eigenspaces. -/
def crossDuality [FiniteDimensional ℂ M]
    (E : LinearMap.BilinForm ℂ M) (hE : E.Nondegenerate)
    (P Q : Submodule ℂ M) (hPQ : IsCompl P Q)
    (hP : ∀ x ∈ P, ∀ y ∈ P, E x y = 0)
    (hQ : ∀ x ∈ Q, ∀ y ∈ Q, E x y = 0) : Q ≃ₗ[ℂ] Module.Dual ℂ P :=
  LinearEquiv.ofBijective (crossPairing E P Q) (crossPairing_bijective E hE P Q hPQ hP hQ)

example [FiniteDimensional ℂ M] (E : LinearMap.BilinForm ℂ M) (hE : E.Nondegenerate)
    (P Q : Submodule ℂ M) (hPQ : IsCompl P Q)
    (hP : ∀ x ∈ P, ∀ y ∈ P, E x y = 0)
    (hQ : ∀ x ∈ Q, ∀ y ∈ Q, E x y = 0) (x : P) (y : Q) :
    crossDuality E hE P Q hPQ hP hQ y x = E x y := rfl

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- Extension of scalars preserves nondegeneracy of the rational polarization. -/
theorem nondegenerate_baseChange [FiniteDimensional ℚ V]
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate) :
    (E.baseChange ℂ).Nondegenerate := by
  let b := Module.finBasis ℚ V
  have hm : LinearMap.BilinForm.toMatrix (b.baseChange ℂ) (E.baseChange ℂ) =
      (LinearMap.BilinForm.toMatrix b E).map (algebraMap ℚ ℂ) := by
    ext i j
    simp [LinearMap.BilinForm.toMatrix_apply, Module.Basis.baseChange_apply]
  apply (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (b.baseChange ℂ)).mpr
  rw [hm]
  change ((algebraMap ℚ ℂ).mapMatrix (LinearMap.BilinForm.toMatrix b E)).det ≠ 0
  rw [← RingHom.map_det]
  exact (map_ne_zero (algebraMap ℚ ℂ)).mpr
    ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hE)

/-- Skewness extends to the complex polarization. -/
theorem skew_baseChange (E : LinearMap.BilinForm ℚ V) (J : Module.End ℚ V)
    (hskew : ∀ x y, E (J x) y = -E x (J y)) (x y : ℂ ⊗[ℚ] V) :
    E.baseChange ℂ (J.baseChange ℂ x) y = -E.baseChange ℂ x (J.baseChange ℂ y) := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    induction y using TensorProduct.inductionOn with
    | tmul b y => simp [hskew]
    | add y z hy hz =>
      simp only [map_add, hy, hz, neg_add_rev]
      abel
  | add x z hx hz =>
    simp only [map_add, LinearMap.add_apply, hx, hz, neg_add_rev]
    abel

/-- Each Weil eigenspace is isotropic for the complexified polarization. -/
theorem weil_isotropic (E : LinearMap.BilinForm ℚ V) (J : Module.End ℚ V)
    (hskew : ∀ x y, E (J x) y = -E x (J y)) :
    (∀ x ∈ Module.End.eigenspace (J.baseChange ℂ) root,
      ∀ y ∈ Module.End.eigenspace (J.baseChange ℂ) root, E.baseChange ℂ x y = 0) ∧
    (∀ x ∈ Module.End.eigenspace (J.baseChange ℂ) (-root),
      ∀ y ∈ Module.End.eigenspace (J.baseChange ℂ) (-root), E.baseChange ℂ x y = 0) := by
  constructor <;> intro x hx y hy
  · exact eigenspaces_orthogonal _ _ (skew_baseChange E J hskew)
      (by intro h; apply root_ne_zero; linear_combination h / 2) hx hy
  · exact eigenspaces_orthogonal _ _ (skew_baseChange E J hskew)
      (by intro h; apply root_ne_zero; linear_combination -h / 2) hx hy

/-- The negative Weil eigenspace is the dual of the positive one via `E_ℂ(x,y)`.
Source: van Geemen, *An introduction to the Hodge conjecture for abelian varieties*, §5–6. -/
def weilDuality [FiniteDimensional ℚ V]
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
    (J : Module.End ℚ V) (hJ : J.comp J = (-3 : ℚ) • LinearMap.id)
    (hskew : ∀ x y, E (J x) y = -E x (J y)) :
    Module.End.eigenspace (J.baseChange ℂ) (-root) ≃ₗ[ℂ]
      Module.Dual ℂ (Module.End.eigenspace (J.baseChange ℂ) root) :=
  crossDuality (E.baseChange ℂ) (nondegenerate_baseChange E hE) _ _
    (isCompl_weilEigenspaces J hJ) (weil_isotropic E J hskew).1 (weil_isotropic E J hskew).2

example [FiniteDimensional ℚ V]
    (E : LinearMap.BilinForm ℚ V) (hE : E.Nondegenerate)
    (J : Module.End ℚ V) (hJ : J.comp J = (-3 : ℚ) • LinearMap.id)
    (hskew : ∀ x y, E (J x) y = -E x (J y))
    (x : Module.End.eigenspace (J.baseChange ℂ) root)
    (y : Module.End.eigenspace (J.baseChange ℂ) (-root)) :
    weilDuality E hE J hJ hskew y x = E.baseChange ℂ x y := rfl

end HodgeLean.Foundations.WeilPower
