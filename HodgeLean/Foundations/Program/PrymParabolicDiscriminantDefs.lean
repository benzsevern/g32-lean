import HodgeLean.Foundations.Program.PrymParabolicSaturated
import HodgeLean.Foundations.Program.PeriodMarkingClassification
import HodgeLean.Foundations.Program.PeriodMarkingParabolic

/-! # H7: the cellular cup-dual form

The form below lives on the saturated rational cellular lattice. It is defined from evaluation
and the inverse transpose of the coordinate cup matrix. Identification with the geometric
intersection pairing is deferred. HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped TensorProduct
open HodgeLean.Papers HodgeLean.Foundations.WeilHermitian
open HodgeLean.Foundations.HermitianForm
namespace HodgeLean.Foundations.Program

/-- The quadratic action on the rationalized saturated cellular lattice.
Source: `hg6_cellOperator_sq`; extension of scalars, Bourbaki, Algebra, Ch. II, §5. -/
def hg7_cellAction : {J : Module.End ℚ (ℚ ⊗[ℤ] hg6_cellLattice) //
    J ∘ₗ J = (-3 : ℚ) • LinearMap.id} :=
  ⟨hg6_cellJ, b64b_baseChange_quadratic _ _ hg6_cellOperator_sq⟩

example : hg7_cellAction.1 = hg6_cellJ := rfl

/-- The six cellular cohomology classes of H6's certificate, through Shapiro.
Source: G32 v0.16, Lemma 6.2; `hp_certK`, `hg4_shapiroZ`. -/
def hg7_classes (i : Fin 6) : hg_eqH1 hg4_sigmaK b4b_root :=
  Submodule.Quotient.mk (hg4_shapiroZ hg4_sigmaK b4b_root
    ⟨hp_certK i, hg4_sigmaK_tuple ▸ hp_certK_mem i⟩)

example (i : Fin 6) : hg7_classes i = Submodule.Quotient.mk
    (hg4_shapiroZ hg4_sigmaK b4b_root ⟨hp_certK i, hg4_sigmaK_tuple ▸ hp_certK_mem i⟩) := rfl

/-- A rational functional in the positive eigenspace, read as a `K`-linear functional.
Source: restriction of scalars; `hg6_isoSpace`, `WeilHermitian.equiv_smul`. -/
def hg7_functional (φ : hg6_isoSpace) :
    WithJ (ℚ ⊗[ℤ] hg6_cellLattice) hg7_cellAction →ₗ[hp_K] hp_K where
  toFun x := φ.1 (WithJ.equiv hg7_cellAction x)
  map_add' x y := map_add φ.1 _ _
  map_smul' z x := by
    change φ.1 (WithJ.equiv hg7_cellAction (z • x)) =
      z * φ.1 (WithJ.equiv hg7_cellAction x)
    rw [equiv_smul, map_add, map_smul, map_smul]
    change z.re • φ.1 _ + z.im • φ.1 (hg6_cellJ _) = _
    have he := congrArg (fun t : hp_K => z.re • φ.1 (WithJ.equiv hg7_cellAction x) + z.im • t)
      (φ.2 (WithJ.equiv hg7_cellAction x))
    refine he.trans ?_
    have hz : z = (z.re : hp_K) + (z.im : hp_K) * QuadraticAlgebra.omega := by
      ext <;> simp
    conv_rhs => rw [hz]
    simp only [Rat.smul_def, smul_eq_mul]
    ring

example (φ : hg6_isoSpace) (x : WithJ (ℚ ⊗[ℤ] hg6_cellLattice) hg7_cellAction) :
    hg7_functional φ x = φ.1 (WithJ.equiv hg7_cellAction x) := rfl

/-- Evaluation on the six classes, with the positive quadratic action `√−3 ↦ 1 + 2Z`.
Source: Hatcher, Algebraic Topology, §3.1; `hg6_theta`, `hg6_theta_le`. -/
def hg7_evaluation : WithJ (ℚ ⊗[ℤ] hg6_cellLattice) hg7_cellAction →ₗ[hp_K] (Fin 6 → hp_K) :=
  LinearMap.pi fun i => hg7_functional
    ⟨hg6_theta (hg7_classes i), hg6_theta_le ⟨hg7_classes i, rfl⟩⟩

example (x : WithJ (ℚ ⊗[ℤ] hg6_cellLattice) hg7_cellAction) (i : Fin 6) :
    hg7_evaluation x i = hg6_theta (hg7_classes i) (WithJ.equiv hg7_cellAction x) := rfl

/-- The normalized coordinate cup matrix on the six certificate cocycles.
Source: Hatcher, §3.2; G32 v0.16, proof of Proposition 6.3; `hg6_coordCup_gram`. -/
def hg7_cupGram : Matrix (Fin 6) (Fin 6) hp_K := fun i j =>
  (1 + 2 * pc_zeta) * (4 * hg6_coordCup b4b_root 0 0
    (hg_shapiroCochain hg4_sigmaK b4b_root (hp_certK i))
    (hg_shapiroCochain hg4_sigmaK b4b_root (hp_certK j)))

example : hg7_cupGram = (Fintype.card b4b_Group : hp_K) • g32H0 pc_zeta := by
  apply Matrix.ext
  intro i j
  exact hg6_coordCup_gram i j

/-- The Hermitian cup-dual form on the rational cellular lattice. For a conjugate-first
Hermitian Gram matrix `G`, the form on the linear dual has Gram `(G⁻¹)ᵀ` in the dual basis.
Evaluation pulls that form back to the lattice; no geometric pairing is used here.
Source: Bourbaki, Algebra, Ch. IX, §1 (dual sesquilinear forms); `hg7_evaluation`, `hg7_cupGram`. -/
def hg7_cellularForm :
    WithJ (ℚ ⊗[ℤ] hg6_cellLattice) hg7_cellAction →ₗ⋆[hp_K]
      WithJ (ℚ ⊗[ℤ] hg6_cellLattice) hg7_cellAction →ₗ[hp_K] hp_K :=
  ((hp_matrixForm hg7_cupGram⁻¹.transpose).comp hg7_evaluation).compl₂ hg7_evaluation

example (x y : WithJ (ℚ ⊗[ℤ] hg6_cellLattice) hg7_cellAction) :
    hg7_cellularForm x y = hp_matrixForm hg7_cupGram⁻¹.transpose
      (hg7_evaluation x) (hg7_evaluation y) := rfl

end HodgeLean.Foundations.Program
