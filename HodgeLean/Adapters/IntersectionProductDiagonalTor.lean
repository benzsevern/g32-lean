import HodgeLean.Adapters.IntersectionProductTorLocal

/-! # Reduction to the diagonal for `Tor`

Let `k` be a field, `S` a commutative `k`-algebra, `T = S ⊗_k S`, `μ : T → S` the multiplication
and `S_Δ` the `T`-module `S` (through `μ`). For an `S`-module `N`, `S ⊗_k N` is a `T`-module
(`(a ⊗ b) · (s ⊗ n) = a s ⊗ b n`, `a3d_XN`). This file proves the facts behind Serre's reduction
to the diagonal, `Tor_i^S(M, N) ≅ Tor_i^T((S ⊗_k N) ⊗_S M, S_Δ)`:
* flat change of rings kills `Tor`: for a flat `φ : A → B`, a `B`-module `Y` projective over `A`
  and an `A`-module `W`, `Tor_{n+1}^B(Y, B ⊗_A W) = 0` (`a3d_isZero_tor_extendScalars`);
* `S ⊗_k N` is the base change of `N` along the right inclusion `S → T` (`a3d_extIso`), so
  `Tor_{n+1}^T(S ⊗_k N, S_Δ) = 0` (`a3d_isZero_tor_XNT`);
* `(S ⊗_k N) ⊗_T S_Δ ≅ N` as `S`-modules (`a3d_pairEquiv`);
* `(S ⊗_k N) ⊗_T P` is projective over `S` for every projective `T`-module `P`
  (`a3d_projective_XNT_tensor`).

Hence `(S ⊗_k N) ⊗_T Q`, for a projective resolution `Q` of `S_Δ`, is a projective resolution of
`N` over `S` (`a3d_res`), and `M ⊗_S ((S ⊗_k N) ⊗_T Q) ≅ (M ⊗_k N) ⊗_T Q` gives
`Tor_n^S(M, N) ≅ Tor_n^T(M ⊗_k N, S_Δ)` (`a3d_tor_diag`).

Source: Serre, *Algèbre locale, multiplicités*, Chapitre V, B.3 (réduction à la diagonale);
Weibel, *An Introduction to Homological Algebra*, Proposition 3.2.9 and Corollary 3.2.10 (flat
change of rings for `Tor`). HC no distance; AV milestone no distance.
-/

open CategoryTheory CategoryTheory.Limits MonoidalCategory TensorProduct
open scoped ChangeOfRings

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace HodgeLean.Adapters
universe u

section CR
variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)

/-- `Y ⊗_B (B ⊗_A W) ≅ Y ⊗_A W` as `A`-modules. -/
def a3d_cancelEquiv (Y : ModuleCat.{u} B) (W : ModuleCat.{u} A) :
    ((ModuleCat.restrictScalars φ).obj (Y ⊗ (ModuleCat.extendScalars φ).obj W) : Type u) ≃ₗ[A]
      ((ModuleCat.restrictScalars φ).obj Y ⊗ W : ModuleCat.{u} A) := by
  letI := φ.toAlgebra
  let Y' := (ModuleCat.restrictScalars φ).obj Y
  haveI : IsScalarTower A B Y' := ⟨fun a b y => by
    change (φ a * b) • y = φ a • (b • y)
    rw [mul_smul]⟩
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange A B B Y' W
  exact
    { e.toAddEquiv with
      map_smul' := fun a x => by
        change e ((φ a) • x) = φ a • e x
        exact e.map_smul (φ a) x }

/-- The isomorphism `a3d_cancelEquiv` is natural in `W`. -/
theorem a3d_cancelEquiv_natural (Y : ModuleCat.{u} B) {W W' : ModuleCat.{u} A} (g : W ⟶ W') :
    (ModuleCat.restrictScalars φ).map (Y ◁ (ModuleCat.extendScalars φ).map g) ≫
        (a3d_cancelEquiv φ Y W').toModuleIso.hom =
      (a3d_cancelEquiv φ Y W).toModuleIso.hom ≫ ((ModuleCat.restrictScalars φ).obj Y ◁ g) := by
  let := φ.toAlgebra
  ext x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
  | tmul y z =>
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' =>
      simp only [TensorProduct.tmul_add, map_add] at hz hz' ⊢; rw [hz, hz']
    | tmul b w => rfl

/-- `restrictScalars φ (Y ⊗ (B ⊗ C)) ≅ restrictScalars φ Y ⊗ C` for a complex `C`. -/
def a3d_cancelCIso (Y : ModuleCat.{u} B) (C : ChainComplex (ModuleCat.{u} A) ℕ) :
    ((ModuleCat.restrictScalars φ).mapHomologicalComplex _).obj
        (a3c_tensC Y (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C)) ≅
      a3c_tensC ((ModuleCat.restrictScalars φ).obj Y) C :=
  HomologicalComplex.Hom.isoOfComponents (fun i => (a3d_cancelEquiv φ Y (C.X i)).toModuleIso)
    (fun i j _ => (a3d_cancelEquiv_natural φ Y (C.d i j)).symm)

/-- Flat change of rings kills `Tor`: for a flat `φ : A → B`, a `B`-module `Y` that is projective
over `A` and any `A`-module `W`, `Tor_{n+1}^B(Y, B ⊗_A W) = 0`, since
`Tor_i^B(Y, B ⊗_A W) ≅ Tor_i^A(Y, W)`.
Source: Weibel, *An Introduction to Homological Algebra*, Proposition 3.2.9 and
Corollary 3.2.10 (flat change of rings for `Tor`). -/
theorem a3d_isZero_tor_extendScalars (hf : φ.Flat) (Y : ModuleCat.{u} B) (W : ModuleCat.{u} A)
    [Projective ((ModuleCat.restrictScalars φ).obj Y)] (n : ℕ) :
    IsZero (((Tor (ModuleCat.{u} B) (n + 1)).obj Y).obj
      ((ModuleCat.extendScalars φ).obj W)) := by
  have := a3q_extendScalars_preservesHomology φ hf
  let F := ModuleCat.extendScalars.{u, u, u} φ
  let G := ModuleCat.restrictScalars.{u} φ
  let Q := ProjectiveResolution.of W
  let Q' := F.mapProjectiveResolution Q
  refine IsZero.of_iso ?_ (a3c_torIso Y _ Q' (n + 1))
  have h1 : IsZero (G.obj ((a3c_tensC Y Q'.complex).homology (n + 1))) := by
    refine IsZero.of_iso ?_ (((a3c_tensC Y Q'.complex).sc (n + 1)).mapHomologyIso G).symm
    refine IsZero.of_iso ?_ (HomologicalComplex.homologyMapIso (a3d_cancelCIso φ Y Q.complex)
      (n + 1))
    refine IsZero.of_iso ?_ (a3c_torIso _ W Q (n + 1)).symm
    obtain ⟨e⟩ := a3c_tor_symm W (n + 1) (G.obj Y)
    exact IsZero.of_iso (isZero_Tor_succ_of_projective (ModuleCat.{u} A) _ _ n) e
  rw [ModuleCat.isZero_iff_subsingleton] at h1 ⊢
  exact h1

end CR

section projTensor
variable {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
  (X : Type u) [AddCommGroup X] [Module T X] [Module S X] [IsScalarTower S T X]
  (Y : Type u) [AddCommGroup Y] [Module T Y]

/-- If `X` is projective over `S` and `Y` is projective over the `S`-algebra `T`, then `X ⊗_T Y`
is projective over `S`. -/
theorem a3d_projective_tensor [Module.Projective S X] [Module.Projective T Y] :
    Module.Projective S (X ⊗[T] Y) := by
  classical
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective T Y)
  have e : X ⊗[T] (Y →₀ T) ≃ₗ[T] (Y →₀ X) := TensorProduct.finsuppScalarRight T T X Y
  have : Module.Projective S (Y →₀ X) :=
    Module.Projective.of_equiv (finsuppLequivDFinsupp (M := X) S).symm
  have : Module.Projective S (X ⊗[T] (Y →₀ T)) :=
    Module.Projective.of_equiv (e.restrictScalars S).symm
  refine Module.Projective.of_split ((LinearMap.lTensor X s).restrictScalars S)
    ((LinearMap.lTensor X (Finsupp.linearCombination T id)).restrictScalars S) ?_
  ext x
  simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
    LinearMap.id_coe, id_eq]
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hs, LinearMap.lTensor_id,
    LinearMap.id_apply]

end projTensor

section XN
variable (k : Type u) [Field k] (S : Type u) [CommRing S] [Algebra k S]
  (N : Type u) [AddCommGroup N] [Module S N] [Module k N] [IsScalarTower k S N]

theorem a3d_right_tmul (b s : S) (n : N) :
    ((Module.End.lTensorAlgHom k N S).comp (Algebra.lsmul k k N)) b (s ⊗ₜ n) = s ⊗ₜ (b • n) :=
  rfl

/-- The action of `S ⊗_k S` on `S ⊗_k N`: `(a ⊗ b) · (s ⊗ n) = a s ⊗ b n`. -/
def a3d_rho : S ⊗[k] S →ₐ[k] Module.End k (S ⊗[k] N) :=
  Algebra.TensorProduct.lift (Algebra.lsmul k k (S ⊗[k] N))
    ((Module.End.lTensorAlgHom k N S).comp (Algebra.lsmul k k N))
    (fun a b => by
      refine LinearMap.ext fun x => ?_
      induction x using TensorProduct.inductionOn with
      | tmul s n =>
        simp only [Module.End.mul_apply, a3d_right_tmul, Algebra.lsmul_coe, smul_tmul',
          smul_eq_mul]
      | add x y hx hy => simp only [Module.End.mul_apply, map_add] at hx hy ⊢; rw [hx, hy])

theorem a3d_rho_tmul (a b s : S) (n : N) :
    a3d_rho k S N (a ⊗ₜ b) (s ⊗ₜ n) = (a * s) ⊗ₜ (b • n) := by
  simp only [a3d_rho, Algebra.TensorProduct.lift_tmul, Module.End.mul_apply, a3d_right_tmul,
    Algebra.lsmul_coe, smul_tmul', smul_eq_mul]

/-- `S ⊗_k N`, a module over `S ⊗_k S` through `a3d_rho`. -/
def a3d_XN : Type u := S ⊗[k] N

instance : AddCommGroup (a3d_XN k S N) := inferInstanceAs (AddCommGroup (S ⊗[k] N))

instance a3d_XN_moduleT : Module (S ⊗[k] S) (a3d_XN k S N) :=
  Module.compHom (S ⊗[k] N) (a3d_rho k S N).toRingHom

instance a3d_XN_moduleS : Module S (a3d_XN k S N) :=
  Module.compHom (a3d_XN k S N) (algebraMap S (S ⊗[k] S))

instance : IsScalarTower S (S ⊗[k] S) (a3d_XN k S N) :=
  ⟨fun s t x => by
    rw [Algebra.smul_def, mul_smul]; rfl⟩

/-- The identification of `S ⊗_k N` with its synonym. -/
def a3d_XN.mk (s : S) (n : N) : a3d_XN k S N := (s ⊗ₜ[k] n : S ⊗[k] N)

theorem a3d_XN_smul_mk (a b s : S) (n : N) :
    (a ⊗ₜ[k] b : S ⊗[k] S) • a3d_XN.mk k S N s n = a3d_XN.mk k S N (a * s) (b • n) :=
  a3d_rho_tmul k S N a b s n

/-- The synonym is `S ⊗_k N` as an `S`-module. -/
def a3d_XN_equiv : a3d_XN k S N ≃ₗ[S] S ⊗[k] N :=
  { AddEquiv.refl _ with
    map_smul' := fun s x => by
      show (a3d_rho k S N (algebraMap S (S ⊗[k] S) s) x : S ⊗[k] N) = s • (show S ⊗[k] N from x)
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      induction x using TensorProduct.inductionOn with
      | tmul a n => rw [a3d_rho_tmul, one_smul, TensorProduct.smul_tmul', smul_eq_mul]
      | add x y hx hy => rw [map_add, hx, hy, smul_add] }

instance : Module.Free S (a3d_XN k S N) := Module.Free.of_equiv (a3d_XN_equiv k S N).symm

/-- The multiplication `S ⊗_k S → S`. -/
abbrev a3d_mu : S ⊗[k] S →+* S := (Algebra.TensorProduct.lmul' k : S ⊗[k] S →ₐ[k] S).toRingHom

/-- `S` as a module over `S ⊗_k S` through the multiplication: the structure sheaf of the
diagonal. -/
def a3d_SD : ModuleCat.{u} (S ⊗[k] S) :=
  (ModuleCat.restrictScalars (a3d_mu k S)).obj (ModuleCat.of S S)

/-- `N` as a module over `S ⊗_k S` through the multiplication. -/
def a3d_ND : ModuleCat.{u} (S ⊗[k] S) :=
  (ModuleCat.restrictScalars (a3d_mu k S)).obj (ModuleCat.of S N)

/-- The augmentation `S ⊗_k N → N`, `a ⊗ n ↦ a n`. -/
def a3d_eps : a3d_XN k S N →+ N :=
  (TensorProduct.lift (Algebra.lsmul k k N).toLinearMap : S ⊗[k] N →ₗ[k] N).toAddMonoidHom

theorem a3d_eps_mk (a : S) (n : N) : a3d_eps k S N (a3d_XN.mk k S N a n) = a • n := rfl

theorem a3d_eps_smul (t : S ⊗[k] S) (x : a3d_XN k S N) :
    a3d_eps k S N (t • x) = a3d_mu k S t • a3d_eps k S N x := by
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    induction x using TensorProduct.inductionOn with
    | tmul s n =>
      change a3d_eps k S N ((a ⊗ₜ[k] b : S ⊗[k] S) • a3d_XN.mk k S N s n) = _
      rw [a3d_XN_smul_mk, a3d_eps_mk]
      change _ = (Algebra.TensorProduct.lmul' k (a ⊗ₜ[k] b)) • (s • n)
      rw [Algebra.TensorProduct.lmul'_apply_tmul, smul_smul, smul_smul]
      congr 1; ring
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  | add t t' ht ht' => rw [add_smul, map_add, ht, ht', map_add, add_smul]

/-- `S ⊗_k N` as an object of `ModuleCat (S ⊗_k S)`. -/
abbrev a3d_XNT : ModuleCat.{u} (S ⊗[k] S) := ModuleCat.of _ (a3d_XN k S N)

/-- The pairing `(S ⊗_k N) ⊗_{S ⊗ S} S → N`, `(a ⊗ n) ⊗ s ↦ s a n`. -/
def a3d_pair : a3d_XNT k S N ⊗ a3d_SD k S ⟶ a3d_ND k S N :=
  ModuleCat.ofHom (X := (a3d_XNT k S N ⊗ a3d_SD k S : ModuleCat.{u} (S ⊗[k] S)))
    (Y := (a3d_ND k S N : Type u)) <| TensorProduct.lift <| LinearMap.mk₂ (S ⊗[k] S)
    (fun (x : a3d_XN k S N) (s : a3d_SD k S) =>
      (show (a3d_ND k S N : Type u) from ((show S from s) • a3d_eps k S N x : N)))
    (fun x y s => by
      change (show S from s) • a3d_eps k S N (x + y) =
        (show S from s) • a3d_eps k S N x + (show S from s) • a3d_eps k S N y
      rw [map_add, smul_add])
    (fun t x s => by
      change (show S from s) • a3d_eps k S N (t • x) =
        a3d_mu k S t • ((show S from s) • a3d_eps k S N x)
      rw [a3d_eps_smul, smul_comm])
    (fun x s s' => by
      change ((show S from s) + (show S from s')) • a3d_eps k S N x =
        (show S from s) • a3d_eps k S N x + (show S from s') • a3d_eps k S N x
      rw [add_smul])
    (fun t x s => by
      change (a3d_mu k S t * (show S from s)) • a3d_eps k S N x =
        a3d_mu k S t • ((show S from s) • a3d_eps k S N x)
      rw [mul_smul])

theorem a3d_pair_tmul (x : a3d_XN k S N) (s : S) :
    a3d_pair k S N (x ⊗ₜ[S ⊗[k] S] (show a3d_SD k S from s)) =
      (show a3d_ND k S N from (s • a3d_eps k S N x : N)) := by
  rfl

theorem a3d_mk_tmul (a s : S) (n : N) :
    a3d_XN.mk k S N a n ⊗ₜ[S ⊗[k] S] (show a3d_SD k S from s) =
      a3d_XN.mk k S N 1 n ⊗ₜ[S ⊗[k] S] (show a3d_SD k S from a * s) := by
  have h : a3d_XN.mk k S N a n = (a ⊗ₜ[k] (1 : S) : S ⊗[k] S) • a3d_XN.mk k S N 1 n := by
    rw [a3d_XN_smul_mk, mul_one, one_smul]
  rw [h, TensorProduct.smul_tmul]
  congr 1
  change Algebra.TensorProduct.lmul' k (a ⊗ₜ[k] (1 : S)) * s = a * s
  rw [Algebra.TensorProduct.lmul'_apply_tmul, mul_one]

theorem a3d_mk_smul_tmul (b s : S) (n : N) :
    a3d_XN.mk k S N 1 (b • n) ⊗ₜ[S ⊗[k] S] (show a3d_SD k S from s) =
      a3d_XN.mk k S N 1 n ⊗ₜ[S ⊗[k] S] (show a3d_SD k S from b * s) := by
  have h : a3d_XN.mk k S N 1 (b • n) = ((1 : S) ⊗ₜ[k] b : S ⊗[k] S) • a3d_XN.mk k S N 1 n := by
    rw [a3d_XN_smul_mk, mul_one]
  rw [h, TensorProduct.smul_tmul]
  congr 1
  change Algebra.TensorProduct.lmul' k ((1 : S) ⊗ₜ[k] b) * s = b * s
  rw [Algebra.TensorProduct.lmul'_apply_tmul, one_mul]

/-- The inverse of the pairing: `n ↦ (1 ⊗ n) ⊗ 1`. -/
def a3d_pairInv (n : N) : (a3d_XNT k S N ⊗ a3d_SD k S : ModuleCat.{u} (S ⊗[k] S)) :=
  a3d_XN.mk k S N 1 n ⊗ₜ[S ⊗[k] S] (show a3d_SD k S from (1 : S))

theorem a3d_pairInv_add (n n' : N) :
    a3d_pairInv k S N (n + n') = a3d_pairInv k S N n + a3d_pairInv k S N n' := by
  unfold a3d_pairInv a3d_XN.mk
  rw [TensorProduct.tmul_add]
  exact TensorProduct.add_tmul _ _ _

theorem a3d_pairInv_pair (z : (a3d_XNT k S N ⊗ a3d_SD k S : ModuleCat.{u} (S ⊗[k] S))) :
    a3d_pairInv k S N (a3d_pair k S N z) = z := by
  induction z using TensorProduct.inductionOn with
  | tmul x s =>
    induction x using TensorProduct.inductionOn with
    | tmul a n =>
      change a3d_XN.mk k S N 1 ((show S from s) • (a • n)) ⊗ₜ[S ⊗[k] S]
        (show a3d_SD k S from (1 : S)) = a3d_XN.mk k S N a n ⊗ₜ[S ⊗[k] S] s
      rw [a3d_mk_tmul k S N a, smul_smul, a3d_mk_smul_tmul, mul_one, mul_comm]
    | add x y hx hy =>
      rw [TensorProduct.add_tmul, map_add, a3d_pairInv_add, hx, hy]
  | add z z' hz hz' => rw [map_add, a3d_pairInv_add, hz, hz']

/-- `(S ⊗_k N) ⊗_{S ⊗ S} S ≅ N` as `S`-modules, `S` acting through the left factor. -/
def a3d_pairEquiv :
    ((ModuleCat.restrictScalars (algebraMap S (S ⊗[k] S))).obj
      (a3d_XNT k S N ⊗ a3d_SD k S) : Type u) ≃ₗ[S] N where
  toFun z := (show N from a3d_pair k S N z)
  map_add' z z' := map_add (a3d_pair k S N).hom z z'
  map_smul' s z := by
    change (show N from a3d_pair k S N ((algebraMap S (S ⊗[k] S) s) • z)) =
      s • (show N from a3d_pair k S N z)
    rw [map_smul]
    change a3d_mu k S (algebraMap S (S ⊗[k] S) s) • (show N from a3d_pair k S N z) = _
    simp
  invFun := a3d_pairInv k S N
  left_inv := a3d_pairInv_pair k S N
  right_inv n := by
    change (1 : S) • a3d_eps k S N (a3d_XN.mk k S N 1 n) = n
    rw [a3d_eps_mk, one_smul, one_smul]

/-- The right inclusion `S → S ⊗_k S`. -/
abbrev a3d_inr : S →+* S ⊗[k] S :=
  (Algebra.TensorProduct.includeRight : S →ₐ[k] S ⊗[k] S).toRingHom

/-- `n ↦ 1 ⊗ n`, as a map to the restriction along the right inclusion. -/
def a3d_unitR : ModuleCat.of S N ⟶ (ModuleCat.restrictScalars (a3d_inr k S)).obj (a3d_XNT k S N) :=
  ModuleCat.ofHom (Y := ((ModuleCat.restrictScalars (a3d_inr k S)).obj (a3d_XNT k S N) : Type u))
    { toFun := fun n => a3d_XN.mk k S N 1 n
      map_add' := fun n n' => TensorProduct.tmul_add _ _ _
      map_smul' := fun s n => by
        change a3d_XN.mk k S N 1 (s • n) = ((1 : S) ⊗ₜ[k] s : S ⊗[k] S) • a3d_XN.mk k S N 1 n
        rw [a3d_XN_smul_mk, mul_one] }

/-- The base change of `N` along the right inclusion. -/
abbrev a3d_ExtN : ModuleCat.{u} (S ⊗[k] S) :=
  (ModuleCat.extendScalars (a3d_inr k S)).obj (ModuleCat.of S N)

/-- `S ⊗_k S` as an `S`-module through the right inclusion. -/
abbrev a3d_Tr : ModuleCat.{u} S :=
  (ModuleCat.restrictScalars (a3d_inr k S)).obj (ModuleCat.of (S ⊗[k] S) (S ⊗[k] S))

/-- `(a, n) ↦ (a ⊗ 1) ⊗ n`. -/
def a3d_toExtFun (a : S) (n : N) : a3d_ExtN k S N :=
  (show a3d_Tr k S from (a ⊗ₜ[k] (1 : S) : S ⊗[k] S)) ⊗ₜ[S] (show ModuleCat.of S N from n)

omit [Module k N] [IsScalarTower k S N] in
theorem a3d_toExtFun_add_left (a a' : S) (n : N) :
    a3d_toExtFun k S N (a + a') n = a3d_toExtFun k S N a n + a3d_toExtFun k S N a' n := by
  unfold a3d_toExtFun
  rw [TensorProduct.add_tmul]
  exact TensorProduct.add_tmul _ _ _

omit [Module k N] [IsScalarTower k S N] in
theorem a3d_toExtFun_add_right (a : S) (n n' : N) :
    a3d_toExtFun k S N a (n + n') = a3d_toExtFun k S N a n + a3d_toExtFun k S N a n' :=
  TensorProduct.tmul_add _ _ _

theorem a3d_toExtFun_smul (c : k) (a : S) (n : N) :
    a3d_toExtFun k S N (c • a) n = a3d_toExtFun k S N a (c • n) := by
  unfold a3d_toExtFun
  rw [← algebraMap_smul S c n]
  change _ = (show a3d_Tr k S from (a ⊗ₜ[k] (1 : S) : S ⊗[k] S)) ⊗ₜ[S]
    ((algebraMap k S c) • (show ModuleCat.of S N from n))
  rw [← TensorProduct.smul_tmul]
  congr 1
  change _ = a3d_inr k S (algebraMap k S c) * (a ⊗ₜ[k] (1 : S))
  simp [Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def]

/-- `S ⊗_k N → (S ⊗ S) ⊗_S N`, `a ⊗ n ↦ (a ⊗ 1) ⊗ n`. -/
def a3d_toExt : a3d_XN k S N →+ a3d_ExtN k S N :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (a3d_toExtFun k S N a)
      (a3d_toExtFun_add_right k S N a))
      (fun a a' => AddMonoidHom.ext fun n => a3d_toExtFun_add_left k S N a a' n))
    (a3d_toExtFun_smul k S N)

theorem a3d_toExt_mk (a : S) (n : N) :
    a3d_toExt k S N (a3d_XN.mk k S N a n) = a3d_toExtFun k S N a n := rfl

theorem a3d_toExt_smul (t : S ⊗[k] S) (x : a3d_XN k S N) :
    a3d_toExt k S N (t • x) = t • a3d_toExt k S N x := by
  induction t using TensorProduct.inductionOn with
  | tmul b c =>
    induction x using TensorProduct.inductionOn with
    | tmul a n =>
      change a3d_toExt k S N ((b ⊗ₜ[k] c : S ⊗[k] S) • a3d_XN.mk k S N a n) = _
      rw [a3d_XN_smul_mk, a3d_toExt_mk]
      change a3d_toExtFun k S N (b * a) (c • n) =
        (b ⊗ₜ[k] c : S ⊗[k] S) • a3d_toExtFun k S N a n
      unfold a3d_toExtFun
      change _ = (show a3d_Tr k S from ((b ⊗ₜ[k] c) * (a ⊗ₜ[k] (1 : S)) : S ⊗[k] S)) ⊗ₜ[S]
        (show ModuleCat.of S N from n)
      rw [show (show ModuleCat.of S N from c • n) = c • (show ModuleCat.of S N from n) from rfl,
        ← TensorProduct.smul_tmul]
      congr 1
      change a3d_inr k S c * ((b * a) ⊗ₜ[k] (1 : S)) = _
      simp [Algebra.TensorProduct.tmul_mul_tmul, mul_comm]
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  | add t t' ht ht' => rw [add_smul, map_add, ht, ht', add_smul]

/-- `(S ⊗ S) ⊗_S N → S ⊗_k N`, `t ⊗ n ↦ t · (1 ⊗ n)`. -/
def a3d_fromExt : a3d_ExtN k S N ⟶ a3d_XNT k S N :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars (a3d_inr k S) (a3d_unitR k S N)

/-- `S ⊗_k N`, with `S ⊗ S` acting factorwise, is the base change of `N` along the right
inclusion `S → S ⊗_k S`. -/
def a3d_extIso : a3d_ExtN k S N ≅ a3d_XNT k S N where
  hom := a3d_fromExt k S N
  inv := ModuleCat.ofHom (X := a3d_XN k S N) (Y := (a3d_ExtN k S N : Type u))
    { toFun := a3d_toExt k S N
      map_add' := map_add _
      map_smul' := a3d_toExt_smul k S N }
  hom_inv_id := by
    ext n
    change a3d_toExt k S N ((1 : S ⊗[k] S) • a3d_XN.mk k S N 1 n) = _
    rw [one_smul, a3d_toExt_mk]
    rfl
  inv_hom_id := by
    ext x
    induction x using TensorProduct.inductionOn with
    | tmul a n =>
      change a3d_fromExt k S N (a3d_toExt k S N (a3d_XN.mk k S N a n)) = a3d_XN.mk k S N a n
      rw [a3d_toExt_mk]
      change ((a ⊗ₜ[k] (1 : S) : S ⊗[k] S)) • a3d_XN.mk k S N 1 n = _
      rw [a3d_XN_smul_mk, mul_one, one_smul]
    | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The right inclusion is flat. -/
theorem a3d_inr_flat : (a3d_inr k S).Flat := by
  have h1 : (algebraMap S (S ⊗[k] S)).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
  have h2 : ((Algebra.TensorProduct.comm k S S).toRingEquiv.toRingHom).Flat :=
    RingHom.Flat.of_bijective (Algebra.TensorProduct.comm k S S).bijective
  have : a3d_inr k S = (Algebra.TensorProduct.comm k S S).toRingEquiv.toRingHom.comp
      (algebraMap S (S ⊗[k] S)) := by
    ext s; simp
  rw [this]
  exact h1.comp h2

/-- `S`, restricted along `S → S ⊗ S → S`, is free. -/
instance a3d_projective_SD :
    Projective ((ModuleCat.restrictScalars (a3d_inr k S)).obj (a3d_SD k S)) := by
  let e : ((ModuleCat.restrictScalars (a3d_inr k S)).obj (a3d_SD k S) : Type u) ≃ₗ[S] S :=
    { AddEquiv.refl _ with
      map_smul' := fun s x => by
        change a3d_mu k S (a3d_inr k S s) * (show S from x) = s * (show S from x)
        simp }
  exact Projective.of_iso (show ModuleCat.of S S ≅
    (ModuleCat.restrictScalars (a3d_inr k S)).obj (a3d_SD k S) from e.symm.toModuleIso)
    inferInstance

/-- `Tor_{n+1}^{S ⊗ S}(S ⊗_k N, S) = 0`. -/
theorem a3d_isZero_tor_XNT (n : ℕ) :
    IsZero (((Tor (ModuleCat.{u} (S ⊗[k] S)) (n + 1)).obj (a3d_XNT k S N)).obj (a3d_SD k S)) := by
  obtain ⟨e⟩ := a3c_tor_symm (a3d_SD k S) (n + 1) (a3d_XNT k S N)
  refine IsZero.of_iso ?_ e
  refine IsZero.of_iso ?_ (((Tor (ModuleCat.{u} (S ⊗[k] S)) (n + 1)).obj (a3d_SD k S)).mapIso
    (a3d_extIso k S N)).symm
  exact a3d_isZero_tor_extendScalars (a3d_inr k S) (a3d_inr_flat k S) _ _ n

instance : SMulCommClass (S ⊗[k] S) S (a3d_XN k S N) :=
  ⟨fun t s x => by
    change t • (algebraMap S (S ⊗[k] S) s • x) = algebraMap S (S ⊗[k] S) s • (t • x)
    rw [smul_smul, smul_smul, mul_comm]⟩

/-- `(S ⊗_k N) ⊗_{S ⊗ S} P` is projective over `S` for every projective `P`. -/
instance a3d_projective_XNT_tensor (Y : ModuleCat.{u} (S ⊗[k] S)) [Projective Y] :
    Projective ((ModuleCat.restrictScalars (algebraMap S (S ⊗[k] S))).obj
      (a3d_XNT k S N ⊗ Y)) := by
  have hY : Module.Projective (S ⊗[k] S) Y :=
    (IsProjective.iff_projective Y).2 (inferInstanceAs (Projective Y))
  have := a3d_projective_tensor (S := S) (T := S ⊗[k] S) (a3d_XN k S N) Y
  exact (IsProjective.iff_projective (a3d_XN k S N ⊗[S ⊗[k] S] Y)).1 this

end XN
section CR2
variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)

/-- The isomorphism `a3d_cancelEquiv` is natural in `Y`. -/
theorem a3d_cancelEquiv_natural_left {Y Y' : ModuleCat.{u} B} (g : Y ⟶ Y') (W : ModuleCat.{u} A) :
    (ModuleCat.restrictScalars φ).map (g ▷ (ModuleCat.extendScalars φ).obj W) ≫
        (a3d_cancelEquiv φ Y' W).toModuleIso.hom =
      (a3d_cancelEquiv φ Y W).toModuleIso.hom ≫ ((ModuleCat.restrictScalars φ).map g ▷ W) := by
  let := φ.toAlgebra
  ext x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
  | tmul y z =>
    induction z using TensorProduct.inductionOn with
    | add z z' hz hz' =>
      simp only [TensorProduct.tmul_add, map_add] at hz hz' ⊢; rw [hz, hz']
    | tmul b w =>
      change (show (ModuleCat.restrictScalars φ).obj Y' from (show B from b) • g y) ⊗ₜ[A] w =
        (show (ModuleCat.restrictScalars φ).obj Y' from g ((show B from b) • y)) ⊗ₜ[A] w
      congr 1
      exact (g.hom.map_smul _ _).symm

/-- `(B ⊗_A M) ⊗_B Z ≅ M ⊗_A Z` after restricting to `A`, natural in `Z`. -/
def a3d_projIso (M : ModuleCat.{u} A) (Z : ModuleCat.{u} B) :
    (ModuleCat.restrictScalars φ).obj ((ModuleCat.extendScalars φ).obj M ⊗ Z) ≅
      M ⊗ (ModuleCat.restrictScalars φ).obj Z :=
  (ModuleCat.restrictScalars φ).mapIso (β_ _ _) ≪≫ (a3d_cancelEquiv φ Z M).toModuleIso ≪≫ β_ _ _

theorem a3d_projIso_natural (M : ModuleCat.{u} A) {Z Z' : ModuleCat.{u} B} (g : Z ⟶ Z') :
    (ModuleCat.restrictScalars φ).map ((ModuleCat.extendScalars φ).obj M ◁ g) ≫
        (a3d_projIso φ M Z').hom =
      (a3d_projIso φ M Z).hom ≫ (M ◁ (ModuleCat.restrictScalars φ).map g) := by
  simp only [a3d_projIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Functor.map_comp_assoc, BraidedCategory.braiding_naturality_right, Functor.map_comp_assoc,
    reassoc_of% (a3d_cancelEquiv_natural_left φ g M)]
  simp

end CR2
section res
variable (k : Type u) [Field k] (S : Type u) [CommRing S] [Algebra k S]
  (N : Type u) [AddCommGroup N] [Module S N] [Module k N] [IsScalarTower k S N]

/-- The left inclusion `S → S ⊗_k S`. -/
abbrev a3d_inl : S →+* S ⊗[k] S := algebraMap S (S ⊗[k] S)

/-- A projective resolution of the diagonal module `S_Δ`. -/
abbrev a3d_Q : ProjectiveResolution (a3d_SD k S) := ProjectiveResolution.of (a3d_SD k S)

/-- The complex `(S ⊗_k N) ⊗_{S ⊗ S} Q`, restricted to `S`: a projective resolution of `N`. -/
abbrev a3d_C : ChainComplex (ModuleCat.{u} S) ℕ :=
  ((ModuleCat.restrictScalars (a3d_inl k S)).mapHomologicalComplex _).obj
    (a3c_tensC (a3d_XNT k S N) (a3d_Q k S).complex)

/-- The augmentation `C₀ → N`. -/
def a3d_π0 : (a3d_C k S N).X 0 ⟶ ModuleCat.of S N :=
  (ModuleCat.restrictScalars (a3d_inl k S)).map (a3d_XNT k S N ◁ (a3d_Q k S).π.f 0) ≫
    (a3d_pairEquiv k S N).toModuleIso.hom

theorem a3d_d_π0 : (a3d_C k S N).d 1 0 ≫ a3d_π0 k S N = 0 := by
  change (ModuleCat.restrictScalars (a3d_inl k S)).map (a3d_XNT k S N ◁ (a3d_Q k S).complex.d 1 0) ≫
    (ModuleCat.restrictScalars (a3d_inl k S)).map (a3d_XNT k S N ◁ (a3d_Q k S).π.f 0) ≫
      (a3d_pairEquiv k S N).toModuleIso.hom = 0
  rw [← Functor.map_comp_assoc, ← MonoidalCategory.whiskerLeft_comp,
    (a3d_Q k S).complex_d_comp_π_f_zero, MonoidalPreadditive.whiskerLeft_zero, Functor.map_zero,
    zero_comp]

theorem a3d_exact₀ : (ShortComplex.mk _ _ (a3d_d_π0 k S N)).Exact := by
  have h := ((a3c_tens_exact₀ (a3d_Q k S) (a3d_XNT k S N)).map
    (ModuleCat.restrictScalars (a3d_inl k S)))
  refine (ShortComplex.exact_iff_of_iso ?_).1 h
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (a3d_pairEquiv k S N).toModuleIso
    (by simp) (by simp [a3d_π0])

instance a3d_epi_π0 : Epi (a3d_π0 k S N) := by
  unfold a3d_π0
  have : Epi (a3d_XNT k S N ◁ (a3d_Q k S).π.f 0) := inferInstance
  infer_instance

theorem a3d_C_exactAt (n : ℕ) : (a3d_C k S N).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  refine IsZero.of_iso ?_ (((a3c_tensC (a3d_XNT k S N) (a3d_Q k S).complex).sc (n + 1)).mapHomologyIso
    (ModuleCat.restrictScalars (a3d_inl k S)))
  refine Functor.map_isZero _ ?_
  exact IsZero.of_iso (a3d_isZero_tor_XNT k S N n) (a3c_torIso _ _ (a3d_Q k S) (n + 1)).symm

/-- `(S ⊗_k N) ⊗_{S ⊗ S} Q`, for a projective resolution `Q` of `S_Δ`, is a projective resolution
of `N` over `S`. -/
def a3d_res : ProjectiveResolution (ModuleCat.of S N) where
  complex := a3d_C k S N
  projective n := by
    have := (a3d_Q k S).projective n
    exact a3d_projective_XNT_tensor k S N _
  π := (ChainComplex.toSingle₀Equiv _ _).symm ⟨a3d_π0 k S N, a3d_d_π0 k S N⟩
  quasiIso := ⟨fun n => by
    cases n
    · rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · dsimp
        refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2
          ⟨a3d_exact₀ k S N, by dsimp; infer_instance⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by simp) (by simp; exact (ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _).symm)
      all_goals first | rfl | simp
    · rw [quasiIsoAt_iff_exactAt']
      · exact a3d_C_exactAt k S N _
      · apply ChainComplex.exactAt_succ_single_obj⟩

/-- The `S ⊗_k S`-module `(S ⊗_S M) ⊗ (S ⊗_k N)`, that is `M ⊗_k N`. -/
abbrev a3d_XM (M : ModuleCat.{u} S) : ModuleCat.{u} (S ⊗[k] S) :=
  (ModuleCat.extendScalars (a3d_inl k S)).obj M ⊗ a3d_XNT k S N

/-- `M ⊗_S ((S ⊗_k N) ⊗ Q) ≅ ((S ⊗_S M) ⊗ (S ⊗_k N)) ⊗ Q` after restricting to `S`. -/
def a3d_diagCIso (M : ModuleCat.{u} S) :
    a3c_tensC M (a3d_C k S N) ≅
      ((ModuleCat.restrictScalars (a3d_inl k S)).mapHomologicalComplex _).obj
        (a3c_tensC (a3d_XM k S N M) (a3d_Q k S).complex) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun j => (a3d_projIso (a3d_inl k S) M (a3d_XNT k S N ⊗ (a3d_Q k S).complex.X j)).symm ≪≫
      (ModuleCat.restrictScalars (a3d_inl k S)).mapIso (α_ _ _ _).symm)
    (fun i j _ => by
      change ((a3d_projIso (a3d_inl k S) M _).inv ≫
          (ModuleCat.restrictScalars (a3d_inl k S)).map (α_ _ _ _).inv) ≫
          (ModuleCat.restrictScalars (a3d_inl k S)).map
            (a3d_XM k S N M ◁ (a3d_Q k S).complex.d i j) =
        (M ◁ (ModuleCat.restrictScalars (a3d_inl k S)).map
          (a3d_XNT k S N ◁ (a3d_Q k S).complex.d i j)) ≫
          (a3d_projIso (a3d_inl k S) M _).inv ≫
            (ModuleCat.restrictScalars (a3d_inl k S)).map (α_ _ _ _).inv
      rw [Category.assoc, ← Functor.map_comp, ← associator_inv_naturality_right, Functor.map_comp,
        ← Category.assoc, ← Category.assoc]
      congr 1
      rw [Iso.inv_comp_eq, ← Category.assoc, ← a3d_projIso_natural, Category.assoc,
        Iso.hom_inv_id, Category.comp_id])

/-- Serre's reduction to the diagonal for `Tor`: over a field `k`,
`Tor_n^S(M, N) ≅ Tor_n^{S ⊗_k S}(M ⊗_k N, S)` as `S`-modules, where `M ⊗_k N` is
`(S ⊗_S M) ⊗_{S ⊗ S} (S ⊗_k N)` and `S ⊗_k S` acts on `S` by multiplication.
Source: Serre, *Algèbre locale, multiplicités*, Chapitre V, B.3 (réduction à la diagonale);
Cartan–Eilenberg, *Homological Algebra*, Chapter IX, §2. -/
theorem a3d_tor_diag (M : ModuleCat.{u} S) (n : ℕ) :
    Nonempty (((Tor (ModuleCat.{u} S) n).obj M).obj (ModuleCat.of S N) ≅
      (ModuleCat.restrictScalars (a3d_inl k S)).obj
        (((Tor (ModuleCat.{u} (S ⊗[k] S)) n).obj (a3d_XM k S N M)).obj (a3d_SD k S))) :=
  ⟨a3c_torIso M _ (a3d_res k S N) n ≪≫
    HomologicalComplex.homologyMapIso (a3d_diagCIso k S N M) n ≪≫
    ((a3c_tensC (a3d_XM k S N M) (a3d_Q k S).complex).sc n).mapHomologyIso
      (ModuleCat.restrictScalars (a3d_inl k S)) ≪≫
    (ModuleCat.restrictScalars (a3d_inl k S)).mapIso (a3c_torIso _ _ (a3d_Q k S) n).symm⟩

end res

end HodgeLean.Adapters
