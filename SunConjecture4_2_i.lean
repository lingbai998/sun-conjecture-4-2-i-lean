/-
Zero-`sorry` Lean 4 Formalization of Zhi-Wei Sun's Conjecture 4.2(i) (arXiv:2108.07723v7)
& OEIS A085807, via the Signed Cyclic-Shift Invariance Master Theorem.

References:
- Zhi-Wei Sun, "Arithmetic properties of some permanents", arXiv:2108.07723v7 (2022), Conjecture 4.2(i)
- OEIS A085807: https://oeis.org/A085807

Main Theorems (ZERO `sorry` in the entire file):
1. `perm_eq_det_of_signed_shift`: For any odd prime `p` and `M : Matrix (Fin p) (Fin p) (ZMod p)`
   satisfying `M (T i) (T j) = ε i * ε j * M i j`, we have `M.permanent = M.det` in `ZMod p`.
2. `sun_conjecture_4_2_i_eq_4_3` (Eq. 4.3 / OEIS A085807):
   For any odd prime `p`, `2 * per[|i - j|] = -1` in `ZMod p`.
3. `sun_conjecture_4_2_i_eq_4_4` (Eq. 4.4):
   For any odd prime `p`, `2 * per[|i - j + 1|] = 1` in `ZMod p`.
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Tactic

open scoped BigOperators
open Matrix Finset

namespace SunConjecture42i

/-- Cyclic shift `T(x) = (x + 1) mod p` on `Fin p`. -/
def shiftPerm (p : ℕ) [NeZero p] : Equiv.Perm (Fin p) where
  toFun x := ⟨(x.val + 1) % p, Nat.mod_lt _ (NeZero.pos p)⟩
  invFun x := ⟨(x.val + p - 1) % p, Nat.mod_lt _ (NeZero.pos p)⟩
  left_inv x := by
    ext
    dsimp only
    have hp := NeZero.pos p; have hx := x.isLt
    by_cases h : x.val + 1 < p
    · rw [Nat.mod_eq_of_lt h, show x.val + 1 + p - 1 = x.val + p by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt hx]
    · have hx' : x.val + 1 = p := by omega
      rw [hx', Nat.mod_self, zero_add, Nat.mod_eq_of_lt (by omega : p - 1 < p)]
      omega
  right_inv x := by
    ext
    dsimp only
    have hp := NeZero.pos p; have hx := x.isLt
    by_cases h : x.val = 0
    · rw [h, zero_add, Nat.mod_eq_of_lt (by omega : p - 1 < p),
          show p - 1 + 1 = p by omega, Nat.mod_self]
    · rw [show x.val + p - 1 = (x.val - 1) + p by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega : x.val - 1 < p),
          show x.val - 1 + 1 = x.val by omega, Nat.mod_eq_of_lt hx]

lemma shiftPerm_pow_apply (p : ℕ) [NeZero p] (r : ℕ) (x : Fin p) :
    ((shiftPerm p ^ r) x).val = (x.val + r) % p := by
  induction r with
  | zero => simp [Nat.mod_eq_of_lt x.isLt]
  | succ r ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    change (((shiftPerm p ^ r) x).val + 1) % p = (x.val + (r + 1)) % p
    rw [ih, Nat.mod_add_mod, add_assoc]

lemma shiftPerm_pow_self (p : ℕ) [NeZero p] :
    shiftPerm p ^ p = 1 := by
  ext x
  rw [shiftPerm_pow_apply, Equiv.Perm.one_apply, Nat.add_mod_right, Nat.mod_eq_of_lt x.isLt]

/-- For an odd prime `p`, `shiftPerm p` is an even permutation (`sign = 1`),
since `(sign T)^p = sign (T^p) = 1` in `ℤˣ`. -/
lemma shiftPerm_sign (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    Equiv.Perm.sign (shiftPerm p) = 1 := by
  have hp_odd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
  have hpow : (Equiv.Perm.sign (shiftPerm p)) ^ p = 1 := by
    rw [← map_pow, shiftPerm_pow_self, map_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (shiftPerm p)) with h | h
  · exact h
  · rw [h, hp_odd.neg_one_pow] at hpow
    exact absurd hpow (by decide)

/-- Sign function `ε(p - 1) = -1` and `ε(x) = 1` for `x < p - 1`. -/
def epsSign (p : ℕ) (x : Fin p) : ZMod p :=
  if x.val = p - 1 then -1 else 1

lemma prod_epsSign (p : ℕ) [NeZero p] :
    ∏ i : Fin p, epsSign p i = (-1 : ZMod p) := by
  have hp := NeZero.pos p
  let top : Fin p := ⟨p - 1, by omega⟩
  rw [Finset.prod_eq_single top]
  · simp [epsSign, top]
  · intro b _ hb
    have hne : b.val ≠ p - 1 := fun h => hb (Fin.ext h)
    simp [epsSign, hne]
  · intro h; exact absurd (Finset.mem_univ top) h

/-! ### Step 1: Prime-order cyclic conjugation action & zero-`sorry` orbit collapse -/

/-- Conjugation action of `Multiplicative (ZMod p)` on `Equiv.Perm (Fin p)` via `shiftPerm p`. -/
@[instance_reducible]
def conjAction (p : ℕ) [NeZero p] :
    MulAction (Multiplicative (ZMod p)) (Equiv.Perm (Fin p)) where
  smul r σ := shiftPerm p ^ (Multiplicative.toAdd r).val * σ * (shiftPerm p ^ (Multiplicative.toAdd r).val)⁻¹
  one_smul σ := by
    change shiftPerm p ^ (0 : ZMod p).val * σ * (shiftPerm p ^ (0 : ZMod p).val)⁻¹ = σ
    simp
  mul_smul r s σ := by
    change shiftPerm p ^ ((Multiplicative.toAdd r + Multiplicative.toAdd s).val) * σ *
        (shiftPerm p ^ ((Multiplicative.toAdd r + Multiplicative.toAdd s).val))⁻¹ =
      shiftPerm p ^ (Multiplicative.toAdd r).val *
        (shiftPerm p ^ (Multiplicative.toAdd s).val * σ *
          (shiftPerm p ^ (Multiplicative.toAdd s).val)⁻¹) *
        (shiftPerm p ^ (Multiplicative.toAdd r).val)⁻¹
    have hpow : shiftPerm p ^ ((Multiplicative.toAdd r + Multiplicative.toAdd s).val) =
        shiftPerm p ^ (Multiplicative.toAdd r).val * shiftPerm p ^ (Multiplicative.toAdd s).val := by
      have hmod : (Multiplicative.toAdd r + Multiplicative.toAdd s).val =
          ((Multiplicative.toAdd r).val + (Multiplicative.toAdd s).val) % p := ZMod.val_add _ _
      rw [hmod, ← pow_add]
      have hdiv := Nat.div_add_mod ((Multiplicative.toAdd r).val + (Multiplicative.toAdd s).val) p
      conv_rhs => rw [← hdiv, pow_add, pow_mul, shiftPerm_pow_self, one_pow, one_mul]
    rw [hpow]
    group

/-- Any function `f : Equiv.Perm (Fin p) → ZMod p` invariant under conjugation by `shiftPerm p`
has the same sum over all `S_p` as over the fixed points `{σ | T * σ * T⁻¹ = σ}`. -/
lemma sum_eq_sum_fixed_of_conj_invariant (p : ℕ) [Fact p.Prime]
    (f : Equiv.Perm (Fin p) → ZMod p)
    (hinv : ∀ σ : Equiv.Perm (Fin p), f (shiftPerm p * σ * (shiftPerm p)⁻¹) = f σ) :
    ∑ σ : Equiv.Perm (Fin p), f σ =
      ∑ σ ∈ Finset.univ.filter (fun σ => shiftPerm p * σ * (shiftPerm p)⁻¹ = σ), f σ := by
  let : MulAction (Multiplicative (ZMod p)) (Equiv.Perm (Fin p)) := conjAction p
  have hinv_pow : ∀ (r : ℕ) (σ : Equiv.Perm (Fin p)),
      f (shiftPerm p ^ r * σ * (shiftPerm p ^ r)⁻¹) = f σ := by
    intro r
    induction r with
    | zero => intro σ; simp
    | succ r ih =>
      intro σ
      have heq : shiftPerm p ^ (r + 1) * σ * (shiftPerm p ^ (r + 1))⁻¹ =
          shiftPerm p * (shiftPerm p ^ r * σ * (shiftPerm p ^ r)⁻¹) * (shiftPerm p)⁻¹ := by
        rw [pow_succ', _root_.mul_inv_rev]; group
      rw [heq, hinv, ih]
  have hinv_smul : ∀ (r : Multiplicative (ZMod p)) (σ : Equiv.Perm (Fin p)), f (r • σ) = f σ :=
    fun r σ => hinv_pow (Multiplicative.toAdd r).val σ
  let rel := MulAction.orbitRel (Multiplicative (ZMod p)) (Equiv.Perm (Fin p))
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := Quotient.mk rel) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)]
  rw [← Finset.sum_fiberwise_of_maps_to (g := Quotient.mk rel) (t := Finset.univ)
      (s := Finset.univ.filter (fun σ => shiftPerm p * σ * (shiftPerm p)⁻¹ = σ))
      (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl ?_
  intro q _
  rcases Quotient.exists_rep q with ⟨σ₀, rfl⟩
  let fib := Finset.univ.filter (fun σ : Equiv.Perm (Fin p) => Quotient.mk rel σ = Quotient.mk rel σ₀)
  have hconst : ∀ σ ∈ fib, f σ = f σ₀ := by
    intro σ hσ
    have hrel : rel σ σ₀ := Quotient.exact (Finset.mem_filter.mp hσ).2
    rcases hrel with ⟨r, hr⟩
    rw [← hr, hinv_smul]
  have hcard_eq : fib.card = Fintype.card (MulAction.orbit (Multiplicative (ZMod p)) σ₀) := by
    rw [Fintype.card_of_subtype fib]
    intro σ
    simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and, MulAction.mem_orbit_iff]
    exact ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩
  have hdvd : fib.card ∣ p := by
    rw [hcard_eq]
    have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (Multiplicative (ZMod p)) σ₀
    have hG : Fintype.card (Multiplicative (ZMod p)) = p := by
      exact (Fintype.card_congr Multiplicative.toAdd).trans (ZMod.card p)
    rw [hG] at h
    exact ⟨_, h.symm⟩
  rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd _ hdvd with h1 | hp_card
  · have hfix : shiftPerm p * σ₀ * (shiftPerm p)⁻¹ = σ₀ := by
      have hmem1 : σ₀ ∈ fib := by simp [fib]
      have hmem2 : shiftPerm p * σ₀ * (shiftPerm p)⁻¹ ∈ fib := by
        simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and]
        apply Quotient.sound
        refine ⟨Multiplicative.ofAdd (1 : ZMod p), ?_⟩
        change shiftPerm p ^ (1 : ZMod p).val * σ₀ * (shiftPerm p ^ (1 : ZMod p).val)⁻¹ = _
        have hval1 : (1 : ZMod p).val = 1 := ZMod.val_one p
        rw [hval1, pow_one]
      rcases Finset.card_eq_one.mp h1 with ⟨a, ha⟩
      rw [ha, Finset.mem_singleton] at hmem1 hmem2
      rw [hmem2, hmem1]
    have hsub : (Finset.univ.filter (fun σ => shiftPerm p * σ * (shiftPerm p)⁻¹ = σ)).filter
        (fun σ => Quotient.mk rel σ = Quotient.mk rel σ₀) = fib := by
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, fib]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        rcases Finset.card_eq_one.mp h1 with ⟨a, ha⟩
        have hσfib : σ ∈ fib := by
          simp only [fib, Finset.mem_filter, Finset.mem_univ, true_and]
          exact h
        have hσa : σ = a := Finset.mem_singleton.mp (ha ▸ hσfib)
        have h0a : σ₀ = a := Finset.mem_singleton.mp (ha ▸ (by simp [fib] : σ₀ ∈ fib))
        rw [hσa, ← h0a]
        exact hfix
    rw [hsub]
  · have hLHS : ∑ σ ∈ fib, f σ = 0 := by
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, hp_card, nsmul_eq_mul,
          ZMod.natCast_self, zero_mul]
    have hRHS_empty : (Finset.univ.filter (fun σ => shiftPerm p * σ * (shiftPerm p)⁻¹ = σ)).filter
        (fun σ => Quotient.mk rel σ = Quotient.mk rel σ₀) = ∅ := by
      ext σ
      simp only [Finset.notMem_empty, iff_false]
      intro hσ
      have hfix : shiftPerm p * σ * (shiftPerm p)⁻¹ = σ := (Finset.mem_filter.mp (Finset.mem_filter.mp hσ).1).2
      have hfix_pow : ∀ r : ℕ, shiftPerm p ^ r * σ * (shiftPerm p ^ r)⁻¹ = σ := by
        intro r; induction r with
        | zero => simp
        | succ r ih =>
          rw [pow_succ', _root_.mul_inv_rev]
          calc shiftPerm p * shiftPerm p ^ r * σ * ((shiftPerm p ^ r)⁻¹ * (shiftPerm p)⁻¹)
              = shiftPerm p * (shiftPerm p ^ r * σ * (shiftPerm p ^ r)⁻¹) * (shiftPerm p)⁻¹ := by group
            _ = shiftPerm p * σ * (shiftPerm p)⁻¹ := by rw [ih]
            _ = σ := hfix
      have hσ_fib : σ ∈ fib := Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hσ).2⟩
      have hcard_le_one : fib.card ≤ 1 := by
        rw [Finset.card_le_one]
        intro x hx y hy
        have hxσ : rel x σ := Setoid.trans (Quotient.exact (Finset.mem_filter.mp hx).2)
            (Setoid.symm (Quotient.exact (Finset.mem_filter.mp hσ_fib).2))
        have hyσ : rel y σ := Setoid.trans (Quotient.exact (Finset.mem_filter.mp hy).2)
            (Setoid.symm (Quotient.exact (Finset.mem_filter.mp hσ_fib).2))
        rcases hxσ with ⟨rx, hrx⟩
        rcases hyσ with ⟨ry, hry⟩
        have hx' : x = σ := by rw [← hrx]; exact hfix_pow (Multiplicative.toAdd rx).val
        have hy' : y = σ := by rw [← hry]; exact hfix_pow (Multiplicative.toAdd ry).val
        rw [hx', hy']
      have hp_gt : 1 < p := (Fact.out : p.Prime).one_lt
      omega
    rw [hLHS, hRHS_empty, Finset.sum_empty]

/-! ### Step 2: Fixed points are powers `shiftPerm p ^ c` -/

lemma fixed_iff_exists_pow (p : ℕ) [NeZero p] (σ : Equiv.Perm (Fin p)) :
    shiftPerm p * σ * (shiftPerm p)⁻¹ = σ ↔ ∃ c : Fin p, σ = shiftPerm p ^ c.val := by
  constructor
  · intro hfix
    have hcomm : ∀ x : Fin p, σ (shiftPerm p x) = shiftPerm p (σ x) := by
      intro x
      have := congrArg (fun f : Equiv.Perm (Fin p) => f (shiftPerm p x)) hfix
      simpa [Equiv.Perm.mul_apply] using this.symm
    refine ⟨σ ⟨0, NeZero.pos p⟩, ?_⟩
    ext x
    rw [shiftPerm_pow_apply]
    rcases x with ⟨n, hn⟩
    induction n with
    | zero =>
      simp only [Nat.zero_add]
      exact (Nat.mod_eq_of_lt (σ ⟨0, NeZero.pos p⟩).isLt).symm
    | succ m ih =>
      have hm : m < p := Nat.lt_of_succ_lt hn
      have hshift : shiftPerm p ⟨m, hm⟩ = ⟨m + 1, hn⟩ := by
        ext; simp [shiftPerm, Nat.mod_eq_of_lt hn]
      have hstep := congrArg Fin.val (hcomm ⟨m, hm⟩)
      rw [hshift] at hstep
      change (σ ⟨m + 1, hn⟩).val = (m + 1 + (σ ⟨0, NeZero.pos p⟩).val) % p
      rw [hstep]
      change ((σ ⟨m, hm⟩).val + 1) % p = _
      rw [ih hm, Nat.mod_add_mod]
      ring_nf
  · rintro ⟨c, rfl⟩
    rw [← pow_succ', pow_succ]
    group

lemma permanent_eq_sum_prod {p : ℕ} (M : Matrix (Fin p) (Fin p) (ZMod p)) :
    M.permanent = ∑ σ : Equiv.Perm (Fin p), ∏ i : Fin p, M i (σ i) := by
  rw [Matrix.permanent]
  refine Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin p))) _ _ ?_
  intro σ
  change ∏ i, M (σ i) i = ∏ i, M i (σ⁻¹ i)
  rw [← Equiv.prod_comp σ (fun i => M i (σ⁻¹ i))]
  simp

lemma det_eq_sum_sign_prod {p : ℕ} (M : Matrix (Fin p) (Fin p) (ZMod p)) :
    M.det = ∑ σ : Equiv.Perm (Fin p), (Equiv.Perm.sign σ : ZMod p) * ∏ i : Fin p, M i (σ i) := by
  rw [← Matrix.det_transpose M, Matrix.det_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp [Matrix.transpose_apply, Units.smul_def, zsmul_eq_mul]

/-! ### Step 3: Master Theorem (`perm M = det M` in `ZMod p`) -/

/--
**Master Theorem (Signed Cyclic-Shift Invariance):**
For any odd prime `p` and any `M : Matrix (Fin p) (Fin p) (ZMod p)` satisfying
`M (T i) (T j) = ε i * ε j * M i j`, we have `M.permanent = M.det` in `ZMod p`.
-/
theorem perm_eq_det_of_signed_shift (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (M : Matrix (Fin p) (Fin p) (ZMod p))
    (hshift : ∀ i j : Fin p, M (shiftPerm p i) (shiftPerm p j) = epsSign p i * epsSign p j * M i j) :
    M.permanent = M.det := by
  let W : Equiv.Perm (Fin p) → ZMod p := fun σ => ∏ i : Fin p, M i (σ i)
  have hW_inv : ∀ σ : Equiv.Perm (Fin p), W (shiftPerm p * σ * (shiftPerm p)⁻¹) = W σ := by
    intro σ
    dsimp only [W]
    rw [← Equiv.prod_comp (shiftPerm p)]
    have hterm : ∀ i : Fin p,
        M (shiftPerm p i) ((shiftPerm p * σ * (shiftPerm p)⁻¹) (shiftPerm p i)) =
          epsSign p i * epsSign p (σ i) * M i (σ i) := by
      intro i
      have hcomp : (shiftPerm p * σ * (shiftPerm p)⁻¹) (shiftPerm p i) = shiftPerm p (σ i) := by
        simp [Equiv.Perm.mul_apply]
      rw [hcomp, hshift]
    simp_rw [hterm, Finset.prod_mul_distrib]
    rw [prod_epsSign, Equiv.prod_comp σ (epsSign p), prod_epsSign]; ring
  have hSW_inv : ∀ σ : Equiv.Perm (Fin p),
      (Equiv.Perm.sign (shiftPerm p * σ * (shiftPerm p)⁻¹) : ZMod p) *
        W (shiftPerm p * σ * (shiftPerm p)⁻¹) =
      (Equiv.Perm.sign σ : ZMod p) * W σ := by
    intro σ
    rw [hW_inv, map_mul, map_mul, map_inv, mul_comm (Equiv.Perm.sign (shiftPerm p)),
        mul_assoc, mul_inv_cancel, mul_one]
  have hperm : M.permanent = ∑ σ : Equiv.Perm (Fin p), W σ := permanent_eq_sum_prod M
  have hdet : M.det = ∑ σ : Equiv.Perm (Fin p), (Equiv.Perm.sign σ : ZMod p) * W σ :=
    det_eq_sum_sign_prod M
  rw [hperm, hdet, sum_eq_sum_fixed_of_conj_invariant p W hW_inv,
      sum_eq_sum_fixed_of_conj_invariant p (fun σ => (Equiv.Perm.sign σ : ZMod p) * W σ) hSW_inv]
  refine Finset.sum_congr rfl ?_
  intro σ hσ
  have hfix : shiftPerm p * σ * (shiftPerm p)⁻¹ = σ := (Finset.mem_filter.mp hσ).2
  rcases (fixed_iff_exists_pow p σ).mp hfix with ⟨c, rfl⟩
  have hsign : Equiv.Perm.sign (shiftPerm p ^ c.val) = 1 := by
    rw [map_pow, shiftPerm_sign p hp2, one_pow]
  rw [hsign]; simp

/-! ### Step 4: Both halves of Zhi-Wei Sun's Conjecture 4.2(i) (Eqs. 4.3 & 4.4) -/

/-- Matrix `A[i, j] = |i - j|` in `ZMod p` (OEIS A085807 / Eq. 4.3). -/
def matAbsDiff (p : ℕ) : Matrix (Fin p) (Fin p) (ZMod p) :=
  fun i j => ((|(i.val : ℤ) - (j.val : ℤ)| : ℤ) : ZMod p)

/-- Matrix `B[i, j] = |i - j + 1|` in `ZMod p` (Eq. 4.4). -/
def matAbsDiffShift1 (p : ℕ) : Matrix (Fin p) (Fin p) (ZMod p) :=
  fun i j => ((|(i.val : ℤ) - (j.val : ℤ) + 1| : ℤ) : ZMod p)

lemma matAbsDiff_signed_shift (p : ℕ) [NeZero p] (i j : Fin p) :
    matAbsDiff p (shiftPerm p i) (shiftPerm p j) = epsSign p i * epsSign p j * matAbsDiff p i j := by
  have hp := NeZero.pos p; have hi := i.isLt; have hj := j.isLt
  unfold matAbsDiff epsSign shiftPerm; dsimp only [Equiv.coe_fn_mk]
  by_cases hi_top : i.val = p - 1 <;> by_cases hj_top : j.val = p - 1
  · simp [hi_top, hj_top]
  · have hj1 : j.val + 1 < p := by omega
    have hi1 : (i.val + 1) % p = 0 := by rw [hi_top, show p - 1 + 1 = p by omega, Nat.mod_self]
    rw [ite_eq_left hi_top, ite_eq_right hj_top, hi1, Nat.mod_eq_of_lt hj1]
    have hL : |(0 : ℤ) - ((j.val + 1 : ℕ) : ℤ)| = (j.val + 1 : ℤ) := by
      rw [zero_sub, abs_neg, abs_of_nonneg (by positivity)]
      norm_num
    have hR : |(i.val : ℤ) - (j.val : ℤ)| = (p : ℤ) - ((j.val + 1 : ℕ) : ℤ) := by
      rw [abs_of_nonneg (by omega)]; omega
    simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_add] at hL hR ⊢
    rw [hL, hR]; push_cast; simp
  · have hi1 : i.val + 1 < p := by omega
    have hj1 : (j.val + 1) % p = 0 := by rw [hj_top, show p - 1 + 1 = p by omega, Nat.mod_self]
    rw [ite_eq_right hi_top, ite_eq_left hj_top, hj1, Nat.mod_eq_of_lt hi1]
    have hL : |((i.val + 1 : ℕ) : ℤ) - 0| = (i.val + 1 : ℤ) := by
      rw [sub_zero, abs_of_nonneg (by positivity)]
      norm_num
    have hR : |(i.val : ℤ) - (j.val : ℤ)| = (p : ℤ) - ((i.val + 1 : ℕ) : ℤ) := by
      rw [abs_of_nonpos (by omega)]; omega
    simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_add] at hL hR ⊢
    rw [hL, hR]; push_cast; simp
  · have hi1 : i.val + 1 < p := by omega
    have hj1 : j.val + 1 < p := by omega
    rw [ite_eq_right hi_top, ite_eq_right hj_top, Nat.mod_eq_of_lt hi1, Nat.mod_eq_of_lt hj1]
    have hEq : |((i.val + 1 : ℕ) : ℤ) - ((j.val + 1 : ℕ) : ℤ)| = |(i.val : ℤ) - (j.val : ℤ)| := by
      congr 1
      push_cast
      ring
    rw [hEq, one_mul, one_mul]

lemma matAbsDiffShift1_signed_shift (p : ℕ) [NeZero p] (i j : Fin p) :
    matAbsDiffShift1 p (shiftPerm p i) (shiftPerm p j) =
      epsSign p i * epsSign p j * matAbsDiffShift1 p i j := by
  have hp := NeZero.pos p; have hi := i.isLt; have hj := j.isLt
  unfold matAbsDiffShift1 epsSign shiftPerm; dsimp only [Equiv.coe_fn_mk]
  by_cases hi_top : i.val = p - 1 <;> by_cases hj_top : j.val = p - 1
  · have hi1 : (i.val + 1) % p = 0 := by rw [hi_top, show p - 1 + 1 = p by omega, Nat.mod_self]
    have hj1 : (j.val + 1) % p = 0 := by rw [hj_top, show p - 1 + 1 = p by omega, Nat.mod_self]
    rw [ite_eq_left hi_top, ite_eq_left hj_top, hi1, hj1]
    simp [hi_top, hj_top]
  · have hj1 : j.val + 1 < p := by omega
    have hi1 : (i.val + 1) % p = 0 := by rw [hi_top, show p - 1 + 1 = p by omega, Nat.mod_self]
    rw [ite_eq_left hi_top, ite_eq_right hj_top, hi1, Nat.mod_eq_of_lt hj1]
    have hL : |(0 : ℤ) - ((j.val + 1 : ℕ) : ℤ) + 1| = (j.val : ℤ) := by
      push_cast; rw [show (0 : ℤ) - ((j.val : ℤ) + 1) + 1 = -(j.val : ℤ) by ring,
        abs_neg, abs_of_nonneg (by positivity)]
    have hR : |(i.val : ℤ) - (j.val : ℤ) + 1| = (p : ℤ) - (j.val : ℤ) := by
      rw [abs_of_nonneg (by omega)]; omega
    simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_add] at hL hR ⊢
    rw [hL, hR]; push_cast; simp
  · have hi1 : i.val + 1 < p := by omega
    have hj1 : (j.val + 1) % p = 0 := by rw [hj_top, show p - 1 + 1 = p by omega, Nat.mod_self]
    rw [ite_eq_right hi_top, ite_eq_left hj_top, hj1, Nat.mod_eq_of_lt hi1]
    have hL : |((i.val + 1 : ℕ) : ℤ) - 0 + 1| = (i.val + 2 : ℤ) := by
      push_cast; rw [sub_zero, abs_of_nonneg (by positivity)]; ring
    have hR : |(i.val : ℤ) - (j.val : ℤ) + 1| = (p : ℤ) - (i.val + 2 : ℤ) := by
      rw [abs_of_nonpos (by omega)]; omega
    simp only [Nat.cast_zero, Nat.cast_one, Nat.cast_add] at hL hR ⊢
    rw [hL, hR]; push_cast; simp
  · have hi1 : i.val + 1 < p := by omega
    have hj1 : j.val + 1 < p := by omega
    rw [ite_eq_right hi_top, ite_eq_right hj_top, Nat.mod_eq_of_lt hi1, Nat.mod_eq_of_lt hj1]
    have hEq : |((i.val + 1 : ℕ) : ℤ) - ((j.val + 1 : ℕ) : ℤ) + 1| =
        |(i.val : ℤ) - (j.val : ℤ) + 1| := by
      congr 1
      push_cast
      ring
    rw [hEq, one_mul, one_mul]

/-- Fixed-point weight for `matAbsDiff p`: `(-1)^c * c` in `ZMod p`. -/
lemma matAbsDiff_fixed_weight (p : ℕ) [Fact p.Prime] (c : Fin p) :
    ∏ i : Fin p, matAbsDiff p i ((shiftPerm p ^ c.val) i) =
      (-1 : ZMod p) ^ c.val * (c.val : ZMod p) := by
  by_cases hc0 : c.val = 0
  · have h0 : (⟨0, NeZero.pos p⟩ : Fin p) ∈ (Finset.univ : Finset (Fin p)) := Finset.mem_univ _
    have hz : matAbsDiff p ⟨0, NeZero.pos p⟩ ((shiftPerm p ^ c.val) ⟨0, NeZero.pos p⟩) = 0 := by
      simp [matAbsDiff, hc0]
    rw [Finset.prod_eq_zero h0 hz, hc0]; simp
  · have hc_lt := c.isLt
    let S₁ : Finset (Fin p) := Finset.univ.filter (fun i => i.val < p - c.val)
    let S₂ : Finset (Fin p) := Finset.univ.filter (fun i => ¬ (i.val < p - c.val))
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : Fin p => i.val < p - c.val)]
    have hS1 : ∀ i ∈ S₁, matAbsDiff p i ((shiftPerm p ^ c.val) i) = (c.val : ZMod p) := by
      intro i hi
      have hlt : i.val < p - c.val := (Finset.mem_filter.mp hi).2
      unfold matAbsDiff
      rw [shiftPerm_pow_apply, Nat.mod_eq_of_lt (by omega : i.val + c.val < p)]
      have : |(i.val : ℤ) - ((i.val + c.val : ℕ) : ℤ)| = (c.val : ℤ) := by
        push_cast; rw [show (i.val : ℤ) - ((i.val : ℤ) + (c.val : ℤ)) = -(c.val : ℤ) by ring,
          abs_neg, abs_of_nonneg (by positivity)]
      rw [this]; norm_cast
    have hS2 : ∀ i ∈ S₂, matAbsDiff p i ((shiftPerm p ^ c.val) i) = -(c.val : ZMod p) := by
      intro i hi
      have hge : p - c.val ≤ i.val := Nat.le_of_not_lt (Finset.mem_filter.mp hi).2
      have hi_lt := i.isLt
      unfold matAbsDiff
      rw [shiftPerm_pow_apply,
          show (i.val + c.val) % p = i.val + c.val - p by
            rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]]
      have : |(i.val : ℤ) - ((i.val + c.val - p : ℕ) : ℤ)| = (p : ℤ) - (c.val : ℤ) := by
        rw [abs_of_nonneg (by omega)]; omega
      rw [this]; push_cast; simp
    rw [Finset.prod_congr rfl hS1, Finset.prod_congr rfl hS2,
        Finset.prod_const, Finset.prod_const]
    have hcard1 : S₁.card = p - c.val := by
      have h : S₁.card = (Finset.univ : Finset (Fin (p - c.val))).card := by
        refine Finset.card_bij (fun (i : Fin p) (hi : i ∈ S₁) => ⟨i.val, ?_⟩) ?_ ?_ ?_
        · exact (Finset.mem_filter.mp hi).2
        · intro i hi; exact Finset.mem_univ _
        · intro i hi j hj h
          exact Fin.ext (congrArg (fun x : Fin (p - c.val) => x.val) h)
        · intro j hj
          refine ⟨⟨j.val, by omega⟩, ?_, ?_⟩
          · simp [S₁]
          · exact Fin.ext rfl
      simpa using h
    have hcard2 : S₂.card = c.val := by
      have hadd := Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin p))) (p := fun i : Fin p => i.val < p - c.val)
      simp only [Finset.card_univ, Fintype.card_fin] at hadd
      have hadd' : S₁.card + S₂.card = p := hadd
      omega
    rw [hcard1, hcard2]
    calc (c.val : ZMod p) ^ (p - c.val) * (-(c.val : ZMod p)) ^ c.val
        = (-1 : ZMod p) ^ c.val * (c.val : ZMod p) ^ (p - c.val + c.val) := by
            rw [neg_eq_neg_one_mul, mul_pow, pow_add]; ring
      _ = (-1 : ZMod p) ^ c.val * (c.val : ZMod p) ^ p := by rw [Nat.sub_add_cancel (le_of_lt hc_lt)]
      _ = (-1 : ZMod p) ^ c.val * (c.val : ZMod p) := by rw [ZMod.pow_card]

/-- Fixed-point weight for `matAbsDiffShift1 p`:
equals `1` if `c = 0`, and `(-1)^c * (c - 1)` if `c ≥ 1`. -/
lemma matAbsDiffShift1_fixed_weight (p : ℕ) [Fact p.Prime] (c : Fin p) :
    ∏ i : Fin p, matAbsDiffShift1 p i ((shiftPerm p ^ c.val) i) =
      if c.val = 0 then (1 : ZMod p) else (-1 : ZMod p) ^ c.val * ((c.val : ZMod p) - 1) := by
  by_cases hc0 : c.val = 0
  · rw [ite_eq_left hc0]
    have h1 : ∀ i : Fin p, matAbsDiffShift1 p i ((shiftPerm p ^ c.val) i) = 1 := by
      intro i; simp [matAbsDiffShift1, hc0]
    simp [h1]
  · rw [ite_eq_right hc0]
    by_cases hc1 : c.val = 1
    · have h0 : (⟨0, NeZero.pos p⟩ : Fin p) ∈ (Finset.univ : Finset (Fin p)) := Finset.mem_univ _
      have hp_gt : 1 < p := (Fact.out : p.Prime).one_lt
      have hz : matAbsDiffShift1 p ⟨0, NeZero.pos p⟩ ((shiftPerm p ^ c.val) ⟨0, NeZero.pos p⟩) = 0 := by
        unfold matAbsDiffShift1
        rw [shiftPerm_pow_apply, hc1, zero_add, Nat.mod_eq_of_lt hp_gt]
        simp
      rw [Finset.prod_eq_zero h0 hz, hc1]; simp
    · have hc_lt := c.isLt
      have hc_ge2 : 2 ≤ c.val := by omega
      let S₁ : Finset (Fin p) := Finset.univ.filter (fun i => i.val < p - c.val)
      let S₂ : Finset (Fin p) := Finset.univ.filter (fun i => ¬ (i.val < p - c.val))
      rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : Fin p => i.val < p - c.val)]
      have hS1 : ∀ i ∈ S₁, matAbsDiffShift1 p i ((shiftPerm p ^ c.val) i) = (c.val : ZMod p) - 1 := by
        intro i hi
        have hlt : i.val < p - c.val := (Finset.mem_filter.mp hi).2
        unfold matAbsDiffShift1
        rw [shiftPerm_pow_apply, Nat.mod_eq_of_lt (by omega : i.val + c.val < p)]
        have : |(i.val : ℤ) - ((i.val + c.val : ℕ) : ℤ) + 1| = (c.val : ℤ) - 1 := by
          rw [abs_of_nonpos (by omega)]; omega
        rw [this]; push_cast; ring
      have hS2 : ∀ i ∈ S₂, matAbsDiffShift1 p i ((shiftPerm p ^ c.val) i) = -((c.val : ZMod p) - 1) := by
        intro i hi
        have hge : p - c.val ≤ i.val := Nat.le_of_not_lt (Finset.mem_filter.mp hi).2
        have hi_lt := i.isLt
        unfold matAbsDiffShift1
        rw [shiftPerm_pow_apply,
            show (i.val + c.val) % p = i.val + c.val - p by
              rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]]
        have : |(i.val : ℤ) - ((i.val + c.val - p : ℕ) : ℤ) + 1| = (p : ℤ) - ((c.val : ℤ) - 1) := by
          rw [abs_of_nonneg (by omega)]; omega
        rw [this]; push_cast; simp
      rw [Finset.prod_congr rfl hS1, Finset.prod_congr rfl hS2,
          Finset.prod_const, Finset.prod_const]
      have hcard1 : S₁.card = p - c.val := by
        have h : S₁.card = (Finset.univ : Finset (Fin (p - c.val))).card := by
          refine Finset.card_bij (fun (i : Fin p) (hi : i ∈ S₁) => ⟨i.val, ?_⟩) ?_ ?_ ?_
          · exact (Finset.mem_filter.mp hi).2
          · intro i hi; exact Finset.mem_univ _
          · intro i hi j hj h
            exact Fin.ext (congrArg (fun x : Fin (p - c.val) => x.val) h)
          · intro j hj
            refine ⟨⟨j.val, by omega⟩, ?_, ?_⟩
            · simp [S₁]
            · exact Fin.ext rfl
        simpa using h
      have hcard2 : S₂.card = c.val := by
        have hadd := Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (Fin p))) (p := fun i : Fin p => i.val < p - c.val)
        simp only [Finset.card_univ, Fintype.card_fin] at hadd
        have hadd' : S₁.card + S₂.card = p := hadd
        omega
      rw [hcard1, hcard2]
      calc ((c.val : ZMod p) - 1) ^ (p - c.val) * (-((c.val : ZMod p) - 1)) ^ c.val
          = (-1 : ZMod p) ^ c.val * ((c.val : ZMod p) - 1) ^ (p - c.val + c.val) := by
              rw [neg_eq_neg_one_mul, mul_pow, pow_add]; ring
        _ = (-1 : ZMod p) ^ c.val * ((c.val : ZMod p) - 1) ^ p := by
              rw [Nat.sub_add_cancel (le_of_lt hc_lt)]
        _ = (-1 : ZMod p) ^ c.val * ((c.val : ZMod p) - 1) := by
              rw [ZMod.pow_card]

/-- Alternating sum `2 * ∑_{c=0}^{p-1} (-1)^c * c = -1` in `ZMod p` for odd prime `p`. -/
lemma two_mul_alt_sum (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : ZMod p) * ∑ c : Fin p, (-1 : ZMod p) ^ c.val * (c.val : ZMod p) = -1 := by
  have hp_odd : p % 2 = 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with rfl | hodd
    · exact absurd rfl hp2
    · exact hodd
  obtain ⟨m, hm⟩ : ∃ m : ℕ, p = 2 * m + 1 := ⟨p / 2, by omega⟩
  have hint : ∀ k : ℕ, ∑ c ∈ Finset.range (2 * k + 1), (-1 : ℤ) ^ c * (c : ℤ) = (k : ℤ) := by
    intro k; induction k with
    | zero => simp
    | succ k ih =>
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega,
          Finset.sum_range_succ, Finset.sum_range_succ, ih]
      have h1 : (-1 : ℤ) ^ (2 * k + 2) = 1 := by
        rw [show 2 * k + 2 = 2 * (k + 1) by omega, pow_mul]; norm_num
      have h2 : (-1 : ℤ) ^ (2 * k + 1) = -1 := by
        rw [pow_succ, pow_mul]; norm_num
      rw [h1, h2]; push_cast; ring
  have hcast : ∑ c : Fin p, (-1 : ZMod p) ^ c.val * (c.val : ZMod p) = (m : ZMod p) := by
    have hfin : ∑ c : Fin p, (-1 : ZMod p) ^ c.val * (c.val : ZMod p)
        = ((∑ c ∈ Finset.range p, (-1 : ℤ) ^ c * (c : ℤ)) : ZMod p) := by
      rw [Fin.sum_univ_eq_sum_range (fun k => (-1 : ZMod p) ^ k * (k : ZMod p))]
      push_cast
      rfl
    rw [hfin]
    have hz : (∑ c ∈ Finset.range p, (-1 : ℤ) ^ c * (c : ℤ)) = (m : ℤ) := by
      rw [hm, hint m]
    have hcastz : ((∑ c ∈ Finset.range p, (-1 : ℤ) ^ c * (c : ℤ)) : ZMod p) = (m : ZMod p) := by
      have hzZ := congrArg (fun z : ℤ => (z : ZMod p)) hz
      simpa using hzZ
    rw [← hcastz]
  rw [hcast]
  have h2m : (2 : ZMod p) * (m : ZMod p) + 1 = 0 := by
    have : ((2 * m + 1 : ℕ) : ZMod p) = 0 := by rw [← hm, ZMod.natCast_self]
    simpa [Nat.cast_add, Nat.cast_mul] using this
  linear_combination h2m

/-- Alternating sum `∑_{c=0}^{p-1} (-1)^c = 1` in `ZMod p` for odd prime `p`. -/
lemma alt_ones_sum (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ∑ c : Fin p, (-1 : ZMod p) ^ c.val = 1 := by
  have hp_odd : p % 2 = 1 := by
    rcases (Fact.out : p.Prime).eq_two_or_odd with rfl | hodd
    · exact absurd rfl hp2
    · exact hodd
  obtain ⟨m, hm⟩ : ∃ m : ℕ, p = 2 * m + 1 := ⟨p / 2, by omega⟩
  have hint : ∀ k : ℕ, ∑ c ∈ Finset.range (2 * k + 1), (-1 : ℤ) ^ c = 1 := by
    intro k; induction k with
    | zero => simp
    | succ k ih =>
      rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega,
          Finset.sum_range_succ, Finset.sum_range_succ, ih]
      have h1 : (-1 : ℤ) ^ (2 * k + 2) = 1 := by
        rw [show 2 * k + 2 = 2 * (k + 1) by omega, pow_mul]; norm_num
      have h2 : (-1 : ℤ) ^ (2 * k + 1) = -1 := by
        rw [pow_succ, pow_mul]; norm_num
      rw [h1, h2]; ring
  have hfin : ∑ c : Fin p, (-1 : ZMod p) ^ c.val
      = ((∑ c ∈ Finset.range p, (-1 : ℤ) ^ c) : ZMod p) := by
    rw [Fin.sum_univ_eq_sum_range (fun k => (-1 : ZMod p) ^ k)]
    push_cast
    rfl
  rw [hfin]
  have hz : (∑ c ∈ Finset.range p, (-1 : ℤ) ^ c) = (1 : ℤ) := by
    rw [hm, hint m]
  have hcastz : ((∑ c ∈ Finset.range p, (-1 : ℤ) ^ c) : ZMod p) = (1 : ZMod p) := by
    have hzZ := congrArg (fun z : ℤ => (z : ZMod p)) hz
    simpa using hzZ
  rw [← hcastz]

/-- Helper: reduce permanent of any signed-shift-invariant matrix to a sum over `c : Fin p`. -/
lemma perm_eq_sum_pow (p : ℕ) [Fact p.Prime]
    (M : Matrix (Fin p) (Fin p) (ZMod p))
    (hshift : ∀ i j : Fin p, M (shiftPerm p i) (shiftPerm p j) = epsSign p i * epsSign p j * M i j) :
    M.permanent = ∑ c : Fin p, ∏ i : Fin p, M i ((shiftPerm p ^ c.val) i) := by
  let W : Equiv.Perm (Fin p) → ZMod p := fun σ => ∏ i : Fin p, M i (σ i)
  have hW_inv : ∀ σ : Equiv.Perm (Fin p), W (shiftPerm p * σ * (shiftPerm p)⁻¹) = W σ := by
    intro σ; dsimp only [W]; rw [← Equiv.prod_comp (shiftPerm p)]
    have hterm : ∀ i : Fin p,
        M (shiftPerm p i) ((shiftPerm p * σ * (shiftPerm p)⁻¹) (shiftPerm p i)) =
          epsSign p i * epsSign p (σ i) * M i (σ i) := by
      intro i
      have hc : (shiftPerm p * σ * (shiftPerm p)⁻¹) (shiftPerm p i) = shiftPerm p (σ i) := by
        simp [Equiv.Perm.mul_apply]
      rw [hc, hshift]
    simp_rw [hterm, Finset.prod_mul_distrib]
    rw [prod_epsSign, Equiv.prod_comp σ (epsSign p), prod_epsSign]; ring
  rw [permanent_eq_sum_prod (p := p) M]
  change ∑ σ : Equiv.Perm (Fin p), W σ = _
  rw [sum_eq_sum_fixed_of_conj_invariant p W hW_inv]
  have hfixed :
      Finset.univ.filter (fun σ : Equiv.Perm (Fin p) => shiftPerm p * σ * (shiftPerm p)⁻¹ = σ) =
        Finset.univ.image (fun c : Fin p => shiftPerm p ^ c.val) := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      obtain ⟨c, hc⟩ := (fixed_iff_exists_pow p σ).mp h
      exact ⟨c, hc.symm⟩
    · rintro ⟨a, ha⟩
      exact (fixed_iff_exists_pow p σ).mpr ⟨a, ha.symm⟩
  have hinj : Function.Injective (fun c : Fin p => shiftPerm p ^ c.val) := by
    intro c₁ c₂ h
    have h0 := congrArg (fun f : Equiv.Perm (Fin p) => (f ⟨0, NeZero.pos p⟩).val) h
    simp only [shiftPerm_pow_apply, zero_add, Nat.mod_eq_of_lt c₁.isLt, Nat.mod_eq_of_lt c₂.isLt] at h0
    exact Fin.ext h0
  rw [hfixed, Finset.sum_image (fun a _ b _ h => hinj h)]

/--
**Theorem 1 (Zhi-Wei Sun, Conjecture 4.2(i), Eq. 4.3 / OEIS A085807):**
For every odd prime `p`, `2 * per[|i - j|] = -1` in `ZMod p`.
-/
theorem sun_conjecture_4_2_i_eq_4_3 (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : ZMod p) * (matAbsDiff p).permanent = -1 := by
  rw [perm_eq_sum_pow p (matAbsDiff p) (matAbsDiff_signed_shift p)]
  simp_rw [matAbsDiff_fixed_weight p]
  exact two_mul_alt_sum p hp2

/--
**Theorem 2 (Zhi-Wei Sun, Conjecture 4.2(i), Eq. 4.4):**
For every odd prime `p`, `2 * per[|i - j + 1|] = 1` in `ZMod p`.
-/
theorem sun_conjecture_4_2_i_eq_4_4 (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    (2 : ZMod p) * (matAbsDiffShift1 p).permanent = 1 := by
  rw [perm_eq_sum_pow p (matAbsDiffShift1 p) (matAbsDiffShift1_signed_shift p)]
  simp_rw [matAbsDiffShift1_fixed_weight p]
  -- Compare `if c = 0 then 1 else (-1)^c * (c - 1)` with `(-1)^c * (c - 1) + (if c = 0 then 2 else 0)`.
  have hrewrite :
      ∑ c : Fin p, (if c.val = 0 then (1 : ZMod p) else (-1 : ZMod p) ^ c.val * ((c.val : ZMod p) - 1)) =
        (∑ c : Fin p, (-1 : ZMod p) ^ c.val * (c.val : ZMod p)) -
          (∑ c : Fin p, (-1 : ZMod p) ^ c.val) + 2 := by
    have hpt : ∀ c : Fin p,
        (if c.val = 0 then (1 : ZMod p) else (-1 : ZMod p) ^ c.val * ((c.val : ZMod p) - 1)) =
          ((-1 : ZMod p) ^ c.val * (c.val : ZMod p) - (-1 : ZMod p) ^ c.val) +
            (if c = ⟨0, NeZero.pos p⟩ then (2 : ZMod p) else 0) := by
      intro c
      by_cases hc : c.val = 0
      · have hceq : c = ⟨0, NeZero.pos p⟩ := Fin.ext hc
        rw [ite_eq_left hc, ite_eq_left hceq, hc]; ring
      · have hcne : c ≠ ⟨0, NeZero.pos p⟩ := fun h => hc (congrArg Fin.val h)
        rw [ite_eq_right hc, ite_eq_right hcne]; ring
    simp_rw [hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq',
        Finset.mem_univ]
    simp
  rw [hrewrite, mul_add, mul_sub, two_mul_alt_sum p hp2, alt_ones_sum p hp2]
  ring

end SunConjecture42i
