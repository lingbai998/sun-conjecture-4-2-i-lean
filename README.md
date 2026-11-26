# Proof and Lean 4 Formalization of Zhi-Wei Sun's Conjecture 4.2(i) (OEIS A085807)

This repository contains a self-contained proof and kernel-verified, zero-`sorry` **Lean 4 / Mathlib 4** formalization of **Conjecture 4.2(i)** from Zhi-Wei Sun's paper [*Arithmetic properties of some permanents*](https://arxiv.org/html/2108.07723v7) (arXiv:2108.07723v7, Eqs. 4.3 & 4.4), also listed as an open conjecture on [OEIS A085807](https://oeis.org/A085807).

> **Independent proof and formalization.** This repository is an independent proof and Lean 4 formalization. After completing it we learned that the same conjecture had already been resolved in the AI-assisted open-problem registry **the-omega-institute/trureturing**: it was pre-registered as Issue [#22003](https://github.com/the-omega-institute/trureturing/issues/22003) on 2026-10-26, and its Lean 4 proof was merged in PR [#23353](https://github.com/the-omega-institute/trureturing/pull/23353) on 2026-10-29 (merge commit [`fe03ef4`](https://github.com/the-omega-institute/trureturing/commit/fe03ef488008aa93b395beab4d1b876d2c2efd98)). The present work was carried out independently and does not claim priority. Its distinguishing features are: (i) a self-contained proof of the general master theorem $\mathrm{per}(M)\equiv\det(M)\pmod p$ for signed cyclic-shift invariant matrices, without invoking the Brualdi–Newman (1965) circulant-matrix theorem; and (ii) extensions to powers $|j-k|^m$, odd prime powers $p^k$, and the exact shift boundary $s=-1$, $s=0$, or $s=1$.

## Main Results

Let $p$ be an odd prime.

1. **Signed Cyclic-Shift Invariance Master Theorem** (`SunConjecture42i.perm_eq_det_of_signed_shift`):
   Let $T(x) = (x+1) \bmod p$ on $\mathbb{Z}/p\mathbb{Z}$, and define the sign $\varepsilon(x) = -1$ if $x = p-1$ and $\varepsilon(x) = 1$ otherwise. If a matrix $M \in M_p(\mathbb{F}_p)$ satisfies

   $M_{T(i),T(j)} = \varepsilon(i)\varepsilon(j) M_{i,j} \quad \text{for all } i, j \in \mathbb{Z}/p\mathbb{Z}$,

   then

   $\mathrm{per}(M) \equiv \det(M) \pmod{p}.$

2. **Conjecture 4.2(i), Eq. (4.3) / OEIS A085807** (`SunConjecture42i.sun_conjecture_4_2_i_eq_4_3`):

   $\displaystyle \mathrm{per}[|j-k|] \equiv -\frac{1}{2} \pmod{p}, \qquad \text{i.e.,} \quad 2 \cdot \mathrm{per}[|j-k|] \equiv -1 \pmod{p}.$

3. **Conjecture 4.2(i), Eq. (4.4)** (`SunConjecture42i.sun_conjecture_4_2_i_eq_4_4`):

   $\displaystyle \mathrm{per}[|j-k+1|] \equiv \frac{1}{2} \pmod{p}, \qquad \text{i.e.,} \quad 2 \cdot \mathrm{per}[|j-k+1|] \equiv 1 \pmod{p}.$

### Extensions (Numerically Verified, Not Formalized in Lean)

The same cyclic-conjugation mechanism suggests several direct generalizations. They are checked numerically in `scripts/verify.py`; they are **not** formalized in `SunConjecture4_2_i.lean`:

* **Exact Shift Boundary**: The signed-shift invariance holds for $\mathrm{per}[|j-k+s|]$ precisely for $s \in \{-1, 0, 1\}$, and fails at $s = 2$ (for $p = 5$, $\det \equiv 0 \pmod 5$ while $\mathrm{per} \equiv 2 \pmod 5$).

* **General Powers**: For any integer $m \ge 1$ and odd prime $p$,

  $\displaystyle \mathrm{per}[|j-k|^m] \equiv \sum_{c=1}^{p-1} (-1)^{mc} c^m \pmod{p}.$

  In particular, for even $m$ this is $0 \pmod p$ if $(p-1)\nmid m$ and $-1 \pmod p$ if $(p-1)\mid m$; for odd $m$ it coincides with the Euler polynomial value $E_m(0) \pmod p$ (e.g., $-\frac{1}{2}$ for $m=1$, $\frac{1}{4}$ for $m=3$, $-\frac{1}{2}$ for $m=5$).

* **Odd Prime Powers**: For any odd prime $p$ and integer $k \ge 1$, $a(p^k) = \mathrm{per}[|j-k|]_{1 \le j,k \le p^k} \equiv -\frac{1}{2} \pmod p$ (and $a(2^k) \equiv 0 \pmod 2$ for $k \ge 2$).

## Proof Idea

Consider the cyclic shift permutation $\tau \in S_p$ given by $\tau(x) = (x+1) \bmod p$.

1. **Conjugation Invariance**: Since $\prod_{i=0}^{p-1} \varepsilon(i) = -1$, conjugating any $\sigma \in S_p$ by $\tau$ leaves the weight $w(\sigma) = \prod_i M_{i, \sigma(i)}$ invariant over $\mathbb{F}_p$:

   $\displaystyle w(\tau \sigma \tau^{-1}) = \left(\prod_{i} \varepsilon(i)\right)\left(\prod_{i} \varepsilon(\sigma(i))\right) w(\sigma) = (-1)^2 w(\sigma) = w(\sigma).$

2. **Orbit-Stabilizer Modulo** $p$: The cyclic group $\langle \tau \rangle \cong \mathbb{Z}/p\mathbb{Z}$ acts on $S_p$ by conjugation. Every non-trivial orbit has size $p$ (which vanishes in the field $\mathbb{F}$ of $p$ elements), so both $\mathrm{per}(M)$ and $\det(M)$ reduce modulo $p$ to the sum over the fixed points of conjugation—namely the centralizer of $\tau$ in $S_p$, $C(\tau) = \{\tau^c : 0 \le c < p\}$. Since $p$ is odd, $\tau$ is an even permutation, so every fixed point has sign $+1$, giving $\mathrm{per}(M) \equiv \det(M) \equiv \sum_{c=0}^{p-1} w(\tau^c) \pmod p$.

3. **Closed-Form Evaluation**:

   * For $M_{i,j} = |i-j|$, $w(\tau^0) = 0$ and for $1 \le c \le p-1$,

     $\displaystyle w(\tau^c) = c^{p-c}(p-c)^c \equiv (-1)^c c^p \equiv (-1)^c c \pmod p,$

     yielding $2 \sum_{c=1}^{p-1} (-1)^c c = -(p-1) \equiv -1 \pmod p$.

   * For $M_{i,j} = |i-j+1|$, the same calculation gives $w(\tau^c) \equiv (-1)^c (c-1) \pmod p$ for $c \ne 1$ (and $w(\tau^1) = 0$), yielding $2 \sum_{c=0}^{p-1} (-1)^c (c-1) \equiv 1 \pmod p$.

## Repository Structure

| File | Description |
| :--- | :--- |
| `SunConjecture4_2_i.lean` | Complete Lean 4 / Mathlib 4 formalization (zero `sorry`, zero `native_decide`) |
| `Axioms.lean` | `#print axioms` verification script for all three main theorems |
| `lakefile.toml` | Lake package configuration with Mathlib 4 dependency |
| `lean-toolchain` | Lean 4 toolchain pin (`leanprover/lean4:v4.37.0-rc1`) |
| `scripts/verify.py` | Independent Python numerical verification (Ryser's algorithm, extensions, shift boundary) |
| `LICENSE` | MIT License |

## Formalized Declarations (`SunConjecture4_2_i.lean`)

| Declaration | Mathematical Content |
| :--- | :--- |
| `SunConjecture42i.sum_eq_sum_fixed_of_conj_invariant` | Conjugation-invariant sums over $S_p$ reduce to fixed points in $\mathbb{F}_p$ |
| `SunConjecture42i.fixed_iff_exists_pow` | Centralizer of the $p$-cycle $\tau$ in $S_p$ is $\{\tau^c : 0 \le c < p\}$ |
| `SunConjecture42i.perm_eq_det_of_signed_shift` | Master Theorem: $\mathrm{per}(M) \equiv \det(M) \pmod p$ |
| `SunConjecture42i.sun_conjecture_4_2_i_eq_4_3` | Proof of Eq. (4.3) / [OEIS A085807](https://oeis.org/A085807): $2 \cdot \mathrm{per}[\vert j-k\vert] \equiv -1 \pmod p$ |
| `SunConjecture42i.sun_conjecture_4_2_i_eq_4_4` | Proof of Eq. (4.4): $2 \cdot \mathrm{per}[\vert j-k+1\vert] \equiv 1 \pmod p$ |

## Verification

### 1. Lean 4 Formal Verification (Verified on `Lean v4.37.0-rc1`)

```bash
lake exe cache get
lake build
lake env lean Axioms.lean
```

Verified output (`lake build` exited with `0` errors and `0` `sorry`):

```text
'SunConjecture42i.perm_eq_det_of_signed_shift' depends on axioms: [propext, Classical.choice, Quot.sound]
'SunConjecture42i.sun_conjecture_4_2_i_eq_4_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'SunConjecture42i.sun_conjecture_4_2_i_eq_4_4' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All three main theorems depend exclusively on the standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`).

### 2. Python Numerical Verification

```bash
python3 scripts/verify.py
```

## References

* Zhi-Wei Sun, *Arithmetic properties of some permanents*, [arXiv:2108.07723v7](https://arxiv.org/html/2108.07723v7) (2022), Conjecture 4.2(i), Eqs. (4.3) and (4.4).

* OEIS Foundation Inc., *Entry A085807: Permanent of the* $n \times n$ *matrix whose* $(i,j)$*-entry is* $|i-j|$, [https://oeis.org/A085807](https://oeis.org/A085807).
* the-omega-institute/trureturing, [Issue #22003](https://github.com/the-omega-institute/trureturing/issues/22003) / [PR #23353](https://github.com/the-omega-institute/trureturing/pull/23353), merged 2026-10-29 (commit `fe03ef4`), independent Lean 4 proof of the same conjecture.

## Acknowledgments

Proof discovery, generalization, and Lean 4 formalization were carried out with AI assistance and independently verified through Lean 4's kernel (`v4.37.0-rc1` + Mathlib 4) and exact Python computation.