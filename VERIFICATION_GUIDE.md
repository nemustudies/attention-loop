# Verification Guide

How to verify the Self-Referring Attention formalization without reading 7,509 lines of Lean.

## Quick version (5 minutes, any platform)

```bash
# 1. Read the theorem statement (one file, Mathlib-only types)
cat AttentionLoop/MainTheorem.lean

# 2. Confirm it imports only Mathlib
grep "^import" AttentionLoop/MainTheorem.lean
# Should show only "import Mathlib.*" lines. No "import AttentionLoop.*".

# 3. Build and verify axioms
lake build
lake env lean AttentionLoop/Verification.lean
# Should print: 'mainTheorem' depends on axioms: [propext, Classical.choice, Quot.sound]
```

That's it. If step 1 shows non-trivial mathematics, step 2 confirms no project
contamination, and step 3 shows only standard axioms, then Lean's kernel has
verified the entire proof chain from Mathlib-only statement through all 52 files.

## Verification tiers

### Tier 1: Standard (any platform)

Install [Lean 4](https://leanprover.github.io/lean4/doc/setup.html) via elan,
then:

```bash
lake build                              # build all ~2800 jobs
lake env lean AttentionLoop/Verification.lean  # check axioms
./validate.sh                           # full automated pipeline (checks 1-6)
```

This covers: build, sorry check, custom axiom check, True placeholder check,
axiom dependencies, and MainTheorem import isolation.

### Tier 2: lean4checker (optional, any platform)

[lean4checker](https://github.com/leanprover/lean4checker) replays every
declaration through a fresh Lean kernel, detecting any environment hacking.

```bash
# Install (one-time)
git clone https://github.com/leanprover/lean4checker
cd lean4checker && git checkout v4.28.0 && lake build && cd ..

# Run (after lake build)
lake env ../lean4checker/.lake/build/bin/lean4checker
```

If this passes, you are trusting only the Lean kernel implementation
(~10K lines of C++) and nothing else.

## Expected output

Running `./validate.sh` on a passing build produces:

```
=== Self-Referring Attention Validation ===

[1] Building...
  PASS: Build succeeded (287s)
[2] Checking for sorry...
  PASS: No sorry found
[3] Checking for custom axioms...
  PASS: No custom axioms
[4] Checking for True placeholders...
  PASS: No True placeholders
[5] Verifying axiom dependencies...
  'mainTheorem' depends on axioms: [propext, Classical.choice, Quot.sound]
  'convergence_under_consolidation' depends on axioms: [propext, Classical.choice, Quot.sound]
  'accumulation_rigidity_aggregate' depends on axioms: [propext, Classical.choice, Quot.sound]
  'accum_sublinear_implies_sigma_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
  'accum_superlinear_implies_sigma_unbounded' depends on axioms: [propext, Classical.choice, Quot.sound]
  'softmax_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound]
  'fanEffect_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
  'opposition_bound_from_weight_max' depends on axioms: [propext, Classical.choice, Quot.sound]
  PASS: mainTheorem uses only standard axioms
[6] Auditing MainTheorem.lean imports...
  PASS: MainTheorem.lean imports only Mathlib

=== Stats ===
  Lean files: 52
  Lines of code: 7,509

=== ALL CHECKS PASSED: 6 passed, 0 failed (312s) ===
```

Step 7 shows SKIP instead of PASS if lean4checker is not installed.

## Trust model

The kernel (type checker, ~10K lines of C++) is the only trusted component.
The 52 project files are verified by the kernel.

You only need to verify that the statement in `MainTheorem.lean` says what
you think it says. That file uses only Mathlib types with no project imports,
so there is no way to hide triviality behind a custom definition.

`#print axioms` shows only `[propext, Classical.choice, Quot.sound]`,
the three standard axioms present in every Lean proof. Any `sorry` would
appear as `sorryAx`; any custom axiom would be listed explicitly.
`lean4checker` replays all declarations through a fresh kernel, guarding
against environment manipulation via metaprogramming.

## Full automated validation

```bash
./validate.sh
```

This checks:
1. Full build (0 errors)
2. No `sorry` in any `.lean` file
3. No custom `axiom` declarations
4. No `True` placeholder statements
5. `#print axioms mainTheorem` shows only standard axioms
6. `MainTheorem.lean` has no project imports
7. lean4checker kernel replay (if installed)

## File-by-file audit path

If you want to go deeper than the quick version:

1. **`AttentionLoop/MainTheorem.lean`**. Read the seven property statements.
   Confirm they are mathematically non-trivial. No project imports:
   - Convergence: V(t) → 0 under repeated consolidation
   - Accumulation rigidity: Σf = Θ(D²) when σ converges
   - Sublinear → σ → 0
   - Superlinear → σ → ∞
   - Softmax Lipschitz: ‖φ(x) - φ(y)‖₁ ≤ 2‖x - y‖∞
   - Fan effect: w_max ≤ 1/(1+(n-1)exp(-g))
   - Opposition: score gap Ω(log n) for bounded max weight

2. **`AttentionLoop/ProofOfMainTheorem.lean`**. The bridge file.
   Imports MainTheorem + project files and proves `mainTheorem :
   StatementOfTheorem`. Constructs project types from inline types
   and shows the definitions match.

3. **`AttentionLoop/Verification.lean`**. Runs `#print axioms` on the
   main theorem and six key component theorems.

4. **Individual proof files**. Doc comments in each file explain
   the proof strategy and cite the paper.

## The seven properties

The formalization proves seven key properties that span all sections of the paper:

### Dynamics (Properties 1, 6, 7)
- **Convergence** (Property 1): Under repeated consolidation, all memories converge
  to the anchor. Requires A+ maps, uses compactness + Lyapunov strict decrease.
- **Fan effect** (Property 6): Adding memories dilutes max retrieval weight.
  Shows w_max ≤ 1/(1+(n-1)exp(-g)) where g is score spread.
- **Opposition** (Property 7): Bounded max weight requires Ω(log n) score gap.
  Formalizes that dominance in large sets needs logarithmic advantage.

### Rigidity (Properties 2-4)
- **Accumulation rigidity** (Property 2): The hardest proof. Shows that for
  C(t+1) = C(t) + a(t)f(t)/C(t), if σ = C/(N₀+t) converges, then Σf = Θ((N₀+t)²).
  Requires delicate ε-δ arguments and telescoping on C².
- **Sublinear → σ → 0** (Property 3): If f grows slower than linear, salience decays.
- **Superlinear → σ → ∞** (Property 4): If f grows faster than quadratic, system diverges.

### Analysis (Property 5)
- **Softmax Lipschitz** (Property 5): ‖φ(x) - φ(y)‖₁ ≤ 2‖x - y‖∞.
  Proved via FTC integration of Jacobian operator norm bound.

Together, these cover all three simplex map levels (A, A+, softmax) and demonstrate
non-trivial content from rigidity, dynamics, and attention saturation.

## Troubleshooting

**Build is slow on first run**
The first `lake build` fetches and compiles Mathlib dependencies (~2800 jobs,
10-20 minutes). Subsequent builds are incremental and fast.

**Network errors during build**
`lake exe cache get` downloads pre-built Mathlib `.olean` files. If this fails
(firewall, no internet), the build will compile Mathlib from source instead —
slower but still works.

**Windows line ending issues**
If you see unexpected build errors on Windows, ensure git didn't convert line
endings: `git config core.autocrlf input` and re-clone.

**`lake build` hangs or shows no output**
Lean's build system prints progress as jobs complete. The first few minutes
may show no output while Mathlib dependencies are resolved. This is normal.

## Reproducibility

The build is fully reproducible:
- `lean-toolchain`: Lean 4.28.0
- `lake-manifest.json`: pins exact Mathlib commit
- Same toolchain + manifest = identical `.olean` files

To reproduce from scratch:
```bash
# Extract release and run
./setup.sh              # Install Lean 4 via elan
lake build              # Fetches Mathlib, builds everything
./validate.sh           # Verify all checks pass
```

## Module breakdown by complexity

The 49 theorem files are organized into four layers:

| Layer | Files | Focus | Key Properties |
|-------|-------|-------|----------------|
| Defs (11) | Foundations | Simplex maps, loop state | All core definitions |
| Rigidity (10) | Hard proofs | Design necessity | Properties 2-4 |
| Core (20) | Dynamics | Convergence, Lyapunov | Properties 1, 6, 7 |
| CaptureInertness (7) | Analysis | Lipschitz, inertness | Property 5 |

The hardest result is **accumulation_rigidity_aggregate** (Rigidity/AccumulationRigidity.lean),
with the longest proof and most delicate technical arguments. It establishes the
rigidity trichotomy that underpins the paper's Section 2.