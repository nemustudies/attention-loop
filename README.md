# Self-Referring Attention

A self-referring attention loop operating on finite memory through five steps
(observe, accumulate, retrieve, consolidate, capture), governed by a
three-level hierarchy of simplex maps and four dimensions of invariance. 

Lean4 verifiaction done for finite X, not done for infinite uncountable X due to time constraints.

Do note that LLMs were used in the formalization of this paper. 

## What's here

| | |
|---|---|
| [`self_referring_attention.pdf`](self_referring_attention.pdf) | The paper |
| [`AttentionLoop/`](AttentionLoop/) | Lean 4 formalization (0 sorries, 52 files, 7,509 lines) |
| `loop_implementation.py` | GPU implementation |
| [`VERIFICATION_GUIDE.md`](VERIFICATION_GUIDE.md) | How to verify the proofs |

> **Reviewers: start here.** See [`VERIFICATION_GUIDE.md`](VERIFICATION_GUIDE.md)
> for a step-by-step walkthrough. The short version: read
> [`AttentionLoop/MainTheorem.lean`](AttentionLoop/MainTheorem.lean) (Mathlib-only
> statement, no project imports), then run
> `lake env lean AttentionLoop/Verification.lean` to confirm only standard axioms.

## Formalization

## Status

| Metric | Value |
|--------|-------|
| Sorries | **0** |
| Axioms | **0** (no `axiom` beyond Lean/Mathlib) |
| Build jobs | ~2,800 |
| Lean files | 52 |
| Lines of code | 7,509 |
| Lean version | 4.28.0 |
| Mathlib version | v4.28.0 |

## Setup

```bash
./setup.sh              # Lean 4 via elan
```

Or install manually: [Lean 4](https://leanprover.github.io/lean4/doc/setup.html)
via elan, then `lake build` (fetches Mathlib on first build).

## Build Instructions

```bash
lake build              # Full build (~2800 jobs, takes several minutes)
```

To check a single file:

```bash
lake env lean AttentionLoop/Rigidity/AccumulationRigidity.lean
```

## Module Structure

| Directory | Files | Description |
|-----------|------:|-------------|
| `Defs/` | 11 | Core definitions: simplex maps, loop state, five-step operations, derived quantities |
| `Core/` | 20 | Main dynamics: convergence, Lyapunov, contraction rate, non-degeneracy, fan effect, opposition |
| `Rigidity/` | 10 | Structural rigidity: why each design choice is forced or invariant |
| `CaptureInertness/` | 7 | Capture-consolidation cycle: sigma convergence, softmax Lipschitz, inertness |

Plus `AttentionLoop.lean` (root import file) and `MainTheorem.lean`, `ProofOfMainTheorem.lean`, `Verification.lean` for 52 total.

## Paper-to-Lean Mapping

### Definitions (Defs/)

| Paper Label | # | Lean File | Description |
|---|---|---|---|
| -- | -- | `Defs/SimplexMap.lean` | Three-level simplex map hierarchy: A, A+, softmax |
| -- | -- | `Defs/BlendRate.lean` | Admissible blend rate class L |
| -- | -- | `Defs/Embedding.lean` | Embedding E : X -> R^d with radius R |
| -- | -- | `Defs/LoopState.lean` | Full loop state: M, C, N, t |
| def:scoring | 1 | `Defs/Scoring.lean` | Perturbed score S'(tau) = S + sigma + b |
| def:observation | 2 | `Defs/Observation.lean` | Step 1: a = phi(S') |
| def:accumulation | 3 | `Defs/Accumulation.lean` | Step 2: C(t+1) = C(t) + a(t) f(t) / C(t) |
| def:retrieval | 4 | `Defs/Retrieval.lean` | Step 3: q = aE, w = phi(qM^T), l = wM, b = EKl |
| def:consolidation | 5 | `Defs/Consolidation.lean` | Step 4: blend toward T_j |
| def:capture | 6 | `Defs/Capture.lean` | Step 5: M' = M union {E(tau) : q.E(tau) > theta} |
| -- | -- | `Defs/DerivedQuantities.lean` | V, D, rho, gamma, g, R, critical memory size |

### Rigidity (Paper Section 2)

| Paper Label | # | Lean File | Description |
|---|---|---|---|
| prop:consolidation_rigidity | 1 | `Rigidity/ConsolidationRigidity.lean` | Forced boundary conditions lambda(0)=1, lambda(1)=0 |
| prop:rigidity | 3 | `Rigidity/AccumulationRigidity.lean` | Rigidity trichotomy: sublinear/linear/superlinear accumulation |
| lem:idempotent | 4 | `Rigidity/IdempotentCapture.lean` | Capture is idempotent |
| cor:capture_scale_invariant | 4 | `Rigidity/CaptureScaleInvariant.lean` | Capture decision is scale-invariant in q |
| prop:capture_rigidity | 5 | `Rigidity/CaptureRigidity.lean` | Max threshold is unique under idempotent capture |
| prop:target_axioms | 6 | `Rigidity/TargetAxioms.lean` | Minimal axioms (T1-T5) for consolidation target |
| prop:pipeline_rigidity | 7 | `Rigidity/PipelineRigidity.lean` | 5-step pipeline is minimal; query formation invariant (iff), dot-product scoring forced |
| prop:scoring_additivity | 9 | `Rigidity/ScoringAdditivity.lean` | Additive scoring is canonical under softmax factorization |
| prop:step_ablation | 10 | `Rigidity/StepAblation.lean` | Each of the 5 steps is necessary |
| thm:classification | 8 | `Rigidity/RigiditySummary.lean` | Classification theorem: forced/invariant/instance-defining trichotomy |

### Core Dynamics (Paper Section 3)

| Paper Label | # | Lean File | Description |
|---|---|---|---|
| cor:N_history_independent | 1 | `Core/HistoryIndependence.lean` | N(t) = N(0) + t, independent of attention history |
| thm:selective | 2 | `Core/SelectivePersistence.lean` | Selective persistence: sigma -> 0 or liminf >= sqrt(delta) |
| lem:stability | 3 | `Core/RetrievalGatedStability.lean` | Anchor unchanged by consolidation, threshold non-decreasing |
| cor:acquisition | 4 | `Core/MonotoneAcquisition.lean` | \|M\| non-decreasing after capture |
| lem:hull | 5 | `Core/ConvexHullInvariance.lean` | conv(M_t) subset conv(E(X)) for all t |
| lem:finite | 6 | `Core/FiniteMemory.lean` | Without consolidation, \|M\| <= \|X\| |
| cor:bounded | 7 | `Core/BoundedBias.lean` | \|b(tau)\| <= R^2 \|\|K\|\|\_op |
| thm:nondegen | 8 | `Core/NonDegeneracy.lean` | Non-degeneracy: a(tau) >= alpha > 0 under A+ |
| cor:retrieval_in_hull | 9 | `Core/RetrievalInHull.lean` | l = wM lies in conv(M) |
| cor:query_norm_bound | 10 | `Core/QueryNormBound.lean` | \|\|q\|\| <= R and q in conv(E(X)) |
| cor:blend_rate_bounds | 11 | `Core/BlendRateBounds.lean` | lambda_v = 0, 0 < lambda_j <= 1 for j != v |
| lem:lyapunov | 12 | `Core/Lyapunov.lean` | V(t+1) < V(t) whenever V(t) > 0 |
| cor:budget | 13 | `Core/AttentionBudget.lean` | sum a(tau) = 1, mean = 1/n |
| cor:contraction | 14 | `Core/ContractionRate.lean` | V(t+1) <= (1 - gamma) V(t) |
| cor:fan | 15 | `Core/FanEffect.lean` | Adding impressions dilutes retrieval weights |
| cor:opposition | 16 | `Core/RetrievalWeightBounds.lean` | 1/n <= max w_j <= 1/(1+(n-1)exp(-g)) |
| cor:sleep | 17 | `Core/Convergence.lean` | D(t) -> 0 under repeated consolidation |
| cor:selflimiting | 18 | `Core/SelfLimiting.lean` | gamma(t) -> 0 as M converges |
| cor:prototype | 19 | `Core/PrototypeFormation.lean` | All rows of M converge to anchor v |
| cor:variability | 20 | `Core/ContextVariation.lean` | Anchor rotation preserves distinct impressions |

### Capture-Consolidation Cycle (Paper Section 5)

| Paper Label | # | Lean File | Description |
|---|---|---|---|
| thm:capture_argmax | 19 | `CaptureInertness/CaptureArgmax.lean` | Total captures <= argmax transitions + 1 |
| prop:capture_inertness | 20 | `CaptureInertness/PerturbativeInertness.lean` | Perturbative inertness for small \|\|K\|\| |
| cor:K_zero_inertness | 21 | `CaptureInertness/KZeroInertness.lean` | K=0 implies finite captures |
| cor:forced_cycle_general_K | 22 | `CaptureInertness/ForcedCycleGeneralK.lean` | Forced cycle for arbitrary K |
| lem:softmax_lipschitz | A.5 | `CaptureInertness/SoftmaxLipschitz.lean` | \|\|phi(x) - phi(y)\|\|\_1 <= 2\|\|x - y\|\|\_inf |
| lem:sigma_increment | A.6 | `CaptureInertness/SigmaIncrement.lean` | \|sigma(t+1) - sigma(t)\| = O(1/t) |
| lem:finite_argmax | A.7 | `CaptureInertness/FiniteArgmax.lean` | E-argmax stabilizes after finitely many transitions |

## Simplex Map Hierarchy

The paper's theorems are stratified by which level of simplex map they require:

- **A** (broadest): any map sending R^n to the probability simplex (nonneg,
  sum-to-one). Covers accumulation rigidity, convex hull invariance, step
  ablation, history independence, bounded bias, monotone acquisition.
- **A+** (positive, order-preserving, continuous): all outputs strictly
  positive, ordering preserved. Covers non-degeneracy, Lyapunov strict
  decrease, convergence, contraction rate, blend rate bounds, sleep efficacy.
- **softmax** (most restrictive): phi(x)\_i = exp(x\_i) / sum exp(x\_j).
  Covers fan effect, retrieval weight bounds, scoring additivity,
  capture-inertness, sleep pressure, monotone pressure, forced cycle.

Each theorem's doc comment in the Lean source indicates its required level.

## Key Theorems

**Accumulation Rigidity** (`Rigidity/AccumulationRigidity.lean`).
The hardest proof in the formalization. Establishes a trichotomy for the
generalized accumulation rule C(t+1) = C(t) + a(t) f(t) / C(t): if f is
sublinear then sigma -> 0; if f is superlinear then sigma -> infinity; and if
sigma converges to a positive constant then sum f = Theta(D^2). The aggregate
formulation is essential. The pointwise statement f = Theta(t) is unprovable
(counterexample: sparse spikes at powers of 2).

**Convergence** (`Core/Convergence.lean`).
The central convergence theorem: under repeated fixed-query consolidation with
A+, the diameter D(t) -> 0 and all impressions converge to the anchor. Built on
the Lyapunov strict decrease lemma and compactness of the convex hull.

**Non-Degeneracy** (`Core/NonDegeneracy.lean`).
Uses compactness of bounded score sets and continuity of A+ maps to prove a
uniform positive lower bound on attention: a(tau) >= alpha > 0 for all tau, t.
Key Mathlib ingredients: `isCompact_univ_pi` and `exists_mem_eq_inf'`.

**Softmax Lipschitz** (`CaptureInertness/SoftmaxLipschitz.lean`).
FTC-based proof that the softmax map is Lipschitz in the L1-to-Linf sense:
||phi(x) - phi(y)||\_1 <= 2 ||x - y||\_inf, via integration of the Jacobian
operator norm bound.

**Pipeline Rigidity** (`Rigidity/PipelineRigidity.lean`).
Shows that the 5-step architecture is minimal: removing any step breaks essential
properties. Demonstrates that query formation is only invariant under the
5-step pipeline (iff), and dot-product scoring is forced by the capture condition.

## Verification

To verify the formalization, run the following checks:

1. Full build (0 errors): `lake build`
2. No `sorry` in any proof file: `grep -r "^ *sorry" AttentionLoop/ --include="*.lean"`
3. No custom `axiom` declarations: `grep -r "^axiom " AttentionLoop/ --include="*.lean"`
4. No `True` placeholders: `grep -r ": True " AttentionLoop/ --include="*.lean" | grep -v "--"`
5. `#print axioms mainTheorem` shows only standard Lean axioms: `lake env lean AttentionLoop/Verification.lean`
6. `MainTheorem.lean` imports only Mathlib (no project dependencies): `grep "^import AttentionLoop\." AttentionLoop/MainTheorem.lean`

Run all checks with `./validate.sh`.

### Manual verification

To inspect the main theorem statement (Mathlib-only, no project types):

```bash
cat AttentionLoop/MainTheorem.lean
```

To verify axiom dependencies:

```bash
lake env lean AttentionLoop/Verification.lean
```

### Main theorem

`AttentionLoop/MainTheorem.lean` states seven key properties using only Mathlib types
(no project imports). `AttentionLoop/ProofOfMainTheorem.lean` proves
`mainTheorem : StatementOfTheorem` by connecting inline definitions to the
project's existing theorems. `AttentionLoop/Verification.lean` runs `#print axioms`
to confirm only standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`)
appear in the proof chain.

The seven properties are:
1. **Convergence** — V(t) → 0 under repeated consolidation
2. **Accumulation rigidity** — Σf = Θ(D²) when σ converges
3. **Sublinear → σ → 0** — Sublinear growth forces salience decay
4. **Superlinear → σ → ∞** — Superlinear growth causes divergence
5. **Softmax Lipschitz** — ‖φ(x) - φ(y)‖₁ ≤ 2‖x - y‖∞
6. **Fan effect** — w_max ≤ 1/(1+(n-1)exp(-g))
7. **Opposition** — Score gap Ω(log n) for bounded max weight

## Paper Reference

> nemu, "What If Attention Feeds Back Into Itself?," 2026.

## License

CC BY 4.0.
