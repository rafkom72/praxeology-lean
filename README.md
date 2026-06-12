# Praxeology in Lean 4

A machine-verified formalization of the Hilbert-style axiomatization of praxeology accompanying

> Komendarczyk, R., Block, W., Levendis, J., and Tipler, F. *A Formalization of Austrian Economics — Praxeological Foundations: The Base System and Its Derived Theorems.* Manuscript, 2026.

This repository contains the Lean 4 companion to the paper. The single file [`Praxeology.lean`](Praxeology.lean) encodes the paper's praxeological signature as a Lean type class, instantiates it with a concrete three-period Robinson Crusoe model, and verifies — by exhaustive case analysis carried out by Lean's type checker — that every axiom of the *action core* (T1–T4, P1–P5, C1) holds on that model.

The file then extends the class to the **full base theory** \(T_{prx}\): the remaining time axioms (T0 first moment, T5 irreversibility, T6 discreteness), free-good exclusion (P6), the scarcity anchor (S1), and the Layer-2 axioms (O0)–(O4) over the primitive scale of values, grounded in the revealed-preference record per the paper's §2.3. Since T6 gives every moment a successor, the full theory has **no finite models** — the consistency witness is an infinite-time Crusoe model (`Time := ℕ`) with a non-greedy alternating history and preference orders that co-vary with it. Acceptance of `NatCrusoe.crusoeNatModel : PraxeologyFull` is a constructive consistency proof of the full base theory.

The file additionally verifies the production-enrichment Order hierarchy (\(T_{prx} + E_5\)) and the diminishing-marginal-utility theorem — in the paper's tightened form, where the reduced marginal end \(E^*\) is derived rather than assumed — together with its structure-preservation corollary, and instantiates the (MU)-axioms on the paper's two-good water/fish allotment schedule.

## What this file verifies

- **Action core:** sorts (Actor, Action, End, Thing, Time), primitive relations, axioms T1–T4 (time order), P1–P5 (incidence), C1 (choice), instantiated on the finite three-period Crusoe model.
- **Derived theorems:** asymmetry of revealed preference (`revPref_asymm`, valid without a distinctness hypothesis — the record definition carries the `E ≠ F` clause), opportunity cost, and `chosen_end_tops_scale` (the paper's `prop:chosen_max`: the performed action's end is the unique maximum of the scale).
- **Full base theory (`PraxeologyFull`):** the primitive preference relation `Pref` (the scale of values) with grounding axiom (O0) and order axioms (O1)–(O4), plus T0/T5/T6, P6, and S1.
- **Infinite-time consistency witness:** `NatCrusoe.crusoeNatModel : PraxeologyFull` — `Time := ℕ`, the net-then-boat history alternating deep-sea (even *t*) and shore fishing (odd *t*), parity-indexed preference ranks; the *t* = 4 vs *t* = 5 preference reversal of the paper's `rem:constancy` is machine-checked.
- **Production enrichment (\(E_5\)):** the higher-order goods hierarchy verified via the `Order` inductive predicate; `CrusoeOrder_total` shows every thing has a finite Order (Plant/Fish/Tuna at order 1, Net/Boat at order 2, Wood at order 3).
- **(MU)-enrichment:** the new sort `Good`, predicates `UnitOf`, `Allot`, `Pref`, the load-bearing axioms (O2 menu-comparability, O3 transitivity, asymmetry, both halves of MU0, and MU4 top-segment in its corrected form, relativized to the good's serviceable ends), the lemma `served_choice_relevant`, and the diminishing-marginal-utility theorem `PraxeologyMU.DMU` (hypotheses: uniqueness, marginality, non-emptiness of the reduced supply; the reduced marginal end is derived) plus its structure-preservation corollary `PraxeologyMU.DMU_structure`.
- **Two-good satisfiability witness:** `waterFishModel : PraxeologyMU` realizes the paper's water/fish allotment schedule, in which two goods alternate down a single value scale — a model the unrelativized MU4 excluded (an `example` verifies the old axiom fails on it), with a worked application of `DMU` at water's marginal end.

The file is **self-contained**: no Mathlib, no external imports, only Lean 4 core. If it compiles cleanly, every theorem and every axiom of both Crusoe models — finite and infinite-time — is verified.

## How to run it

### Web playground (no install needed)

1. Open <https://live.lean-lang.org>
2. Paste the entire contents of [`Praxeology.lean`](Praxeology.lean)
3. Wait ~30 seconds for compilation
4. Errors (if any) appear underlined and in the right-hand panel; no errors means everything verified

### Local install

1. Install Lean 4 from <https://docs.lean-lang.org/lean4/doc/quickstart.html> (or use [`elan`](https://github.com/leanprover/elan))
2. Install the `lean4` extension in VS Code
3. Clone this repository and open `Praxeology.lean` in VS Code — the Lean Infoview shows the proof state as you click around
4. Or from the command line: `lean Praxeology.lean` (no output = all proofs succeeded)

This repository pins a known-working Lean version via [`lean-toolchain`](lean-toolchain); `elan` will fetch the correct version automatically.

## Citation

If you use this formalization in academic work, please cite the accompanying paper:

```bibtex
@unpublished{Komendarczyk2026Praxeology,
  author       = {Komendarczyk, Rafa{\l} and Block, Walter and Levendis, John and Tipler, Frank},
  title        = {A Formalization of Austrian Economics --- Praxeological Foundations: The Base System and Its Derived Theorems},
  year         = {2026},
  note         = {Lean~4 companion: \url{https://github.com/rafkom72/praxeology-lean}}
}
```

## License

The Lean code in this repository is released under the MIT License — see [`LICENSE`](LICENSE).

## Authors

- **Rafał Komendarczyk** — Tulane University, Department of Mathematics
- **Walter Block** — Loyola University New Orleans, J.A. Butt College of Business
- **John Levendis** — Tulane University, Connolly Alexander Institute for Data Science (CAIDS)
- **Frank Tipler** — Tulane University, Department of Mathematics

*(Postal addresses to be added.)*
