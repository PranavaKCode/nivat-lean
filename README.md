# Nivat manuscript formalization

**The full Nivat conjecture is proved in Lean 4.34.1.**

The final declaration is [`KumarNivat.nivat`](KumarNivat/Nivat.lean). It has type `FullNivat`, with no additional hypotheses. The proof formalizes the supplied manuscript's argument through its periodic-wedge bound, generating polygon, periodic reference, and both geometric selection cases.

## Exact theorem statement

For every finite alphabet `A` in any universe and every configuration `c : ℤ × ℤ → A`, if some positive integers `k, n` satisfy

```text
number of occurring k × n rectangular patterns ≤ k * n,
```

then there is a nonzero `h : ℤ × ℤ` such that `c (g + h) = c g` for every `g : ℤ × ℤ`.

Patterns are counted over all translations of the original axis-aligned rectangle. Equality at the threshold and one-cell-wide or one-cell-high rectangles are included. The conclusion concerns the original configuration.

[`Statement.lean`](KumarNivat/Statement.lean) defines the statement and checks its expansion. [`FullTarget.lean`](scripts/FullTarget.lean) compiles both `nivat : FullNivat` and a literal expansion using the translated-pattern set's natural cardinality.

## Proof map

| Manuscript argument | Main formalization |
| --- | --- |
| Integer alphabet reduction and initial annihilator | `exists_integer_model`, `exists_integer_annihilator` |
| Sections 2–4: annihilators, directional filters, and the pattern-count contradiction | [`PeriodicWedgeBound.lean`](KumarNivat/PeriodicWedgeBound.lean), `periodic_wedge_bound` |
| Section 5: generating polygon and periodic reference | [`GeneratingSets.lean`](KumarNivat/GeneratingSets.lean), [`LowComplexityPeriodicReference.lean`](KumarNivat/LowComplexityPeriodicReference.lean) |
| Structural paired-direction input in the integer case used by the proof | [`CollePairedDirection.lean`](KumarNivat/CollePairedDirection.lean), with the actual source sequence and retained failed facet constructed internally |
| Sections 6–8: matching half-strip case | [`MainMatchingBackgroundHalfStrip.lean`](KumarNivat/MainMatchingBackgroundHalfStrip.lean) |
| Sections 6–8: no-matching half-strip case | [`NoMatchingWedgeSelection.lean`](KumarNivat/NoMatchingWedgeSelection.lean) |
| Selection of the same nonperiodic orbit point and its fully periodic wedge background | [`IntegerWedgeSelectionProof.lean`](KumarNivat/IntegerWedgeSelectionProof.lean) |
| Final deduction, including thin rectangles and arbitrary finite alphabets | [`FinalDeduction.lean`](KumarNivat/FinalDeduction.lean), [`Nivat.lean`](KumarNivat/Nivat.lean) |

The authored library contains 339 Lean source files. Both selection cases preserve the same configuration throughout the nonperiodicity and background-wedge conclusions. Polygon models, Newton summands, finite disagreement witnesses, and failed layers are derived inside the formalization.

## Verification

The complete library build and all **923** principal axiom audits passed. The full target acceptance check passed, including the expanded literal statement. The authored-source scan found no admitted proofs, custom axioms, or native verification escapes.

The final theorem's axiom report is:

```text
'KumarNivat.nivat' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are Lean's ordinary foundational axioms. The saved evidence is in [`audit/verification.json`](audit/verification.json), [`audit/build.log`](audit/build.log), [`audit/axioms.log`](audit/axioms.log), and [`audit/full-target.log`](audit/full-target.log). The receipt records hashes of the exact authored sources, inputs, build configuration, verification scripts, and logs.

## Reproduce

The toolchain is pinned in `lean-toolchain`; Mathlib and its dependencies are pinned in `lake-manifest.json`. Mathlib is at `d13f23b723b8a846827a245b89c10fc7d3f11612`. All nine dependency checkouts used for verification were clean and matched their pinned revisions.

With Elan installed, run from the extracted project directory:

```powershell
lake exe cache get
powershell.exe -NoProfile -ExecutionPolicy Bypass -File scripts/verify.ps1
```

The verification script builds the complete library, scans every authored Lean file, requires an axiom report for every audited declaration, and checks the full theorem. The individual compiler commands are:

```text
lake build
lake env lean scripts/Audit.lean
lake env lean scripts/FullTarget.lean
```

`python scripts/check_receipt.py` compares the delivered files with the saved verification snapshot.

The source package uses ordinary pinned dependencies and contains no local cache paths. Build caches, temporary work, and reference checkouts are excluded from the archive.

## Supplied manuscript

The source is Pranava Kumar's *A proof of Nivat's conjecture*, dated 14 September 2026. The supplied PDF and the archive's PDF are byte-identical and preserved under `inputs/`.

- PDF SHA-256: `6b3b5efdeb7aa549fdd0ca06cfda61b4be60241b369eb790d49b1f8fbf6b16e0`
- LaTeX SHA-256: `da6d92e41bef1dc3a7560dc6505fdee228f9fd261d582a58f442c3e469211c4f`
