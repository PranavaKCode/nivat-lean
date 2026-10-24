# Nivat's conjecture

This repository formalizes Pranava Kumar's manuscript argument for the full Nivat conjecture. The original October 1 verification snapshot is preserved at [`3cbea761cbc5cb8039ef1a5990f52be3ba2a23bd`](https://github.com/PranavaKCode/nivat-lean/tree/3cbea761cbc5cb8039ef1a5990f52be3ba2a23bd). This branch prepares that development for Palomar, including its required toolchain, module system, independent statement, licensing, and provenance metadata.

## Exact theorem statement

For every finite alphabet `A` in any universe and every configuration `c : ℤ × ℤ → A`, if some positive integers `k, n` satisfy

```text
number of occurring k × n rectangular patterns ≤ k * n,
```

then there is a nonzero `h : ℤ × ℤ` such that `c (g + h) = c g` for every `g : ℤ × ℤ`.

Patterns are counted over all translations of the original axis-aligned rectangle. Equality at the threshold and rectangles of width or height one are included. The conclusion concerns the original configuration.

The proved declaration is [`KumarNivat.nivat`](KumarNivat/Nivat.lean), of type `FullNivat`. [`Statement.lean`](KumarNivat/Statement.lean) defines that type and checks its expansion. [`FullTarget.lean`](scripts/FullTarget.lean) checks both the named type and a literal expansion. The Palomar entry theorem [`PalomarNivat.nivat`](Solution.lean) exposes the same literal statement.

## Proof map

| Manuscript argument | Main formalization |
| --- | --- |
| Integer alphabet reduction and initial annihilator | `exists_integer_model`, `exists_integer_annihilator` |
| Sections 2–4: annihilators, directional filters, pattern-count contradiction | [`PeriodicWedgeBound.lean`](KumarNivat/PeriodicWedgeBound.lean), `periodic_wedge_bound` |
| Section 5: generating polygon and periodic reference | [`GeneratingSets.lean`](KumarNivat/GeneratingSets.lean), [`LowComplexityPeriodicReference.lean`](KumarNivat/LowComplexityPeriodicReference.lean) |
| Paired-direction structural input in the required integer case | [`CollePairedDirection.lean`](KumarNivat/CollePairedDirection.lean) |
| Sections 6–8: matching half-strip case | [`MainMatchingBackgroundHalfStrip.lean`](KumarNivat/MainMatchingBackgroundHalfStrip.lean) |
| Sections 6–8: no-matching half-strip case | [`NoMatchingWedgeSelection.lean`](KumarNivat/NoMatchingWedgeSelection.lean) |
| Same nonperiodic orbit point and its periodic wedge background | [`IntegerWedgeSelectionProof.lean`](KumarNivat/IntegerWedgeSelectionProof.lean) |
| Final deduction, thin rectangles, arbitrary finite alphabets | [`FinalDeduction.lean`](KumarNivat/FinalDeduction.lean), [`Nivat.lean`](KumarNivat/Nivat.lean) |

The proof library has 339 Lean source files. Both selection cases preserve the same configuration in the nonperiodicity and background-wedge conclusions. Polygon models, Newton summands, finite disagreement witnesses, failed layers, and the structural inputs used by the proof are constructed internally.

## Palomar verification

This branch pins Lean **v4.35.0-rc2** and canonical Mathlib commit **`065356127b1dc0016f66b7283ce0ce2c4055aa55`**. Every committed Lean source uses the module system. Dependency revisions are recorded in [`lake-manifest.json`](lake-manifest.json).

[`Challenge.lean`](Challenge.lean) states the conjecture independently using canonical Mathlib notions. It contains one explicitly documented private specification axiom, used only to expose an unproved statement as a theorem for Comparator. **Challenge is a specification, not a proof.** [`Solution.lean`](Solution.lean) does not import Challenge; it invokes the manuscript's proved theorem. Neither Solution nor the proof library contains admitted proofs or custom axiom declarations. The solution's permitted dependencies are only `propext`, `Classical.choice`, and `Quot.sound`.

[`comparator.json`](comparator.json) requires the Challenge and Solution declarations to agree. The pinned official [Palomar mechanical workflow](.github/workflows/palomar-preflight.yml) runs in `full` mode on each push to `palomar-submission`. Consult the [Actions run](https://github.com/PranavaKCode/nivat-lean/actions/workflows/palomar-preflight.yml) and its `mechanical-report-preflight001` artifact for the result on an exact commit. A result for the earlier toolchain does not certify the upgraded snapshot. Registry registration is a separate final action.

The companion `manuscript-audit` job builds all 339 proof-library modules, validates all 923 principal axiom reports, and checks both the expanded target and the Solution's axiom dependencies. Its `manuscript-audit-<run_id>-<attempt>` artifact contains the complete logs and a report bound to the source commit.

With Elan installed, the compiler checks are:

```text
lake exe cache get
lake build
lake env lean scripts/Audit.lean
lake env lean scripts/FullTarget.lean
lake comparator --config comparator.json
```

The PowerShell wrapper `scripts/verify.ps1` runs the library and theorem checks. It writes logs under `audit/`; the existing tracked logs belong to the historical snapshot described below. The full official preflight additionally runs Palomar's source guards and independent kernel checks.

## Historical verification evidence

The October 1 snapshot passed the complete Lean 4.34.1 library build, 923 principal axiom audits, source scan, and expanded full-target acceptance check. Its final theorem reported only:

```text
'KumarNivat.nivat' depends on axioms: [propext, Classical.choice, Quot.sound]
```

[`audit/verification.json`](audit/verification.json), the saved logs, and `nivat-lean-verified.zip` describe that **historical snapshot**, with Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. They are not receipts for this branch's upgraded sources. Check all 353 recorded file hashes against the historical Git commit with:

```text
python scripts/check_receipt.py --revision 3cbea761cbc5cb8039ef1a5990f52be3ba2a23bd
```

Without `--revision`, the checker compares current files and will reject a modified snapshot.

## Manuscripts and chronology

The supplied *A proof of Nivat's conjecture*, dated 14 September 2026, is preserved byte-for-byte as [`inputs/paper101.pdf`](inputs/paper101.pdf). It is identical to `inputs/nivat.pdf`.

- PDF SHA-256: `6b3b5efdeb7aa549fdd0ca06cfda61b4be60241b369eb790d49b1f8fbf6b16e0`
- LaTeX SHA-256: `da6d92e41bef1dc3a7560dc6505fdee228f9fd261d582a58f442c3e469211c4f`

An earlier version, *Rectangular complexity, periodic regions, and local observables*, was publicly deposited on [Zenodo on 8 September 2026](https://doi.org/10.5281/zenodo.22666792), before the identified parallel repository was created on 14 September. The deposited PDF is preserved as [`inputs/zenodo-22666792.pdf`](inputs/zenodo-22666792.pdf). Zenodo's server timestamps and DataCite's DOI registration corroborate the earlier deposit. Kumar identifies it as the earlier presentation of the argument formalized here and claims priority for that argument. The two manuscript versions contain revisions and are not byte-identical. The dated evidence and its limits are recorded in [`provenance/chronology.json`](provenance/chronology.json).

A [parallel Lean formalization](https://github.com/PalomarArchive/boonsuan--nivat--8f5b1fc73411/tree/0d94547e934418c9d1b75fcbb7d6af493e86759d) was supplied as a reference. It is disclosed under `related_formalizations` in [`formalization.yaml`](formalization.yaml). This proof development attributes its mathematical source to Kumar's manuscripts.

## AI assistance and licenses

AI assistance was used to translate the pre-existing paper's arguments into Lean, including supporting lemmas, formal proof construction, debugging, and verification. The responsible maintainer reports models including GPT-6 Astra through the custom agentic framework Catenation. Exact model-run identifiers and framework logs were not recorded in the original public snapshot; those model and framework names are the maintainer's attribution. Full disclosure and source alignment appear in [`formalization.yaml`](formalization.yaml).

Code, scripts, and project metadata are licensed under [Apache-2.0](LICENSE). The manuscripts are licensed under [CC BY 4.0](inputs/PAPER-LICENSE.md). See [`NOTICE`](NOTICE) for the distinction.
