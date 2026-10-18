> **Nota (2026-10-18).** Documento histórico de la entrega. El estado final de la
> integración local, las correcciones aplicadas y la evidencia están en `../CIERRE.md` y
> `NOTA_TOOLCHAIN.md`.

# Integration: endpoint-replicated db2 extension

## Local files used
* `Solution.lean` (baseline, unchanged, SHA-256 `c3231f1e…287c`). Read for the definitions
  `convolutionOperator`, `foldKernel`, `tensorKernel`, `cascadeRadius`, `cascadeSupport`,
  `cascadeTap`, `cascadeOffset`, `cascadeKernel`, `cascadeOperator`, and the theorems
  `cascade_opNorm_formula` and `cascade_opNorm_uniform`.
* `extension/ThresholdExtension/ThresholdCertificate.lean` (abstract certificate, unchanged).
* `extension/ThresholdExtension/Db2ThresholdCertificate.lean` (db2 bridge, unchanged). It provides
  `cascadeL`, `cascadeC`, `cascade1_opNorm_le_L`, `cascade1_opNorm_eq_C`, `cascadeC_nonneg` and
  `cascadeC_le_L`.
* `extension/lakefile.toml`, `extension/lake-manifest.json`, root `lakefile.toml`,
  `lake-manifest.json`, `lean-toolchain` and `lean-toolchain.txt`.

## Layout

```
<baseline root>/            unchanged
└── extension/
    ├── lakefile.toml                         (changed: two roots added)
    └── ThresholdExtension/
        ├── ThresholdCertificate.lean         (unchanged)
        ├── Db2ThresholdCertificate.lean      (unchanged)
        ├── EndpointReplication.lean          (new; imports Solution)
        └── NonperiodicDb2Certificate.lean    (new; imports EndpointReplication and
                                               Db2ThresholdCertificate)
```

Both new files start with `module` and use `@[expose] public section`, matching the existing modules.

## The only change to an existing file: `extension/lakefile.toml`

The `roots` list of `lean_lib ThresholdExtension` now reads:

```toml
roots = ["ThresholdExtension.ThresholdCertificate", "ThresholdExtension.Db2ThresholdCertificate",
         "ThresholdExtension.EndpointReplication", "ThresholdExtension.NonperiodicDb2Certificate"]
```

Everything else in that file is unchanged: the Mathlib pin, the path dependency on the baseline,
and `packagesDir`.

## How the baseline is reused (nothing reproved, nothing assumed)
* The nonperiodic operator is connected to the actual `TWSPeriodic.cascadeOperator j M 1` by
  `directOp_eq_restrict_cascade_pad`. The proof unfolds the baseline definitions
  (`convolutionOperator`, `tensorKernel`, `cascadeKernel`, `foldKernel`, `cascadeOffset`).
* The exact bound `cascadeC j` comes from `cascade1_opNorm_eq_C j M (cascadeSupport_le_padLen j n)`,
  which is the bridge to the baseline `cascade_opNorm_formula`. The side condition `s ≤ M` is
  proved, not assumed.
* The uniform bound `cascadeL` comes from `cascade1_opNorm_le_L j M`, which is the bridge to the
  baseline `cascade_opNorm_uniform`.
* The threshold statements are direct applications of `ThresholdCert.certifiedAbove_sound`,
  `certifiedNotAbove_sound`, `coord_perturbation` and `symmDiff_subset_band` with `T = directOp j n`.

## Reproducing
From `extension/`, with the v4.35.0-rc2 toolchain binaries first on `PATH`:

```
lake build                                  # builds all four ThresholdExtension modules
lake env lean <file with #print axioms ...>
```

The baseline `Solution` olean must exist. It is built by `lake build Solution` in the baseline root.

The exact commands, exit codes and the full axiom output are in `NONPERIODIC_VERIFICATION.txt`.
