# Cierre de fase formal

Estado: **CERRADA_LOCAL**
Commit de partida: `44f4bb79abddf1a4d0a8a3da9a07068c633ed2ab` (rama `extension/db2-threshold`), un
commit documental por delante de la base aprobada `1121b6d5d00ab04be218fea36a4eb36d5990f287`.
Versiones reales y pin: Lean `4.35.0-rc2` (arm64-apple-darwin24.6.0, commit `11acb17`),
Lake `5.0.0-src+11acb17`, Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`,
macOS 15.7.9 (24G830). Registro: `extension/verification/entorno.txt`.
Archivos integrados/modificados: `extension/` completo (5 módulos Lean, `lakefile.toml`,
`AxiomCheck.lean`, especificaciones, `scripts/`, `verification/`). La base versionada no se
modificó: los 30 archivos del commit de partida conservan su SHA256
(`extension/verification/integrity-before.json`).

| Puerta | PASS/FAIL | Evidencia y ruta |
|---|---|---|
| G0 Integridad | **PASS** | `Solution.lean` SHA256 `c3231f1e…b287c`, idéntico al aprobado; snapshot de 30 archivos y `integrity.py check` → `PASS 30 files` (`verification/integrity-before.json`, `verification/integridad-despues.txt`). Los 7 archivos que difieren de la referencia son el commit documental `44f4bb7` posterior a la aprobación, identificado y no revertido. |
| G1 Entorno | **PASS** | Lean/Lake/Mathlib reales y coherentes con el pin; sin revisión accidental de dependencias (`verification/entorno.txt`). |
| G2 Integración | **PASS** | `cd extension && lake build` → `Build completed successfully (8938 jobs)`, `EXIT=0`; 5 módulos como roots (`verification/build-2.log`). |
| G3 Matemática | **PASS** | `cascadeTap_sum_one`, `directOp_const`, `directOp_one_eq_id` demostrados en `ThresholdExtension/ConstantPreservation.lean`; más `cascadeInt_sum` como identidad entera de base. `exact_checks.py` → `PASS: 20 rational direct/padded cases; signed masses j=0..4` (no sustituye a Lean). |
| G4 Auditoría | **PASS** | `lake env lean AxiomCheck.lean` → `EXIT=0`, 92 nombres auditados, 0 errores, 0 `sorryAx`; conjuntos: 82 × `[propext, Classical.choice, Quot.sound]`, 9 × `[propext, Quot.sound]`, 1 × `[propext]` (`verification/axioms-1.log`). |
| G5 Reproducción | **PASS** | Copia temporal limpia: `lake build Solution` → `SOLUTION_EXIT=0`; `extension && lake build` → `EXT_EXIT=0`; `lake env lean AxiomCheck.lean` → `AXIOM_EXIT=0`. Reutilizado: solo `.lake/packages` (oleans de Mathlib). Recompilado: `Solution.lean` y los 5 módulos desde fuente (`verification/clean-build.log`). |
| G6 Correspondencia | **PASS** | Tablas de `NONPERIODIC_SPEC.md` y `THRESHOLD_CERTIFICATE_SPEC.md` actualizadas con las declaraciones nuevas; `NOTA_TOOLCHAIN.md` corrige la afirmación de `v4.28.0` sin reescribir los logs históricos; los 4 módulos entregados son byte-idénticos al paquete (SHA256 comparado). |
| G7 Entrega | **PASS** | Fuentes, configuración, informe, inventario (`verification/inventario.txt`), diff de la rama y pasos de reproducción. |

## Declaraciones nuevas (enunciado y supuestos)

| Declaración | Enunciado | Supuestos |
|---|---|---|
| `ThresholdCert.Nonperiodic.cascadeInt_sum` | `∑_{n ∈ [-r_j, r_j]} cascadeInt j n = cascadeScale j` | ninguno |
| `ThresholdCert.Nonperiodic.cascadeTap_sum_one` | `∑ a : Fin (cascadeSupport j), cascadeTap j a = 1` | ninguno |
| `ThresholdCert.Nonperiodic.directOp_const` | `directOp j n (fun _ => c) = fun _ => c` | `[NeZero n]` |
| `ThresholdCert.Nonperiodic.directOp_one_eq_id` | `directOp j 1 = ContinuousLinearMap.id ℝ (Fin 1 → ℝ)` | ninguno |

Las tres últimas no requieren `n ≥ cascadeSupport j` ni hipótesis de ruido, y no redefinen el
operador. `directOp_one_eq_id` reutiliza `directOp_n_one`, ya presente en la entrega.

## Comandos exactos y códigos de salida

Ejecutados desde `extension/` salvo indicación:

```
lake build                                   # Build completed successfully (8938 jobs), EXIT=0
lake env lean AxiomCheck.lean                # EXIT=0, 92 líneas de auditoría
lake env lean ThresholdExtension/ConstantPreservation.lean   # EXIT=0, sin warnings
python3 scripts/exact_checks.py              # PASS: 20 casos racionales, EXIT=0
python3 scripts/integrity.py check .. extension/verification/integrity-before.json
                                             # PASS 30 files, EXIT=0
```

Recompilación limpia (directorio temporal, `$TMP`): `lake build Solution` →
`SOLUTION_EXIT=0`; `cd extension && lake build` → `EXT_EXIT=0`; `lake env lean AxiomCheck.lean`
→ `AXIOM_EXIT=0`. Transcripción en `verification/clean-build.log`.

## Correcciones respecto a la entrega original

1. **Raíz de Lake.** El `lakefile.toml` entregado ya listaba los cuatro módulos; se añadió
   `ThresholdExtension.ConstantPreservation` como quinta raíz.
2. **Auditoría de axiomas.** `AxiomCheck.lean` cubría 31 nombres de la primera fase; ahora cubre
   los 90 públicos de los cinco módulos más las dos cotas base.
3. **Especificación.** `NONPERIODIC_SPEC.md` afirmaba que la suma de taps no se calculaba para
   `j` general; la afirmación era correcta para la entrega y ahora es falsa: se actualizó.
4. **Toolchain.** `INTEGRATION.md` y los `VERIFICATION.txt` históricos afirman que el
   `lean-toolchain` base dice `v4.28.0`. En este repositorio dice `leanprover/lean4:v4.35.0-rc2`,
   igual que el toolchain de Mathlib en el pin. Se corrige la interpretación en
   `NOTA_TOOLCHAIN.md`; los logs históricos no se reescriben.
5. Los cuatro módulos Lean entregados **no se modificaron** (byte-idénticos, SHA256 verificado).

## Integridad de la base antes/después

Antes: snapshot de 30 archivos versionados (`verification/integrity-before.json`).
Después: `integrity.py check` → `PASS 30 files`; `git status` solo muestra `extension/` como
contenido nuevo, sin modificaciones a archivos versionados de la base.

## Estado CI

`NO_EJECUTADA`. No se ha hecho push, por lo que no hay ejecución de GitHub Actions que reportar.

## Estado Palomar extensión

`NO_SOMETIDA`. No se sometió la extensión a revisión Palomar.

## Limitaciones

- Los certificados se refieren a `A x`, no a `x`; no hay garantía de denoising.
- `cascadeC j` y `cascadeL` son **cotas superiores** del operador no periódico, no normas
  exactas ni óptimas.
- No hay aritmética real formal más allá de `ℝ` de Mathlib, ni garantías de punto flotante,
  ni recuperación de `x`, ni multidimensionalidad.
- `directOp_const` y `directOp_one_eq_id` no se usan en los certificados de umbral; se registran
  como parte del cierre formal.
- `exact_checks.py` orienta y detecta regresiones; no prueba cuantificadores universales.

## Bloqueos

Ninguno. No se requirió `sorry`, `admit`, axiomas nuevos ni debilitar metas.

## Cómo reproducir desde una copia de fuentes

```bash
git clone https://github.com/jelincovil/tws-palomar.git
cd tws-palomar
git checkout 44f4bb79abddf1a4d0a8a3da9a07068c633ed2ab
lake exe cache get          # o disponer de Mathlib 0653561 ya compilado
lake build Solution         # EXIT=0 esperado
cd extension
lake build                  # EXIT=0 esperado, 5 módulos
lake env lean AxiomCheck.lean          # 92 líneas; solo propext / Classical.choice / Quot.sound
python3 scripts/exact_checks.py        # PASS
```

El paquete `extension/` es autocontenido: `packagesDir = "../.lake/packages"` reutiliza el
checkout de Mathlib del paquete padre y `tws-palomar` entra como dependencia de ruta, por lo
que `Solution` se compila desde fuente y no se hereda ningún `.olean` propio.
