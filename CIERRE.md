# Cierre de fase formal

Estado: **CERRADA_LOCAL** — fase formal local completada.

- Base matemática aprobada: `1121b6d5d00ab04be218fea36a4eb36d5990f287`.
- Commit del que parte la integración: `44f4bb79abddf1a4d0a8a3da9a07068c633ed2ab`, un commit
  documental posterior a la aprobación que **no contiene** `extension/`.
- Revisión de la extensión verificada por CI: `ea50a104a1870a08828bdf104ec8022f934b12c8`.
- Ejecución de CI de esa revisión: run `39176786511`, workflow `extension-ci.yml`, **PASS**.
- Publicación: la extensión, sus scripts y su workflow están publicados en la rama
  `extension/db2-threshold`. Los commits posteriores a `ea50a10` solo modifican documentación
  (este expediente, el inventario y el diff); no se les atribuye una compilación nueva.
- Versiones reales y pin: Lean `4.35.0-rc2` (arm64-apple-darwin24.6.0, commit `11acb17`),
  Lake `5.0.0-src+11acb17`, Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`,
  macOS 15.7.9 (24G830). Registro: `extension/verification/entorno.txt`.
- Archivos: `extension/` completo, `.github/workflows/extension-ci.yml` (nuevo; `ci.yml` intacto)
  y este `CIERRE.md`. La base versionada no se modificó: los 30 archivos del commit de partida
  conservan su SHA256 (`extension/verification/integrity-before.json`).

| Ámbito | Estado |
|---|---|
| Fase formal local (extensión) | **Completada** |
| CI de extensión | **PASS** en `ea50a104a1870a08828bdf104ec8022f934b12c8`, run [39176786511](https://github.com/jelincovil/tws-palomar/actions/runs/39176786511) |
| Palomar extensión | `NO_SOMETIDA` |

| Puerta | PASS/FAIL | Evidencia y ruta |
|---|---|---|
| G0 Integridad | **PASS** | `Solution.lean` SHA256 `c3231f1e…b287c`, idéntico al aprobado; snapshot de 30 archivos y `integrity.py check` → `PASS 30 files` (`verification/integrity-before.json`, `verification/integridad-despues.txt`, `verification/repro/06-integrity.log`). Los 7 archivos que difieren de la referencia son el commit documental `44f4bb7` posterior a la aprobación, identificado y no revertido. |
| G1 Entorno | **PASS** | Lean/Lake/Mathlib reales y coherentes con el pin; sin revisión accidental de dependencias (`verification/entorno.txt`, `verification/repro/00-environment.txt`). |
| G2 Integración | **PASS** | `cd extension && lake build` → `Build completed successfully`, `EXIT=0`; 5 módulos como roots (`verification/build-2.log`, `verification/repro/02-extension-build.log`). |
| G3 Matemática | **PASS** | `cascadeTap_sum_one`, `directOp_const`, `directOp_one_eq_id` demostrados en `ThresholdExtension/ConstantPreservation.lean`; más `cascadeInt_sum` como identidad entera de base. `exact_checks.py` → `PASS: 20 rational direct/padded cases; signed masses j=0..4` (no sustituye a Lean). |
| G4 Auditoría | **PASS** | `lake env lean AxiomCheck.lean` → `EXIT=0`, 92 nombres, 0 errores, 0 `sorryAx`; conjuntos: 82 × `[propext, Classical.choice, Quot.sound]`, 9 × `[propext, Quot.sound]`, 1 × `[propext]` (`verification/axioms-2.log`). El comprobador `scripts/axiom_check.py` deriva los nombres de `AxiomCheck.lean` y rechaza salida vacía, truncada, duplicada, con nombres no solicitados o con axiomas fuera del conjunto permitido (`verification/repro/04-axioms-check.log`, `verification/checker-selftest.log`). |
| G5 Reproducción | **PASS** | Copia temporal del árbol completo, mismo layout: `lake build Solution`, `lake build` en `extension/`, auditoría, casos racionales e integridad, todo desde fuente → `ALL CHECKS PASSED`. Reutilizado: solo `.lake/packages` (oleans de Mathlib). Recompilado: `Solution.lean` y los 5 módulos (`verification/repro-clean/`). |
| G6 Correspondencia | **PASS** | Tablas de `NONPERIODIC_SPEC.md` y `THRESHOLD_CERTIFICATE_SPEC.md` actualizadas; `NOTA_TOOLCHAIN.md` corrige la afirmación de `v4.28.0` sin reescribir los logs históricos; los 4 módulos entregados son byte-idénticos al paquete (SHA256 comparado). |
| G7 Entrega | **PASS** | Fuentes, configuración, informe, inventario (`verification/inventario.txt`), diff de la rama, workflow de extensión y pasos de reproducción verificados. |

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

Cada comando se ejecuta en el directorio indicado; la ruta relativa cambia con él.

| Directorio | Comando | Resultado |
|---|---|---|
| raíz | `python3 scripts/preflight.py` | `PASS`, 22 enunciados, `EXIT=0` |
| `extension/` | `lake build` | 5 módulos, `EXIT=0` |
| `extension/` | `lake env lean AxiomCheck.lean` | `EXIT=0`, 92 líneas |
| `extension/` | `python3 scripts/axiom_check.py verification/axioms-2.log` | `PASS: 92 audited names` |
| `extension/` | `python3 scripts/test_axiom_check.py` | `PASS: checker self-test` (5 casos) |
| `extension/` | `python3 scripts/exact_checks.py` | `PASS: 20 rational…` |
| `extension/` | `python3 scripts/integrity.py check .. verification/integrity-before.json` | `PASS 30 files` |
| raíz | `python3 extension/scripts/integrity.py check . extension/verification/integrity-before.json` | `PASS 30 files` |
| `extension/` | `bash scripts/verify_extension.sh` | `ALL CHECKS PASSED` |

**Corrección de ruta.** El expediente anterior documentaba desde `extension/` la ruta
`.. extension/verification/integrity-before.json`, que duplica el directorio y no resuelve. La
forma correcta es `.. verification/integrity-before.json` (tabla anterior). Los registros
históricos de compilación no se reescriben; esta nota queda como aclaración fechada.

## Correcciones aplicadas en este encargo

1. **Raíz de Lake.** El `lakefile.toml` entregado ya listaba los cuatro módulos; se añadió
   `ThresholdExtension.ConstantPreservation` como quinta raíz.
2. **Auditoría de axiomas.** `AxiomCheck.lean` cubría 31 nombres; ahora cubre los 90 públicos de
   los cinco módulos más las dos cotas base.
3. **Especificación.** `NONPERIODIC_SPEC.md` afirmaba que la suma de taps no se calculaba para
   `j` general; era correcto para la entrega y ahora es falso: se actualizó.
4. **Toolchain.** `INTEGRATION.md` y los `VERIFICATION.txt` históricos afirman que el
   `lean-toolchain` base dice `v4.28.0`. En este repositorio dice `leanprover/lean4:v4.35.0-rc2`,
   igual que el de Mathlib en el pin. Se corrige la interpretación en `NOTA_TOOLCHAIN.md`.
5. Los cuatro módulos Lean entregados **no se modificaron** (byte-idénticos).
6. **Cabecera de módulo (detectada por CI).** El primer run falló en `scripts/preflight.py`
   porque `extension/AxiomCheck.lean` no empezaba con `module`; corregido.
7. **Instrucciones de reproducción.** Hacían `checkout` de `44f4bb7`, que no contiene
   `extension/`. Ahora fijan una revisión explícita (ejemplo: `ea50a10…`, la verificada por CI)
   y comprueban `extension/lakefile.toml` y `extension/scripts/verify_extension.sh` antes de
   continuar (ver más abajo).
8. **Comando de integridad.** Ruta duplicada corregida; comprobado que el manifiesto histórico
   no se regenera y que los 30 archivos protegidos siguen intactos.
9. **Workflow de extensión.** El expediente anterior decía que se entregaba «como propuesta
   revisable, no aplicada», pero el archivo no existía. Ahora existe
   `.github/workflows/extension-ci.yml`, verificado estructuralmente, ejecutado en local y
   ejecutado en GitHub (run `39176786511` sobre `ea50a10`); `.github/workflows/ci.yml`
   permanece intacto.
10. **Auditoría ejecutable.** Se añadió `extension/scripts/axiom_check.py`, que falla ante
    errores de Lean, salida vacía o incompleta, nombres no solicitados o axiomas fuera de
    `{propext, Classical.choice, Quot.sound}`; su autotest cubre los cuatro casos.
11. **Limitación mal redactada.** La frase sobre «aritmética real formal» se sustituyó por la
    formulación precisa de la sección de limitaciones.

## Integridad de la base antes/después

El manifiesto `extension/verification/integrity-before.json` protege los 30 archivos versionados
de la base y **no se regenera**: es el snapshot histórico tomado antes de integrar la extensión.

- Antes: snapshot de 30 archivos.
- Después: `integrity.py check` → `PASS 30 files`, ejecutado desde `extension/`
  (`verification/repro/06-integrity.log`) y desde la raíz, y también en la copia temporal
  completa (`verification/repro-clean/06-integrity.log`).
- `git status` no muestra modificaciones en archivos versionados de la base: el contenido
  nuevo está en `extension/` y en `.github/workflows/extension-ci.yml`, y las ediciones de este
  expediente son documentales.

## Estado de verificación

| Ámbito | Estado | Evidencia |
|---|---|---|
| Extensión, verificación local | **PASS** | Compilación de 5 módulos, auditoría de 92 nombres, casos racionales e integridad; ejecutado dos veces: en el árbol de trabajo (`verification/repro/`) y en una copia temporal completa desde fuente (`verification/repro-clean/`). Solo se reutilizó la caché de Mathlib. |
| CI de la base (histórico) | **PASS** | Runs [39173766127](https://github.com/jelincovil/tws-palomar/actions/runs/39173766127) sobre `8988874` y [39174026246](https://github.com/jelincovil/tws-palomar/actions/runs/39174026246) sobre `f7ead24`, workflow `ci.yml`. Alcance: base (preflight, `lake build` de `Challenge`/`Solution`, `AxiomAudit`, Comparator). **No cubre `extension/`.** |
| CI de extensión (nuevo) | **PASS** | Run [39176786511](https://github.com/jelincovil/tws-palomar/actions/runs/39176786511) sobre `ea50a10`, workflow `extension-ci.yml`, 2m 21s. Compila `Solution` desde la raíz, compila los cinco módulos, ejecuta `AxiomCheck.lean` con su comprobador, los casos racionales y la integridad, en un runner limpio; artifact `extension-verification-ea50a10…` con los siete registros. |
| Palomar extensión | **NO_SOMETIDA** | No se sometió la extensión a revisión Palomar. |

El `PASS` remoto de la extensión corresponde al run `39176786511` sobre `ea50a10`, la revisión
que contiene el código, el comprobador y el workflow. Los commits posteriores solo modifican
documentación y no se presentan como una compilación nueva. La verificación local
(`verification/repro/`, `verification/repro-clean/`) se conserva como evidencia independiente
del runner.

## Estado Palomar extensión

`NO_SOMETIDA`. No se sometió la extensión a revisión Palomar.

## Limitaciones

- Los certificados se refieren a `A x`, no a `x`; no se afirma recuperación de `x` ni exactitud
  de denoising.
- `cascadeC j` y `cascadeL` son **cotas superiores** del operador no periódico, no normas
  exactas ni óptimas.
- Las garantías están formalizadas sobre `ℝ` de Mathlib; no incluyen una implementación
  certificada en punto flotante ni una cota del error de redondeo.
- No se afirma optimalidad, multidimensionalidad ni aceptación editorial nueva.
- `directOp_const` y `directOp_one_eq_id` no se usan en los certificados de umbral; se registran
  como parte del cierre formal.
- `exact_checks.py` orienta y detecta regresiones; no prueba cuantificadores universales.

## Bloqueos

Ninguno. No se requirió `sorry`, `admit`, axiomas nuevos ni debilitar metas.

## Cómo reproducir desde una copia de fuentes

Requisitos: Git, Python 3 (solo biblioteca estándar para los scripts), `elan` (resuelve el
`lean-toolchain` del repositorio) y acceso a las dependencias fijadas para `lake exe cache get`.

Ejemplo ejecutable sobre la revisión verificada por CI:

```bash
set -euo pipefail

REVISION=ea50a104a1870a08828bdf104ec8022f934b12c8
git clone https://github.com/jelincovil/tws-palomar.git
cd tws-palomar
git checkout --detach "$REVISION"

test -f extension/lakefile.toml
test -f extension/scripts/verify_extension.sh

lake exe cache get                    # dependencias fijadas (Mathlib 0653561…)
bash extension/scripts/verify_extension.sh
```

El script compila `Solution` desde la raíz, compila los cinco módulos de `extension/`, ejecuta
`AxiomCheck.lean` con su comprobador, corre los casos racionales y comprueba la integridad de la
base. Deja los registros en `verification-logs/extension/` y devuelve un código de salida
distinto de cero ante cualquier fallo.

**Reproducir una revisión frente a seguir la rama.** Una rama se mueve:
`git clone --branch extension/db2-threshold …` sirve para trabajar, pero no identifica por sí
solo una ejecución. Para reproducir un resultado hay que fijar `REVISION` al SHA deseado, como
en el ejemplo; el valor mostrado corresponde a la revisión que verificó el CI.

El paquete `extension/` es autocontenido: `packagesDir = "../.lake/packages"` reutiliza el
checkout de Mathlib del paquete padre y `tws-palomar` entra como dependencia de ruta, por lo que
`Solution` se compila desde fuente y no se hereda ningún `.olean` propio.
