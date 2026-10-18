# Nota sobre el toolchain (corrección de interpretación)

Fecha: 2026-10-18. Esta nota **no reescribe** los informes históricos de la entrega; corrige su
lectura, como exige la cláusula de correspondencia G6.

## Hecho comprobado

| Archivo | Contenido real en este repositorio |
|---|---|
| `lean-toolchain` (raíz) | `leanprover/lean4:v4.35.0-rc2` |
| `.lake/packages/mathlib/lean-toolchain` (pin `0653561…`) | `leanprover/lean4:v4.35.0-rc2` |
| `extension/lean-toolchain` | `leanprover/lean4:v4.35.0-rc2` (generado por Lake en el primer build) |

## Qué dicen los informes históricos

`INTEGRATION.md` (§ Caveats), `VERIFICATION.txt` y `NONPERIODIC_VERIFICATION.txt` afirman que el
`lean-toolchain` de la base dice `v4.28.0` y que esa versión no estaba instalada. Esos informes
describen la copia de la base que se adjuntó al entorno de Aristotle, no el archivo de este
repositorio fijado en `44f4bb7` / `1121b6d`.

## Resolución

1. En este repositorio no hay discrepancia de toolchain: base, Mathlib y extensión coinciden en
   `v4.35.0-rc2`, y todas las comprobaciones locales se ejecutaron con esa versión.
2. No se migró ninguna versión y no se modificó el `lean-toolchain` de la base.
3. La extensión conserva un `lean-toolchain` propio con la versión de referencia (permitido por
   la instrucción de integración), generado por Lake y no editado a mano. Hace explícito el pin
   si la extensión se compila fuera del paquete padre.
4. La advertencia de `INTEGRATION.md` sobre revertir `Set.mem_ofPred_eq` a `Set.mem_setOf_eq`
   tampoco aplica: `Set.mem_ofPred_eq` existe en el pin `0653561…` y los módulos compilan sin
   cambios.

Consecuencia: las afirmaciones de los informes históricos sobre `v4.28.0` quedan identificadas
como referidas a otro entorno, no como defecto de este repositorio.
