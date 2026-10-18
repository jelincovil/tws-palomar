# Propuesta de sustitución y auditoría

Esta carpeta es la versión corregida. El 2026-10-17, `lake build` y
`#print axioms` sí se ejecutaron con Lean `v4.35.0-rc2` en Darwin. Los siete
enunciados no cambiaron. En `Solution.lean` se corrigieron dos desajustes de
API: `unit_le_opNorm` recibe la señal testigo, y la inyectividad de los
desplazamientos usa `sub_add_cancel` porque esta revisión de Mathlib no tiene
`sub_right_cancel`. En Darwin, Comparator se repitió sin sandbox. El script
oficial exige bubblewrap y no fue ese comando local. En GitHub Actions run
39040759159 el script con sandbox terminó bien para el commit
e6698f352a4362e01ed84e4e6ece13d0cf431d6d. La verificación de Palomar
39042287485 aceptó las pruebas. El registro no fue ofrecido. Las pruebas de
Solution siguen sin `sorry`.

## Qué cambia

Se formaliza un operador lineal continuo real de convolución periódica, su
norma supremo, el efecto de periodizar un stencil, la tensorización y la
instancia db2. Se incluye un testigo que alcanza la constante. No se incorpora
la estabilidad del Skeleton con diagramas vacíos, identidad y predicados True.

La norma de operador es la de Mathlib, no una definición que iguala una suma
a la constante deseada. La cota inferior se obtiene con una señal de signos.
La conexión con db2 se expresa mediante la autocorrelación del filtro explícito.

## Cómo reemplazar el repositorio

Trabaja en una rama nueva y conserva la historia Git. Copia **el contenido**
de esta carpeta a la raíz del repositorio; no copies la carpeta contenedora
como un subdirectorio de proyecto. El ZIP incluye los archivos ocultos.

Elimina de la rama de sustitución estos archivos antiguos si todavía existen:

- `TWS.lean`.
- La carpeta antigua `TWS/` completa, después de verificar que no contiene
  cambios propios no incluidos en tu copia de seguridad.
- `scripts/landrun-wrapper.sh`, sustituido por el flujo oficial actual.
- Otros workflows antiguos que ejecuten el verificador anterior, después de
  compararlos con el nuevo `.github/workflows/ci.yml`.

Reemplaza `Challenge.lean`, `Solution.lean`, `formalization.yaml`,
`comparator.json`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`,
`README.md`, `NOTICE`, `LICENSE` y `scripts/verify-comparator.sh` con esta propuesta.
Añade el resto de archivos del paquete. No borres `.git`, no copies `.lake`
ni subas binarios descargados para verificar.

**No basta con pegar encima:** los archivos Lean antiguos sin `module` también
pueden ser examinados por Palomar aunque ya no sean importados.

## Procedencia: por qué ya no se declara como wrapper

El rechazo anterior tenía razón sobre el antiguo paquete. En esta propuesta
las pruebas nuevas completas están en Solution.lean. Por ello se propone un
repositorio sustantivo, con el bloque `repository` omitido conforme al esquema
actual. Se conserva la procedencia de tws-repro y sus commits en los metadatos.

Esto no es una instrucción para borrar el bloque de un wrapper sin cambiar su
contenido. Si prefieres mantener las pruebas en tws-repro, debes portarlas allí,
validar ese proyecto y declarar su nuevo SHA como formalización sustantiva.
El SHA antiguo no contiene el desarrollo nuevo y no sirve para representarlo.

## Orden de auditoría

1. Lee Challenge.lean: comprueba la norma Pi, la convolución, el plegado de
   coeficientes, los desplazamientos centrados y el producto separable.
2. Revisa el uso real del kernel en tu implementación numérica: normalización,
   nivel uno, periodicidad y ausencia de decimación. No se demuestra aquí que
   una biblioteca Python ejecute exactamente este operador. Los niveles 1, 2
   y 3 de la cascada sin decimar siguen seleccionados: `299/256`,
   `9663/8192` y `309991/262144`, para periodos al menos 19, 43 y 91.
   También hay forma cerrada para todo nivel: si `N` alcanza el soporte,
   la norma es `c_j^d`, con
   `c_j = 1651/1395 - (4/63)4^{-j} + (1/180)16^{-j} - (1/1736)32^{-j}`.
   Para todo periodo positivo la norma es a lo más `(1651/1395)^d`, y esa
   potencia es la menor cota común. La condición sobre el soporte es
   suficiente, no necesaria. No se afirma que un periodo fijo alcance el límite.
3. Revisa Solution.lean, en especial el testigo de signos y la inyectividad
   de los siete desplazamientos para N >= 7.
4. Ejecuta los comandos del README en el orden indicado. Corrige los posibles
   errores de API, elaboración o prueba sin debilitar los enunciados.
5. Comprueba el reporte de axiomas y el resultado de Comparator. La presencia
   de `sorry` en Challenge es intencionada; en Solution no es admisible.
6. Revisa autores, contribuciones y el uso de IA. Se conservaron los autores
   del proyecto anterior; ninguno figura como revisor de esta versión nueva.
7. Actualiza VERIFICATION.md y `review` de formalization.yaml únicamente con
   verificaciones realmente completadas. Incluye el SHA que audites.
8. Decide si la nota matemática presenta suficiente interés para un
   especialista. Los lemas generales son estándar; no anuncies novedad
   por haberlos escrito en Lean ni cuentes declaraciones como contribuciones.

## Riesgos concretos aún pendientes

- La elaboración local ya cerró los dos errores de API encontrados. Eso no
  sustituye el criterio editorial de Palomar.
- El script oficial con bubblewrap se ejecutó en GitHub Actions run
  39040759159, y la verificación mecánica de Palomar 39042287485 aceptó el
  commit e6698f352a4362e01ed84e4e6ece13d0cf431d6d. El registro no fue ofrecido.
- Palomar puede seguir considerando rutinario el resultado especializado,
  incluso si las pruebas son correctas. Ningún cambio de redacción garantiza
  superar el umbral editorial.
- La fuente PDF se incluye sin modificaciones. Su sección de formalización
  y disponibilidad debe actualizarse posteriormente para describir la versión
  efectivamente verificada; no atribuyas al PDF pruebas que todavía no tenía.

## Qué entregar a Palomar

Tras completar las verificaciones: repositorio público, SHA completo del
nuevo commit, directorio de proyecto raíz y `comparator.json`. No introduzcas
un ID de registro previo para este simple reintento si nunca se registró.
