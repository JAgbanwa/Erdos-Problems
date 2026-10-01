# Paper IV v1.0 — estándar de auditoría interna posterior al freeze

**Protocolo:** `PIV-INTERNAL-AUDIT-1.0`  
**Preparado:** 27 de septiembre de 2026  
**Estado al prepararlo:** `PLANNED_NOT_EXECUTED`; ejecutado posteriormente sobre `piv-v1.0-f1769273dd2c` con resultado `PASS_INTERNAL_AUTHOR_SIDE` ([informe final](01_INTERNAL_AUDITS/run_20260927_v1.0_f1769273dd2c/10_REPORT/INTERNAL_AUDIT_FINAL_REPORT.md)).  
**Clase:** auditoría interna, del lado del autor; no independiente  
**Activación:** sólo cuando el autor solicite ejecutarlo, después de completar el build combinado, congelar Lean y actualizar la información del freeze en los preprints.  
**Alcance editorial:** cerrado. Este protocolo no autoriza otra revisión de estilo, nuevos teoremas, cambios de constantes ni publicación.

## 1. Objetivo y criterio de éxito

La auditoría debe permitir que un tercero identifique **qué se revisó, sobre qué archivos, con qué herramientas, qué resultado produjo cada prueba y qué no queda certificado por ella**.

El resultado exigido es un paquete con:

1. Una correspondencia completa entre los teoremas, corolarios y afirmaciones verificables del preprint definitivo y sus declaraciones formales o evidencia matemática.
2. Revisión de la compilación y las auditorías del corte exacto que se publica, sin repetir por defecto el build completo.
3. Pruebas matemáticas independientes del código de construcción cuando sea posible, con datos, scripts, registros, certificados y controles negativos.
4. Un informe **Markdown y PDF por bloque de prueba**, acompañado de su ZIP reproducible.
5. Un informe general **Markdown y PDF**, una matriz consolidada de resultados y un ZIP general con manifiestos y hashes.

No basta acumular comprobaciones que terminan sin error. Cada comprobación debe declarar una obligación concreta y una condición de fallo. No se fija de antemano un número de PASS que deba alcanzarse.

## 2. Estándar de referencia y mejoras explícitas

Se revisaron estas fuentes de Paper III, conservadas en
`C:/Users/jtraverso/e81p4/preprints/PAPER_III/02_validation/`:

- `README.md`: separación de auditoría interna, auditoría adversarial y cierre de hallazgos; conservación del historial.
- `01_INTERNAL_AUDITS/00_CONTROL/AUDIT_PROTOCOL.md` y `AUDIT_INDEX.md`.
- `01_INTERNAL_AUDITS/run_2026-08-22_v1.4/00_CONTROL/AUDIT_PROTOCOL.md`: gates G0–G8, regresiones obligatorias y no repetición del build completo.
- `01_INTERNAL_AUDITS/20_EVIDENCE/G2_MATHEMATICS/AUDIT_RECORD.md`: identidades, controles exactos, modelos sobre grafos reales y scripts con sus salidas.
- `01_INTERNAL_AUDITS/20_EVIDENCE/G2_MATHEMATICS/block02_common_profile_LP/`: ejemplo de bloque reproducible y corrección histórica de un control exacto descrito pero inicialmente no ejecutado.
- `01_INTERNAL_AUDITS/20_EVIDENCE/G4_RECORDED_BUILD/AUDIT_RECORD.md`: alcance de `PASS_RECORDED_BUILD`.
- `01_INTERNAL_AUDITS/10_REPORT/INTERNAL_AUDIT_FINAL_REPORT.{md,tex,pdf}`: estructura del informe consolidado y plantilla visual.
- `01_INTERNAL_AUDITS/30_PACKAGE/README.md`: paquete sellado.
- `01_INTERNAL_AUDITS/run_2026-08-23_v1.5_internal_residual/00_CONTROL/AUDIT_PROTOCOL.md`: auditoría de cambios sin reescribir evidencia anterior.

Los protocolos de Paper III citan `preprints/INTERNAL_AUDIT_STANDARD_v1.3.md`. Ese archivo normativo no fue localizado en las copias consultadas; **no se afirma haberlo leído**. Este documento es autocontenido y toma como referencia los protocolos y expedientes efectivamente disponibles.

Se conservan los gates G0–G8 y se refuerzan cuatro aspectos:

- Un informe `.md` **y** `.pdf`, y un ZIP, para cada bloque, no sólo para el informe general.
- Vinculación de los certificados Certo con la especificación exacta mediante hash y revisión de sus supuestos.
- Separación entre factibilidad, cota inferior, cota superior y optimalidad. Una cubierta dual racional más un óptimo numérico aproximado **no** certifica por sí sola una igualdad exacta: ésta requiere también un primal racional de igual valor u otra prueba exacta de la desigualdad opuesta.
- Identificación del corte combinado: retorno optimizado **más** delta local y exports. El PASS remoto del árbol anterior no certifica automáticamente los módulos añadidos después.

## 3. Condiciones previas: no ejecutar antes de cerrar la entrada

El gate de entrada necesita los siguientes archivos y hechos, todos ligados al mismo `freeze_id`:

| Entrada obligatoria | Evidencia requerida |
|---|---|
| Lean congelado | Fuentes, configuración, manifiesto SHA-256 y archivo del freeze; no sólo una carpeta de trabajo |
| Build combinado terminado | Lista de targets, fuentes y opciones, versiones, códigos de salida, registros completos y resumen sin módulos omitidos |
| Auditorías formales | Axiomas y dependencias de las declaraciones públicas, incluido el delta editorial |
| Preprints ES/EN actualizados | Markdown, TeX y PDF de v1.0, con identificación correcta del freeze y sin cambios editoriales adicionales |
| Inventario de afirmaciones | Teoremas, corolarios, ecuaciones cuantitativas, resultados computacionales y alcance de cada uno |
| Dependencias disponibles | Lean y paquetes fijados ya instalados; ruta local de la caché compartida |
| Autorización de ejecución | Petición expresa del autor de ejecutar esta auditoría |

Al iniciar se crea `TARGET.json`, con rutas **resueltas**, hashes y fecha. Se elige la ubicación real del preprint final: no se presupone que las carpetas de borradores sean la publicación. El número de módulos, exports o impresiones de axiomas se calcula, no se copia de conversaciones.

Referencia de preparación, no freeze: el receptor actual es
`C:/Users/jtraverso/e81p4/opt_build_20260927/`. Su integración incorpora
`PaperIVEditorial.ConstructorBudget` y su auditoría. En la preparación se configuraron
504 módulos y 13 targets; estos números se deben confirmar al iniciar la auditoría.

Si una entrada falta, el resultado es `BLOCKED_INPUT`, no PASS parcial del paquete. Se puede preparar el inventario, pero no emitir el dictamen final.

## 4. Protección del corte y de los recursos

### 4.1 Sin otra instalación de Mathlib

- **No ejecutar** `lake update`, descargas de caché, reinstalaciones de Lean, clonaciones de Mathlib ni instalaciones automáticas de paquetes.
- Reutilizar la instalación existente, comprobando `lean-toolchain`, revisiones de `lake-manifest.json`, cambios locales de los paquetes y procedencia de los artefactos.
- Registrar la ruta física de los paquetes compartidos en `ENVIRONMENT.json`; la unión local puede usarse para ejecutar, pero no debe convertirse en una dependencia absoluta del ZIP entregado.
- No modificar ni limpiar la caché compartida. Los artefactos propios de la auditoría, si se necesitan, van a un directorio separado.
- Si la versión fijada no está disponible, detener esa parte y registrar el bloqueo. No descargar otra por iniciativa del runner.
- Las instrucciones para un tercero describirán cómo usar **su** instalación compatible. La prohibición de nuevas descargas se aplica a esta ejecución local; no se dirá que el ZIP contiene Mathlib.

### 4.2 Sin otro build completo por defecto

G4 revisará el build registrado del freeze. El build local combinado ya solicitado es evidencia de entrada, no una prueba que deba repetirse por cada bloque.

Si falta un `#print axioms` o una comprobación de exportación, se admite una consulta Lean pequeña contra artefactos válidos del mismo corte: un proceso, un hilo, opciones y hashes registrados. No lanzar esa consulta mientras exista otro build que compita por los mismos artefactos. Una consulta no reemplaza el registro de compilación del módulo que importa.

Si se descubre que hace falta reconstruir un módulo o corregir una prueba, se abre un hallazgo y se devuelve a integración; no se repara silenciosamente durante la auditoría. La reproducción independiente completa se reserva al carril adversarial, en un expediente distinto.

### 4.3 Presupuesto de cómputo

- Por defecto, un worker pesado a la vez; no añadir MILP, enumeradores y Lean simultáneamente a la carga del equipo.
- Certo y solvers: presupuesto inicial máximo de 60 segundos y 2 GB por instancia; anotar cualquier ajuste antes de repetirla. Un presupuesto agotado significa `INCONCLUSIVE`.
- Acotar los dominios antes del barrido. No ampliar automáticamente un censo ni intentar evaluar una torre numérica gigantesca.
- No detener procesos ajenos. Registrar la concurrencia observada si afecta a los tiempos.
- No enviar fuentes o credenciales a Aristotle ni a otros servicios durante esta auditoría sin una instrucción adicional.

## 5. Matriz de gates G0–G8

| Gate | Objeto | Condición de aprobación |
|---|---|---|
| G0 — Identidad e integridad | Corte, fuentes, configuración, manuscritos y archivos | Todos los hashes coinciden; no se mezclan cortes ni se confunden fuentes con artefactos compilados |
| G1 — Afirmaciones y alcance | Cada afirmación del preprint | Correspondencia completa con la evidencia; hipótesis, cuantificadores y rangos preservados |
| G2 — Matemática y regresiones | Bloques B01–B10 de §6 | Controles obligatorios completos, certificados válidos y limitaciones declaradas |
| G3 — Conformidad formal | Definiciones, puentes, exports y dependencias | El teorema Lean expresa lo publicado; todos los enunciados prometidos están accesibles por la entrada pública indicada |
| G4 — Build y axiomas | Evidencia del corte combinado | `PASS_RECORDED_BUILD`, salida correcta, opciones y fuentes vinculadas, auditorías sin axiomas no permitidos |
| G5 — Paridad ES/EN y formatos | Matemática, estados y referencias cruzadas | Sin diferencias semánticas ni información de freeze desactualizada entre MD, TeX y PDF |
| G6 — PDF y artefactos | PDFs finales y de auditoría | Procedencia de compilación, texto y fuentes correctos; inspección visual de todas las páginas |
| G7 — Procedencia y licencias | Serie, contribuciones, herramientas y código reutilizado | Atribución coherente y corpus identificado; no se infiere originalidad de un namespace limpio |
| G8 — Reproducción y entrega | Scripts, datos, reportes, ZIPs y manifiestos | Un tercero puede identificar y repetir cada prueba; sin secretos, cachés gigantes, rutas absolutas obligatorias ni evidencia obsoleta |

G1 debe distinguir al menos:

- Cota para todo orden con constante aditiva o error lineal, frente a la cota aguda eventual.
- Optimalidad del coeficiente frente a optimalidad de una constante aditiva no demostrada.
- Resultado lejano para **todo grafo** cuando así esté enunciado, no sólo para cordales.
- Resultados de defecto enraizado con sus rangos y normalizaciones reales.
- Estabilidad, rigidez y gap nulo sólo en los dominios demostrados.
- Umbral cercano frente al umbral global, que incluye la rama lejana.
- Cota explícita de tipo torre frente a una cota numéricamente útil.
- `b=0` universal y resultados nuevos de investigación: **fuera del alcance de esta liberación** salvo autorización y nueva entrada formal.

## 6. Bloques matemáticos: una entrega por parte probada

La numeración del preprint se fijará en `CLAIM_MAP.csv` al iniciar. Los nombres siguientes identifican componentes, no sustituyen las hipótesis de sus declaraciones Lean. Todo teorema o corolario publicado debe tener una fila, incluso si su prueba se obtiene por composición; no basta listar el teorema principal.

### B01 — Modelo físico, ganancia y partición completa

**Qué revisar.** Aristas reales; piezas de órdenes permitidos; ausencia de reutilización; cobertura exacta al completar con `K_2`; ganancias 2 y 5; identidad `|Q|=e(G)-g(P)` en su dominio.

**Pruebas.** Reconstruir las aristas desde las listas de vértices de las piezas con un checker separado del constructor. Comparar las dos definiciones de `gainOf` sólo donde coinciden; añadir un control de orden 5 que detecte su divergencia. Probar grafos vacíos, sin aristas, completos, desconexos y vértices aislados cuando estén admitidos.

**Controles negativos.** Arista duplicada, pieza no clique, pieza fuera de orden, arista omitida y valor de ganancia alterado: deben rechazarse por la razón esperada.

**Certo.** `cover` para cobertura exacta, seguido de verificación del certificado. Certo no debe recibir como dato verdadero que una pieza es clique: eso debe comprobarlo el adaptador o el checker literal.

### B02 — Óptimo fraccional, dualidad y puentes de modelos

**Qué revisar.** No negatividad, capacidad por arista, copias reales de `K_3/K_4`, peso correcto y existencia de un óptimo certificado. Puentes entre racionales/reales y entre modelos.

**Pruebas.** Construir el LP directamente desde grafos pequeños, enumerando todas las copias; contrastar con la presentación reducida donde exista. Para afirmar igualdad exacta, verificar primal y dual racionales factibles, con el mismo valor. La factibilidad de un solo lado no prueba optimalidad.

**Certo.** `opt`, `farkas` y `verify`, según admita la especificación. Guardar restricciones, correspondencia variable–clique, solución racional y multiplicadores. Si la búsqueda usa flotantes, el resultado sólo asciende a certificado cuando se verifica exactamente.

### B03 — Redondeo mixto lejano, codegrado y selección marcada

**Qué revisar.** Ganancias por tipo, cuotas, cargas conjuntas, factores de escala, limpieza, paso del matching auxiliar a un packing literal, y orden de elección de parámetros. La precisión positiva debe fijarse antes del grafo.

**Pruebas.** Reconstruir las identidades de cargas y pérdida con racionales; ensayar ejemplos con ambos tipos presentes y conflictos entre tipos. Comprobar que no se reemplaza una ganancia ponderada por cardinalidad ni se suman dos packings que compiten por aristas.

**Superficies orientativas.** `RC01Final`, adaptadores del modelo mixto, infraestructura `Nibble`, `MarkedQuotaGate` y resultados lejanos para todo grafo. El mapa definitivo sale del freeze.

**Certo.** `farkas`/`ratio` para desigualdades representables y `cover` para realizaciones finitas. Los ejemplos no sustituyen el nibble universal ni prueban el umbral asintótico.

### B04 — B7, E18/E19 y propagación de constantes explícitas

**Qué revisar.** Enlace efectivo R3/F1, presupuesto de perfiles, schedule cuantitativo, cota de la rama lejana, conexión con la rama cercana y constante aditiva global.

**Pruebas.** Auditar el cono exigido por `E17.ExplicitFarAudit` y sus vetos al redondeador antiguo. Extraer una tabla de desigualdades con sus hipótesis y factores; verificar extremos y cambios de escala con aritmética exacta. La torre permanece simbólica: se prueban sus relaciones de monotonía y cotas, no se intenta construir su expansión decimal.

**Certo.** Certificados aritméticos de subpasos finitos. No delegar una torre no representada en el lenguaje de la herramienta a un cálculo aproximado ni anunciar una optimización de constantes durante esta auditoría.

### B05 — Localización, regularización y constructor cercano

**Qué revisar.** Partición de vértices, condición de clique, reservas, listas, compatibilidad física y presupuesto. Las cuentas deben describir **el mismo packing o partición**, no testigos existenciales distintos.

**Pruebas.** Derivar de nuevo las cuentas de coste y crédito; probar parámetros de frontera y ramas de `AllInput.hkey` dentro de sus dominios. Revisar que no se asumió sin descarga la existencia del objeto que paga el presupuesto universal.

**Delta obligatorio.** `PaperIV.Editorial.ConstructorBudget.cancel_budget` y
`partition_with_net_budget`: copia exacta, exportación y auditoría en el receptor combinado. La hipótesis local `AllInput` sigue visible; no confundir ese lema con el teorema incondicional.

**Certo.** `farkas` para cancelaciones, `check --hypotheses-only` para detectar regímenes vacíos y `audit` para controles de hipótesis seleccionadas. Un testigo aritmético puede no ser realizable como grafo: se etiquetará como tal.

### B06 — Ensamblaje universal y alcance de los corolarios

**Qué revisar.** Ramas exhaustivas, desigualdades estrictas/no estrictas, casos pequeños, obtención del óptimo, descenso y cierre del objetivo. No afirmar que dos ramas existenciales son mutuamente excluyentes sin prueba.

**Pruebas.** Trazar los argumentos del teorema final. No debe conservar como parámetro una interfaz universal pendiente disfrazada de hipótesis ordinaria. Auditar las fórmulas con pisos, restas naturales, residuos módulo tres y traducción de `M(n)+b` a la forma del problema.

**Controles de alcance.** Mantener el corolario lejano para todos los grafos; separar las restricciones de cordalidad que sí utiliza la rama cercana; comprobar los resultados de defecto enraizado y sus testigos, y el resultado sobre insuficiencia de piezas de orden tres si figura en el paper.

**Certo.** `prove`, `peak` o `induct` sólo si su especificación expresa exactamente el subproblema. No usar una verificación de casos pequeños para declarar `b=0` universal.

### B07 — Testigos extremales, valor split y optimalidad

**Qué revisar.** Cordalidad de los testigos, valores exactos con sus hipótesis, paridades, clasificación de tamaños de núcleo y alcance de la cota inferior para particiones de órdenes arbitrarios.

**Pruebas.** Recalcular la identidad de la parábola y los pisos; comparar todos los maximizadores, incluido el residuo que tiene dos. Verificar certificado físico superior y cota inferior por separado. Distinguir coincidencia de valores óptimos de integralidad del politopo.

**Certo.** `peak`, `opt`, `mixed` y `cover`. `mixed --prove-optimal` se reserva a instancias pequeñas donde haga falta optimalidad y termine con certificado; un incumbent o timeout no basta.

### B08 — Estabilidad y byproducts incluidos

**Qué revisar.** Estabilidad integral, identidad de edición, clasificación extremal, absorción compatible, reserva equilibrada y gap nulo en la familia correspondiente, sólo en la medida en que sean resultados del preprint definitivo.

**Pruebas.** Comparar normalizaciones, constantes, signos y coerciones. Comprobar que absorbedor y packing previo forman una única familia disjunta y que las hipótesis de recursos libres no desaparecen. Revisar que una cota condicional del gap no se convierta en un gap lineal universal.

**Certo.** Identidades exactas y certificados finitos de compatibilidad; separar la experimentación de la demostración paramétrica.

### B09 — Biblioteca estructural y contribuciones citadas

**Qué revisar.** Sólo las interfaces estructurales o contribuciones que el preprint afirme incluir o verificar. Distinguir código del freeze, extracción contrib y material de Papers I–III/V.

**Regresiones obligatorias cuando corresponda.** Grafo vacío; bolsas duplicadas; bosque desconexo; distinción entre hoja y vértice simplicial; hipótesis de no vacuidad, maximalidad, inyectividad y conectividad local. Conservar los contraejemplos que impiden versiones ingenuas de los enunciados.

Las dos extracciones contrib verificadas por separado no se considerarán auditadas para esta entrega sólo por estar próximas en el disco. Si se distribuyen, registrar su propio manifiesto, licencia y evidencia; si no, declararlas fuera de alcance.

### B10 — Regresión literal integrada y controles negativos

**Dominio inicial acotado.** Grafos etiquetados de hasta seis vértices, generados por máscaras de aristas, y familias paramétricas pequeñas de split, dos cliques y ejemplos con `K_4`. Registrar el dominio exacto, cardinalidad, filtros y razones de exclusión. Si se usan representantes no isomorfos, justificar la cobertura; la ausencia de duplicados no demuestra completitud.

**Finalidad.** Detectar traducciones incorrectas de grafos, pesos, particiones y fórmulas. Los teoremas eventuales con umbral enorme no se prueban directamente en estos órdenes. No exigir sus conclusiones fuera de hipótesis ni inventar una reducción que los haga aplicables.

**Certificación.** Reconstruir los grafos y comprobar todas las piezas. Para óptimos pequeños usar búsqueda exacta, programación dinámica o certificado primal/dual apropiado; el estado «optimal» de un solver flotante aislado no es un certificado exacto.

**Controles negativos.** Al menos una mutación semántica por clase de certificado utilizada: cobertura incompleta, sobrecarga, peso incorrecto, hipótesis omitida, dominio alterado y evidencia de otro corte. Un checker que acepta una alteración de una propiedad crítica bloquea el bloque afectado.

## 7. Uso de Certo: contribución concreta y límites

En la preparación se identificó Certo **0.20.1**, esquema de certificados **5**. Estos datos no fijan aún la herramienta de la ejecución: se registrarán versión, hash del código instalado o paquete, solver y opciones en el inicio. No se actualizará Certo en medio de una corrida.

Se usarán las funciones sólo cuando estén disponibles y verificadas en esa versión:

| Uso | Evidencia que debe conservarse | Lo que no autoriza afirmar |
|---|---|---|
| `farkas`, `ratio`, `peak` | Especificación, dominio, certificado exacto, replay | Que el modelo corresponde al teorema sin revisar el adaptador |
| `opt`, `mixed` | Restricciones, testigos, cota y tipo de resultado | Optimalidad a partir de una solución factible |
| `cover` | Universo literal y piezas con incidencias | Validez de cliques si ésta no fue comprobada |
| `verify --spec` | Resultado ligado al hash de la especificación | Corrección de una especificación antigua para una nueva |
| `verify --tamper` | Mutaciones, aceptación/rechazo y análisis | Que cambiar un campo descriptivo deba invalidar un teorema |
| `repro`, `pack`, `status` | Inventario de archivos y certificados | Sustitución de los manifiestos o gates generales del paquete |
| `bind`, si procede | Declaración Lean, tipo, hipótesis y hashes vinculados | Que compartir nombre o hash pruebe equivalencia semántica |

Reglas de uso:

1. Leer la ayuda de la versión fijada antes de escribir los comandos del runner. Este protocolo no presupone un API futuro.
2. Ejecutar generación y verificación como pasos distintos. Guardar ambas salidas y sus códigos.
3. Verificar los testigos combinatorios con un checker pequeño que no reutilice la función que los construyó. Certo desarrollado por el autor sigue siendo herramienta interna, no una auditoría independiente.
4. `--explore`, `likely`, timeout y ausencia de contraejemplos no son PASS de una proposición universal. Si se usa exploración, queda en un subdirectorio separado.
5. Distinguir certificados verificables sin solver de los que necesitan uno; registrar esa dependencia.
6. No introducir `native_decide`, axiomas, interfaces nuevas ni traducciones no auditadas al Lean congelado para facilitar una prueba computacional.
7. Si una función no aporta una obligación verificable al bloque, no usarla sólo para aumentar el número de herramientas.

## 8. Trazabilidad formal obligatoria

`CLAIM_MAP.csv` tendrá, como mínimo:

```text
claim_id,section_es,section_en,statement_hash,protected_hypotheses,
lean_declaration,module,public_entry,export_evidence,build_evidence,
axiom_evidence,constant_cone_evidence,math_block,scope,verdict
```

Para cada resultado publicado se distinguen cinco preguntas:

1. ¿Está la fuente incluida?
2. ¿Fue compilado su módulo en este corte?
3. ¿Se exporta por el punto de entrada prometido?
4. ¿Su tipo formal expresa el enunciado del preprint, sin hipótesis sustantivas omitidas?
5. ¿Su dependencia transitiva usa sólo los axiomas permitidos y la ruta declarada?

Los únicos axiomas permitidos en las declaraciones auditadas son subconjuntos de
`{propext, Classical.choice, Quot.sound}`; no se exige usar los tres.
La inspección textual de `sorry/admit/axiom` es complementaria, no reemplaza el recorrido de tipos y términos de prueba. Eliminar el namespace de procedencia tampoco demuestra independencia de código o bibliográfica: deben mantenerse atribuciones y antecedentes.

La prueba de exportación importa sólo la raíz pública, no un auditor que pueda ocultar una omisión. Las auditorías se conservan como targets separados si ésa es la arquitectura. Se registra el número de **declaraciones distintas** además del número de impresiones, interpretando salidas multilínea.

Los filtros de dependencias y las exigencias positivas de ruta —en particular B7— no se relajan para obtener PASS. Cualquier cambio requiere un hallazgo y una nueva validación del corte.

## 9. Expediente reproducible y formatos de entrega

La ejecución creará una carpeta nueva; no sobrescribirá auditorías del draft:

```text
02_validation/
  INTERNAL_AUDIT_STANDARD_v1.0.md
  01_INTERNAL_AUDITS/
    run_<fecha>_v1.0_<freeze_id>/
      00_CONTROL/
        AUDIT_PROTOCOL.md
        TARGET.json
        ENVIRONMENT.json
        CLAIM_MAP.csv
        PROTECTED_ELEMENTS.json
        TEST_PLAN.json
        FINDINGS.md
        FINDINGS.json
        EXECUTION_LEDGER.jsonl
      10_REPORT/
        INTERNAL_AUDIT_FINAL_REPORT.md
        INTERNAL_AUDIT_FINAL_REPORT.tex
        INTERNAL_AUDIT_FINAL_REPORT.pdf
        INTERNAL_AUDIT_SUMMARY.json
      20_EVIDENCE/
        G0_INTEGRITY/ ... G8_PACKAGE/
        G2_MATHEMATICS/
          B01_MODEL/ ... B10_REGRESSION/
            README.md
            SPEC.md
            scripts/
            inputs/
            results/
            certificates/
            negative_controls/
            REPORT.md
            REPORT.tex
            REPORT.pdf
            REPORT_QA.json
            MANIFEST.sha256
      30_PACKAGE/
        blocks/B01_<freeze_id>.zip ... B10_<freeze_id>.zip
        reports/G0_<freeze_id>.zip ... G8_<freeze_id>.zip
        INTERNAL_AUDIT_<freeze_id>.zip
        INTERNAL_AUDIT_<freeze_id>.zip.sha256
        PACKAGE_INDEX.json
```

Cada gate G0–G8 también tendrá `REPORT.md`, `.tex`, `.pdf`, resultados y manifiesto. G2 puede remitir a sus diez bloques sin duplicar todos los datos en la prosa. «Un informe por parte probada» significa esta granularidad de obligaciones; no miles de PDFs, uno por lema auxiliar.

Cada ZIP de bloque debe poder extraerse y revisarse por separado: scripts propios, especificación, entradas o referencia inmutable a un archivo común identificado, resultados, checker, certificados, informe y versiones. Una ruta a una carpeta mutable de otro equipo no sirve como evidencia. Si un archivo común es grande, puede distribuirse una sola vez con su hash y un resolutor documentado; el bloque debe declarar esa dependencia explícitamente.

No incluir `.env`, credenciales, conversaciones privadas, `.git`, `.lake/packages`, cachés de Mathlib, enlaces de Windows ni objetos compilados de varios cortes. El código de terceros necesario se identifica con versión, hash y licencia; no se redistribuye sin verificar su permiso.

### Contenido mínimo de REPORT.md y REPORT.pdf

1. Identidad del bloque, versión del protocolo y freeze exacto.
2. Pregunta matemática y enunciados que cubre.
3. Hipótesis, dominio, casos fuera de alcance y puente al modelo formal.
4. Método y grado de independencia respecto del constructor.
5. Comandos, versiones, límites, duración y códigos de salida.
6. Resultados esperados frente a observados; factibilidad/optimalidad claramente separadas.
7. Controles negativos y fallos encontrados.
8. Veredicto y límites de la evidencia.
9. Instrucciones de reproducción y catálogo de archivos.

`results/` conserva tanto salidas estructuradas como stdout/stderr. Un resumen no reemplaza el resultado completo. Los fallos y reintentos no se borran: cada intento tiene ID, causa y relación con la corrección.

El informe general agrega la matriz de gates y de afirmaciones, los hallazgos, las limitaciones y la recomendación de paso a auditoría adversarial. No puede ser más concluyente que sus bloques obligatorios.

## 10. Producción de PDF y cierre editorial ya acordado

Los informes se generan desde su Markdown final, con TeX conservado y el estilo de los informes de Paper III como referencia, adaptando sólo idioma y metadatos. Se registran compilador, log y relación hash entre fuente y PDF. Se inspeccionan todas las páginas, incluidas tablas, identificadores largos y URLs. No se entrega un PDF previo a la última edición del informe.

Para los preprints ES/EN, la revisión es de **integridad y paridad**, no otra ronda editorial: se comprueba que la actualización de freeze no cambió matemática, numeración, atribución ni formato. Cualquier problema sustantivo se registra como `CONTENT_QUERY`; no se reescribe el paper durante la auditoría.

Si falta la capacidad de generar o revisar un PDF obligatorio, ese bloque queda `INCOMPLETE_ARTIFACTS`. No se elimina el requisito ni se etiqueta como cerrado sólo por tener Markdown.

## 11. Estados, hallazgos y criterio de PASS

Estados de ejecución: `PLANNED_NOT_EXECUTED`, `RUNNING`, `BLOCKED_INPUT`, `COMPLETED`.

Veredictos de pruebas: `PASS`, `FAIL`, `INCONCLUSIVE`, `NOT_APPLICABLE` y
`INCOMPLETE_ARTIFACTS`. Los calificadores `PASS_RECORDED_BUILD` y
`PASS_FINITE_REGRESSION` precisan el alcance; no son sinónimos de una prueba universal nueva.

Severidades:

| Severidad | Ejemplos | Acción |
|---|---|---|
| Bloqueante | Teorema no corresponde al paper, axioma no permitido, partición inválida, freeze sin identidad, artefacto de otro corte | No liberar; volver a investigación o integración |
| Mayor | Export ausente, condición omitida, certificado no reproducible, parte obligatoria sin evidencia | Cerrar y repetir verificaciones afectadas |
| Menor | Defecto documental no semántico y sin efecto en reproducción | Corregir en el expediente y regenerar derivados |
| Observación | Mejora opcional fuera de alcance | Registrar; no reabrir la matemática |

Una ausencia de hipótesis usada en la demostración es un hallazgo, no una invitación a debilitar el teorema. Las etiquetas editoriales, cuando se necesiten, serán `RETURN_TO_RESEARCH`, `RETURN_TO_AUDIT` o `EDITORIALLY_READY_WITH_QUERIES`, según la causa. La preparación de este protocolo no cambia el estado editorial del preprint.

**PASS interno global:** todos los gates y pruebas obligatorias aplicables pasan, no quedan bloqueantes ni mayores, todos los artefactos exigidos existen y sus hashes verifican. Cada `NOT_APPLICABLE` requiere justificación; no puede usarse para omitir un resultado anunciado. Una prueba obligatoria inconclusa impide el PASS global. Las observaciones externas pendientes se enumeran expresamente.

Un PASS interno no significa revisión humana independiente, prioridad bibliográfica acreditada, autorización de publicación ni cierre de `b=0`.

## 12. Secuencia de ejecución y sellado

1. Comprobar autorización, entradas y ausencia de builds que se vayan a duplicar.
2. Fijar `TARGET.json`, herramientas y manifiesto inicial; calcular el inventario real.
3. Revisar G0, G1, G3 y G4 antes de consumir recursos en experimentos.
4. Ejecutar B01–B10 con límites prefijados; verificar certificados y controles negativos.
5. Revisar G5–G7 conservando el cierre editorial; remitir hallazgos sin reparaciones silenciosas.
6. Redactar informes por bloque y gate; generar TeX/PDF y su revisión visual.
7. Redactar el informe general, resultados estructurados y matriz de hallazgos.
8. Verificar G8 y la integridad del target después de las pruebas. La auditoría no debe haber cambiado las fuentes congeladas.
9. Generar manifiestos de contenidos finales, sin incluir el propio manifiesto en su hash. Crear ZIPs por bloque, comprobar CRC y SHA-256 de cada entrada contra su manifiesto; crear sus hashes externos.
10. Crear el ZIP general al final. Su hash queda en un sidecar externo; evitar referencias circulares donde un informe pretenda contener el hash del ZIP que contiene ese mismo informe.
11. Comprobar de sólo lectura el archivo sellado. Cualquier cambio posterior invalida los hashes y archivos afectados; se crea un nuevo intento, preservando el anterior.
12. Entregar resultados y recomendar, si procede, la auditoría adversarial. No enviar ni publicar automáticamente.

## 13. Regla de reanudación y cambios posteriores

La versión del preprint permanece **v1.0**. Los intentos de auditoría se distinguen por fecha, `freeze_id` y número de corrida.

Si cambia una fuente Lean, se invalida la evidencia de ese módulo y su cierre de dependientes, exports y auditorías. Si cambia el manuscrito o la información del freeze, se invalidan sus TeX/PDF, paridad, QA y paquetes. Un cambio de script, especificación o checker invalida sus resultados; no basta que los datos de entrada sean iguales.

Las pruebas no afectadas pueden reutilizarse sólo con hashes idénticos de entradas, scripts, especificaciones, checker y configuración, y con el motivo de reutilización registrado. No se copiará un PASS histórico sin esa comparación.

Una optimización que conserva los tipos públicos no convierte automáticamente sus logs antiguos en evidencia del nuevo código. Se conserva la comparación y el registro de compilación del corte nuevo. Lo mismo se aplica a un cambio de Certo o de solver.

## 14. Entrega de esta preparación

Este documento deja definido el estándar que se ejecutará cuando el autor lo pida. **No se han ejecutado aquí las pruebas, generado sus informes ni sellado paquetes de auditoría.** La inspección de Paper III y de la ayuda de Certo sirve para diseñar el protocolo, no cuenta como ejecución de los gates.

Lista de estado:

- Plan activo: preparar la auditoría interna posterior al freeze.
- Resultado: protocolo autocontenido con G0–G8 y diez bloques matemáticos.
- Estado matemático: sin cambios al preprint ni a Lean; no se certifica un resultado nuevo.
- Dependencias: corte congelado, evidencia del build combinado, preprints sincronizados y herramientas locales fijadas.
- Pendiente: completar y sellar esas entradas; autorización de ejecución.
- Siguiente acción: al recibirla, abrir una corrida nueva y empezar por G0/G1/G3/G4, sin otra descarga de Mathlib ni otro build completo por defecto.
