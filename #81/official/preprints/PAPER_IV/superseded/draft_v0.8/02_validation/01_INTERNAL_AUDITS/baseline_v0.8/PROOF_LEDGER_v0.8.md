# Paper IV — ledger de prueba y exposición v0.8

Fecha: 21-09-2026. Manuscrito: `PAPER_IV_preprint_v0.8_es.md`.
Árbol contrastado, sin editarlo: `C:/Users/jtraverso/e81p4/paper4_lean`.
Este ledger sustituye editorialmente el de v0.7; no mezcla árboles ni migra formalizaciones.

## 1. Alcance y criterio de estado

Una demostración universal: redondeo mixto en el régimen con margen y descenso más construcción en el régimen crítico. La forma híbrida conserva el testigo; el puente de modelos conserva recursos y valores. No se cuentan como tres pruebas independientes.

**PASS Lean final** significa que la declaración figura en la auditoría ejecutada para este corte local, con huella fundacional estándar. **Fuente intermedia contrastada** significa que se leyó el contrato o su implementación dentro de esa cadena, sin presentar una auditoría individual nueva. **Exposición ampliada** describe trabajo editorial, no un teorema matemático nuevo.

La revisión comprueba cuatro targets separados: `PaperIV/Audit.lean`, `PaperIV/ConeAudit.lean`, `SupplementAudit.lean` de esta entrega y `BoundedCliqueGap/AxiomCheck.lean`. Los comandos, salidas, recuentos y hashes actuales están en `AUDIT_SNAPSHOT.json` y `AUDIT_SUMMARY.json`; no se reproduce como propio el total de 817 declaraciones comunicado en el feedback. La auditoría suplementaria cubre siete declaraciones de `FarExploration` y `ThreeRegime`; la biblioteca triangular ejecuta además su comprobación automática de huellas y cinco impresiones finales. Hay solapamiento entre declaraciones y dependencias, de modo que esos recuentos no deben sumarse.

Los imports reutilizan la caché existente; no se hizo una reconstrucción íntegra desde cero ni una auditoría humana independiente de Papers I–III. No aparece `sorryAx` en las huellas ni aparecen `sorry/admit/axiom/native_decide/implemented_by` en la búsqueda de tokens de las fuentes inventariadas, excluidos comentarios y cadenas. Esto no sustituye una comprobación desde un entorno nuevo. El corte local comprimido incluye fuentes, configuración y manifiestos de dependencias, no cachés ni credenciales; lo identifica `LEAN_CUT.json`. Falta su commit/URL público.

El veto del espacio de nombres `Erdos81` certifica ausencia de esos nombres en los conos examinados. No certifica por sí solo ausencia de código copiado y renombrado ni originalidad bibliográfica. Mathlib es el único paquete de terceros requerido **directamente**; existen sus dependencias transitivas. Los complementos están en el snapshot y tienen auditorías propias: no se afirma que `PaperIV.lean` los reexporte.

## 2. Cadena mínima, paso por paso

| Paso | Entrada | Operación y salida | Evidencia y lugar en el texto |
|---|---|---|---|
| 01 | Grafo finito, piezas reales K3/K4 | Capacidades por arista; ganancias 2/5. Completar con K2 cuesta exactamente e−g. | §2.1, Lema 2.1; modelos `Model`, `FarRounding`. |
| 02 | PL finito racional | Óptimo alcanzado y cubierta de igual valor; ningún óptimo se recibe como axioma. | §2.2; `CertifiedOptimumExistence.exists_certifiedFractionalOptimum`, `PaperI.FiniteLP.exists_optimal_pair`, PASS Lean final. |
| 03 | Óptimo mixto | Definir F4=e−W*, margen Δ=M−F4. Identidad e−g≤M ⇔ W*−g≤Δ. | §1.1 y §2.3; identidad contable, no criterio suficiente de existencia por sí solo. |
| 03a | Partición literal, sin restricción de orden | Sumar choose(|K|,2)−1 por pieza; g(Q)+|Q|=e. Olvidar OrderAtMost transfiere la cota c4 a cp. | §1.1, §6.3; `LossBudget.budget_iff`, `erdos81_cp_form`, `erdos81_cp_form_all_orders`, auditados. |
| 03b | Familias admisibles S⊆S′ | Extender pesos por cero implica W*S≤W*S′ y ΔS≤ΔS′. | (1.3b), deducción escrita; no nueva declaración Lean general atribuida. La monotonía no es estricta universalmente. |
| L01 | Rango acotado, cargas≤1, codegrado pequeño | Nibble con pérdida β·masa + β·|U| + C. | Lema 3.2; `PaperIIISlackNibbleAdapter.boundedRankNibbleAt`, entrada demostrada de Paper III. |
| L02 | Familia uniforme y subfamilia marcada | Extender con dos depósitos de tokens; proyectar un matching que conserva dos cuotas. | Lema 3.3; `MarkedQuotaSlackGate.slackMarkedQuotaNibbleAt_proved`. Exposición del adaptador ampliada. |
| L03 | Triángulos/K4 físicos | Agrupar parejas disjuntas de triángulos, marcar K4; ganancia 4·total+marcados. | Lema 3.4; `MarkedQuotaPairing.paired_typed_gain_slack`, `JointTwoQuotaPhysical.mixed_physical_packing_of_slackMarkedQuota`. |
| L04 | Partición regular, masa transferida | Eliminar recursos malos una vez; ψ_H≤t²; presupuestos a3t³/a4t⁴; sumar codegrados físicos. | Apéndice C; `RC01PatternMassScale`, `RC01CleanedGate.cleanedPacking_joint_codegree_le_of_served_patterns`. |
| L05 | Precisión fija ξ>0 | Elegir selector, parámetros, límite de clases y N antes del grafo; unir masas triangular grande/pequeña. | Teorema 3.1; `RC01Final.rc01_uniformRoundingTarget`, PASS Lean final. |
| L06 | F4<n²/6−η0n² | Redondear con ξ=η0/2 y completar. | Corolario 3.5; `RC01FarAssembly.farRegime_cliquePartition`, PASS Lean final. |
| C01 | Cordal | Dos copias opuestas: 2F4≤F4(izq)+F4(der); seleccionar dirección y potencial lexicográfico; terminal split. | Lema 4.1; `VertexCopyMonotone.two_mul_F4_le_add`, `VertexCopyGate`, `GatedTerminalSplit.exists_split_terminal_symmetrizationPath`. |
| C02 | **Cercanía local supuesta**, valor crítico | Elegir comparador C. Robustez por edición y cálculo split calibran su tamaño. C no es clique de G. | Lema 5.1; `NearH1SplitComparator`, `NearH1CalibratedRoot`. |
| C03 | Comparador C y cordalidad | Clique máxima P en G[C]; faltan ≥u(u+1)/2 pares; trasladar ≤un ediciones. | Lema 5.1; `ChordalCoreMissing`. Produce presupuesto a²/65536. |
| C04 | Clique P calibrada | Retirar columnas malas e incorporar hubs; no-C4 prueba R clique; cuentas dan paleta, anchura y defectos. | Proposición 5.2; `Regularization`, `RegularizationBounds`, `RegularizedRootGoal`; wrapper auditado `RootRegularizationBridge.exists_regularizedRoot_engineFree`. |
| C05 | Raíz R regularizada | Vizing, equilibrio de clases, clases pesadas y desplazamiento cíclico; producir f triángulos exteriores. | §5.3; `NearH1PhaseI`, `RD09PaddedL1Mass`. |
| C06 | **La misma** fase I y enlaces ocupados | Uno/dos candidatos por factor; momentos y promedio; producir bases internas no fallidas. | §5.3; `RD09FactorCandidateMoments`, `RD09FactorCandidateAverage`. |
| C07 | Dos fases compatibles | `canonicalBad` excluye exactamente enlaces ocupados y faltas de adyacencia; la compatibilidad se demuestra y el conteo es aditivo. Lema 5.3 da coste≤B−m/20−A/2. | `RD09H1SpokeRealization.isSpokeCompatible_surviving_canonicalBad`, `RD09SpokeCompatibility.card_union_phases`, `NearH1FinalAssembly`, `RD09PhysicalLedger`; §5.3. |
| C07a | C02–C07, cercanía supuesta y valor crítico | Teorema 5.0: raíz real de tamaño entre n/4 y n/2 y partición con el ahorro estricto. | Contrato expositivo compuesto de los lemas; no nueva declaración Lean independiente. No usa C09. |
| C08 | C02–C07 bajo cercanía local | F4≤coste y envolvente racional ⇒ m+10A≤20D ⇒ distancia≤20D. | Lema 4.2; `NearH1WindowAccounts.exists_window_accounts`. No usa localización global. |
| C09 | C01, C08 y cambio≤1/n por paso | Descender desde distancia cero; ventana exterior y contracción interior. | Proposición 4.3; `NearH1Localization.exists_localized_split_core`. Umbral cercano 2·10^13. |
| C10 | Grafo original localizado | Reaplicar constructor local y conservar comparador, raíz, empaquetamiento y cuentas. | §5.4; `HybridDichotomy.chordal_far_or_nearStructure`, PASS Lean final. |
| F01 | Casos lejano/crítico exhaustivos | Partición del mismo grafo original con coste≤M para n≥max(Nlej,Ncer). | Teorema B; `Erdos81Unconditional.erdos81_cliquePartition`, PASS Lean final. |
| F02 | Completo-split con 2≤k≤h | Pesos −1/+1 dan cota inferior irrestricta; factorización la alcanza; testigo es cordal. | §6.1–6.2; `SplitCompleteSharpValue`, `PaperTheorems.erdos81_max_eq`, PASS Lean final. |
| F03 | Cota eventual | Absorber órdenes finitos restantes con b=N²; no dar valor numérico global falso. | Teorema A; `Erdos81AllOrders.erdos81_all_orders_additive`, PASS Lean final. |

**Orden lógico de C02–C09:** se prueba primero la construcción bajo la hipótesis local de cercanía. Luego esa construcción alimenta la contracción que demuestra la cercanía del grafo original. El orden expositivo presenta el contrato local antes del descenso y desarrolla su construcción en §5. No hay que sustituir ese orden por una llamada circular a la conclusión global.

## 3. Consecuencias y herramientas

| Resultado | Estado y alcance | Enunciado auditado |
|---|---|---|
| Estabilidad integral | Teorema 6.1, m/20+A/2≤δ y distancia≤20δ. No cambiar por 9δ. | `IntegralStability.chordal_linear_stability` |
| Clasificación extremal | Corolario 6.2, eventual; usa cota inferior irrestricta. | `ExtremalClassification.chordal_extremal_classification` |
| Exceso pieza a pieza | §6.4, particiones irrestrictas; defectos cero sólo enlaces y triángulos con host. | `SplitCompleteDefect.size_add_choose_eq_mul_add_sum_defect` y `defect_eq_zero_iff` |
| Coeficiente lineal óptimo | §6.3; 1/6 es inevitable, b absoluto no optimizado. | `LinearCoefficient.linear_coefficient_optimal` |
| Gap mixto cero | Proposición 6.3; sólo completo-split 2≤k≤h. No integralidad del politopo. | `SplitMixedGap.mixed_gap_zero` |
| Absorción compatible y presupuestada | Apéndice B.1; libertad de recursos explícita. No reemplazo universal automático. | `SpreadAbsorptionCompatibility.exists_budgeted_compatible_spread_absorber` |
| Reserva equilibrada | Apéndice B.2, Beck–Fiala de Paper III. | `BalancedReserve.exists_balanced_reserve` |
| Sensibilidad de umbral | §4.2, suficiencia parametrizada; no Θ ni umbral óptimo. | `NearThresholdSensitivity.near_threshold_of_budget` |
| Remate con cuatro anfitriones | Incorporado en B.3 y auditado. Grado≤3, cuatro hosts dados, distintos y fuera de las bases; no existencia universal de hosts. | `FourHostClosure.exists_fourHost_packing`, `fourHost_saving` |
| Reserva exacta | Incorporada en §6.7. k≤n y choose(k,2)≤k(n−k); conserva pisos y resta natural no negativa. | `ReserveIdentity.targetSize_eq_baseline_add_reserve` |
| Grafos completos, todos los órdenes | Apéndice D, c4(Kn)≤M(n), sin umbral; caso de b=0 en esa familia, no todos los cordales. | `ThreeRegime.CompleteStateAllOrders.complete_state_closes`, `exists_packing`; auditoría suplementaria. |
| Barrera para una limpieza concreta | §8.3, ε≤1/(7e^34) implica N0>e^72 para `CleanupAtWith` sobre todos los grafos. No es una cota inferior demostrada para Nlej de RC01. | `CleanupRigidVerdict.threshold_gt_exp`, `threshold_superpolynomial`, `threshold_gt_exp_seventy_two`; auditoría suplementaria. |
| Gap triangular, clique acotada | §8.2, ν3*−ν3≤(10+d/2)n si G es cordal y K(d+2)-free. d es fijo para interpretar O(n); no es el gap mixto. | `BoundedCliqueGap.chordal_gap_linear_cliqueFree`; `BoundedCliqueGap/AxiomCheck.lean`. |
| Forma por anchura de bolsas | §8.2, árbol de cliques con bolsas de tamaño≤d+1; equivalencia con excluir K(d+2). No se importa un operador general treewidth de Mathlib. | `chordal_gap_linear_of_cliqueTree_width`, `exists_cliqueTree_width_le_iff_cliqueFree`. |
| Límite cordal del testigo rígido | §8.3, n≥2: PEO y ausencia de K4 dan e≤2n−3; rigidez da 3T≤e; la masa requerida exige n≤20/ε. | Observación escrita del feedback, desarrollada en (8.4)–(8.5); no se atribuye una nueva declaración Lean a esta composición. |

## 4. Elementos protegidos

- M(n) conserva el piso. b es absoluto. No se afirma M(n) para todos los órdenes ni b=0.
- ε0=10^-12, η0=10^-16; cambio de umbral cercano solicitado y verificado: 10^14→2·10^13. No sustituir Nlej por Ncer.
- Ganancias mixtas 2/5; una sola capacidad por arista, compatible entre las dos fases.
- Tabla 2: 1600,2920,219 y 200,35,8; consecuencia 19/365,253/500 y versión m/20+A/2, preservadas.
- Conteos exactos, paridades y rango 2≤k≤h preservados. Ganancia general y ganancia capada no intercambiables fuera de K3/K4.
- Fuente [5] citada por título, firma, fecha y commit. No se deriva prioridad de una auditoría de namespaces.

## 5. Pendientes de publicación, no premisas del teorema

1. Publicar el corte comprimido identificado por SHA-256 con URL/commit. El snapshot local ya está adjunto; no se finge que el commit del repositorio padre incluya el árbol limpio.
2. Revisión humana de la correspondencia de las nuevas exposiciones §§3–5 con sus contratos Lean; las auditorías no sustituyen esa lectura.
3. Adjuntar las auditorías propias de Papers I–III si se promete auditar la serie completa; aquí se comprobó su uso transitivo.
4. Mantener separada la investigación experimental de órdenes pequeños. No afirmar exhaustividad por un recuento comunicado.
5. Versión inglesa como prioridad editorial antes de circulación internacional y decisión de venue. No se produjo en este encargo de revisión española.
6. Cerrar la revisión bibliográfica del proyecto anunciado de Whitman y colaboradores cuando exista un manuscrito comparable. No se envió correspondencia en esta revisión.

Los archivos `AUDIT_DECLARATIONS.tsv`, `AUDIT_SNAPSHOT.json`, `AUDIT_SUMMARY.json`, `NUMBERING_MAP.json` y `MANIFEST_SHA256.md` dan la evidencia reproducible de esta entrega.

## 6. Detalle añadido para lectura humana

1. **Terminación:** terminal ⇒ dos simpliciales de Dirac con vecindario común; argumento de componente ⇒ exterior independiente ⇒ completo-split. Fuera del terminal, la copia de clase menor a mayor gana al menos 2(s−t+1) pares ordenados; si baja F4, la dirección opuesta lo sube. Finitud termina el proceso.
2. **Comparador:** casos de pocos vértices en núcleo o sin hosts y tres ramas del perfil fraccional explícitas. Sólo después de excluir ramas alejadas se usa B_n(k).
3. **Constructor:** Teorema 5.0 expone el contrato local antes de usarlo globalmente. Fórmula de aristas y número de triángulos demuestra la identidad de piezas.
4. **Calibración:** s/a≤1/48 se obtiene de los cambios exactos por X,Y. El denominador conserva q−1 y su margen racional positivo sobre 393/100.
5. **Umbral:** se escribe 10/(3n)+5/(6n²)<2.48·10^-13. El valor 2·10^13 es suficiente localmente; no es el umbral global ni una ley Θ demostrada.
6. **Motor lejano:** prueba trasladada íntegra al Apéndice C, no eliminada ni atribuida por completo a Paper III. Los números de los lemas y ecuaciones se conservan.
7. **Notación:** los fallos de fase II son ℓ, no g; g(P) sigue siendo la ganancia.

## 7. Complementos y límites de su incorporación

- La biblioteca de gap triangular acotado está ahora integrada y se incorpora como complemento (§8.2), con auditoría propia. No se importa al cono del resultado mixto durante esta edición.
- Algoritmo eficiente: no se deduce de existencia Lean ni se asigna complejidad sin análisis.
- Diseños y Skolem: se incorpora la exposición del resultado ya formalizado en `ThreeRegime`, sin portar código ni declararlo antecedente necesario de la cota universal.
- Para cordales, anchura de árbol acotada y número de clique acotado no son dos regímenes distintos (tw=ω−1 para grafos no vacíos). No se usa esa falsa distinción editorial.
- b=0 y gap universal O(n): preguntas abiertas del alcance de esta ruta, no conclusiones experimentales ni independencia lógica demostrada.

## 8. Cambios semánticos controlados respecto de v0.7

Las 115 fórmulas desplegadas de v0.7 siguen presentes. Hay 118 en v0.8: se añaden el gap triangular acotado y las dos cuentas que delimitan el testigo rígido cordal. No se alteró la prueba central, sus ganancias, sus constantes ni sus cuantificadores. Se conservaron los ocho fragmentos Lean literales, cotejados con fuentes del corte. El argumento cordal evita apelar a una noción general de treewidth: se cuenta directamente por un PEO y se explicita n≥2.

La comparación bibliográfica separa tres preguntas: qué concluye el manuscrito, qué hipótesis conserva su formalización y qué mecanismos emplea. La forma M(n)+b se obtiene de cualquier cota eventual con absorción finita; no se presenta como una ventaja matemática frente al Teorema eventual de [5]. La barrera de limpieza es un complemento condicionado a su contrato, no un argumento de imposibilidad de todo redondeador alternativo.

El depósito Zenodo v3 se verificó en la API pública: DOI de versión 10.5281/zenodo.22064657, DOI de concepto 10.5281/zenodo.21273143, fecha de publicación 23-08-2026, seis PDF. La cronología identifica versiones; no decide prioridad ni demuestra que [15] use o no use la serie.

## 9. Pendiente de investigación separado de la edición

La observación (8.5) no prueba `CodegreeCleanupAt` restringido a cordales ni establece N=O(1/ε) para ese contrato. Tampoco se declara aquí formalizado el adaptador restringido limpieza→redondeo. Su eventual demostración sería investigación nueva, no una premisa omitida del resultado actual. La familia de Ruzsa–Szemerédi no se etiqueta íntegramente como no cordal: la exclusión afecta a sus instancias densas responsables de la barrera, no necesariamente a casos pequeños o degenerados.
