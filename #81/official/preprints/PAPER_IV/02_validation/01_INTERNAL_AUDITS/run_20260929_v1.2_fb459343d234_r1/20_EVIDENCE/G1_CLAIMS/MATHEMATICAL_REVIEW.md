# Paper IV v1.2: revisión semántica y matemática interna

Fecha: 30 de septiembre de 2026. Revisor: Codex, del lado del autor; no independiente. Corte `piv-v12-fb459343d234`; manuscritos `piv-v12-manuscripts-2451d43bface`. No se modificaron sus fuentes. Veredicto: PASS interno con el alcance descrito, no certificación humana independiente.

## Qué se comparó

Los tipos elaborados de `G4_LEAN/EXPORT_TYPES.txt`, los encabezados y pruebas de las interfaces públicas, la cadena de importaciones, los registros de axiomas y la prosa ES/EN. `CLAIM_MAP.csv` distingue las interfaces publicadas de las auxiliares: comprobar 224 exportaciones no equivale a haber rederivado 224 teoremas desde cero. Los 607 módulos tienen procedencia de compilación fresca, distribuida entre dos segmentos; esta auditoría no invocó Lean de nuevo.

### B01: modelo físico

La cobertura es igualdad con el conjunto de aristas, no inclusión. Las piezas tienen al menos dos vértices; el límite cuatro es un predicado adicional. Completar un packing mixto por aristas da exactamente e menos ganancia, con ganancias dos y cinco. La función general por pieza es C(card,2)-1; no se sustituye por la función mixta capada para piezas grandes. El control con orden cinco distingue ambas.

### B02: fracciones y todos los órdenes

La igualdad primal-dual requiere ambos certificados factibles con el mismo valor racional. La mera salida numérica del solver no se acepta. Para las cotas nuevas, `certified_shifted_fractional_bound_all_orders` conserva s<=n y `certified_refined_fractional_bound_all_orders` exige 4s<=n. La suma de min(s,j), la estrella de precios y el caso de núcleo pequeño se separan en F.2; no se multiplica una desigualdad por un coeficiente negativo sin invertirla. El caso n=0 queda cubierto. El argumento de estrella se atribuye a [15], no se presenta como método original.

### B03: redondeo mixto

La precisión se fija antes del grafo y del parámetro s. Las cargas de triángulos y K4 se controlan en el mismo hipergrafo; cotas por tipo aisladas no bastarían. La selección marcada retiene simultáneamente masa total y marcada en un único matching. La combinación de las cuotas usa r>=2 y los dos errores parciales; no convierte una cota cardinal en una cota de ganancia por sí sola. El ejemplo K5 del bloque detecta esa sustitución falsa. La normalización de perfiles utiliza masa como máximo t al cuadrado, no uno. El paso físico conserva recursos y el peso de las piezas desmarcadas.

### B04: umbrales explícitos

Se distinguen el umbral cercano 4 por 10^12, el umbral lejano y su máximo global. La evaluación simbólica de la torre no es una cota práctica. `E17.ExplicitFarAudit` exige los dos componentes de la limpieza mejorada y veta los antiguos teoremas finales; `E35` conserva el coeficiente cuatro en la calibración lejana. La forma inversa exige n>=tower2(Ptower 0). La propagación a la constante aditiva no convierte el umbral cercano en el umbral global. Las regresiones exactas prueban subcuentas pequeñas, no evalúan la torre ni demuestran el teorema asintótico.

### B05: construcción cercana

La cordalidad hace clique la raíz regularizada; el presupuesto numérico solo no lo haría. La segunda fase usa los radios que deja la primera, no un packing independiente. De f>=40m/73-3A/40 y ell<=11A/100+29f/1000 se obtiene un coste como máximo B-117m/1825-12687A/20000, por tanto B-m/16-A/2. La desigualdad de momentos usa la misma asignación inicial y el mismo residuo. Las dos premisas de `cancel_budget` siguen visibles: el control negativo muestra que no puede omitirse la premisa física. `AllInput` es una interfaz local descargada por la cadena global, no una hipótesis pendiente del teorema final.

### B06: alcance global

El Teorema A es para todo orden con constante aditiva; B es agudo eventual. C usa la clase de defecto enraizado fijo y piezas de orden como máximo cuatro. La cota inferior de los testigos vale para particiones irrestrictas. La rama lejana vale para todo grafo. El descenso de grado usa diferencias de pisos y una única cadena; no acumula una constante por ronda. La eliminación de la constante en E.2 usa además el terminal de grado mínimo, no solo el borrado reiterado. En 6.5 se elige una raíz minimizando una puntuación antes de fijar la precisión y antes de la partición. La conclusión sobre exceso positivo no afirma una igualdad asintótica para grafos dispersos. No se sustituye s creciente en un teorema con umbral para s fijo.

### B07: testigos y obstrucción

La parábola 6B+(n-3k)(n-3k+1)=n(n+1) controla todos los maximizadores; hay dos si n es uno módulo tres. El peso -1 en el núcleo y +1 en los radios da cota inferior para cualquier orden de pieza. D.3 solo afirma igualdad de valores óptimos cuando 2<=k<=h, no integralidad del politopo. En 6.3a, delta=(3d^2-d)/2 y 2(e(G)-e(T))=d(4q-4s-d-1). La diferencia frente a nd/4 es no negativa porque 5q-7s-2d-2=4(q-2s-2)+(q-2d)+s+6. El argumento vale para toda rotulación del comparador por su número de aristas. El déficit uno y órdenes arbitrariamente grandes impiden una cota lineal solo en delta hasta la familia de tamaño óptimo.

### B08: estabilidad y raíz común

En el caso cordal la reserva r+m/16+A/2<=delta implica m+A<=16delta y r+A+3m<=48delta. El defecto de una pieza es 1+C(a,2)+3C(b,2)-ab; es cero exactamente para (a,b)=(1,1),(2,1). Cuando es positivo, sus aristas son como máximo diez veces el defecto, con igualdad numérica en (3,2). Esto explica 480, sin afirmar optimalidad de la constante global. La raíz precede al cuantificador sobre todas las particiones, incluso irrestrictas.

Para defecto fijo, `fixed_defect_joint_stability_real` entrega un mismo C,D,H, con C clique real de G y |D|=s, antes de toda Q. El paso a parámetros reales usa el piso del déficit y no una elección distinta de raíz para cada aproximación racional. La comparación con un núcleo de tamaño óptimo paga aparte el término de raíz cuadrada; no afirma que el núcleo redimensionado siga siendo clique de G. La clasificación con delta cero utiliza la estabilidad incondicional, no solo la implicación condicional E32. Las reservas y absorbedores del apéndice B conservan explícita la libertad de recursos y forman un único packing.

### B09 y B10: estructura y regresiones

Las hipótesis de conectividad, no vacuidad y maximalidad de bolsas no se suprimen. El grafo vacío, las bolsas duplicadas, el árbol aislado y una hoja con dos vértices privados refutan los enunciados ingenuos. F.3a cuenta no-aristas ordenadas y utiliza parte positiva. Los enumeradores literales de ciclos inducidos y de eliminación perfecta coinciden en el dominio finito comprobado; esa coincidencia no es la prueba universal de su equivalencia.

## Cotejos obligatorios de las ampliaciones

| Bloque | Declaraciones y comprobación | Dictamen |
|---|---|---|
| E.4 paleta | `AllInput.params_strict`: k=2(c-2sigma)-floor(rho/1000); floor>=rho/2000; k<=n; mantiene las dos capacidades y las reservas previas | PASS |
| E.4 cuenta física | `constructor_retained`, `normalized_deficit_budget`: theta=1/[2000(s+1)^2]; conserva el ahorro exterior en la misma Q; D0+a+theta m+R<=delta | PASS |
| E.4 excepciones | `AllInput.hkey_strict`: suma rho/800 a cada contribución. Los casos j=0, 1<=j<=s-nu y j>=s-nu+1 siguen exhaustivos; R>=t rho/800>=0 | PASS |
| E.4 exceso | `core_excess_le_residual`: mismo L; 2(L+t)<= (c+b+s)/3 y grado<=n dan E<=R+nt | PASS |
| E.4 clique | `AllInput.no_core_pairs`, `clique_core_or_large_excess`: la prohibición usa vecinos comunes normalizados, no rsd sola; c>=20(s+1)^2; clique de tamaño c-s o c-s<=2E | PASS |
| E.4 desplazamiento | `exists_clique_core_with_shift`: r<=s y r c<=4sE, luego rn<=16sE con c>=n/4 | PASS |
| E.4 edición | `template_distance_before_shift`, `exists_root_partition`: clique C de G, |D|=s, partición de vértices; coste interior E+rn y cambio adicional rn+2nt; total<=40000(s+1)^3 delta | PASS |
| F.3a | `exists_clique_additive_defect`: inducción, x=(|D|-1-|P|-s) positivo; si y>=x+1, (x+1)^2<=x^2+2y; si y<=x, adjuntar v a P; conserva el grafo ambiente | PASS |
| F.3b | `ordNE_le_twice_deleted`, `recover_clique_from_edit`: u>=0, dos orientaciones por no-arista; interfaz racional y argumento real explícitamente distinguidos | PASS |
| F.5 A | `l11_caseA`: todas las coloraciones tienen muchos conflictos; tamaño y precisión antes del muestreo; conteo con reemplazo | PASS |
| F.5 B1 | `l11_caseB1`: coloración con pocos conflictos pero sección mala; prefijo de longitud y, factor de extensiones n^(m-y), delta11*y^2=1/4 | PASS |
| F.5 B2 | `l11_caseB2`: sin sección mala; rangos normalizados a <=n; edición menor que delta11*n^2+K*eta*n^2<=epsilon*n^2 contradice lejanía | PASS |

En E.4 los nombres cortos viven en distintos namespaces; `CLAIM_MAP.csv`, las fuentes nombradas y los registros de build resuelven los módulos. Se leyeron StrictParams, StrictBudget, ResidualExcess, CoreCliqueAlternative, LargeCliqueCore, TemplateDistance, RootPartition y las interfaces de publicación. La inspección no se reduce a comparar nombres.

## Las siete obligaciones expositivas de A.2

Los siguientes juicios son para un paper acompañado de fuentes formales y referencias explícitas. No declaran que el texto solo contenga una demostración elemental íntegra de cada resultado clásico.

1. **Regularización: ACCEPTABLE_SUMMARY.** Se especifican conjuntos retirados/incorporados, umbrales y déficits; las cotas de masa salen de contar incidencias deficientes, y la exclusión de C4 sostiene cliqueidad. Las capacidades se expresan antes del constructor. La evaluación exacta de todas las constantes sigue en RegularizationBounds; no es una nueva premisa.
2. **Limpieza: ACCEPTABLE_SUMMARY.** C.2 separa pares irregulares, baja densidad y copias tocadas, con multiplicidades y capacidades. La cuenta de copias mejorada no se confunde con la de perfiles; el enlace B7 auditado conserva ambos términos.
3. **Fibras: ACCEPTABLE_SUMMARY.** C.1 y C.2 explicitan regularidad, fibra limpia y codegrado conjunto, seguidos por la normalización de masa. La referencia a '§3.2' debe leerse como Lema 3.2/C.1; se deja aclarada en la errata del expediente. No se usa regularidad para una fibra arbitraria sin limpieza.
4. **Nibble y torre: ACCEPTABLE_SUMMARY.** C.3 fija el orden de parámetros y una tabla de dominaciones; los pasos son monotonía y aritmética sobre funciones explícitas. No se intenta evaluar una torre gigante ni se cita un umbral existencial como efectivo. El nibble de Paper III conserva su atribución.
5. **Normalización preterminal: ACCEPTABLE_SUMMARY.** E.1 define las regiones y las escalas, da las cotas de error usadas y separa el terminal local del umbral de localización. F.1 expone la composición de umbrales. Es una exposición por contratos con implementaciones nombradas, no una prueba en prosa de cada filtrado.
6. **Presupuesto terminal: ACCEPTABLE_SUMMARY.** E.1 ya despliega la desigualdad conjunta y sus tres casos; E.4 retiene el crédito estricto y paga extracción y desplazamiento. La revisión anterior identificaba un esbozo; esta versión aporta las cancelaciones y las cotas necesarias para seguir el argumento.
7. **Bose/Skolem: ACCEPTABLE_SUMMARY.** D.1 identifica los diseños clásicos, sus congruencias y la contabilidad por residuos; atribuye las construcciones y mantiene la verificación formal de los modelos finitos. No necesita reivindicar ni rederivar como nuevo el diseño clásico completo. Se separa esta prueba de la optimalidad de orden cuatro.

Ningún juicio anterior se deduce únicamente del PASS de Lean. Un árbitro puede pedir más expansión expositiva; eso no se contabiliza como una demostración humana independiente ya realizada.

## Anexo separado y límites

El resultado de gap con clique máxima acotada es triangular, con coeficiente dependiente del ancho. Los 38 módulos BoundedCliqueGap y su cierre histórico se cotejaron con fuentes y logs propios. No se exportan fingidamente desde PaperIV ni se usan para demostrar un gap mixto lineal universal. Las extracciones contrib no distribuidas en el corte no están certificadas por proximidad de carpeta.

No se afirma b=0 universal, prioridad bibliográfica, independencia histórica a partir de namespaces ni nueva reproducción independiente de Lean. La auditoría adversarial sigue pendiente. Las pruebas finitas tienen solo el dominio que declaran sus especificaciones.
