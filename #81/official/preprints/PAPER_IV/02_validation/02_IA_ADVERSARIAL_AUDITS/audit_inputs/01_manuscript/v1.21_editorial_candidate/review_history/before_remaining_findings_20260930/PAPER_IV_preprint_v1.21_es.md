# Particiones de cliques con defecto simplicial enraizado: estabilidad cuantitativa y cotas agudas para órdenes grandes

**Juan Pablo Traverso Gianini**  
Investigador independiente, Santiago, Chile  
[jtraverso@gmail.com](mailto:jtraverso@gmail.com)  
[ORCID: 0009-0003-6068-4096](https://orcid.org/0009-0003-6068-4096)

**Paper IV de la serie**  
**Preprint:** versión 1.21, candidata a revisión editorial.
**Fecha de esta revisión:** 30 de septiembre de 2026.
**Estado:** revisión de trabajo en Markdown preparada en paralelo con la auditoría externa de la versión 1.2. El corte Lean sigue siendo `piv-v12-fb459343d234`; esta revisión no modifica sus fuentes. La versión 1.2 completó su auditoría interna y su auditoría externa está en curso. Ninguno de esos veredictos se transfiere automáticamente a las explicaciones añadidas aquí. Quedan pendientes las ediciones maquetadas y la revisión editorial y bilingüe de la versión 1.21. Esta candidata no se ha publicado ni tiene un DOI propio.
**DOI de concepto de la serie:** <https://doi.org/10.5281/zenodo.21273143>. El DOI de versión del depósito que reunirá Papers I–IV todavía no está asignado.

**MSC 2020:** Primario 05C70; secundarios 05C35, 05C72.

## Resumen

Estudiamos cómo un número de partición en cliques grande restringe la estructura de un grafo y de sus particiones casi óptimas. Para cada defecto simplicial enraizado fijo \(s\), demostramos estabilidad cuantitativa en el modelo \(c_4\), cuyas piezas tienen orden a lo sumo cuatro. Si \(c_4(G)\ge Q_s(n)-\delta\), con \(0\le\delta\le\gamma_s n^2\) y \(n\) por encima de un umbral explícito, el grafo está a distancia de a lo sumo \(A_s\delta\) ediciones de aristas de una plantilla de defecto sobre una clique real del grafo. Esa misma raíz controla toda partición irrestricta casi óptima, tanto en su número de piezas no canónicas como en la cantidad total de aristas que contienen. La aproximación por una plantilla de tamaño óptimo tiene una cota separada \(A_s\delta+n\sqrt{(1+4A_s)\delta}\). Una familia explícita está a distancia de al menos \(n\sqrt{\delta}/8\) de toda plantilla de tamaño óptimo, lo que explica por qué deben distinguirse ambas formas de aproximación.

Para grafos cordales, las constantes especializadas son \(16\delta\) ediciones, \(\tau+48\delta\) piezas no canónicas y \(10\tau+480\delta\) aristas en esas piezas cuando la partición tiene a lo sumo \(M(n)+\tau\) partes. Aquí
\[
M(n)=\left\lfloor\frac{n(n+1)}6\right\rfloor,\qquad
Q_s(n)=M(n+s)-\binom{s+1}{2}.
\]
Nuestra construcción alcanza la cota superior eventual \(Q_s(n)\) con piezas de orden a lo sumo cuatro y recupera la familia extremal irrestricta de Okechukwu [15, Teorema 1.1]. Para grafos cordales da una prueba formal de \(c_4(G)\le M(n)+b\) a todo orden y, por tanto, de la cota pedida en el problema 81 de Erdős. La cota aditiva a todo orden para particiones en cliques sin restricción también se obtiene en [5] y [15, Corolario 1.2]. No se reclama prioridad del valor extremal.

Para defecto enraizado sublineal, obtenemos una aproximación de orden cuatro y estabilidad a lo largo de sucesiones arbitrarias de órdenes que tienden a infinito, de nuevo con una misma raíz que controla todas las particiones casi óptimas. La prueba combina el redondeo mixto de la infraestructura de los Papers I–III, las cuentas conservadas de los constructores y argumentos de localización y remoción con atribución explícita. Los enunciados están formalizados en Lean 4 usando sólo sus axiomas fundacionales estándar. Los umbrales son explícitos, pero no prácticos; no se afirma la optimalidad de las constantes de estabilidad ni \(b=0\) para todos los grafos cordales.

**Palabras clave:** grafo cordal; partición en cliques; empaquetamiento mixto; redondeo fraccional; grafo completo-split; formalización matemática.

## 1. Introducción

Una partición en cliques de un grafo \(G\) es una familia de cliques cuyos conjuntos de aristas son disjuntos y cuya unión es \(E(G)\). Escribimos \(\operatorname{cp}(G)\) para el menor número de piezas. Los vértices pueden pertenecer a varias piezas; lo que no puede repetirse es una arista. Para \(r\ge2\), denotamos por \(c_r(G)\) el mínimo cuando todas las piezas tienen orden a lo sumo \(r\).

El problema de Erdős, Ordman y Zalcstein [1,8] pide una cota de la forma \(n^2/6+O(n)\) para grafos cordales. Los ejemplos completo-split explican el coeficiente cuadrático. Sin embargo, una cota fraccional de ese orden no produce inmediatamente una partición con error lineal: el redondeo general permite una pérdida subcuadrática, que puede ser mucho mayor que \(n\).

Los tres papers anteriores de la serie separan aspectos de esta dificultad. Paper I [2] estudia perfiles de vecindario sobre una presentación split y reduce el problema residual a un politopo fijo. Paper II [3] determina el máximo exacto del déficit fraccional triangular sobre todos los cordales mediante copias de vértices. Paper III [4] construye particiones con error lineal para grafos split, distinguiendo los regímenes en que basta la holgura fraccional de aquellos que requieren una construcción más precisa. Su desarrollo formal aporta además la infraestructura de nibble y redondeo que se reutiliza en la Sección 3 y en el Apéndice B.

Este trabajo forma parte de la serie: sus entradas se enuncian donde se aplican.

El resultado estructural principal conserva información que una cota del número de piezas por sí sola descarta. En el caso cordal, el Teorema 6.1 da la cota de ediciones \(16\delta\); la misma raíz controla \(\tau+48\delta\) piezas no canónicas y a lo sumo \(10\tau+480\delta\) aristas en ellas. La Sección 6.6 extiende la conclusión con una misma raíz a cada defecto fijo, con constantes y umbrales explícitos, y distingue aproximar por una plantilla de defecto de aproximar por una de tamaño óptimo. La Sección 6.7 trata el defecto sublineal uniformemente, sin sustituir un parámetro creciente en un teorema de defecto fijo. Todos estos enunciados están vinculados a pruebas verificadas por el kernel. El umbral explícito de redondeo mixto también proporciona la constante aditiva para todo orden de §6.3.

El preprint público [5] también establece el máximo eventual para grafos cordales, del que se deduce una cota aditiva para todos los órdenes. Okechukwu [15, Teorema 1.1] demuestra el máximo eventual para cada defecto simplicial enraizado fijo, junto con una cota aditiva para todos los órdenes para particiones irrestrictas y una clasificación de la igualdad; su caso cordal es [15, Corolario 1.2]. No se reclama prioridad de estos enunciados. El Teorema C demuestra la cota superior con piezas de orden a lo sumo cuatro, y el Teorema C′ recupera la clasificación de la igualdad. Junto con el Corolario 6.3, da una forma cuantitativa de la estabilidad cualitativa por ediciones de [15, Corolario 5.5]. El Teorema 6.5 recupera la conclusión estructural de [15, Teorema 1.3] y añade control simultáneo de las particiones casi óptimas.

Las cadenas formales de los resultados cordales y de los Teoremas C y C′ no invocan los resultados de [5,15] como entradas. Esto no afirma independencia de todos los métodos del paper ampliado: la Proposición 6.4 y, en consecuencia, la aproximación del Teorema 6.5 siguen el argumento de estrella con signos de [15, Lema 3.1], con atribución e implementación completa. El paso de edición hacia un cordal sigue a de Joannis de Verclos [22]. La Sección 8 compara los enunciados y mecanismos.

Cipollini [21] anunció la cota parcial \(n^2/6+o(n^2)\) para grafos cordales. Ese anuncio identifica la dificultad restante entre el error subcuadrático y el lineal; es un antecedente, no una entrada de nuestra prueba.

La formulación de [8] pregunta: «Can the edges of \(G\) be partitioned into \(n^2/6+O(n)\) many cliques?», para \(G\) cordal. Erdős, Ordman y Zalcstein [1] habían probado una cota \((1/4-\epsilon)n^2\), con una constante positiva pequeña \(\epsilon\). El Teorema A da la forma solicitada para todos los órdenes.

En esta investigación extendemos la distinción entre margen y construcción al caso cordal, con un modelo mixto de triángulos y \(K_4\). El segundo tipo de pieza tiene seis aristas y sustituye seis piezas individuales por una. Su ganancia es, por tanto, cinco; la de un triángulo es dos. Esas ganancias deben mantenerse durante el redondeo. Preservar sólo el número de copias no preserva el coste de la partición.

### Teorema A. Cota para todos los órdenes

Existe una constante absoluta \(b\in\mathbb N\) tal que, para todo \(n\ge0\) y todo grafo cordal \(G\) de orden \(n\),
\[
\operatorname{cp}(G)\le c_4(G)\le M(n)+b
\le\frac{n^2}{6}+\frac n6+b.
\tag{A}
\]
En consecuencia, existe \(C\ge0\) tal que \(c_4(G)\le n^2/6+Cn\) para todos esos grafos. Esto da la cota pedida en el problema 81 de Erdős [1,8] para todo orden, sin excepciones. La cota para particiones en cliques sin restricción también se obtiene en [5] y [15, Corolario 1.2], como se discute en §8.1. La constante aditiva \(b\) no se afirma óptima.

### Teorema B. Cota aguda y máximo eventual

Existe un entero \(N\) tal que todo grafo cordal \(G\) de orden \(n\ge N\) admite una partición en cliques de orden a lo sumo cuatro con a lo sumo \(M(n)\) piezas. En particular,
\[
\operatorname{cp}(G)\le c_4(G)\le M(n).
\tag{1.1}
\]
Para los mismos órdenes, aumentando \(N\) si es necesario,
\[
\max_{\substack{|V(G)|=n\\G\text{ cordal}}}\operatorname{cp}(G)=M(n).
\tag{1.2}
\]

La segunda afirmación se obtiene de la cota superior y de un testigo completo-split, cuya optimalidad se demuestra frente a todas las particiones en cliques, no sólo frente a las de orden acotado. Este argumento por sí solo no clasifica todos los grafos extremales. El Teorema B es más preciso que la cota pedida en el problema; el Teorema A expresa su consecuencia válida para todo orden.

El ejemplo que fija la escala es concreto: para \(n\ge6\), tomemos \(k=\lceil n/3\rceil\), \(h=n-k\) y \(S=K_k\vee I_h\). Eliminar primero los anfitriones independientes y después el núcleo da un orden de eliminación perfecto, luego \(S\) es cordal. Una base del núcleo por triángulo permite construir una partición de coste \(kh-\binom k2=M(n)\); el argumento de pesos de §6.1 muestra que ninguna partición, ni siquiera con cliques mayores, cuesta menos.

La construcción da más que el valor extremal. El Teorema 6.1 acota las ediciones necesarias para llegar a un grafo completo-split, mientras que el Corolario 6.1a utiliza la misma raíz, elegida independientemente de la partición, para controlar las piezas de toda partición casi óptima. Al anular el déficit se identifican además los grafos extremales eventuales.

### Teorema C. Defecto simplicial enraizado fijo

Siguiendo a Okechukwu [15, §1], decimos que \(G\) tiene **defecto simplicial enraizado a lo sumo \(s\)** si cumple la siguiente condición. Dados un conjunto inducido \(U\subseteq V(G)\) y una clique prescrita \(R\subsetneq U\), existe \(v\in U\setminus R\) cuyo vecindario en \(U\) contiene una clique que omite a lo sumo \(s\) de sus vecinos. Se permite \(R=\varnothing\). La cuantificación sobre todas las raíces prescritas es parte de la definición, no una propiedad que se deduzca de un único orden de eliminación. Conservamos también la notación \(Q_s\) de [15, (1.1)].

Para cada entero fijo \(s\ge0\), existe \(N_s\) tal que, si \(G\) pertenece a esta clase y tiene orden \(n\ge N_s\), entonces
\[
\operatorname{cp}(G)\le c_4(G)\le Q_s(n),
\qquad
Q_s(n):=M(n+s)-\binom{s+1}{2}.
\tag{C}
\]
Además, para cada orden suficientemente grande existe un grafo de la clase con \(\operatorname{cp}(G)=Q_s(n)\). Por tanto, el máximo eventual coincide con \(Q_s(n)\), también cuando se permiten cliques de cualquier orden.

Éste es un refuerzo con piezas de orden a lo sumo cuatro de la cota superior eventual de [15, Teorema 1.1]. La Proposición D.2 muestra que cuatro no puede sustituirse por tres uniformemente sobre las clases del Teorema C: la obstrucción ya aparece para \(s=0\). No afirma minimalidad por separado para cada defecto positivo.

El máximo irrestricto y la familia de igualdad son los de [15, Teorema 1.1]; no se reclama prioridad de ellos. Todo grafo cordal pertenece a la clase \(s=0\), y \(Q_0=M\). El Apéndice E demuestra el Teorema C mediante la cadena explícita de localización. El Corolario 6.6 da una cota de torre para su umbral, uniforme en el defecto. El umbral de estabilidad que sigue se especifica por separado; no debe asignarse el mismo umbral a la cota exacta y a la de estabilidad sin una comparación adicional.

### Teorema C′. Estabilidad con una misma raíz para defecto fijo

Para cada \(s\ge0\) fijo, existen \(N_s^{\rm stab}\), \(\gamma_s>0\) y \(A_s=2\cdot10^{41}(s+1)^8\) explícitos con la siguiente propiedad. Supongamos \(n\ge N_s^{\rm stab}\), \(\operatorname{rsd}(G)\le s\) y \(c_4(G)\ge Q_s(n)-\delta\), donde \(0\le\delta\le\gamma_s n^2\). Entonces \(V(G)\) admite una partición \(C\sqcup D\sqcup H\), con \(C\) una clique de \(G\), \(|D|=s\) y \(2\le |C|\le |H|\), tal que la plantilla \(T=(K_C\sqcup I_D)\vee I_H\) satisface
\[
d_E(G,T)\le A_s\delta,\qquad
0\le Q_s(n)-\left(k(n-k)-\binom{k-s}{2}\right)\le(1+4A_s)\delta,
\quad k=|C|+s.
\]
Para esta misma raíz, toda partición irrestricta en cliques con a lo sumo \(Q_s(n)+\tau\) piezas tiene a lo sumo \(\tau+(1+7A_s)\delta\) piezas no canónicas, que contienen a lo sumo \(10\tau+10(1+7A_s)\delta\) aristas en total. Aquí las piezas canónicas son las aristas entre \(C\cup D\) y \(H\), y los triángulos con dos vértices en \(C\) y uno en \(H\).

La Sección 6.6 da los parámetros y la prueba. Con déficit cero se recupera la clasificación de la igualdad; con déficit positivo, el núcleo no tiene por qué tener tamaño óptimo. El Corolario 6.3 cuantifica el coste adicional de exigir tamaño óptimo. La Proposición 6.3a proporciona ejemplos a escala de raíz cuadrada, incluidos grafos de déficit exactamente uno cuya distancia a toda plantilla de tamaño óptimo crece con el orden. Estas constantes de defecto fijo no se sustituyen en un límite con \(s\) creciente: §6.7 trata ese límite por separado.

### 1.1. La condición común: presupuesto de pérdida

Sea \(W^*(G)\) la ganancia óptima fraccional mixta de triángulos y \(K_4\), con ganancias dos y cinco. Escribamos
\[
F_4(G)=e(G)-W^*(G),\qquad \Delta(G)=M(n)-F_4(G).
\]
Para un empaquetamiento físico \(\mathcal P\), de ganancia \(g(\mathcal P)\), completar las aristas no cubiertas como piezas individuales cuesta exactamente \(e(G)-g(\mathcal P)\). Por tanto,
\[
\boxed{
e(G)-g(\mathcal P)\le M(n)
\quad\Longleftrightarrow\quad
W^*(G)-g(\mathcal P)\le\Delta(G).
}
\tag{1.3}
\]
La desigualdad de la derecha tiene una lectura concreta. La cantidad \(W^*(G)-g(\mathcal P)\) mide la ganancia que se pierde al pasar del óptimo fraccional al empaquetamiento construido; \(\Delta(G)\) mide el margen que deja ese óptimo respecto de \(M(n)\). Si la pérdida no supera el margen, la partición completada tiene a lo sumo \(M(n)\) piezas. Llamaremos a esta comparación **presupuesto de pérdida**. La identidad no indica cómo elegir \(\mathcal P\): permite comprobar cualquier construcción de copias disjuntas por aristas.

La cuenta admite una forma independiente del modelo mixto. Sea \(Q\) cualquier partición en cliques, con piezas de orden al menos dos, y definamos su ganancia total por
\[
g(Q)=\sum_{K\in Q}\left(\binom{|K|}{2}-1\right).
\]
La cobertura exacta y la disyunción de las aristas dan, para cualquier objetivo \(T\),
\[
g(Q)+|Q|=e(G),\qquad
|Q|\le T\quad\Longleftrightarrow\quad e(G)\le g(Q)+T.
\tag{1.3a}
\]
No se ha usado una cota sobre el orden de las piezas. En particular, las piezas \(K_2\) tienen ganancia cero y pueden conservarse en la suma o añadirse al completar un empaquetamiento. Ésta es la identidad formalizada en `LossBudget.budget_iff`; para piezas grandes se usa la ganancia ordinaria, no la función capada del modelo mixto.

Para comparar familias, fijemos un conjunto \(S\subseteq\{3,\ldots,n\}\) de órdenes permitidos. Denotemos por \(W_S^*(G)\) la máxima ganancia fraccional con esas piezas, por \(F_S(G)=e(G)-W_S^*(G)\) el coste fraccional y por \(\Delta_S(G)=M(n)-F_S(G)\) su margen. Las capacidades siguen siendo una por arista. Extender un empaquetamiento por cero muestra que, si \(S\subseteq S'\), entonces \(W_S^*\le W_{S'}^*\) y \(\Delta_S\le\Delta_{S'}\). Para \(4\le L\le n\), resulta
\[
\Delta_{\{3,4\}}(G)\le\Delta_{\{3,\ldots,L\}}(G)
\le\Delta_{\mathrm{cp}}(G),
\tag{1.3b}
\]
donde el último término permite todos los órdenes hasta \(n\). Con la misma convención se obtiene \(c_4(G)\ge c_L(G)\ge\operatorname{cp}(G)\). Las desigualdades de margen no tienen por qué ser estrictas. Además, para una construcción fija, ampliar \(S\) aumenta tanto el óptimo con el que se mide la pérdida como el margen: la ventaja consiste en disponer de más construcciones admisibles, no en mejorar automáticamente su saldo.

Así, (1.3) es el caso mixto de una identidad de cuentas general. La dificultad sigue siendo producir una construcción que la cumpla para cada cordal. El resultado estructural siguiente proporciona esa cobertura en nuestra familia de piezas.

En esta investigación demostramos que el redondeo uniforme RC01 produce una pérdida menor que el margen en el régimen lejano. Para el régimen crítico, el descenso localiza una raíz y la construcción H1/RD09 produce \(\mathcal P\) directamente en \(G\), sin escoger un índice de primera entrada. Sus cuentas físicas, desarrolladas en la Sección 5, demuestran
\[
e(G)-g(\mathcal P)
\le B_n(p)-\frac m{20}-\frac A2
\le M(n),
\tag{1.4}
\]
y (1.3) da el presupuesto requerido.

Fijamos tres términos. El **margen** es \(\Delta(G)\); la **pérdida** es \(W^*(G)-g(\mathcal P)\). La **holgura del selector** se refiere, en cambio, a la capacidad que no está ocupada en un empaquetamiento fraccional auxiliar. Esta última no exige una cota inferior para las cargas y no debe confundirse con el margen del grafo.

### 1.2. Dicotomía estructural y mecanismos de resolución

**Dicotomía estructural.** Para \(\eta_0=10^{-16}\) y todo cordal suficientemente grande,
\[
\boxed{
F_4(G)<\frac{n^2}{6}-\eta_0n^2
\quad\text{o}\quad
\exists\,\text{testigo estructural cercano de }G.
}
\tag{1.5}
\]
El testigo incluye un comparador completo-split, una raíz que es clique de \(G\) y un empaquetamiento del grafo original con sus cuentas físicas. Las alternativas son exhaustivas; no se afirma que la existencia del testigo sea incompatible con tener margen cuadrático. No es una condición meramente métrica: conserva los recursos que permiten terminar la partición. El Apéndice A identifica la declaración formal de esta dicotomía.

En la primera rama, el redondeo mixto produce una pérdida menor que el margen disponible en (1.3). En la segunda, las cuentas del constructor verifican directamente el objetivo. Para concluir bastan el empaquetamiento, su factibilidad y la desigualdad de cuentas. El testigo cercano conserva además la estructura que los produce.

La Figura 1 sigue únicamente nuestra demostración. Para conectar el esquema con el texto, llamaremos **rama L** al caso lejano: el Teorema 3.1 redondea y el Corolario 3.5 paga su pérdida. La **rama C** es el caso crítico: la Proposición 4.3 localiza el comparador, la Sección 5 construye en \(G\) y el Lema 5.3 paga las pérdidas. Ambas ramas terminan en el Teorema B; la Sección 6.3 extiende su conclusión a todos los órdenes y demuestra el Teorema A. Las letras L y C designan los dos casos de una misma prueba.

El testigo cercano se conserva porque su raíz y sus cuentas dan más que una cota superior. La **forma híbrida** registra `NearStructureWitness` —raíz, comparador y cuentas— y conduce a los resultados de estabilidad del grafo y de sus particiones de la Sección 6.5. El **puente de modelos** tiene otra función: conserva recursos y ganancias al cambiar la representación formal de las piezas, como se documenta en la Sección 7.2. Ninguno de los dos refinamientos constituye una tercera prueba del Teorema B.

![Mapa de la demostración. La rama L se desarrolla en el Teorema 3.1 y el Corolario 3.5; la rama C, en la Proposición 4.3 y el Lema 5.3. Las líneas continuas forman la prueba de los Teoremas A y B. Las discontinuas señalan refinamientos que no se necesitan para esas cotas: el puente de modelos de la Sección 7.2 y el testigo conservado de la Sección 5.4.](figures/fig2_prueba_y_variantes.png)

### 1.3. Organización y uso de la cordalidad

**Observación 1.1.** La rama de redondeo vale para grafos arbitrarios. La rama crítica usa la cordalidad en tres puntos diferentes: la existencia y conservación de los pasos de copia de §4.1; la extracción de una clique y la ausencia de cuadrados inducidos en §5.1; y el orden de eliminación perfecto que orienta las aristas exteriores en §5.3. El orden de eliminación también certifica que los ejemplos que alcanzan la cota son cordales. Ninguna de esas propiedades se deduce sólo de las desigualdades numéricas del presupuesto.

La Sección 2 fija el modelo. La Sección 3 enuncia el resultado de redondeo y explica su uso; el Apéndice C desarrolla su prueba técnica. Las Secciones 4 y 5 establecen la localización y la construcción crítica. La Sección 6 ensambla la prueba cordal y obtiene estabilidad, clasificación y valores exactos. Las Secciones 6.6 y 6.7 extienden después la estabilidad al defecto enraizado fijo y sublineal; el Apéndice F registra sus parámetros, interfaces de prueba y procedencia adicional. La Sección 7 resume el alcance formal; el Apéndice A da las declaraciones y su correspondencia. La Sección 8 compara los mecanismos con [5,15]. El Apéndice B reúne herramientas complementarias. El Apéndice D también registra las identidades del comparador, y el Apéndice G trata la brecha triangular con clique acotada y la limitación separada del contrato de limpieza.

En la numeración actual de la serie, el motor general de transferencia se reserva para Paper V. Las menciones a ese motor como «Paper IV» en versiones anteriores de [2–4] corresponden al plan antiguo, no a una dependencia adicional del presente resultado.

## 2. Ganancia mixta, dualidad y particiones

Todos los grafos son finitos, simples y no dirigidos. Una clique se identifica con su conjunto de vértices; sus aristas son todas las parejas de vértices distintos de ese conjunto. Un grafo es cordal si no tiene un ciclo inducido de longitud al menos cuatro. Los subgrafos inducidos de un cordal son cordales.

### 2.1. Por qué se redondea una ganancia

Sea \(\mathcal K(G)\) la familia de las cliques de orden tres o cuatro. Un empaquetamiento mixto es una subfamilia \(\mathcal P\subseteq\mathcal K(G)\) de copias disjuntas por aristas. Definimos
\[
g(K)=\binom{|K|}{2}-1,\qquad
g(\mathcal P)=\sum_{K\in\mathcal P}g(K).
\]

| Pieza | Aristas cubiertas | Piezas que sustituye | Ganancia |
|:--|--:|--:|--:|
| \(K_2\) | 1 | 1 | 0 |
| \(K_3\) | 3 | 3 | 2 |
| \(K_4\) | 6 | 6 | 5 |

**Tabla 1.** El coste se mide respecto de cubrir cada arista por separado.

### Lema 2.1

Sea \(Q\) la partición obtenida al añadir a \(\mathcal P\) cada arista no cubierta como una pieza \(K_2\). Su número de piezas es exactamente
\[
|Q|=e(G)-g(\mathcal P).
\tag{2.1}
\]
**Demostración.** Las piezas de \(\mathcal P\) cubren \(\sum_K\binom{|K|}{2}\) aristas, porque no se solapan. Quedan \(e(G)-\sum_K\binom{|K|}{2}\) aristas individuales. Al sumar las \(|\mathcal P|\) piezas iniciales se obtiene (2.1). La cobertura es exacta por construcción.

### 2.2. El óptimo fraccional y su certificado

Un empaquetamiento fraccional asigna un peso \(x_K\ge0\) a cada copia real \(K\), con
\[
\sum_{K:e\in E(K)}x_K\le1\qquad(e\in E(G)).
\tag{2.2}
\]
Su valor es \(w(x)=\sum_K g(K)x_K\), y \(W^*(G)\) es el máximo de esos valores. El dual asigna precios \(y_e\ge0\) a las aristas. Para cada triángulo \(T\) y cada \(K_4\), denotado por \(Q\), exige respectivamente
\[
\sum_{e\in E(T)}y_e\ge2,\qquad
\sum_{e\in E(Q)}y_e\ge5.
\tag{2.3}
\]
La factibilidad primal contiene al vector cero. Cada coordenada primal está acotada por uno, puesto que toda copia contiene alguna arista. La dualidad finita proporciona óptimos primal y dual de igual valor. El modelo formal utiliza datos racionales y construye ambos óptimos: el valor \(w\) no entra como una suposición sin testigo. Paper I [2, Apéndice B] aporta el antecedente de dualidad empaquetamiento–cobertura; el desarrollo racional usado aquí prueba su versión mediante eliminación de Fourier–Motzkin.

De (2.2), sumando capacidades, resulta también
\[
w(x)\le\frac56\sum_K |E(K)|x_K\le\frac56e(G).
\tag{2.4}
\]
Esta estimación controla el coste de reducir multiplicativamente un empaquetamiento. No es por sí sola la cota extremal cordal.

### 2.3. Relación con los funcionales anteriores

La extensión por cero de un empaquetamiento triangular da
\[
W^*(G)\ge2\nu_3^*(G),\qquad
F_4(G)\le e(G)-2\nu_3^*(G).
\tag{2.5}
\]
Paper II [3, Teorema 1.1] acota la segunda cantidad por
\(\lfloor(2n+1)^2/24\rfloor\). Para \(n\) entero este piso coincide con \(M(n)\): el producto \(n(n+1)\) es congruente con 0 o 2 módulo 6 y sumar \(1/24\) no cruza un entero. Esto explica el objetivo de la serie. El paso desde ese valor fraccional a una partición sigue requiriendo las dos ramas posteriores.

### 2.4. Notación de las dos ramas

| Símbolo | Significado |
|:--|:--|
| \(M(n)\), \(B_n(p)\) | Objetivo entero y perfil completo-split |
| \(W^*(G)\), \(W(G)\) | Ganancias óptimas mixta fraccional y entera |
| \(g(\mathcal P)\) | Ganancia del empaquetamiento físico elegido |
| \(F_4=e-W^*\), \(\Delta=M-F_4\) | Coste fraccional y margen hasta el objetivo |
| \(W_S^*,F_S,\Delta_S\) | Las mismas cantidades para una familia de órdenes \(S\), sólo en §§1.1 y 8 |
| \(C,P,R\) | Núcleo del comparador, clique extraída y raíz regularizada |
| \(a,p,q\) | \(|P|,|R|,n-|R|\) |
| \(m,A\) | Aristas exteriores y enlaces ausentes respecto de \(R\) |
| \(f,\ell\) | Triángulos de la primera fase y bases fallidas de la segunda |
| \(d(G)\) | Distancia de edición normalizada a la familia completo-split |

Los símbolos auxiliares del selector del Apéndice C se definen allí. En particular, \(\ell\) en §5 es un conteo de fallos y no una ganancia.

## 3. Redondeo mixto y régimen con margen

Ésta es la rama L de la Figura 1. Su entrada es un empaquetamiento fraccional; su salida es uno físico con pérdida subcuadrática uniforme. El Corolario 3.5 explicará cuándo esa pérdida cabe dentro del margen disponible.

### Teorema 3.1

Para cada racional \(\xi>0\), existe \(N_\xi\) tal que, para todo grafo \(G\) de orden \(n\ge N_\xi\) y todo empaquetamiento fraccional mixto racional \(x\), existe un empaquetamiento mixto \(\mathcal P\) con
\[
w(x)-g(\mathcal P)\le\xi n^2.
\tag{3.1}
\]
No se exige cordalidad. El umbral se elige después de \(\xi\), pero antes de \(G\), \(n\) y \(x\).

Su alcance es una transferencia uniforme de la ganancia ponderada. Los teoremas de Haxell–Rödl y Yuster [6,7] proporcionan el contexto de transferencia fraccional a integral. Precisamos a continuación la entrada de Paper III y el adaptador de dos cuotas que conserva los pesos dos y cinco.

**Estructura de la demostración.** El lema de rango acotado de Paper III, reproducido como Lema 3.2 en el Apéndice C, redondea una familia con cargas a lo sumo uno y codegrado suficientemente pequeño. No distingue por sí solo las ganancias dos y cinco. El Lema 3.3 añade marcas y obtiene dos cuotas para un mismo emparejamiento; el Lema 3.4 agrupa parejas de triángulos y marca las copias de \(K_4\), de modo que la ganancia se recupera como cuatro veces la cuota total más la marcada.

Para aplicar ese selector a un grafo arbitrario, una partición regular y la limpieza de perfiles producen un sistema con cargas y codegrados controlados. La masa que se retira se carga una sola vez a sus recursos. Primero se fija \(\xi\), después los parámetros del selector y de regularidad, y sólo al final el umbral \(N_\xi\), independiente de la instancia. El caso de masa triangular pequeña se trata aparte. El Apéndice C conserva las estimaciones completas y la jerarquía de parámetros; su numeración 3.2–3.14 corresponde a la prueba de este teorema.

Por tanto, el Teorema 3.1 no se cita como una caja negra de Paper III. La entrada de ese paper es el nibble; la selección de dos cuotas, su realización mixta y el ensamblaje uniforme son los pasos de Paper IV. El contrato cerrado de (3.1) es todo lo que se usa a continuación.

### Corolario 3.5

Fijado un racional \(\eta>0\), todo grafo suficientemente grande con
\(F_4(G)<n^2/6-\eta n^2\) admite una partición de orden a lo sumo cuatro con a lo sumo \(M(n)\) piezas.

**Demostración.** Se aplica el Teorema 3.1 a un óptimo racional con \(\xi=\eta/2\). El Lema 2.1 da
\[
c_4(G)\le e(G)-g(\mathcal P)
\le F_4(G)+\frac\eta2n^2
<\frac{n^2}{6}-\frac\eta2n^2.
\]
Para \(n\ge6\), la desigualdad \(\lfloor t\rfloor\ge t-1\) da \(M(n)\ge n(n+1)/6-1\ge n^2/6\). La conclusión se sigue aumentando el umbral si hace falta.

El argumento no necesita una cota lineal universal para \(W^*(G)-W(G)\). Sólo requiere que la pérdida sea menor que el margen de la instancia.

## 4. Localización del régimen crítico

Comenzamos la rama C de la Figura 1. La Proposición 4.3 localiza un comparador completo-split. La Sección 5 convierte esa información en una partición del grafo original.

Fijamos, como en el desarrollo formal,
\[
\varepsilon_0=10^{-12},\qquad \eta_0=10^{-16}.
\tag{4.1}
\]
Durante el desarrollo de nuestro constructor cercano, su umbral se redujo de \(10^{32}\) a \(4\cdot10^{12}\). La comparación es entre versiones de ese constructor, no entre los umbrales globales de distintos papers. Corresponde a la localización y al constructor cercano, no a toda la prueba: el redondeo de la Sección 3 puede imponer un umbral mayor. No se deduce de esa mejora un umbral global de \(4\cdot10^{12}\).

### 4.1. Distancia a una familia fija

Para grafos sobre el mismo conjunto de vértices, sea
\(d_E(G,H)=|E(G)\mathbin{\triangle}E(H)|\).
Consideremos la familia de todos los completo-split etiquetados
\(S_C=K_C\vee I_{V\setminus C}\), y definamos
\[
d(G)=\frac1{n^2}\min_C d_E(G,S_C).
\]
El mínimo se alcanza, porque la familia es finita. La desigualdad triangular implica
\[
|d(G)-d(H)|\le\frac{d_E(G,H)}{n^2}.
\tag{4.2}
\]
Una copia de un vértice modifica a lo sumo \(n-1\) aristas. Por tanto, el cambio de \(d\) en un paso es a lo sumo \(1/n\). Esta cota no exige que la distancia disminuya a lo largo de todo el camino.

Paper II [3] explica el mecanismo de copia de clases simpliciales y la terminación en un completo-split para el funcional triangular. El desarrollo mixto requiere sus propios transportes de valor y termina en un grafo de la misma familia. La cordalidad se conserva en las copias admisibles; la cota mixta no se deduce simplemente de cambiar el nombre del funcional triangular.

**Lema 4.1 (camino mixto admisible).** Todo cordal \(G\) admite una sucesión finita \(G=G_0,\ldots,G_\ell\), sobre sus mismos vértices, tal que \(G_\ell\) es completo-split, cada \(G_i\) es cordal, cada paso copia un único vértice no adyacente y simplicial, y
\[
F_4(G_i)\le F_4(G_{i+1}),\qquad
d_E(G_i,G_{i+1})\le n-1.
\tag{4.3}
\]

**Demostración.** Para dos vértices simpliciales no adyacentes \(u,v\), consideremos las dos copias opuestas \(G_{u\to v}\) y \(G_{v\to u}\). El transporte mixto de empaquetamientos da
\[
W^*(G_{u\to v})+W^*(G_{v\to u})\le2W^*(G).
\tag{4.4}
\]
Es la versión mixta del transporte de Paper II. Se transportan los dos empaquetamientos al grafo original y se toma su promedio con peso \(1/2\). Un enlace puede recibir carga de las piezas transportadas desde ambos extremos; el control previo es carga a lo sumo dos, no uno. El promedio restablece la capacidad uno y divide por dos también la suma de ganancias. La suma de los números de aristas de las dos copias es \(2e(G)\). Al restar (4.4) se obtiene \(2F_4(G)\le F_4(G_{u\to v})+F_4(G_{v\to u})\); al menos una dirección no disminuye \(F_4\).

Falta justificar que siempre existe un paso fuera del terminal y que los pasos no se repiten. Llamemos gemelos a dos vértices con el mismo vecindario abierto. Si todo par simplicial no adyacente fuera gemelo, Dirac proporciona, en el caso no completo, un par \(x,y\) con vecindario común \(C\), que es clique. El exterior de \(C\) es independiente: de contener una componente con una arista, la forma enraizada de Dirac daría en ella un vértice simplicial del grafo, cuyo vecindario tendría que ser \(C\), contradiciendo que tiene un vecino en esa componente. Cada vértice exterior es entonces simplicial y, por la condición sobre pares, tiene exactamente vecindario \(C\). Por tanto, el grafo es \(K_C\vee I_{V\setminus C}\). El caso completo ya es terminal. La contraposición da las dos clases distintas que requiere el paso.

Contemos ahora pares ordenados de gemelos distintos. Sean \(t\le s\) los tamaños de las dos clases, y copiemos un vértice de la menor hacia la mayor. Entre los vértices no copiados no se destruye ninguna igualdad de vecindarios: todos sufren la misma sustitución de la coordenada del vértice copiado. Se pierden a lo sumo \(2(t-1)\) pares que lo contenían y se ganan \(2s\), así que el incremento es al menos \(2(s-t+1)>0\). Si esta dirección no disminuye \(F_4\), aumenta lexicográficamente la pareja formada por \(F_4\) y ese conteo. Si disminuye \(F_4\), (4.4) obliga a que la dirección inversa lo aumente estrictamente; también aumenta la pareja. Hay sólo finitos grafos etiquetados sobre \(V\), de modo que el proceso termina.

Por último, al borrar el vértice que se va a copiar queda un inducido cordal. Reincorporarlo con el vecindario clique de la fuente añade un simplicial; cualquier ciclo que lo atraviese y tenga longitud al menos cuatro tiene la cuerda entre sus dos vecinos. Se conserva, pues, la cordalidad. Sólo cambian aristas incidentes al vértice copiado, a lo sumo \(n-1\). Esto prueba (4.3).

**Lema 4.2 (cuenta dentro de la ventana).** Si \(X\) es cordal, \(n\ge4\cdot10^{12}\), \(F_4(X)\ge n^2/6-\eta_0n^2\) y \(d(X)<\varepsilon_0\), entonces
\[
d(X)\le16D/n^2,\qquad D=\eta_0n^2+n/6+1/24.
\tag{4.5}
\]

**Demostración.** Aplique la construcción local del Teorema 5.0, cuya prueba no usa la Proposición 4.3. Su cuenta reforzada (5.15a) entrega una raíz clique \(R\) y una partición \(Q\) con
\[
F_4(X)\le |Q|\le B_n(|R|)-\frac{117}{1825}m-\frac{12687}{20000}A.
\]
La primera desigualdad se debe a que el óptimo fraccional domina la ganancia del empaquetamiento físico. Por (5.16), \(B_n(|R|)\le(2n+1)^2/24\). Al restar la cota inferior supuesta para \(F_4(X)\), resulta
\[
\frac{117}{1825}m+\frac{12687}{20000}A\le D.
\]
Como \(16(117/1825)>1\) y \(16(12687/20000)>10\), deducimos \(m+10A\le16D\). Puesto que \(R\) es clique, \(d_E(X,S_R)=m+A\le16D\), que prueba (4.5). La cuenta reforzada se obtiene dentro de la construcción **local bajo cercanía**; la localización global se demuestra a continuación usando este lema. Así no hay dependencia circular.

### 4.2. Descenso desde el terminal

El argumento de localización puede verse como una inducción hacia atrás. Supongamos que \(G_0,\ldots,G_\ell\) es un camino admisible y que \(G_\ell\) es completo-split. Su distancia es cero. La estimación local de cuentas asegura que, dentro de la ventana \(d(X)<\varepsilon_0\), los grafos del camino con el valor fraccional requerido satisfacen
\[
d(X)\le\frac{16D}{n^2}<\varepsilon_0-\frac1n,\qquad
D=\eta_0n^2+\frac n6+\frac1{24}.
\tag{4.6}
\]
La calibración verifica esta última desigualdad para \(n\ge4\cdot10^{12}\).

En concreto, la desigualdad a verificar es
\[
\frac{16}{6n}+\frac1n+\frac{16}{24n^2}
<\varepsilon_0-16\eta_0.
\tag{4.6a}
\]
El cambio tiene dos causas concretas. La cuenta (5.15a) reduce el factor de presupuesto de 20 a 16; además, el descenso admite la barrera interior máxima \(\varepsilon_0-1/n\), sin reservar por separado las mitades \(\varepsilon_0/2\) y \(\varepsilon_0/4\). La desigualdad (4.6a) se cumple en \(n=4\cdot10^{12}\) y su lado izquierdo decrece con \(n\). La desigualdad de contracción con esta barrera falla para \(n\le3.6\cdot10^{12}\) con los valores actuales de \(\varepsilon_0,\eta_0\) y el factor 16. Ese límite se refiere a esta calibración, no a todos los métodos posibles.

Si \(d(G_{i+1})<\varepsilon_0-1/n\), entonces (4.2) da
\[
d(G_i)<\varepsilon_0.
\]
Ahora se puede aplicar (4.6) a \(G_i\), lo que lo devuelve al intervalo \(d(G_i)<\varepsilon_0-1/n\). El paso se repite hasta el grafo original. Se usan una ventana exterior y una contracción interior; no se necesita escoger el primer índice que cruza un umbral.

Esta inducción no elimina la estimación de estabilidad local (4.6). Explica exactamente qué entrada permite sustituir la elección de primera entrada por un descenso. La monotonía del valor fraccional preserva las hipótesis numéricas, aunque la distancia oscile.

La misma propagación puede demostrarse eliminando el último paso y razonando por la longitud del camino. Son dos pruebas del lema de localización, no dos soluciones globales adicionales. Ninguna necesita escoger un índice mínimo.

El umbral cercano refleja la interacción de dos escalas: retirar \(u\) vértices del comparador cuesta a lo sumo \(un\), mientras que la cuenta cordal controla \(u(u+1)/2\) por el número de ediciones. Una versión parametrizada toma un presupuesto \(a^2/B\), con \(B\ge1\), una cota \(a\ge\alpha n\), con \(0<\alpha\le1\), y \(\eta\ge0\). Las condiciones
\[
\varepsilon=\frac{\alpha^4}{8B^2},\qquad
1280B^2\eta\le\alpha^4,\qquad
n\ge\frac{1280B^2}{\alpha^4}
\]
son suficientes para la contracción numérica del descenso. No se afirma que esa escala sea necesaria ni óptima. La calibración específica utilizada aquí aprovecha estimaciones más ajustadas y da el umbral cercano indicado en la Proposición 4.3.

### Proposición 4.3

Sea \(G\) cordal, de orden \(n\ge4\cdot10^{12}\), y supongamos
\[
F_4(G)\ge n^2/6-\eta_0n^2.
\]
Existe un conjunto no vacío \(C\subseteq V(G)\) tal que
\[
d_E(G,S_C)\le\varepsilon_0n^2,
\tag{4.7}
\]
\[
(6|C|-2n-1)^2
\le24\left((\eta_0+6\varepsilon_0)n^2+\frac n6+\frac1{24}\right).
\tag{4.8}
\]

La localización anterior y la estimación del comparador producen (4.7)–(4.8). El conjunto \(C\) no se declara una clique de \(G\): lo es del comparador \(S_C\). La siguiente construcción obtiene una raíz que sí es clique del grafo original. Esta distinción evita trasladar una partición a través de un conjunto de ediciones que puede tener tamaño cuadrático.

## 5. Raíz regularizada y cuentas físicas

### Teorema 5.0. Constructor cercano bajo hipótesis locales

Sean \(\varepsilon_0=10^{-12}\), \(\eta_0=10^{-16}\) y \(G\) cordal de orden \(n\ge4\cdot10^{12}\). Supongamos
\[
d(G)<\varepsilon_0,\qquad F_4(G)\ge n^2/6-\eta_0n^2.
\]
Existen una clique \(R\) de \(G\), de tamaño \(p\) con \(|3p-n|\le n/50\), y una partición \(Q\) de orden a lo sumo cuatro tales que, si \(m=e(G-R)\) y \(A\) cuenta los enlaces ausentes entre \(R\) y su exterior,
\[
|Q|\le B_n(p)-\frac m{20}-\frac A2,\qquad
B_n(p)=p(n-p)-\binom p2.
\tag{5.0}
\]

**Demostración y organización.** El Lema 5.1 extrae una clique real; la Proposición 5.2 la regulariza. Las dos fases de §§5.2–5.3 construyen sobre los mismos recursos un empaquetamiento cuya completación satisface la Tabla 2. El Lema 5.3 da (5.0). Para la ventana de tamaño, el Lema 5.1 da \(a\ge33n/100\). Las cuentas de regularización proporcionan \(99a\le100p\) y \(48(2p-(n-p))\le a\), interpretando la resta como truncada antes de pasar a la desigualdad racional. Junto con \(p+(n-p)=n\), estas relaciones implican \(3267n\le10000p\) y \(3539p\le1188n\), de donde \(|3p-n|\le n/50\). En particular, se conserva la ventana anterior \(n/4\le p\le n/2\). Ninguno de estos pasos usa la localización global de la Proposición 4.3. Así puede aplicarse el presente teorema en el Lema 4.2, y sólo después obtenerse esa localización. Los apartados siguientes prueban cada paso del contrato.

### 5.1. Regularización sobre el grafo original

La construcción de esta sección es local: recibe un cordal \(G\) que ya satisface \(d(G)<\varepsilon_0\) y \(F_4(G)\ge n^2/6-\eta_0n^2\). Por eso puede utilizarse en el Lema 4.2 antes de concluir la localización global. Una vez demostrada la Proposición 4.3 se aplica al grafo original.

**Lema 5.1 (extracción de una clique real).** Bajo esas hipótesis y \(n\ge4\cdot10^{12}\), existe una clique \(P\) de \(G\), de tamaño \(a\), tal que
\[
\begin{gathered}
a\ge1024,\qquad |n-3a|\le a/64,\\
e(G-P)+\#\{\text{enlaces ausentes entre }P\text{ y }V\setminus P\}
\le a^2/65536.
\end{gathered}
\tag{5.1}
\]

**Demostración.** Sea \(C\) un núcleo del comparador más cercano y escribamos \(r=|C|\). La robustez fraccional por edición da \(|F_4(G)-F_4(S_C)|\le6d_E(G,S_C)\). Pongamos \(\delta_C=(\eta_0+6\varepsilon_0)n^2+n/6+1/24\); la hipótesis implica \(F_4(S_C)\ge(2n+1)^2/24-\delta_C\).

Expliquemos qué ocurre fuera del régimen split de muchos anfitriones. Escribamos \(a_0=\binom r2\), \(b_0=r(n-r)\). Los empaquetamientos fraccionales explícitos del comparador dan las cotas
\[
F_4(S_C)\le
\begin{cases}
b_0-a_0,&b_0\ge2a_0,\\
(2b_0-a_0)/3,&a_0\le b_0\le2a_0,\\
(a_0+b_0)/6,&b_0\le a_0.
\end{cases}
\tag{5.1a}
\]
Estas tres construcciones se aplican para \(r\ge4\) y exterior no vacío. La rama intermedia está acotada por \((4n+1)^2/120\), y la tercera por \(n(n-1)/12\). Para \(n\ge9\), ambas quedan estrictamente por debajo de \((2n+1)^2/24-n^2/40\). Como aquí \(\delta_C\le n^2/40\), ninguna satisface la hipótesis de cercanía fraccional. Si \(r<4\), basta la cota \(F_4(S_C)\le3n\); si el exterior es vacío, el empaquetamiento uniforme de \(K_4\) da \(F_4(S_C)\le n(n-1)/12\). Para \(n\ge100\), también se excluyen estos casos. Queda la primera rama: \(F_4(S_C)\le b_0-a_0=B_n(r)\). Completar el cuadrado da entonces \((6r-2n-1)^2\le24\delta_C\). Así se justifica la estimación sin extender indebidamente una identidad split a todos los tamaños de núcleo.

Tomemos ahora una clique máxima \(P\) del inducido cordal \(G[C]\), y pongamos \(u=r-a\). Un orden de eliminación perfecto acota sus aristas por \((a-1)r-\binom a2\). En consecuencia, faltan al menos
\[
\binom r2-\left((a-1)r-\binom a2\right)
=\binom{u+1}{2}
\]
pares dentro de \(C\). Todos ellos se cuentan entre las ediciones del comparador, por lo que \(u(u+1)/2\le\varepsilon_0n^2\). En particular, \(u\le3n/(2\cdot10^6)\). Al retirar esos \(u\) vértices del núcleo del comparador se modifican a lo sumo \(un\) pares adicionales. Por tanto, el defecto exterior y cruzado respecto de \(P\) suma a lo sumo \(\varepsilon_0n^2+un\).

Para ver la escala de la calibración, \(\delta_C\le(61/10)\varepsilon_0n^2\) sitúa \(r\) a distancia menor que \(3\cdot10^{-6}n\) de \(n/3\). Junto con la cota de \(u\), implica \(a\ge33n/100\) y \(|n-3a|\le a/64\). Además
\[
\varepsilon_0n^2+un\le(10^{-12}+1.5\cdot10^{-6})n^2
\le\frac{(33n/100)^2}{65536}\le\frac{a^2}{65536}.
\]
Son comparaciones racionales con las constantes fijadas en (4.1). El umbral de \(n\) da también \(a\ge1024\). Así se obtiene (5.1) sin tratar nunca \(C\) como clique de \(G\).

La raíz definitiva se define explícitamente. Se retiran de \(P\) los vértices cuya columna de enlaces ausentes tiene tamaño al menos \(|P|/4\), y se incorporan los vértices exteriores de grado exterior al menos \(7|P|/4\). Si esos conjuntos son \(X\) y \(Y\), respectivamente,
\[
R=(P\setminus X)\cup Y.
\tag{5.2}
\]
El presupuesto de defecto da
\[
16384|X|\le |P|,\qquad 57344|Y|\le |P|.
\tag{5.3}
\]
**Proposición 5.2 (regularización).** La raíz \(R\) de (5.2) es clique. Si \(p=|R|\), \(q=n-p\), \(m=e(G-R)\), \(A\) es su defecto cruzado y \(D\) el máximo defecto de una columna, satisface las cotas de paleta y anchura de (5.7), y
\[
\begin{gathered}
99a/100\le p\le101a/100,\quad q\ge p,\quad
44352q\ge87947a,\\
48(2p-q)_+\le a,\quad 3D\le a,\quad
400m<a^2,\quad2000(A+2m)\le11a^2.
\end{gathered}
\tag{5.4}
\]

**Demostración.** La suma de las columnas ausentes es parte del presupuesto (5.1), así que \((a/4)|X|\le a^2/65536\). La suma de los grados exteriores es el doble del número de aristas exteriores, y da \((7a/4)|Y|\le2a^2/65536\). Son las dos cotas de (5.3).

Toda clique exterior a \(P\) tiene a lo sumo \(a/128+1\) vértices: sus pares internos se cuentan en el mismo presupuesto. En un cordal, los vecinos comunes de dos vértices no adyacentes forman una clique, pues dos vecinos comunes no adyacentes completarían un cuadrado inducido. Si dos miembros de \(Y\) no fueran adyacentes, sus vecindarios exteriores tendrían intersección de tamaño al menos \(7a/2-129a/64=95a/64\), incompatible con la cota de clique exterior. Aquí se usó \(|V\setminus P|\le129a/64\), que se sigue de (5.1). Así, \(Y\) es clique. Si \(x\in P\) no es adyacente a un miembro de \(Y\), la misma propiedad acota los vecinos comunes exteriores por \(a/128+1\). El grado exterior del miembro de \(Y\) fuerza entonces al menos \(a/4\) ausencias en la columna de \(x\); por tanto \(x\in X\). Esto prueba que \(R\) es clique.

Para las cotas restantes se cuentan los recursos que cambian al retirar \(X\) e incorporar \(Y\). Si \(m_P,A_P\) son los defectos respecto de \(P\), se tiene \(m\le m_P+|X|n\) y \(A\le A_P+|Y|n\). Los grados y la anchura exteriores satisfacen
\[
64d_{\max}(G-R)\le113a+64|X|,\qquad
128\omega(G-R)\le a+128+128|X|.
\]
El coeficiente \(113/64\) procede de las columnas retiradas: un vértice de \(X\) omite al menos \(a/4\) de los a lo sumo \(129a/64\) vértices del exterior anterior y, por tanto, tiene allí a lo sumo \(113a/64\) vecinos. Un vértice de ese exterior que no pertenezca a \(Y\) tiene allí grado menor que \(7a/4\le113a/64\). Trasladar \(X\) añade a lo sumo \(|X|\) vecinos en ambos casos. Las columnas retenidas parten de menos de \(a/4\) ausencias; las incorporadas se controlan con el mismo argumento de vecinos comunes. Sustituir (5.3), \(a\ge1024\) y \(127a\le64|V\setminus P|\le129a\) en estas cuentas da (5.4) y (5.7). Son las cotas que se consumen abajo: el defecto no se vuelve a elegir después de construir el empaquetamiento.

El objetivo de (5.2) no es minimizar una energía abstracta. Se separan los dos defectos que impedirían asignar anfitriones: columnas con demasiadas ausencias y vértices exteriores con demasiado grado residual. El resultado conserva cotas explícitas de tamaño, anchura exterior y disponibilidad de enlaces.

### 5.2. De emparejamientos a triángulos

Un emparejamiento de bases \(uv\), junto con un vértice \(z\) adyacente a todos sus extremos, produce los triángulos \(zuv\) (Figura 2). Son disjuntos por aristas: dentro del emparejamiento ningún extremo se repite, de modo que tampoco se repite un enlace a \(z\).

![Dos bases disjuntas con un anfitrión común producen dos triángulos que comparten un vértice, pero ninguna arista. Esta es la unidad física utilizada en las asignaciones por clases de color.](figures/fig3_anfitrion.png)

Para varios anfitriones se exige, además, que sean distintos, que ningún anfitrión sea extremo de las bases y que las familias de bases sean disjuntas. Esas condiciones prueban la compatibilidad entre clases; no se suma la ganancia de construcciones cuya disjunción no haya sido verificada.

La primera fase aplica esta realización a aristas exteriores usando vértices de la raíz como anfitriones. Una coloración equilibrada y el orden de eliminación enraizado controlan cuántas bases pueden alojarse. La segunda fase factoriza las aristas de la raíz en matchings y les asigna candidatos exteriores. Las listas de candidatos excluyen tanto enlaces ausentes como recursos ya utilizados por la primera fase.

### 5.3. Las tres cuentas que pagan la construcción

Para comparar la construcción real con el modelo completo-split, fijemos primero el tamaño de la raíz. Pongamos \(p=|R|\) y \(q=n-p\). Si todas las aristas entre la raíz y su exterior estuvieran presentes y no hubiera aristas exteriores, el coste de referencia sería
\[
B_n(p)=p(n-p)-\binom p2.
\]
En efecto, cubrir individualmente las aristas del completo-split costaría \(p(n-p)+\binom p2\) piezas. Cada una de las \(\binom p2\) bases internas se incorpora a un triángulo con un anfitrión exterior; ese triángulo sustituye tres aristas individuales por una pieza y ahorra dos. El coste resultante es, por tanto, \(p(n-p)+\binom p2-2\binom p2=B_n(p)\). Con esta referencia fijada **antes** de construir, introducimos las desviaciones reales. Sean \(m\) el número de aristas exteriores a \(R\), \(A\) el número de enlaces ausentes entre \(R\) y su exterior, \(f\) el número de triángulos de la primera fase y \(\ell\) el número de bases fallidas de la segunda. Si \(Q\) es la completación física, los lemas de construcción producen las tres relaciones siguientes.

| Cuenta | Identidad o desigualdad | Función |
|:--|:--|:--|
| Conteo de piezas | \(|Q|+A+2f=B_n(p)+m+2\ell\) | Expresa el coste real |
| Primera fase | \(1600m\le2920f+219A\) | Paga las aristas exteriores |
| Segunda fase | \(200\ell\le35A+8f\) | Acota las bases fallidas |

**Tabla 2.** Todas las cantidades de pérdida proceden de familias finitas. El valor de referencia \(B_n(p)\) se fija antes de contar \(Q\).

La identidad del primer renglón se obtiene contando. Hay \(e(G)=\binom p2+pq+m-A\) aristas. La primera fase aporta \(f\) triángulos y la segunda \(\binom p2-\ell\). Como las familias son compatibles, el Lema 2.1 da
\[
|Q|=\binom p2+pq+m-A-2\left(f+\binom p2-\ell\right)
=B_n(p)+m-A-2f+2\ell.
\tag{5.4a}
\]
Reordenar esta igualdad da la primera cuenta. En particular, no se estima por separado el coste de dos construcciones que pudieran competir por las mismas aristas.

La compatibilidad tiene una verificación concreta. Si un triángulo de la primera fase usa una arista exterior \(uv\) y un anfitrión \(z\in R\), consume los enlaces \(zu,zv\). La segunda fase no puede asignar \(u\) ni \(v\) a una base que contenga \(z\). Ésta es la tercera condición de exclusión de `canonicalBad`; las otras dos exigen adyacencia a ambos extremos de la base. El lema `isSpokeCompatible_surviving_canonicalBad` demuestra que las asignaciones supervivientes no reutilizan esos enlaces. Finalmente, `RD09SpokeCompatibility.card_union_phases` da la suma exacta de los números de triángulos de las dos fases.

Demostremos las otras dos estimaciones. La primera cuenta cuántas aristas exteriores sobreviven a la asignación de anfitriones. La segunda cuenta cuántas bases internas pueden quedarse sin anfitrión después de esa elección. El orden importa: las listas de la segunda fase excluyen los enlaces que realmente utilizó la primera.

**Primera fase: selección de colores y pérdidas por incompatibilidad.** Escribamos \(H=G-R\), \(w=\omega(H)\) y \(c=\max\{p,d_{\max}(H)+1\}\), donde \(d_{\max}(H)\) es el grado máximo. Vizing proporciona una coloración propia con a lo sumo \(c\) colores. Entre las coloraciones sobre esa paleta, escogemos una que minimice la suma de cuadrados de los tamaños de sus clases. Si dos clases difirieran en al menos dos aristas, su unión contendría un camino alternante con una arista más del color mayor; intercambiar sus colores reduciría la suma de cuadrados. Por tanto, las clases difieren en tamaño a lo sumo uno, y cada una tiene a lo sumo \(t=\lceil m/c\rceil\) aristas.

Conservamos las \(p\) clases mayores. Si contienen \(m_0\) aristas en total, comparar su tamaño medio con el promedio de todas las clases da
\[
m_0\ge\frac pc\,m.
\tag{5.5}
\]
Tomamos un orden de eliminación perfecto que termina en \(R\) y orientamos cada arista exterior hacia su extremo posterior. Si \(u\to v\), los vecinos posteriores de \(u\) forman una clique, por lo que todo vecino de \(u\) en \(R\) también es vecino de \(v\). En consecuencia, los anfitriones inválidos para \(uv\) son exactamente los vértices de \(R\) no adyacentes a \(u\). Si \(a_u\) es su número, el vértice \(u\) contribuye a lo sumo \((w-1)a_u\) incidencias inválidas: tiene a lo sumo \(w-1\) vecinos posteriores exteriores. Sumando y usando \(\sum_{u\notin R}a_u=A\), obtenemos a lo sumo \((w-1)A\) incidencias inválidas.

Enumeramos las clases conservadas y la raíz cíclicamente. Entre los \(p\) desplazamientos, cada clase recibe cada anfitrión una vez. El promedio de aristas descartadas es, por tanto, a lo sumo \((w-1)A/p\). Algún desplazamiento conserva un número \(f\) de aristas que satisface
\[
f\ge m_0-\frac{w-1}{p}A
\ge\frac pc\,m-\frac{w-1}{p}A.
\tag{5.6}
\]
Cada arista conservada produce un triángulo. Dentro de una clase las bases forman un emparejamiento, y clases distintas tienen anfitriones distintos; de ahí la disjunción por aristas. Las cotas de paleta y anchura que entrega la raíz regularizada son
\[
40c\le73p,\qquad 40(w-1)\le3p.
\tag{5.7}
\]
Al sustituirlas en (5.6), resulta \(f\ge40m/73-3A/40\). Multiplicar por \(2920\) da precisamente \(1600m\le2920f+219A\), la primera estimación de la Tabla 2. El Apéndice A.2 identifica las declaraciones de selección y promedio.

**Segunda fase: uno o dos candidatos por factor.** Factorizamos \(K_p\) en matchings y, si hace falta, añadimos una clase vacía para trabajar con \(p\) factores. Puesto que \(q\ge p\), podemos dar un candidato a cada factor. Sea \(s=\max\{2p-q,0\}\). Elegimos \(s\) factores con un solo candidato y damos dos a cada factor restante. Los \(2p-s\) puestos disponibles se asignan inyectivamente a vértices exteriores: ningún candidato pertenece a dos factores.

Para \(x\in R\), sean \(a_x\) el número de enlaces ausentes y \(u_x\) el número de enlaces ya usados por la primera fase. Definamos \(d_x=a_x+u_x\). Tenemos
\[
\sum_xa_x=A,\quad \sum_xu_x=2f,\quad
a_x\le D,\quad u_x\le2t,\quad
S:=\sum_xd_x=A+2f,
\tag{5.8}
\]
donde \(D=\max_xa_x\). La última cota puntual procede de que el emparejamiento asignado a \(x\) tiene a lo sumo \(t\) bases. Para la base \(e=xy\), denotemos por \(b_e\) el número de candidatos inválidos: falta alguno de los enlaces \(xz,yz\), o ya fue usado. La unión de esas prohibiciones da \(b_e\le d_x+d_y\).

Las tres estimaciones de momentos se obtienen contando sobre las parejas no ordenadas de la raíz:
\[
\begin{aligned}
\sum_e b_e&\le(p-1)S,\\
\sum_e b_e^2&\le(p-2)\sum_xd_x^2+S^2,\\
\sum_xd_x^2&\le(D+4t)A+4tf.
\end{aligned}
\tag{5.9}
\]
La primera cuenta cada \(d_x\) en las \(p-1\) bases que contienen \(x\). Para la segunda se expande \(\sum_{x<y}(d_x+d_y)^2\): los cuadrados aparecen \(p-1\) veces, y los productos cruzados suman \(S^2-\sum_xd_x^2\). Para la tercera se usa, término a término,
\[
(a_x+u_x)^2\le Da_x+4ta_x+2tu_x,
\]
y se aplican las sumas de (5.8). Así, cada término de (5.9) procede de las incidencias reales ausentes u ocupadas.

Promediemos ahora sobre la elección uniforme de los \(s\) factores simples y sobre las inyecciones de candidatos. Una base con un candidato falla con probabilidad \(b_e/q\); con dos candidatos distintos falla con probabilidad \(b_e(b_e-1)/(q(q-1))\). Por ello su probabilidad total de fallo es
\[
\frac{s}{p}\frac{b_e}{q}
+\left(1-\frac{s}{p}\right)\frac{b_e(b_e-1)}{q(q-1)}.
\tag{5.10}
\]
Sumamos, usamos \((p-1)/p\le1\), \(b_e(b_e-1)\le b_e^2\) y (5.9). Alguna asignación tiene un número \(\ell\) de bases fallidas no mayor que el promedio, de modo que
\[
\ell\le\frac{s}{q}(A+2f)
+\frac{(p-2)((D+4t)A+4tf)+(A+2f)^2}{q(q-1)}.
\tag{5.11}
\]
Para cada base que no falla, escogemos uno de sus candidatos válidos. Las bases del mismo factor son disjuntas; las de factores distintos usan candidatos distintos. Además, la definición de candidato válido excluye todo enlace ya utilizado. Esto verifica simultáneamente la compatibilidad dentro de la segunda fase y con el empaquetamiento de la primera.

Falta evaluar (5.11) con las cotas que entrega la regularización. Denotemos por \(a=|P|\) el tamaño de la clique de referencia anterior a (5.2). El certificado cercano da
\[
\begin{gathered}
a\ge1024,\quad \frac qa\ge\frac{87947}{44352},\quad
\frac pa\le\frac{101}{100},\quad \frac Da\le\frac13,\\
\frac ta\le\frac1{256},\quad \frac sa\le\frac1{48},\quad
\frac{A+2f}{a^2}\le\frac{11}{2000}.
\end{gathered}
\tag{5.12}
\]
Estas cotas pertenecen al certificado de la raíz regularizada y a su primera fase. Por ejemplo, ese certificado da \(p\ge99a/100\), \(m<a^2/400\) y \(2000(A+2m)\le11a^2\). Como \(c\ge p\), el tamaño de cada clase satisface \(t\le m/p+1<a/396+1\le a/256\), donde la última comparación usa \(a\ge1024\). Además \(f\le m\), de modo que la cota de masa para \(A+2f\) se sigue de la de \(A+2m\). Se comprueba así que las cantidades de (5.12) son las de la construcción elegida, no parámetros ajustados después de contar los fallos.
La cota de \(s\) necesita las estimaciones finas de (5.3), no sólo los extremos redondeados de \(p/a\) y \(q/a\). Si \(q_P=n-a\), entonces \(p=a-|X|+|Y|\), \(q=q_P+|X|-|Y|\), y
\[
2p-q=2a-q_P-3|X|+3|Y|
\le a/64+3a/57344<a/48.
\tag{5.12a}
\]
Tomar la parte positiva prueba \(s/a\le1/48\). Por su parte, el denominador conserva el término \(q-1\):
\[
\frac{q(q-1)}{a^2}\ge
\left(\frac{87947}{44352}\right)^2
-\frac{87947}{44352\cdot1024}\ge\frac{393}{100}.
\tag{5.13}
\]
El lado intermedio es aproximadamente \(3.93008\), mientras que la cota usada es \(3.93\). La diferencia es pequeña pero positiva; se conserva la comparación racional exacta, sin redondearla hacia arriba ni cambiar \(R_0\) en las cuentas siguientes.
Para linealizar el numerador, usamos \((A+2f)^2\le(11/2000)a^2(A+2f)\) y \(p-2\le p\). Si escribimos \(Q_0=87947/44352\) y \(R_0=393/100\), los coeficientes de \(A\) y \(f\) quedan acotados, respectivamente, por
\[
\begin{aligned}
\frac{1}{48Q_0}
+\frac{(101/100)(1/3+1/64)+11/2000}{R_0}
&\le\frac{11}{100},\\
\frac{1}{24Q_0}
+\frac{(101/100)/64+11/1000}{R_0}
&\le\frac{29}{1000}.
\end{aligned}
\tag{5.14}
\]
Son comparaciones racionales directas. Obtenemos \(\ell\le11A/100+29f/1000\). Como \(A,f\ge0\), esta cota implica \(\ell\le7A/40+f/25\), que al multiplicar por \(200\) es la segunda estimación de la Tabla 2. Se han usado así las dos contribuciones, la de enlaces ausentes y la de enlaces ocupados, sobre una misma asignación física. El Apéndice A.2 identifica los lemas de momentos, promedio y calibración.

### Lema 5.3

Si se conserva la estimación fuerte de (5.14) para la misma partición \(Q\), se obtiene
\[
|Q|\le B_n(p)-\frac{117}{1825}m-\frac{12687}{20000}A
\le B_n(p)-\frac m{16}-\frac A2.
\tag{5.15a}
\]
En particular, las tres cuentas de la Tabla 2 también implican la forma anterior
\[
|Q|\le B_n(p)-\frac{19}{365}m-\frac{253}{500}A
\le B_n(p)-\frac m{20}-\frac A2.
\tag{5.15}
\]

**Demostración.** De la cuenta de segunda fase,
\(\ell\le7A/40+f/25\). Al sustituir en la identidad de piezas,
\[
|Q|\le B_n(p)+m-\frac{13}{20}A-\frac{48}{25}f.
\]
La primera fase da \(f\ge40m/73-3A/40\). Su coeficiente en la desigualdad anterior es negativo; por ello se utiliza esta cota inferior. Los coeficientes resultantes son
\[
1-\frac{48}{25}\frac{40}{73}=-\frac{19}{365},\qquad
-\frac{13}{20}+\frac{48}{25}\frac3{40}=-\frac{253}{500}.
\]
Como \(m,A\ge0\), \(19/365\ge1/20\) y \(253/500\ge1/2\), se obtiene la segunda desigualdad.

Para (5.15a), se vuelve a la cota anterior a esa relajación, \(\ell\le11A/100+29f/1000\), sin modificar la asignación física. La identidad de piezas da
\[
|Q|\le B_n(p)+m-\frac{39}{50}A-\frac{971}{500}f.
\]
Al usar de nuevo \(f\ge40m/73-3A/40\), los coeficientes se convierten en \(-117/1825\) y \(-12687/20000\). Finalmente \(117/1825>1/16\) y \(12687/20000>1/2\). Esta reserva no requiere elegir otra raíz ni otro packing.

Por otra parte,
\[
B_n(p)=\frac{(2n+1)^2}{24}-\frac{(6p-2n-1)^2}{24}.
\tag{5.16}
\]
La forma entera de la misma identidad es (6.3): \(6B_n(p)+(n-3p)(n-3p+1)=n(n+1)\). Como el producto de dos enteros consecutivos es no negativo, \(6B_n(p)\le n(n+1)\). Ahora sí, la integralidad de \(B_n(p)\) da \(B_n(p)\le\lfloor n(n+1)/6\rfloor=M(n)\). No se ha identificado el piso con la función racional: la envolvente de (5.16) excede \(n(n+1)/6\) en \(1/24\), y ese término no debe borrarse.

### 5.4. El testigo que conserva la prueba

La conclusión cercana entrega conjuntamente el comparador de (4.7)–(4.8), la raíz regularizada, un empaquetamiento en \(G\) y las cuentas de la Tabla 2. Por (5.15)–(5.16), su completación tiene coste a lo sumo \(M(n)\).

En particular, no se construye una partición barata en \(S_C\) para luego reparar todas sus diferencias con \(G\). Las ediciones sirven para localizar y calibrar la raíz. La partición se realiza directamente en \(G\), y las pérdidas se pagan mediante sus propias familias de aristas y triángulos.

**Corolario 5.4 (geometría cuantitativa de la rama crítica).** Para todo cordal \(G\) de orden suficientemente grande, o bien \(F_4(G)<n^2/6-\eta_0n^2\), o bien existen una clique \(R\) del grafo original y un núcleo comparador \(C\) tales que
\[
|3|R|-n|\le\frac n{50},\qquad
|3|C|-n|\le\frac n{10^4},\qquad
d_E(G,S_C)\le\varepsilon_0n^2,
\tag{5.17}
\]
y, en la segunda rama,
\[
\left|e(G)-\frac{5n^2}{18}\right|\le\frac{n^2}{10^4}.
\tag{5.18}
\]
En (5.17) basta tomar \(n\ge4\cdot10^{12}\) además del umbral de la dicotomía. La clique real procede de las tres razones de regularización utilizadas en el Teorema 5.0. La cota de \(C\) se obtiene de (4.8) y la calibración. Si \(k=|C|=n/3+t\), entonces \(|t|\le n/30000\) y
\[
e(S_C)=\binom k2+k(n-k)
=\frac{5n^2}{18}+\frac{2nt}{3}-\frac{t^2}{2}-\frac{k}{2}.
\]
La última desigualdad se sigue al comparar esta cuenta con \(e(G)\) mediante (4.7). La constante \(5/9\) describe la densidad *asintótica* relativa al grafo completo; no es una identidad de densidad para un orden finito. El corolario determina tamaños, no la unicidad de \(R\) o \(C\) como conjuntos.

## 6. Ensamblaje y valor extremo

### Demostración del Teorema B: cota superior

Sea \(N_{\mathrm{lej}}\) el umbral del Corolario 3.5 con \(\eta=\eta_0\), y tomemos
\(N\ge\max\{N_{\mathrm{lej}},4\cdot10^{12},6\}\).
Para un cordal \(G\) de orden \(n\ge N\), se construye un óptimo mixto certificado. Si \(F_4(G)<n^2/6-\eta_0n^2\), el Corolario 3.5 proporciona la partición. En caso contrario, las Secciones 4 y 5 producen el testigo cercano y la completación al objetivo. Los dos casos agotan los valores de \(F_4(G)\), y ambas salidas son particiones del mismo grafo original.

La elección del óptimo es interna al argumento. Tampoco queda pendiente elegir un parámetro de cercanía para cada grafo: \(\eta_0\), \(\varepsilon_0\) y todos los umbrales se fijan de antemano.

### 6.1. Optimalidad irrestricta en completo-split

Sea \(S=K_k\vee I_h\), con \(2\le k\le h\). Sus aristas se dividen en \(\binom k2\) aristas interiores y \(kh\) enlaces. El argumento de pesos de Paper III [4, Corolario 10.2a] asigna peso \(-1\) a las primeras y \(+1\) a los segundos.

Toda clique contiene a lo sumo un anfitrión. Si tiene uno y \(s\ge1\) vértices del núcleo, su peso es
\[
s-\binom s2\le1.
\]
Si está enteramente en el núcleo, su peso es negativo. Por tanto, cualquier partición \(\mathcal Q\), sin restricción en el orden de las cliques, satisface
\[
|\mathcal Q|\ge kh-\binom k2.
\tag{6.1}
\]

Para alcanzar la cota, se factorizan las aristas de \(K_k\) en \(k-1\) matchings perfectos si \(k\) es par y en \(k\) matchings si \(k\) es impar. En el segundo caso basta factorizar \(K_{k+1}\) y retirar el vértice añadido. Como \(h\ge k\), cada clase recibe un anfitrión distinto. Se obtiene un triángulo por arista del núcleo, sin compartir enlaces. Tras completar los enlaces restantes con aristas individuales, el número total de piezas es
\[
\binom k2+kh-2\binom k2=kh-\binom k2.
\]
La igualdad obtenida expresa el número de piezas de esa partición. Junto con (6.1), prueba
\[
\operatorname{cp}(S)=c_3(S)=c_4(S)=kh-\binom k2.
\tag{6.2}
\]
El enunciado público auditado se expresa como una partición de orden a lo sumo cuatro y una cota inferior irrestricta; la construcción descrita utiliza triángulos y aristas.

### 6.2. El máximo eventual

La elección del núcleo extremal se explica mediante una identidad. Para \(f(n,k)=k(n-k)-\binom k2\), con la resta interpretada en los enteros,
\[
6f(n,k)+(n-3k)(n-3k+1)=n(n+1).
\tag{6.3}
\]
El producto de dos enteros consecutivos es no negativo. Por eso \(f(n,k)\le M(n)\). Para alcanzar el piso, ese producto debe ser el resto de \(n(n+1)\) módulo seis, que vale cero o dos. Así, \(n-3k\) sólo puede pertenecer a \(\{-2,-1,0,1\}\). Al imponer su congruencia módulo tres se obtienen exactamente los tamaños
\[
\begin{cases}
k=r,& n=3r,\\
k=r\text{ o }r+1,& n=3r+1,\\
k=r+1,& n=3r+2.
\end{cases}
\tag{6.4}
\]
Dentro de la familia completo-split con \(2\le k\le n-k\), el tamaño óptimo es único salvo en la segunda fila, donde hay dos tamaños consecutivos. Ésta es la clasificación de núcleos de `SplitCompleteRigidity.optimal_cores`; no es, por sí sola, una clasificación de todos los cordales extremales.

Para \(n\ge6\), la elección \(k=\lceil n/3\rceil\) pertenece siempre a (6.4) y satisface \(2\le k\le h=n-k\). El grafo \(K_k\vee I_h\) es cordal: eliminamos primero los anfitriones, cuyos vecinos posteriores están en el núcleo completo, y después el núcleo. Es un orden de eliminación perfecto, formalizado en `PaperTheorems.splitGraph_isChordal`. Por (6.2), este cordal alcanza \(M(n)\). Junto con la cota superior se obtiene el máximo del Teorema B.

### 6.3. Todos los órdenes y optimalidad del término lineal

**Demostración del Teorema A.** Fijemos un umbral global \(N\) del Teorema B y pongamos \(b=N^2\). Si \(n\ge N\), ya existe una partición con a lo sumo \(M(n)\) piezas. Si \(n<N\), cubrimos cada arista por separado. El número de piezas es
\[
e(G)\le\binom n2\le N^2\le M(n)+b.
\]
También cubre \(n=0\). Finalmente, \(M(n)\le n^2/6+n/6\); para \(n\ge1\), la constante \(C=b+1/6\) da la forma \(n^2/6+Cn\), y para \(n=0\) la partición es vacía. Esto demuestra la respuesta al problema sin excepciones de orden.

El testigo \(b=N^2\) depende del umbral **global**, no sólo del cercano \(4\cdot10^{12}\). Ahora puede elegirse de manera explícita. Definamos la torre de doses por \(T(0)=1\) y \(T(j+1)=2^{T(j)}\), y pongamos
\[
h=4\cdot8^5\cdot2208^5\cdot4500^{105}\cdot(2\cdot10^{16})^{105}.
\]
La cuenta del Apéndice C.3 permite tomar
\[
N=T(h+7),\qquad b=N^2\le T(h+8).
\]
En efecto, la rama lejana con \(\eta_0=10^{-16}\) requiere a lo sumo \(T(h+7)\), y este número también supera el umbral cercano. Para \(n<N\), la partición por aristas individuales tiene a lo sumo \(n^2\le N^2\) piezas. Finalmente, \(N\ge4\) permite aplicar la desigualdad entera \(N^2\le2^N=T(h+8)\).

Esta cota es explícita, pero no es práctica ni se afirma óptima. No demuestra que \(b=0\), ni sustituye la torre por un umbral polinomial. La evaluación incluye las constantes del selector marcado: no queda un umbral de redondeo sin especificar dentro de la expresión. La identidad con el término continuo sigue siendo \(M(n)=n^2/6+n/6-\vartheta_n\), con \(0\le\vartheta_n<1\).

**Optimalidad del coeficiente cuadrático.** El \(1/6\) de \(n^2/6\) no puede reducirse, aunque se permitan cliques de cualquier orden. En efecto, si una cota \(\operatorname{cp}(G)\le c n^2+C n\) valiera para todos los cordales de orden suficientemente grande, aplicaríamos esa cota al completo-split crítico de §6.2. Por (6.2) y la definición de \(M(n)\), obtendríamos
\[
\frac{n^2+n}{6}-1\le M(n)\le cn^2+Cn.
\tag{6.5a}
\]
Si \(c<1/6\), la diferencia \((1/6-c)n^2\) excede a \(|C|n+1\) para \(n\) grande, contradiciendo (6.5a). La declaración `SharpConstantOptimality.erdos81_quadratic_constant_optimal` formaliza esta necesidad para \(c,C\in\mathbb Q\), y `erdos81_quadratic_constant_isLeast` combina la necesidad con el Teorema A. La extensión de la afirmación matemática a coeficientes reales se obtiene escogiendo racionales entre \(c\) y \(1/6\), y por encima de \(C\). Es distinta de la optimalidad del coeficiente *lineal* que sigue; ninguna de las dos afirmaciones decide si \(b=0\).

Fijado el término cuadrático \(n^2/6\), el coeficiente \(1/6\) del término lineal también es óptimo. Dados \(c<1/6\) y una constante \(B_0\), para todos los órdenes suficientemente grandes el testigo completo-split satisface
\[
\operatorname{cp}(G)=M(n)
\ge\frac{n^2}{6}+\frac n6-1
>\frac{n^2}{6}+cn+B_0.
\tag{6.5}
\]
La última desigualdad se cumple en cuanto \((1/6-c)n>B_0+1\). La formalización `LinearCoefficient.linear_coefficient_optimal` da esta conclusión para parámetros racionales; la afirmación para parámetros reales se sigue escogiendo un racional entre \(c\) y \(1/6\) y otro mayor que \(B_0\). Así se distingue la optimalidad del término asintótico de la constante aditiva necesaria para los órdenes pequeños.

La restricción de orden también aclara el alcance del Teorema A: olvidar \(Q.\mathrm{OrderAtMost}\ 4\) entrega inmediatamente la forma \(\operatorname{cp}(G)\le M(n)+b\) del problema original. `LossBudget.erdos81_cp_form_all_orders` y `erdos81_cp_form` registran ese paso para las dos cotas. La implicación inversa no es una regla válida para cotas arbitrarias: para \(n\ge2\), \(\operatorname{cp}(K_n)=1\), mientras que una pieza de orden a lo sumo cuatro cubre como máximo seis aristas, y por ello \(c_4(K_n)\ge\binom n2/6\). Esta comparación entre parámetros no demuestra una separación lógica entre los dos enunciados universales con el objetivo particular \(M(n)\).

### 6.4. El exceso de una partición completo-split

Mantengamos el régimen \(2\le k\le h\) de la Sección 6.1. Su argumento de pesos admite una lectura pieza por pieza. Para una clique \(C\) de \(K_k\vee I_h\), definamos
\[
d(C)=1+e_{\rm int}(C)-e_{\rm cruz}(C),
\]
donde se cuentan por separado las aristas internas del núcleo y las que unen núcleo y anfitrión. Entonces, para toda partición \(\mathcal Q\), sin restricción de orden,
\[
|\mathcal Q|-\left(kh-\binom k2\right)
=\sum_{C\in\mathcal Q}d(C).
\tag{6.6}
\]
**Demostración.** Las aristas internas suman \(\binom k2\) sobre las piezas y las cruzadas suman \(kh\), porque la cobertura es exacta. Sumando la definición se obtiene (6.6). Si \(C\) tiene un anfitrión y \(s\ge1\) vértices del núcleo,
\[
d(C)=1+\binom s2-s=\frac{(s-1)(s-2)}2\ge0;
\]
si no tiene anfitrión, \(d(C)=1+\binom{|C|}2>0\). No hay piezas contenidas sólo en los anfitriones: éstos forman un conjunto independiente y las piezas tienen al menos dos vértices. Los casos anteriores son, por tanto, exhaustivos. El defecto es cero exactamente en las aristas núcleo–anfitrión y los triángulos con dos vértices de núcleo y un anfitrión. Una partición óptima sólo utiliza esas piezas. Más generalmente, una partición con exceso a lo sumo \(t\) tiene a lo sumo \(t\) piezas de defecto positivo, pues cada una aporta al menos una unidad a (6.6). No se afirma unicidad de la partición óptima: puede haber distintas asignaciones de los mismos tipos de pieza.

### 6.5. Estabilidad integral y clasificación de los extremizadores

El argumento de la cota superior conserva la cuenta cercana reforzada (5.15a), aunque el Teorema B sólo necesita (5.15). Un grafo cuyo número óptimo de piezas está cerca de \(M(n)\) no puede pertenecer a la rama lejana, donde el redondeo produce una partición bastante por debajo de ese objetivo. La cuenta conservada convierte entonces un déficit integral pequeño en cotas para las aristas exteriores y los enlaces ausentes. Una vez elegida la raíz, una identidad por piezas controla toda partición próxima al mismo objetivo; no se elige de nuevo la raíz para cada partición.

**Teorema 6.1 (estabilidad integral).** Existe \(\gamma>0\) y un umbral \(N_{\rm est}\) tales que, si \(n\ge N_{\rm est}\), \(G\) es cordal, \(0\le\delta\le\gamma n^2\) y toda partición de orden a lo sumo cuatro tiene al menos \(M(n)-\delta\) piezas, entonces existe una clique \(R\) de \(G\) para la cual
\[
\bigl(M(n)-B_n(|R|)\bigr)+\frac m{16}+\frac A2\le\delta,
\qquad
d_E(G,S_R)=m+A\le16\delta.
\tag{6.7}
\]
Aquí \(m=e(G-R)\) y \(A\) es el número de enlaces ausentes entre \(R\) y \(V(G)\setminus R\).

Expliquemos la prueba. Se toma \(\gamma=\eta_0/4\) y se aplica la dicotomía. En la rama lejana, RC01 conserva al menos \(\eta_0n^2/2\) de margen y produce una partición con
\[
|Q|<\frac{n^2}{6}-\frac{\eta_0}{2}n^2
\le M(n)-\frac{\eta_0}{2}n^2.
\]
Esto contradice \(|Q|\ge M(n)-\delta\), porque \(\delta\le\eta_0n^2/4\). Por tanto, sólo puede ocurrir la rama cercana. Allí la cuenta fuerte (5.15a), conservada para el mismo testigo físico, da
\[
M(n)-\delta\le |Q|
\le B_n(|R|)-\frac m{16}-\frac A2,
\]
de donde sale la primera desigualdad de (6.7). Como \(B_n(|R|)\le M(n)\) y \(A\ge0\),
\[
m+A\le16\left(\frac m{16}+\frac A2\right)\le16\delta.
\]
Finalmente, que \(R\) sea clique identifica exactamente las ediciones necesarias para transformar \(G\) en \(S_R\): se eliminan las \(m\) aristas exteriores y se añaden los \(A\) enlaces ausentes. Esto prueba la igualdad de (6.7).

La misma raíz controla no sólo al grafo, sino también a sus particiones cercanas al máximo. Para cualquier partición \(Q\), incluso si admite cliques de más de cuatro vértices, escribamos \(a_K=|K\cap R|\) y \(b_K=|K\setminus R|\) para cada pieza \(K\). Definimos su defecto respecto de \(R\) por
\[
d_R(K)=1+\binom{a_K}{2}+3\binom{b_K}{2}-a_Kb_K
=\frac{(a_K-b_K)(a_K-b_K-1)}2+(b_K-1)^2.
\tag{6.7a}
\]
El primer término de la derecha es no negativo para todo entero \(a_K-b_K\). Por tanto \(d_R(K)=0\) exactamente para las aristas raíz–exterior y los triángulos con dos vértices en la raíz y uno fuera.

**Corolario 6.1a (estabilidad de las particiones).** Bajo las hipótesis del Teorema 6.1, la raíz \(R\) puede elegirse de forma que toda partición irrestricta en cliques \(Q\) con \(|Q|\le M(n)+\tau\), \(\tau\ge0\), tenga a lo sumo \(\tau+48\delta\) piezas no canónicas. El número total de aristas en esas piezas es a lo sumo \(10\tau+480\delta\). Ambas conclusiones usan la misma raíz; no hay restricción sobre el orden de las piezas.

**Demostración.** La cobertura exacta cuenta las aristas internas de \(R\), las exteriores a \(R\) y las que cruzan el corte como \(\binom{|R|}{2}\), \(m\) y \(|R|(n-|R|)-A\), respectivamente. Al sumar (6.7a) sobre las piezas se obtiene
\[
\sum_{K\in Q}d_R(K)=|Q|-B_n(|R|)+A+3m.
\tag{6.7b}
\]
Cada pieza no canónica aporta al menos uno. Si \(r=M(n)-B_n(|R|)\), la hipótesis sobre \(Q\) acota el defecto total por \(\tau+r+A+3m\). La reserva de (6.7) implica \(r+A+3m\le48\delta\). Para contar las aristas, la cota numérica local \(\binom{a+b}{2}\le10d_R(K)\) vale siempre que \(d_R(K)>0\), donde \(a=|K\cap R|\) y \(b=|K\setminus R|\). Las piezas de defecto cero son exactamente las canónicas. Sumando esta desigualdad sobre las piezas no canónicas se acotan sus aristas por diez veces el mismo defecto total, lo que da \(10\tau+480\delta\). La raíz proviene del testigo del Teorema 6.1 y no depende de \(Q\).

**Corolario 6.2 (clasificación eventual).** Los cordales extremales de orden suficientemente grande son exactamente los completo-split con los tamaños de núcleo de (6.4).

**Demostración.** Al poner \(\delta=0\), (6.7) fuerza \(m=A=0\), luego \(G=S_R\). La identidad aritmética
\[
6B_n(k)+(n-3k)(n-3k+1)=n(n+1)
\tag{6.8}
\]
clasifica entonces los tamaños que alcanzan \(M(n)\). En consecuencia, para \(n\) suficientemente grande,
\[
\operatorname{cp}(G)=M(n)
\quad\Longleftrightarrow\quad
c_4(G)=M(n)
\quad\Longleftrightarrow\quad
G\text{ es completo-split con núcleo óptimo},
\tag{6.9}
\]
donde el tamaño del núcleo es \(r\) si \(n=3r\), \(r\) o \(r+1\) si \(n=3r+1\), y \(r+1\) si \(n=3r+2\). La equivalencia usa la cota inferior irrestricta de la Sección 6.1; por eso clasifica simultáneamente los extremizadores para \(\operatorname{cp}\) y para \(c_4\).

### 6.6. Estabilidad para defecto fijo sobre una misma raíz

El Teorema C proporciona un valor agudo. Para conservar la geometría que lo explica, particionemos los vértices como \(V=C\sqcup D\sqcup H\), donde \(C\) es una clique de \(G\), \(|D|=s\) y \(2\le |C|\le |H|\). La **plantilla de defecto** asociada es
\[
T(C,D,H)=(K_C\sqcup I_D)\vee I_H.
\]
En el grafo original sólo se impone que \(C\) sea clique: \(D\) y \(H\) no tienen por qué ser independientes allí. Pongamos \(k=|C|+s\). La plantilla tiene valor base
\[
B_{s,n}(k)=k(n-k)-\binom{k-s}{2}.
\tag{6.10}
\]
Una pieza canónica es una arista entre \(C\cup D\) y \(H\), o un triángulo con dos vértices en \(C\) y uno en \(H\). Escribimos \(N_{\rm bad}(Q)\) para el número de las demás piezas y \(E_{\rm bad}(Q)\) para la suma de sus números de aristas. Esta última cuenta aristas distintas, pues \(Q\) es una partición.

**Teorema C′ (estabilidad para defecto fijo con una misma raíz).** Para cada entero fijo \(s\ge0\), existen \(\gamma_s>0\) y \(N_s^{\rm stab}\) explícitos con la siguiente propiedad. Pongamos
\[
\epsilon_s=\frac1{10^{41}(s+1)^8},\qquad
A_s=\max\{40000(s+1)^3,\,2/\epsilon_s\}.
\tag{6.11}
\]
Si \(n\ge N_s^{\rm stab}\), \(\operatorname{rsd}(G)\le s\) y
\[
c_4(G)\ge Q_s(n)-\delta,\qquad 0\le\delta\le\gamma_s n^2,
\]
entonces existe una misma raíz \((C,D,H)\) como la anterior tal que
\[
\begin{aligned}
d_E(G,T(C,D,H))&\le A_s\delta,\\
0\le Q_s(n)-B_{s,n}(k)&\le(1+4A_s)\delta.
\end{aligned}
\tag{6.12}
\]
Para esa raíz, toda partición irrestricta en cliques \(Q\) con \(|Q|\le Q_s(n)+\tau\), \(\tau\ge0\), satisface
\[
\begin{aligned}
N_{\rm bad}(Q)&\le\tau+(1+7A_s)\delta,\\
E_{\rm bad}(Q)&\le10\tau+10(1+7A_s)\delta.
\end{aligned}
\tag{6.13}
\]
Tanto \(\delta\) como \(\tau\) pueden ser reales. La raíz se elige antes de \(Q\) y de \(\tau\).

El máximo de (6.11) es \(2\cdot10^{41}(s+1)^8\): su segundo término domina la constante terminal \(40000(s+1)^3\) para todo \(s\ge0\). No se afirma que los coeficientes sean óptimos. Para \(s=0\), sigue siendo preferible el argumento cordal especializado: da \(16\), \(48\) y \(480\), en lugar de las grandes constantes de (6.11).

![Estructura de la prueba de estabilidad con una misma raíz para defecto fijo.](figures/fig4_same_root_stability.png)

**Figura 3.** Teorema C′: el borrado de vértices de grado bajo alcanza el terminal controlado, y la reinserción transporta su raíz al grafo original. Las cuentas conservadas controlan entonces toda partición sobre esa misma raíz. Ajustar el tamaño para obtener una plantilla óptima es un paso separado (Corolario 6.3), cuyo coste de raíz cuadrada ilustra la Proposición 6.3a. El diagrama es esquemático; el Apéndice F.1 proporciona la ventana de inducción.

**Demostración.** Primero explicamos la estimación conservada en el terminal de grado mínimo, y luego el paso a un grafo arbitrario de la clase. En la presentación normalizada del Apéndice E, sea \(a\) el número de enlaces ausentes entre \(S\) y \(H\), \(m=e(G[H])\), \(t_W=|W|\), y
\[
E=e(G[S])-\binom{|S|-s}{2}\ge0.
\]
El constructor conserva un crédito residual no negativo \(R_*\). La extracción de una clique real \(C\subseteq S\) da \(|S|=|C|+s+r\), con \(r\ge0\). Las cuentas conservadas son
\[
\begin{gathered}
a+\frac{m}{2000(s+1)^2}+R_*\le\delta,\qquad
nt_W\le800(s+1)^2R_*,\\
E\le R_*+nt_W,\qquad rn\le16sE,\\
d_E(G,T(C,D,H))\le a+m+E+2rn+2nt_W.
\end{gathered}
\tag{6.14}
\]
Aquí \(D,H\) en la última línea son las clases finales de la raíz, no necesariamente la clase intermedia de anfitriones. El Apéndice E.4 deduce las cinco cuentas: reducir la paleta de la primera fase conserva un múltiplo positivo de \(m\), el presupuesto estricto de los vértices excepcionales paga \(nt_W\), y se extrae una clique real de \(S\) antes de formar la plantilla final. En particular, los dos cargos \(rn\) tienen orígenes distintos: reducir el tamaño de la clique en la cuenta interior y trasladar los vértices restantes a la clase de anfitriones. Los productores estructurales son NormalizedDeficit, ResidualExcess, NormalizedCliqueCore y RootPartition; NormalizedStability los combina.

Sustituir las cotas intermedias en la última da
\[
d_E(G,T)\le a+m+
\bigl(1+32s+800(3+32s)(s+1)^2\bigr)R_*.
\]
El coeficiente de \(R_*\) es a lo sumo \(38000(s+1)^3\). Como \(a+m/[2000(s+1)^2]+R_*\le\delta\), se obtiene \(d_E(G,T)\le40000(s+1)^3\delta\). Así se explica la constante terminal de (6.11), en vez de introducirla como una pérdida sin justificar.

El borrado de vértices de grado bajo extiende la conclusión a todos los grafos de defecto enraizado a lo sumo \(s\). En el orden corriente \(t\), borramos un vértice de grado menor que \((1/3-\epsilon_s)t\) y ponemos
\[
u=Q_s(t)-Q_s(t-1),\qquad
\delta'=\delta+\deg(v)-u.
\tag{6.15}
\]
Toda partición de orden cuatro del hijo cuesta al menos \(Q_s(t-1)-\delta'\): en caso contrario, restaurar las aristas incidentes contradice la hipótesis sobre el padre. El Teorema C aplicado al hijo implica \(\delta'\ge0\). Además, \(u\ge(t-1)/3\), luego
\[
\delta'\le\delta-\epsilon_s t+\frac13.
\]
Reinsertar el vértice en la clase de anfitriones de la plantilla del hijo cambia a lo sumo \(t-1\) aristas. El coeficiente \(A_s\ge2/\epsilon_s\) paga ese coste. La inducción usa la ventana \(\delta\le\gamma_0t(t-N_0)\), con \(\gamma_0\le\epsilon_s/4\), en lugar de suponer repetidamente una ventana cuadrática de radio inalterado. Por encima de \(2N_0\), esta última se obtiene con \(\gamma_s=\gamma_0/2\). Las elecciones exactas de parámetros están en el Apéndice F. Esto demuestra la primera línea de (6.12).

Para la misma raíz, una partición de la plantilla se puede reparar en una partición de \(G\), de orden a lo sumo cuatro y coste a lo sumo \(B_{s,n}(k)+4d_E(G,T)\). Comparar con la cota inferior \(Q_s(n)-\delta\) demuestra la cota superior del déficit de valor base en (6.12); la inferior es la desigualdad entera del comparador.

Por último, la cuenta por piezas respecto de \(C\cup D\) y \(H\) da
\[
\begin{aligned}
N_{\rm bad}(Q)&\le |Q|-B_{s,n}(k)+3d_E(G,T),\\
E_{\rm bad}(Q)&\le10\bigl(|Q|-B_{s,n}(k)+3d_E(G,T)\bigr).
\end{aligned}
\tag{6.16}
\]
El defecto numérico es el de (6.7a). Un triángulo de defecto cero que no es canónico debe usar una arista extra dentro de \(C\cup D\), fuera de \(C\); esos triángulos se cargan a aristas extras distintas. Las piezas de defecto positivo satisfacen \(\binom{|K|}{2}\le10d(K)\). La suma da (6.16), y sustituir (6.12) demuestra (6.13). Para déficits reales, los costes enteros de las particiones permiten sustituir \(\delta\) por \(\lfloor\delta\rfloor\) en la prueba racional; la monotonía recupera las cotas reales enunciadas.

**Corolario 6.3 (comparación con tamaño óptimo e igualdad).** Bajo las hipótesis del Teorema C′ existe una plantilla extremal de tamaño óptimo \(T_*\) con
\[
d_E(G,T_*)\le A_s\delta+n\sqrt{(1+4A_s)\delta}.
\tag{6.17}
\]
Para \(\delta=0\) y \(n\) suficientemente grande,
\[
\operatorname{cp}(G)=Q_s(n)
\quad\Longleftrightarrow\quad c_4(G)=Q_s(n)
\quad\Longleftrightarrow\quad
G\cong(K_{k-s}\sqcup I_s)\vee I_{n-k},
\tag{6.18}
\]
donde \(k\) es un entero más cercano a \((2(n+s)+1)/6\).

**Demostración.** Sea \(\mathcal K_{s,n}\) el conjunto de esos enteros más cercanos. La parábola discreta del comparador implica
\[
\operatorname{dist}(k,\mathcal K_{s,n})^2
\le Q_s(n)-B_{s,n}(k).
\tag{6.19}
\]
Mover \(d\) vértices entre las clases núcleo y anfitriones, sin alterar \(D\), cambia a lo sumo \(nd\) aristas. Aplicamos (6.19) y (6.12), y después la desigualdad triangular de la distancia por ediciones, para obtener (6.17). El núcleo redimensionado no tiene por qué seguir siendo clique de \(G\); la afirmación de clique real corresponde a la raíz original del Teorema C′. El conjunto \(\mathcal K_{s,n}\), y no un maximizador predeterminado, es esencial cuando \(n+s\equiv1\pmod3\).

Si \(\delta=0\), (6.12) ya da \(G=T(C,D,H)\) e igualdad entre su valor base y \(Q_s(n)\). Esto demuestra la clasificación directa para \(c_4\). Como \(\operatorname{cp}\le c_4\le Q_s(n)\), también cubre la igualdad para \(\operatorname{cp}\). El testigo inferior irrestricto del Apéndice E da la recíproca. Así se recupera la clasificación de igualdad de [15, Teorema 1.1], con la cota superior adicional de orden cuatro.

**Proposición 6.3a (una obstrucción de raíz cuadrada).** Fijemos \(s\ge0\). Sean \(q,d\) enteros con \(2s+2\le q\) y \(1\le d\le q/2\), y pongamos \(n=3q-s\). El grafo
\[
G_{s,q,d}=(K_{q+d-s}\sqcup I_s)\vee I_{2q-s-d}
\]
tiene defecto simplicial enraizado a lo sumo \(s\) y satisface
\[
\operatorname{cp}(G_{s,q,d})=c_4(G_{s,q,d})
=Q_s(n)-\delta_d,\qquad
\delta_d=d^2+\binom d2=\frac{3d^2-d}{2}.
\tag{6.20}
\]
Para toda plantilla de tamaño óptimo \(T\) sobre el mismo conjunto de vértices, con cualquier etiquetado,
\[
d_E(G_{s,q,d},T)\ge\frac{nd}{4}
\ge\frac{n\sqrt{\delta_d}}8.
\tag{6.21}
\]

**Demostración.** El argumento de defecto enraizado del Apéndice E.3 no requiere un núcleo de tamaño óptimo: se aplica a \(G_{s,q,d}\) y da \(\operatorname{rsd}(G_{s,q,d})\le s\). El núcleo clique tiene al menos dos vértices y no tiene más vértices que el conjunto de anfitriones. Por tanto, la construcción del comparador da una partición de orden a lo sumo cuatro con coste \(B_{s,n}(q+d)\). El argumento de pesos del Apéndice E.3 también se aplica a este núcleo de tamaño no óptimo: toda partición irrestricta tiene al menos ese número de piezas. Restar este baseline de \(Q_s(n)\) da (6.20).

Como \(n+s=3q\), el único tamaño óptimo del núcleo combinado es \(q\). Toda plantilla óptima tiene, en consecuencia, el mismo número de aristas, independientemente de su etiquetado. Al contar las aristas del núcleo y los enlaces cruzados se obtiene
\[
2\bigl(e(G_{s,q,d})-e(T)\bigr)
=d(4q-4s-d-1).
\]
En particular,
\[
4\bigl(e(G_{s,q,d})-e(T)\bigr)-nd
=d(5q-7s-2d-2)\ge0.
\]
Para la última desigualdad, escribamos el segundo factor como
\(4(q-2s-2)+(q-2d)+s+6\).
Una edición cambia el número total de aristas a lo sumo en uno, luego
\(d_E(G_{s,q,d},T)\ge e(G_{s,q,d})-e(T)\ge nd/4\).
Finalmente, \(\delta_d\le2d^2\le4d^2\), lo que prueba (6.21). \(\square\)

Tomar \(d=1\) da déficit exactamente uno y distancia no acotada a toda la familia de tamaño óptimo cuando \(q\) crece. Por tanto, ningún coeficiente que dependa sólo de \(s\) puede reemplazar (6.17) por una cota lineal en \(\delta\). Estos ejemplos pertenecen a cualquier ventana positiva fija de casi extremalidad una vez que su orden es suficientemente grande. Más generalmente, (6.21) exhibe la escala de raíz cuadrada a lo largo de la familia de déficits indicada. Es una obstrucción de peor caso, no una cota inferior puntual para todo grafo o todo déficit real, y no afirma constantes óptimas. Es compatible con el Teorema C′: cada ejemplo ya es una plantilla, pero su núcleo no tiene tamaño óptimo.

### 6.7. Cotas uniformes y defecto sublineal

Un umbral para \(s\) fijo no se puede aplicar a una sucesión arbitraria \(s=o(n)\): podría crecer mucho más rápido que el orden. Conservamos, en cambio, una cota uniforme en el defecto antes de invocar RC01.

**Proposición 6.4 (cotas fraccionales finitas).** Si \(\operatorname{rsd}(G)\le s\le n\), entonces, para todo orden incluido cero,
\[
F_4(G)\le M(n-s)+ns.
\tag{6.22}
\]
En la banda \(4s\le n\) se tiene la cota más fuerte
\[
F_4(G)\le M(n-s)+ns-\binom{s+1}{2}.
\tag{6.23}
\]
Para cada \(\varepsilon>0\), un mismo umbral \(N(\varepsilon)\), independiente de \(s\), hace válida la cota correspondiente para \(c_4(G)\) tras añadir \(\varepsilon n^2\), siempre que \(n\ge N(\varepsilon)\) y se cumpla la respectiva condición de banda.

El argumento de estrella con pesos de ambos signos sigue [15, Lema 3.1]; se cita como método utilizado aquí, no como un principio nuevo de localización. Nuestro cálculo usa \(L=4\), conserva el cargo truncado por excepciones \(\sum_{j<q}\min(s,j)\) y acota mediante el comparador entero, sin redondear hacia abajo una desigualdad fraccional. El Apéndice F describe las dos estimaciones de estrella y el control de órdenes pequeños. Para la conclusión integral, primero se elige el umbral de RC01 a partir de \(\varepsilon\). Completar el empaquetamiento redondeado cuesta a lo sumo \(F_4(G)+\varepsilon n^2\); se inserta (6.22) o (6.23). La elección de \(N\) nunca depende del grafo ni de \(s\).

**Teorema 6.5 (defecto sublineal y una raíz para todas las particiones).** Sean \(n_j\to\infty\), sin hipótesis de monotonía, y \(G_j\) grafos de orden \(n_j\) y defecto enraizado a lo sumo \(s_j=o(n_j)\). Existen particiones \(Q_j\) de orden a lo sumo cuatro tales que
\[
\max\{0,|Q_j|-n_j^2/6\}=o(n_j^2).
\tag{6.24}
\]
Supongamos además que, eventualmente,
\[
c_4(G_j)\ge n_j^2/6-\delta_j,\qquad \delta_j=o(n_j^2).
\]
La sucesión de déficits se puede tomar racional, como en el enunciado formal. Existen cliques \(R_j\) de los grafos originales y errores no negativos \(e_j=o(n_j^2)\) tales que
\[
|R_j|=n_j/3+o(n_j),\qquad
d_E(G_j,S_{R_j})=o(n_j^2),
\tag{6.25}
\]
y, para todo \(j\), toda partición irrestricta en cliques \(Q\) y todo racional \(\tau\) con \(|Q|\le M(n_j)+\tau\),
\[
N_{\rm bad}(Q)\le\tau+e_j,\qquad
E_{\rm bad}(Q)\le10\tau+10e_j.
\tag{6.26}
\]
Las piezas canónicas son aquí las del Corolario 6.1a respecto de \(R_j\). Ni la raíz ni \(e_j\) dependen de \(Q\) o de \(\tau\).

**Demostración.** Aplicamos la cota integral uniforme de la Proposición 6.4 a particiones mínimas de orden cuatro. Para cada precisión fija, \(s_j/n_j\) es eventualmente pequeño y \(n_j\) supera el umbral fijo de redondeo. Esto demuestra (6.24); se acota el error superior, no se afirma una igualdad \(|Q_j|=n_j^2/6+o(n_j^2)\) para grafos dispersos.

La localización uniforme da, para cada precisión, una clique real con error pequeño de tamaño y poca masa exterior y de enlaces ausentes. Para elegir una clique independiente de la precisión, minimizamos sobre todas las cliques \(R\) de \(G_j\) la cantidad no negativa
\[
\mathcal S_G(R)=n\bigl||R|-n/3\bigr|
 +e(G-R)+A_R+\bigl(M(n)-B_n(|R|)\bigr),
\tag{6.27}
\]
donde \(A_R\) cuenta los enlaces raíz–exterior ausentes. La familia de cliques es finita y no vacía (incluye la clique vacía). La estimación de localización y la parábola del comparador muestran que el mínimo es \(o(n_j^2)\). Cada sumando no negativo está acotado por ese valor, lo que demuestra (6.25). Pongamos \(e_j=3\mathcal S_{G_j}(R_j)\). La identidad (6.7b) y la desigualdad de masa de aristas usada en (6.16) demuestran (6.26) simultáneamente para todas las particiones. Para la localización estructural uniforme, la prueba realiza primero una pequeña edición cordal mediante el desarrollo de remoción de [22], transfiere la estabilidad integral y recupera una clique real del grafo original. El Apéndice F.3 detalla las pérdidas. No se trata de aplicar el Teorema C′ con \(s\) creciente.

**Corolario 6.6 (cota exacta, uniforme en el defecto).** Sean \(T(0)=1\), \(T(j+1)=2^{T(j)}\), como en §6.3, y definamos
\[
\begin{aligned}
c_{\rm poly}&=4\cdot17664^5\cdot9000^{105}+3006,\\
c_{\rm far}&=c_{\rm poly}(128\cdot10^{82})^{105},\\
c_T&=h_{\rm iter}+c_{\rm far}+841780,\qquad
P(s)=c_T(s+1)^{1680},
\end{aligned}
\tag{6.28}
\]
donde \(h_{\rm iter}=h\) es el entero explícito definido en §6.3. Si \(\operatorname{rsd}(G)\le s\) y \(n\ge T(P(s))\), entonces \(c_4(G)\le Q_s(n)\). Más generalmente, \(n\ge T(P(S))\) basta simultáneamente para todo \(s\le S\).

Para \(n\ge T(P(0))\), el conjunto finito siguiente no es vacío y podemos poner
\[
s_{\max}(n)=\max\{S\in\mathbb N:S\le n,\ T(P(S))\le n\}.
\tag{6.29}
\]
Entonces la cota exacta vale simultáneamente para todos los \(s\le s_{\max}(n)\). La restricción inferior sobre \(n\) es esencial para esta formulación: por debajo de ella, la inversa formal devuelve cero aunque el predicado que la define pueda no tener solución.

**Demostración.** E35.Fexp_le_tower prueba \(F_s\le T(P(s))\) para el umbral explícito del Apéndice E.2. Su cuenta numérica combina la cota lejana uniforme (C.4), el umbral de edición hacia un cordal y los costes finitos de ensamblaje. Apliquemos el Teorema C con \(F_s\). Tanto \(P\) como \(T\) son no decrecientes, de modo que el mismo umbral para \(S\) cubre todos los \(s\le S\). Finalmente, el predicado que define \(s_{\max}\) se cumple porque el conjunto contiene cero. \(\square\)

Ésta es una banda exacta uniforme, no una cota exacta para toda sucesión de defectos sublineales. Su altura es polinómica en \(s\), pero el umbral mismo es una torre. No se pretende utilidad numérica. Acota el umbral del Teorema C, no automáticamente el umbral de estabilidad \(N_s^{\rm stab}\) de (F.1).

## 7. Formalización, código y reproducibilidad

El suplemento Lean identificado de esta versión usa Lean y Mathlib v4.28.0. Las declaraciones finales no reciben como argumentos el redondeo, la existencia del óptimo ni el constructor cercano: los invocan como teoremas demostrados en sus dependencias. Los axiomas fundacionales permitidos se distinguen de cualquier hipótesis matemática adicional.

El alcance formal difiere del documentado por [5] en el commit citado. Su archivo `lean/FORMALIZATION_STATUS.md` declara una verificación condicionada a `ExternalInputs.Inputs`: Vizing, Häggkvist–Janssen y una transferencia de empaquetamiento que incluye certificados de optimalidad racional. Esas entradas son parámetros explícitos, no axiomas ocultos. Aquí se descargan las entradas empleadas por nuestra cadena, incluido Vizing; no se utiliza Häggkvist–Janssen. La comparación concierne a lo comprobado por cada desarrollo Lean: no afirma que la demostración matemática de [5] quede condicionada a conjeturas.

Los identificadores formales se imprimen con letra monoespaciada. Una flecha de continuación en un salto de línea es una marca tipográfica, no parte del identificador; las fuentes Markdown y Lean conservan su escritura literal.

La configuración declara Mathlib como paquete de terceros y una selección de módulos `Nibble` de Paper III como dependencia local de la serie. `ConeAudit` recorre los tipos y términos de prueba de las declaraciones seleccionadas y comprueba que sus dependencias transitivas no contengan nombres bajo la raíz `Erdos81`, utilizada por [5]. Nuestros módulos PaperIV.Erdos81Unconditional y PaperIV.Erdos81AllOrders tienen raíz de espacio de nombres PaperIV; no son la raíz excluida Erdos81 que usa [5]. La ausencia de estos nombres es un resultado de auditoría reproducible, no una inferencia de la lista de importaciones. Su alcance es preciso: certifica esa exclusión en el corte examinado; por sí sola no detectaría código trasladado y renombrado ni determinaría la procedencia histórica de cada argumento. La atribución de fuentes se documenta por separado. El mismo control de espacios de nombres no permite emitir un veredicto sobre [15]. La extensión utiliza el método de estrella con signos de [15, Lema 3.1] y el método de remoción de [22]; demostrar sus implementaciones en este suplemento no convierte esos métodos en nuevos.

La interfaz pública del Teorema C en esta revisión es DefectExplicitPublication: utiliza E34.theoremC_fully_explicit_final y el testigo inferior irrestricto ya demostrado en DefectSharpPublication. El ensamblaje existencial anterior permanece como comparación histórica, no como la prueba seleccionada para el Teorema C. Su localización utiliza remoción inducida de Alon–Shapira [23]; el ensamblaje explícito seleccionado utiliza, en cambio, el desarrollo de remoción cordal polinómica de [22]. El control adicional FDCheck.ASCheck recorre términos de prueba y tipos para comprobar la exclusión de los resultados de remoción identificados en estas declaraciones seleccionadas. Esto no excluye el espacio de nombres AlonShapira: se siguen usando definiciones compartidas de cordalidad, distancia de edición y copias inducidas.

El punto único de ejecución es `python tools/audit_publication.py`. Lee los 19 objetivos de FREEZE_SCOPE.json, los ejecuta secuencialmente y conserva sus registros individuales; las dependencias sin cambios reutilizan la caché fijada. Se ejecutan de nuevo los objetivos de auditoría deliberadamente, porque importar un módulo de auditoría ya compilado no volvería a ejecutar todos sus comandos. PublicationIncrementAudit conserva los controles históricos; ResearchAudit y FDCheck.FinalAudit cubren las interfaces de la extensión; E34.Audit cubre remoción; E35.Audit cubre las nuevas cotas de umbral; OptimalTemplateObstructionAudit comprueba las seis declaraciones que sostienen la Proposición 6.3a. ReleaseExportCheck comprueba las exportaciones públicas sólo a través de PaperIV. La interfaz del constructor PaperIV.Editorial.ConstructorBudget conserva una misma partición en ambas conclusiones del Apéndice E. Las identidades de ejecución y la lista literal de objetivos especifican qué controles se ejecutaron; la auditoría interna histórica no reemplaza una nueva revisión de correspondencia entre fuentes y manuscrito para la versión 1.2.

| Resultado en el texto | Módulo de referencia |
|:--|:--|
| **Entradas y construcción** | |
| Óptimo racional alcanzado | `PaperI.FiniteLPDuality`, `CertifiedOptimumExistence` |
| Redondeo mixto uniforme, Teorema 3.1 | `RC01Final`, `MixedRoundingAdapter`; infraestructura `Nibble.*` de Paper III |
| Corolario 3.5, régimen lejano para todos los grafos | `FarRegimeAllGraphs.farRegime_cliquePartition_allGraphs`; versión explícita en `E17.ExplicitFarAssembly` |
| Limpieza mejorada completa y umbral explícito | `E17.Cleanup`, `E17.FarBudget`, `E17.ExplicitFarRounding`, `E17.ExplicitFarAssembly`; constantes de `E18` y `E19` |
| Selección fraccional por nibble, Paper III | `Nibble.FracNibbleLE`, `Nibble.FracNibbleRepaired`; adaptadores `PaperIIISlackNibbleAdapter`, `PaperIIINibbleAdapter` |
| Localización, raíz y ventana crítica | `NearH1Localization`, `NearRootWindow`, `RootRegularizationBridge` |
| Dicotomía e interfaz absorbible | `HybridDichotomy`, `SeparationAbsorptionRoute` |
| Contabilidad y partición cercana | `RD09PhysicalLedger`, `NearH1FinalAssembly`, `NearH1LocalConstructor` |
| **Conclusiones extremales** | |
| Cota aguda y máximo eventual | `Erdos81Unconditional`, `PaperTheorems` |
| Cotas para todos los órdenes | `Erdos81AllOrders`; cota explícita en `ExplicitThreshold` |
| Defecto enraizado fijo y máximo, Teorema C | `DefectExplicitPublication`; ensamblaje explícito `E34.L11Main`; testigo inferior `DefectSharpPublication` |
| Necesidad del orden cuatro, Proposición D.2 | `DefectSharpPublication.order_three_insufficient`, `E11K10` |
| Presupuesto general y paso a \(\operatorname{cp}\) | `LossBudget`, `SplitMixedGap` |
| Estabilidad del grafo, estabilidad de particiones y clasificación extremal | `IntegralStability`, `RootPartitionStability`, `ExtremalClassification` |
| Valor completo-split y núcleos | `SplitCompleteSharpValue`, `SplitCompleteRigidity` |
| Defecto de partición y coeficientes óptimos | `SplitCompleteDefect`, `LinearCoefficient`, `SharpConstantOptimality` |
| Densidad de aristas en la rama crítica | `NearEdgeDensity`, `NearCriticalDichotomy` |
| Igualdad de óptimos mixtos, Apéndice D.2 | `SplitMixedGap`, `SplitCompleteSharpValue` |
| **Herramientas complementarias** | |
| Absorción compatible con presupuesto | `SpreadAbsorptionCompatibility` |
| Reserva equilibrada, Apéndice B.2 | `BalancedReserve`, `Nibble.BeckFiala` de Paper III |
| Completación con cuatro anfitriones, Apéndice B.3 | `FourHostClosure`; Vizing y `MultiHostTriangleLift` |
| Reserva exacta y sensibilidad del umbral | `ReserveIdentity`, `NearThresholdSensitivity` |
| Estructura cordal reutilizable | `CliqueTree` |

**Tabla 3.** Los prefijos `PaperI`, `Nibble` y `MixedRounding` señalan, respectivamente, el desarrollo racional vinculado a Paper I, la infraestructura de nibble de Paper III y la biblioteca neutral del modelo mixto. Los prefijos `E17`, `E18`, `E19` y `A4S1` identifican los módulos de los incrementos integrados en el proyecto; los demás nombres sin prefijo pertenecen a `PaperIV`; `MixedRoundingAdapter` es un adaptador de ese espacio hacia la biblioteca `MixedRounding`. RC01 incorpora y adapta herramientas de Paper III, pero su ensamblaje mixto de dos cuotas es el de la Sección 3 de esta investigación. La tabla relaciona resultados y fuentes; el suplemento conserva la lista exacta de dependencias.

La estructura cordal y Dirac proceden de la contribución de Paper II, portada en `ChordalStructure`. El lema de regularidad de Szemerédi se reutiliza de Mathlib; la construcción y los adaptadores de perfiles limpios y de selección mixta pertenecen a Paper IV. Esta procedencia se distingue de la ubicación actual de un archivo bajo `PaperIV`.

Las comprobaciones locales del 27 de septiembre incluyen el agregado, la auditoría general de 81 declaraciones y la auditoría específica de nueve resultados del enlace B7 y su propagación. Esta última examina tipos y términos de prueba, exige que la construcción use las dos cuentas de limpieza mejorada y admite sólo `propext`, `Classical.choice` y `Quot.sound`. Los recuentos no son disjuntos y no deben sumarse. Reutilizar un teorema demostrado del nibble no equivale a introducirlo como hipótesis pendiente.

El control de exportación contiene 224 comandos literales `#check` sólo a través de `import PaperIV`. Todos pasaron en el nuevo corte. Esto establece el acceso a esa lista, no que toda declaración del suplemento pertenezca a la interfaz canónica. ResearchAudit recorre tipos y términos de prueba de 75 declaraciones seleccionadas de la extensión; OptimalTemplateObstructionAudit, con seis declaraciones, y los demás objetivos proporcionan sus propios controles de alcance delimitado. BoundedCliqueGap permanece como anexo separado, no como premisa del teorema principal.

El corte fuente `piv-v12-fb459343d234` contiene 607 módulos Lean y 615 entradas de fuentes, configuración y documentación. La reconstrucción secuencial completa compiló los 607 módulos en dos tramos verificados. Tras un reinicio del equipo, se verificaron y reutilizaron 421 objetos recién compilados en el primer tramo; el tramo reanudado compiló 186 módulos. No se utilizaron objetos previos del proyecto y ningún módulo falló, quedó bloqueado ni fue omitido. Los 19 objetivos seleccionados se ejecutaron de nuevo con código de salida cero en el tramo reanudado. La salida contiene 461 registros de axiomas, cada uno restringido a `propext`, `Classical.choice`, `Quot.sound` o un subconjunto; estos registros no cuentan teoremas distintos. Las fuentes no cambiaron y los objetos reutilizados se contrastaron con sus registros de fuentes, dependencias y compilación. El SHA-256 del manifiesto es `fb459343d234f968d7d32eff1491ea8a09aa2e135b313a80623012e7449042f5`; el del archivo de sólo fuentes es `cb2741454380736ffe01b59933057b5079fa9f865d5bbdd3f67534bf808a62e6`. Los registros, la procedencia combinada y la validación final se conservan en `03_reproducibility/full_rebuild_v12_20260929_resume/`, con enlaces al primer tramo preservado. Éste es un control formal local y un congelado de fuentes, no una auditoría interna o independiente completada de la versión 1.2.

El corte anterior `piv-stability-fe9bb18343da` y las ejecuciones separadas de integración se conservan bajo sus identidades originales. El nuevo corte los sustituye como identidad fuente seleccionada; no reescribe su evidencia. Los cuatro módulos E35L y FDCheck.TowerAudit se retiraron del nuevo árbol porque E35 reemplaza sus estimaciones y ninguno pertenece al conjunto de dependencias seleccionado. Todos los módulos Lean locales restantes pertenecen al cierre de dependencias de los 19 objetivos seleccionados. Ese cierre incluye definiciones históricas y controles comparativos; no se afirma que sea la biblioteca de prueba más pequeña posible.

**Estado de auditoría de esta candidata editorial.** La evidencia de reconstrucción anterior es previa a las auditorías. Posteriormente, la ejecución interna `run_20260929_v1.2_fb459343d234_r1` registró PASS para su alcance declarado. La ejecución externa `run_v1.2_r1` sigue en curso al preparar esta candidata. Ambas se refieren a la versión 1.2; las explicaciones ampliadas de la versión 1.21 requieren una revisión separada de correspondencia con las fuentes y de paridad bilingüe. La identidad de fuentes Lean no ha cambiado.

### 7.1. Repositorios y contribuciones

El repositorio de la serie, disponible en <https://github.com/jtraverso/erdos-81-chordal-clique-partitions>, contiene los manuscritos y materiales de Papers I–III [2–4] y el borrador público v0.8 de Paper IV, identificado por el commit `f783a792404a60983a7ef754d055fbe6c341188b`. Ese commit identifica sólo la versión anterior. El nuevo congelado de fuentes que sostiene esta candidata se identifica localmente arriba; no se ha asignado a esta candidata un commit de repositorio ni una fecha de publicación.

Las contribuciones reutilizables tienen referencias propias. El empaquetamiento de triángulos suma-cero corresponde al PR #348 de Lean Pool [12], <https://github.com/Vilin97/lean-pool/pull/348>, fusionado en el commit `540d8e3`. Los emparejamientos por grado mínimo y su selección ponderada corresponden al PR #420 [9], <https://github.com/Vilin97/lean-pool/pull/420>, fusionado en `d1de6d2`. Las fuentes de la serie conservan los antecedentes y adaptaciones de Vizing y Beck–Fiala. La atribución de las formalizaciones se distingue de la autoría de los teoremas clásicos.

Se preparan además cuatro componentes para su reutilización fuera de esta demostración: las factorizaciones por emparejamientos de grafos completos, la recoloración equitativa de aristas con una misma paleta, los órdenes de eliminación perfecta que terminan en una clique prescrita y la selección equilibrada de una reserva de aristas. La carpeta `contrib/Extraction` los separa del modelo de empaquetamiento de Paper IV. Los dos últimos conservan, respectivamente, las pruebas de Dirac de Paper II y de Beck–Fiala de Paper III como soporte identificado. Se trata de extracciones de formalizaciones, no de una reclamación de novedad para esos resultados. Su validación independiente y la revisión de las interfaces para Mathlib siguen pendientes; no se presentan como contribuciones aceptadas ni como parte del corte congelado.

La biblioteca de árboles de cliques se prepara por separado en `contrib/CliqueTreeExtraction`. Reúne la representación por bolsas, las propiedades de intersección, los separadores y las identidades de conteo, con soporte de cordalidad procedente de Paper II. Conserva las hipótesis que distinguen árboles conexos, bolsas repetidas y casos vacíos, así como los contraejemplos a formulaciones que las omiten. Su extracción tampoco se declara validada hasta completar la compilación y la auditoría independientes.

Lean [10] y Mathlib [11] proporcionan el entorno de comprobación. La auditoría del código no reemplaza la revisión humana de las definiciones ni la correspondencia entre un enunciado formal y su expresión en el manuscrito. Los experimentos orientaron la búsqueda y detectaron afirmaciones falsas; no se usan como premisas de universalidad.

### 7.2. Puente de modelos y convención de ganancia

El refinamiento de representación de la Figura 1 se verifica en `MixedRoundingAdapter`. El adaptador identifica las aristas de una pieza y el predicado de copia admisible, transporta las capacidades de un empaquetamiento fraccional y prueba la igualdad de valores mediante `value_toFarFrac`. Para un empaquetamiento entero, `gain_toFarPacking` conserva la ganancia. Por tanto, el Teorema 3.1 puede utilizarse a través de esta presentación neutral sin cambiar el presupuesto (1.3). Esto no constituye una nueva demostración del redondeo.

Hay dos funciones llamadas `gainOf` cuyo dominio de uso debe distinguirse. `Model.gainOf` vale dos en cardinal tres, cinco en cardinal cuatro y cero en los demás cardinales. `FarRounding.gainOf` vale \(\binom{|K|}{2}\mathbin{\dot-}1\), donde \(\dot-\) es la resta truncada en los naturales. Coinciden en cardinales de cero a cuatro, pero desde cinco dejan de coincidir. En los ítems mixtos, que tienen cardinal tres o cuatro, el transporte es legítimo. Para particiones irrestrictas, como las de la Sección 6.4, se usa la cuenta de aristas o `FarRounding.gainOf`; nunca se sustituye por la función de ganancia acotada de `Model`. Puesto que las piezas de una partición tienen al menos dos vértices, allí la resta truncada coincide con la resta ordinaria.

## 8. Comparación de mecanismos y alcance

Los Papers I–III [2–4], en sus ediciones inglesa y española, están reunidos en el depósito Zenodo v3 del 23 de agosto de 2026, identificado por el DOI de versión `10.5281/zenodo.22064657`. Las fechas que figuran en [5] y [15] son, respectivamente, el 8 y el 15 de septiembre de 2026. Se registran para identificar las versiones comparadas; esa cronología no establece por sí sola prioridad matemática ni dependencia entre las demostraciones.

La cuenta general (1.3a) permite comparar familias de piezas sin identificar las pruebas. La tabla siguiente separa el modelo utilizado de la conclusión obtenida. En ella \(L\ge4\) se fija antes del grafo y las piezas \(K_2\), de ganancia cero, se añaden para completar las aristas restantes.

| Desarrollo | Piezas con ganancia positiva | Parámetro acotado | Margen del modelo |
|:--|:--|:--|:--|
| Preprint [5] | \(K_3,K_4\) en su construcción final | \(c_4\) | \(\Delta_{\{3,4\}}\) |
| Okechukwu [15] | \(K_3,\ldots,K_L\) en la aproximación usada para localizar | \(q_L\) en el Lema 3.4; \(\operatorname{cp}\) en el Teorema 1.1 | \(\Delta_{\{3,\ldots,L\}}\) para el modelo auxiliar |
| Esta investigación | \(K_3,K_4\) | \(c_4\) | \(\Delta_{\{3,4\}}\) |

**Tabla 4.** Instancias del presupuesto general. \(q_L\) es la notación de [15] para el mínimo con piezas de orden a lo sumo \(L\). Los márgenes se comparan para el mismo grafo; (1.3b) da una desigualdad débil, no una separación estricta universal.

Las tres conclusiones pueden expresarse mediante (1.3a), cada una en su familia. La coincidencia de esa cuenta no es una equivalencia entre los mecanismos, ni permite sustituir una partición con piezas grandes por otra de orden a lo sumo cuatro. Respecto de esta restricción, [5] y nuestra conclusión coinciden; la comparación con [15] debe mantener visible su familia más amplia.

La identidad (1.3) permite comparar resultados sin identificar sus pruebas. El preprint [5, §§2 y 9] emplea transferencia fraccional–integral en el régimen con margen. En el régimen crítico usa su construcción alrededor de una raíz [5, §3], la regularización y estabilidad local [5, §§4–5], y una localización por primera entrada [5, §8]. Su teorema de cota eventual [5, §9] produce piezas de orden a lo sumo cuatro. Si de esa partición se retiran las piezas \(K_2\) y se conserva como \(\mathcal P\) el conjunto de piezas \(K_3,K_4\), el Lema 2.1 da
\[
W^*(G)-g(\mathcal P)
=\bigl(e(G)-g(\mathcal P)\bigr)-F_4(G)
\le M(n)-F_4(G)=\Delta(G).
\tag{8.1}
\]
Por tanto, su conclusión cumple el mismo presupuesto. Esta observación contable no es un adaptador formal entre su desarrollo y nuestro testigo estructural.

Nuestra prueba también separa dos casos, pero realiza el paso crítico mediante el descenso de la Sección 4 y la asignación de uno o dos candidatos por factor de la Sección 5. Conserva una estabilidad local; no afirma que toda estabilización pueda suprimirse. Lo que evita es escoger un primer índice de entrada. La Figura 4 sitúa las diferencias sin dibujar el régimen lejano como si fuera una etapa previa al crítico.

![Comparación de mecanismos. El preprint [5] y esta investigación separan dos casos alternativos y construyen una partición que cumple (1.3). Las flechas indican implicaciones hacia la conclusión, no el paso de un régimen al otro. Los localizadores de la columna izquierda están en la Sección 8.](figures/fig1_presupuesto_comparado.png)

| Componente | Preprint [5] | Esta investigación |
|:--|:--|:--|
| Margen cuadrático | Transferencia, §§2 y 9 | Redondeo mixto, §3 |
| Camino de copias | Adaptación de Paper II, §6 | Transporte mixto y selección, Lema 4.1 |
| Localización | Primera entrada, §8 | Descenso desde el terminal, §4.2 |
| Construcción cercana | Coloración por listas, §3 | Clases equilibradas y candidatos, §5.3 |
| Cuentas estructurales | Estabilidad local, §5 | Testigo conservado y Teorema 6.1 |
| Conclusión extremal | Cota eventual, §9 | Teorema B y Corolario 6.2 |

**Tabla 5.** Comparación de pasos y localizadores. No es una tabla de prioridad bibliográfica ni afirma que los antecedentes de cada paso sean exclusivos de un desarrollo.

La relación con la serie está documentada en el propio preprint [5]. Su introducción cita la cota fraccional de Paper II y el resultado split de Paper III; su Sección 6 atribuye a Paper II el esquema de copias, la selección por clases y el terminal split, y desarrolla la adaptación mixta. Esta procedencia no implica que todo paso de [5] sea consecuencia formal de la serie, del mismo modo que compartir esos antecedentes no identifica nuestros dos mecanismos críticos.

### 8.1. El antecedente de defecto simplicial acotado

Okechukwu [15, Teorema 1.1] establece el máximo eventual para defecto fijo, una cota aditiva para todos los órdenes para \(\operatorname{cp}\) y la clasificación de los grafos de igualdad. La clase de grafos, \(Q_s(n)\) y la familia que alcanza el máximo coinciden con los nuestros, y utilizamos su definición de defecto enraizado. Los Teoremas C y C′ implican las tres cláusulas: la cota superior vale con piezas de orden a lo sumo cuatro; el rango finito restante se absorbe en una constante aditiva; y el déficit cero da la clasificación irrestricta de la igualdad. Ni la fórmula extremal ni la familia de igualdad se presentan como nuevas. Esta comparación no afirma que el método de [15] no pueda dar la cota más fuerte sobre el tamaño de las piezas.

| Componente | Okechukwu [15] | Esta investigación |
|:--|:--|:--|
| Localización | Dual con signos, Teorema 3.3 | Descenso por copias, §4 |
| Transferencia | Haxell–Rödl, plantillas conjuntas, Lema 3.4 | Selección mixta de dos cuotas, §3 y Apéndice C |
| Construcción crítica | Coloración por listas y excepciones, §§4–5 | Raíz regularizada y candidatos, §5 |

**Tabla 6.** Comparación con la prueba cordal de §§3–5; [15] no se identifica con [5]. Las extensiones a defecto fijo y sublineal de §§6.6–6.7 también utilizan los desarrollos de localización y remoción especificados en el Apéndice F. La tabla no afirma que todas las partes de este paper ampliado utilicen descenso por copias.

El corte de orden en [15] requiere cuidado. Su Teorema 3.3 elige \(L\) en función de la precisión de localización, y el argumento de estabilidad utilizado por la Proposición 5.4 y el Teorema 1.1 aplica ese corte mediante el Lema 3.4. No fija \(L=4\). La elección explícita \(L=4\) que sigue a la prueba de [15, Teorema 1.3] demuestra su aproximación separada (1.5), no la cota exacta del Teorema 1.1. Así, nuestra conclusión con orden fijo cuatro refuerza la cota superior exacta enunciada; no se afirma que toda adaptación posible del método de [15] necesite cliques mayores.

Para el modelo auxiliar de la Tabla 4, [15, Lema 3.4] proporciona \(q_L(G)\le q_L^*(G)+\zeta n^2\). Su partición fraccional exacta es equivalente al modelo de ganancia de §1.1, luego \(q_L^*=F_{\{3,\ldots,L\}}\). Algebraicamente, esta estimación satisface el presupuesto de partición si \(\zeta n^2\le M(n)-q_L^*(G)\). Esa cuenta condicional no describe la construcción final de [15, Teorema 1.1]: su prueba usa el Lema 3.4 a través de la localización estructural, y después un argumento de contraejemplo mínimo y las construcciones triangulares de [15, §§4–5]. El corte auxiliar \(L\) no debe leerse como el orden de las piezas de esa construcción final.

El Teorema C′ da estabilidad lineal por ediciones hacia una plantilla de defecto cuyo núcleo no se exige de tamaño óptimo. La comparación con la familia óptima pertinente a [15, Corolario 5.5] es, en cambio, (6.17), que conserva el término de raíz cuadrada. Para \(s\) fijo y \(\delta=\alpha n^2\), la cota normalizada es \(A_s\alpha+\sqrt{(1+4A_s)\alpha}\), que tiende a cero con \(\alpha\). Esto da una cota superior explícita en dirección a la pregunta cuantitativa de [15, §7], bajo la hipótesis más débil de casi extremalidad sobre \(c_4\): la cota inferior correspondiente sobre \(\operatorname{cp}\) la implica, pues \(\operatorname{cp}\le c_4\). La Proposición 6.3a da la misma escala de raíz cuadrada a lo largo de una familia explícita, para cada \(s\) fijo. No establece constantes óptimas ni dependencia óptima respecto de \(s\).

El Teorema 6.5 recupera la conclusión estructural de [15, Teorema 1.3] y añade control simultáneo de particiones. La Proposición 6.4 junto con (6.24) recupera su aproximación (1.5) con una conclusión enunciada para \(c_4\), y conserva la expresión finita \(M(n-s)+ns-\binom{s+1}{2}\) en la banda \(4s\le n\). La prueba de (1.5) en [15] ya elige \(L=4\); esa elección no es un ingrediente nuevo aquí. Nuestro argumento de estrella con signos se atribuye explícitamente a [15, Lema 3.1]. Los añadidos aquí son el perfil finito retenido y su certificación formal. Estas conclusiones no dan distancia lineal a la familia de tamaño óptimo, constantes uniformes de estabilidad lineal para defecto creciente ni un reemplazo de [15, §6].

El término \(n/6+1/24\) de la prueba de [15, Teorema 3.3] también aparece en nuestra calibración: en ambos casos \((2n+1)^2/24=n^2/6+n/6+1/24\). Proviene de la envolvente cuadrática continua; por sí solo no es el error de piso de \(M(n)\). El perfil entero del Apéndice D.3 conserva también ese piso. Los núcleos óptimos de [15, Corolario 1.2], descritos por los enteros más cercanos a \((2n+1)/6\), coinciden con (6.4), incluido el empate cuando \(n\equiv1\pmod3\).

El preprint [5] tiene un desarrollo Lean público. Nuestra auditoría se refiere al corte propio y al veto descrito en §7; no es una afirmación de exclusividad de la formalización. Tampoco la forma aditiva para todos los órdenes distingue por sí sola los resultados: una cota eventual \(c_4\le M\), como la obtenida por la construcción de [5], implica \(c_4\le M+b\) al absorber el rango finito restante, exactamente como en §6.3.

El control cuantitativo del defecto también aparece en [5]: su lema estricto de regularización de raíz acota el coste construido por \(B_n(p)-m/9-A/2\). Por tanto, no presentamos la existencia de una estimación lineal del defecto, ni la constante \(16\), como una mejora sobre esa estimación local. Las conclusiones que destacamos son la extensión enunciada para defecto fijo, el control simultáneo de particiones irrestrictas sobre una misma raíz y las interfaces cuantitativas verificadas.

Se registra también el proyecto *Clique Partitions of Split Graphs* de Henderson, Koerts, Roberge, Spirkl y Whitman, anunciado en preparación [16]. Consultada el 27 de septiembre de 2026, la página no enlaza un manuscrito; por eso no se le atribuyen resultados ni se afirma un solapamiento.

## Apéndice A. Correspondencia formal y reproducción

### A.1. Enunciados y comprobaciones

En la tabla siguiente se omite el prefijo común `PaperIV`. Las declaraciones anteriores se comprueban en `Audit.lean` y sus targets asociados; las nuevas interfaces de estabilidad y defecto sublineal tienen entradas separadas más abajo. La identidad de fuentes se fija en `03_reproducibility/build_piv-v12-fb459343d234/SOURCE_MANIFEST.json`. Los logs de targets registran tipos elaborados y controles de axiomas. Los mapas históricos no certifican las secciones nuevas; el mapa de revisión de la versión 1.2 acompaña estos manuscritos.

| Resultado | Declaración Lean |
|:--|:--|
| Teorema A, forma aditiva | `Erdos81AllOrders.erdos81_all_orders_additive` |
| Teorema B, cota superior | `Erdos81Unconditional.erdos81_cliquePartition` |
| Teorema B, máximo | `PaperTheorems.erdos81_max_eq` |
| Teorema 3.1 | `RC01Final.rc01_uniformRoundingTarget` |
| Corolario 3.5 | `FarRegimeAllGraphs.farRegime_cliquePartition_allGraphs` |
| Dicotomía (1.5) | `HybridDichotomy.chordal_far_or_nearStructure` |
| Teorema 5.0, ventana reforzada | `NearH1LocalConstructor.exists_near_partition_paid_by_root_sharp` |
| Teorema 5.0, interfaz anterior | `NearH1LocalConstructor.exists_near_partition_paid_by_root` |
| Corolario 5.4, tamaño y densidad | `NearCriticalDichotomy.chordal_far_or_criticalRoot`, `chordal_far_or_edge_density` |
| Coeficiente cuadrático óptimo | `SharpConstantOptimality.erdos81_quadratic_constant_optimal`, `erdos81_quadratic_constant_isLeast` |
| Teorema 6.1, forma reforzada | `IntegralStability.chordal_linear_stability_sixteen` |
| Teorema 6.1, interfaz anterior | `IntegralStability.chordal_linear_stability` |
| Corolario 6.1a, número de piezas | `RootPartitionStability.chordal_partition_stability` |
| Corolario 6.1a, cotas reales conjuntas de piezas y aristas | `SublinearResearch.chordal_joint_stability_real` en `PublicationStability` |
| Identidad (6.7b) | `RootPartitionStability.sum_rootPieceDefect_eq` |
| Corolario 6.2 | `ExtremalClassification.chordal_extremal_classification` |
| Proposición D.3 | `SplitMixedGap.mixed_gap_zero` junto con la construcción acotada de `SplitCompleteSharpValue` |

**Tabla 7.** Declaraciones finales. La tabla de módulos de la Sección 7 localiza la implementación; esta tabla identifica qué enunciado se audita.

El comando único de auditoría descrito en §7 ejecuta los 19 objetivos, incluidos la raíz, los objetivos individuales de auditoría y el control de exportación. Las revisiones de Lean y sus dependencias están registradas en lean-toolchain y lake-manifest.json. Compilación, exportación pública, inspección de axiomas y correspondencia semántica son controles distintos. El nuevo congelado de fuentes se identifica localmente; las nuevas revisiones interna y adversarial de este par ampliado de fuentes y manuscritos siguen pendientes.

**Definiciones literales.** Los fragmentos siguientes reproducen las definiciones y las cabeceras de los teoremas, omitiendo sus demostraciones, no sus hipótesis. En el primer fragmento el espacio es `SimpleGraph`; en los tres siguientes es `PaperIV.FarRounding`, con \(V\) finito, igualdad decidible y adyacencia decidible para \(G\). La última definición está en `PaperIV`. Los nombres de los espacios se conservan en el archivo complementario de extractos.

```lean
def IsChordal (G : SimpleGraph V) : Prop :=
  ∀ ⦃v : V⦄ (c : G.Walk v v), c.IsCycle → 4 ≤ c.length →
    ∃ x y : V, x ∈ c.support ∧ y ∈ c.support ∧ G.Adj x y ∧ s(x, y) ∉ c.edges
```

```lean
def pairs (K : Finset V) : Finset (Sym2 V) := K.sym2.filter fun e => ¬ e.IsDiag

structure CliquePartition where
  pieces : Finset (Finset V)
  isClique : ∀ K ∈ pieces, ∀ a ∈ K, ∀ b ∈ K, a ≠ b → G.Adj a b
  two_le_card : ∀ K ∈ pieces, 2 ≤ K.card
  edgeDisjoint : ∀ K ∈ pieces, ∀ L ∈ pieces, K ≠ L → Disjoint (pairs K) (pairs L)
  covers : pieces.biUnion pairs = G.edgeFinset

def CliquePartition.size (Q : CliquePartition G) : ℕ := Q.pieces.card

def CliquePartition.OrderAtMost (Q : CliquePartition G) (r : ℕ) : Prop :=
  ∀ K ∈ Q.pieces, K.card ≤ r
```

```lean
def targetSize (n : ℕ) : ℕ := n * (n + 1) / 6
```

La división de naturales implementa el piso de \(M(n)\). El símbolo expositivo \(c_4\) designa el mínimo sobre esas particiones con `OrderAtMost 4`; el enunciado exportado no presupone una función mínimo, sino que entrega directamente una partición testigo. La cordalidad de `FarRounding` es un alias literal de la definición por ciclos anterior.

**Teoremas exportados.** En `PaperIV.Erdos81AllOrders` y `PaperIV.Erdos81Unconditional`, respectivamente, las cabeceras exactas son:

```lean
theorem erdos81_all_orders_additive :
    ∃ b : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PaperIV.FarRounding.IsChordal G →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ PaperIV.targetSize n + b
```

```lean
theorem erdos81_cliquePartition :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      PaperIV.FarRounding.IsChordal G →
        ∃ Q : CliquePartition G, Q.OrderAtMost 4 ∧ Q.size ≤ targetSize n
```

Estas cabeceras permiten comprobar el orden de cuantificadores y la cobertura exacta sin inferirlos del nombre del teorema. La auditoría adjunta no contiene `sorryAx` entre los axiomas de las declaraciones examinadas. El informe complementario distingue esa comprobación transitiva de la búsqueda textual de `native_decide` en las fuentes del proyecto y de una reconstrucción completa de las dependencias.

### A.2. Contratos intermedios de las pruebas

**Alcance de la demostración escrita.** La tabla siguiente registra derivaciones cuya exposición requiere especial atención. La revisión 1.21 desarrolla la limpieza bilateral de fibras en C.2, las cuentas de normalización y la eliminación conjunta en E.1, y las definiciones del calendario numérico en C.3. La dominación numérica de ese calendario sigue resumida, no desarrollada desigualdad por desigualdad. Las fuentes Lean congeladas contienen las pruebas correspondientes; un build exitoso verifica derivaciones formales, no la suficiencia de su exposición. La primera auditoría externa dejó abierta la rederivación matemática independiente. Las explicaciones añadidas requieren revisión y no cierran por sí mismas esos hallazgos de auditoría. Son obligaciones de revisión, no hipótesis adicionales de los teoremas.

| Ubicación | Derivación por revisar, incluidas las cuentas desarrolladas |
|:--|:--|
| §5.1, (5.4) y (5.7) | Estimaciones de masa, grado, paleta y anchura tras regularizar |
| C.2, (3.8) y (3.10) | Conteos de descarte y retención con las convenciones de partición |
| Lema 3.2 y C.1–C.2 | Cotas inferiores de fibras desde pares regulares y su normalización |
| C.3, Tabla C.1 | Dominación numérica de las constantes del nibble e iteraciones de la torre |
| E.1 | Cotas de normalización previas al constructor terminal |
| E.1, (E.2b) y (E.2d) | Estimaciones terminales y presupuesto de tres casos |
| D.1 | Construcciones de marcos Bose/Skolem que sustentan la tabla de residuos |

El nibble importado de Paper III y las construcciones clásicas de diseños conservan sus referencias indicadas. El mapa de fuentes siguiente localiza las implementaciones formales; no sustituye esas derivaciones por nombres de teoremas.

El nibble de rango acotado se reutiliza mediante `PaperIIISlackNibbleAdapter.boundedRankNibbleAt`. La construcción de las dos cuotas está en `MarkedQuotaSlackGate.slackMarkedQuotaNibbleAt_proved`; el emparejamiento de soportes triangulares y su realización física están en `MarkedQuotaPairing` y `JointTwoQuotaPhysical`. La escala conjunta de codegrado corresponde a `RC01CleanedGate.cleanedPacking_joint_codegree_le_of_served_patterns`. Los perfiles tienen masa a lo sumo \(t^2\), no uno: es la normalización física de `RC01PatternMassScale`.

Para el camino mixto, `VertexCopyMonotone.two_mul_F4_le_add` prueba la desigualdad de las dos direcciones. `VertexCopyGate` selecciona el paso y su potencial finito; `GatedTerminalSplit.exists_split_terminal_symmetrizationPath` entrega la sucesión completa. La cuenta local se construye en `NearH1WindowAccounts`, antes de importarla en `NearH1Localization`. Esta dirección de dependencias corresponde al orden lógico explicado en el Lema 4.2.

La extracción de la clique y la calibración están en `ChordalCoreMissing` y `NearH1CalibratedRoot`. `Regularization`, `RegularizationBounds` y `RegularizedRootGoal` prueban las propiedades de la raíz que utiliza `RootRegularizationBridge`. Finalmente, `NearH1PhaseI`, `RD09FactorCandidateMoments` y `RD09FactorCandidateAverage` producen las dos cuentas; `NearH1FinalAssembly` las une usando la misma primera asignación y sus enlaces ocupados. No se aplica la segunda fase a una copia independiente de los recursos.

El Teorema 5.0 tiene una forma reforzada, `NearH1LocalConstructor.exists_near_partition_paid_by_root_sharp`, que añade \(|3|R|-n|\le n/50\) al constructor físico; la interfaz anterior `exists_near_partition_paid_by_root` se conserva como corolario. La reserva reforzada de (5.15a) se conserva para ese mismo testigo en `NearStructureWitness.accounts_count_le_improved`; `IntegralStability.chordal_linear_stability_sixteen` y `RootPartitionStability.chordal_partition_stability` la utilizan sin recombinar raíces ni packings. La selección cíclica de la fase I está en `RD09PaddedL1Mass`; la última evaluación de la fase II, en `H1ImprovedConstants.l10_of_raw_rd09L2`. Los regímenes del comparador de (5.1a) se comprueban en `SplitComparatorResidual.residual_sq_le_of_near_split_universal`. La reserva (D.8) es `ReserveIdentity.targetSize_eq_baseline_add_reserve`; la contracción mejorada corresponde a `NearThresholdSensitivity.descent_threshold_maximal_barrier` y `near_threshold_binding`. Los resultados de geometría crítica están en `NearRootWindow`, `NearEdgeDensity` y `NearCriticalDichotomy`.

Las adiciones de esta revisión tienen puntos de entrada públicos separados. El Teorema C y su máximo son PaperIV.DefectExplicitPublication.rooted_defect_eventual y rooted_defect_maximum; el espacio de nombres histórico DefectSharpPublication conserva el testigo inferior y order_three_insufficient para la Proposición D.2. E35.theoremC_tower y sus variantes uniformes dan el Corolario 6.6. La cuenta completa (3.11) es E17Bridge.improved_far_loss_explicit. El Corolario 3.5 con umbral explícito es E17Bridge.ExplicitAssembly.farRegime_allGraphs_explicit. Finalmente, PaperIV.ExplicitThreshold.erdos81_sharp_explicit y erdos81_all_orders_bounded_additive dan el resultado global con la torre de §6.3. Estos nombres identifican declaraciones, no nuevas hipótesis.

El enlace B7 se audita mediante `E17.ExplicitFarAudit`. Reutiliza las constantes numéricas de `E18` y `E19`, pero construye el empaquetamiento mediante la limpieza mejorada: la auditoría exige sus dos cuentas en el cono y excluye los antiguos teoremas finales de existencia. Ese target pasó en la ejecución local combinada del corte identificado; la auditoría interna del autor revisó su log y sus hipótesis, con las limitaciones consignadas en el informe.

### A.3. Límites del resultado

No se demuestra un gap fraccionario–integral \(O(n)\) para todo cordal. Tampoco se afirma que toda demostración deba pasar por copias, regularización o un constructor particular. La cota eventual no resuelve si \(b=0\) en el Teorema A: esa igualdad conservaría el término \(n/6\) contenido en \(M(n)\), no lo eliminaría.

Las comprobaciones experimentales de órdenes pequeños no se usan como premisas. Su documentación, incluidos los requisitos de completitud y certificación, pertenece al registro de investigación separado.

La biblioteca de árboles de cliques conserva contraejemplos a formulaciones sin las hipótesis adecuadas: una hoja no equivale por sí sola a un único vértice simplicial, y las afirmaciones sobre separadores deben tratar las bolsas repetidas y los casos degenerados. Estos resultados delimitan el uso de esa biblioteca; no añaden supuestos al teorema principal.

## Apéndice B. Herramientas de construcción complementarias

### B.1. Absorción compatible con presupuesto

La construcción cercana no es la única interfaz que convierte recursos disponibles en ganancia. Un emparejamiento perfecto sobre un conjunto par \(U\), junto con un anfitrión común \(z\), absorbe todos los enlaces \(zu\) mediante triángulos: cada pareja usa dos de esos enlaces y una base de \(G[U]\).

Supongamos que
\[
d_{G[U]}(v)\ge |U|/2+t\qquad(v\in U),
\tag{B.1}
\]
con \(t\) entero no negativo. La infraestructura de Paper III [4] y su contribución de emparejamientos [9] producen \(t+1\) emparejamientos perfectos disjuntos por aristas. La razón es que borrar un emparejamiento reduce cada grado exactamente en uno; la condición de grado sigue permitiendo el siguiente hasta completar esas rondas.

Para un coste no negativo \(b(u,v)\), el promedio sobre esa familia selecciona un emparejamiento, representado por una involución \(f\), con
\[
\sum_{u\in U}b(u,f(u))
\le\frac1{t+1}\sum_{u\in U}\sum_{v\in U}b(u,v).
\tag{B.2}
\]
La suma de la izquierda está orientada por vértices. Si se interpreta como coste por pareja, debe ajustarse la convención; no se omite un factor dos por cambiar de representación.

Sea ahora \(\mathcal P\) un empaquetamiento previo y supongamos que ninguna de sus aristas cubiertas tiene ambos extremos en \(U\cup\{z\}\). Si \(z\) es adyacente a todo \(U\), los triángulos seleccionados forman con \(\mathcal P\) un único empaquetamiento y
\[
g(\mathcal P\cup\mathcal A)=g(\mathcal P)+|U|.
\tag{B.3}
\]
En efecto, hay \(|U|/2\) triángulos nuevos, cada uno de ganancia dos. Sus bases son disjuntas, sus enlaces al anfitrión no se repiten y la hipótesis de recursos libres garantiza la compatibilidad con \(\mathcal P\).

La selección y la compatibilidad se obtienen para **un mismo** certificado. Si un presupuesto \(B_{\rm abs}\) satisface
\[
\sum_{u\in U}\sum_{v\in U}b(u,v)\le(t+1)B_{\rm abs},
\]
existe un emparejamiento cuya unión física con \(\mathcal P\) es un único empaquetamiento, aumenta la ganancia exactamente en \(|U|\) y tiene coste orientado a lo sumo \(B_{\rm abs}\). Primero se elige el testigo de (B.2); después se aplica a ese testigo la compatibilidad, válida para cualquier emparejamiento bajo la libertad de recursos indicada. Este orden evita combinar dos elecciones existenciales distintas. La declaración es `SpreadAbsorptionCompatibility.exists_budgeted_compatible_spread_absorber`. Se exige que \(U\) sea no vacío y par, además de la condición de grado, la adyacencia de \(z\) y la libertad de recursos ya especificadas.

Este mecanismo no suministra automáticamente \(U\), \(z\) y los recursos libres en todo cordal. Su utilidad es ofrecer otra descarga física cuando esos datos ya están disponibles, sin confundir esa interfaz con una segunda prueba universal.

### B.2. Reservas equilibradas

Para todo grafo finito \(F\) y toda fracción real \(0\le\theta\le1\), existe \(R\subseteq E(F)\) tal que
\[
|d_R(v)-\theta d_F(v)|\le2\qquad(v\in V(F)).
\tag{B.4}
\]
Es la especialización de Beck–Fiala de `BalancedReserve.exists_balanced_reserve`. Para verla, escribimos cada arista como su conjunto de dos extremos y le asignamos peso \(\theta\). La matriz de incidencias tiene dos unos por columna. El redondeo de Beck–Fiala utilizado en la infraestructura de Paper III elige columnas enteras y desvía cada suma de fila a lo sumo dos. Las sumas fraccionarias de fila son \(\theta d_F(v)\); las enteras son \(d_R(v)\). El adaptador formal verifica que el paso de aristas a conjuntos de extremos es inyectivo y conserva exactamente esos grados.

El resultado controla cómo se distribuye una reserva, pero no garantiza que un empaquetamiento posterior la evite. Es una herramienta auxiliar, no otra prueba del teorema principal.

### B.3. Remate con cuatro anfitriones

Sea \(H\) un subgrafo de \(G\), de grado máximo a lo sumo tres. Supongamos dados cuatro vértices distintos \(z_0,z_1,z_2,z_3\), ninguno extremo de una arista de \(H\), y cada uno adyacente en \(G\) a todos esos extremos. Existe un empaquetamiento de \(|E(H)|\) triángulos que cubre todas las bases de \(H\) y tiene ganancia \(2|E(H)|\).

Vizing colorea las aristas de \(H\) con cuatro colores. Cada clase es un emparejamiento; asignemos a la clase \(i\) el anfitrión \(z_i\). Las bases son disjuntas entre clases, los anfitriones son distintos y están fuera de las bases, y cada enlace al anfitrión se usa una sola vez dentro de su clase. Los triángulos son, por tanto, disjuntos por aristas y la ganancia se cuenta exactamente. Éste es el contenido de `FourHostClosure.exists_fourHost_packing`.

La existencia de los cuatro anfitriones es una hipótesis visible. Para añadir estos triángulos a un empaquetamiento previo se necesita, además, que sus bases y enlaces estén libres; el resultado no garantiza esa libertad ni una aplicación automática a todo residuo cordal.

## Apéndice C. Prueba técnica del redondeo mixto

Los Lemas 3.2–3.4 y las ecuaciones 3.2–3.14 completan la prueba del Teorema 3.1. Se mantienen sus números para facilitar las referencias desde la rama L.

### Lema 3.2. Nibble de rango acotado con holgura, entrada de Paper III

Para cada entero \(r\ge2\) y cada \(\beta>0\), existen \(\gamma,C>0\) con la propiedad siguiente. Sean \(U\) un conjunto finito, \(\mathcal H\) una familia de subconjuntos no vacíos de \(U\), de tamaños a lo sumo \(r\), y \(z_H\ge0\) pesos tales que
\[
\sum_{H\ni v}z_H\le1,\qquad
\sum_{H\supseteq\{v,w\}}z_H\le\gamma\quad(v\ne w).
\tag{3.2}
\]
Existe una subfamilia \(\mathcal M\subseteq\mathcal H\) de miembros disjuntos dos a dos con
\[
|\mathcal M|\ge(1-\beta)\sum_{H\in\mathcal H}z_H-\beta|U|-C.
\tag{3.3}
\]
Las constantes se fijan antes de \(U,\mathcal H,z\). No se exige carga cercana a uno ni se introduce un conjunto excepcional. Ésta es la forma con holgura del nibble de Paper III, no un resultado nuevo del presente trabajo. El Apéndice A identifica su declaración y el adaptador, que sólo traduce el predicado de emparejamiento.

### Lema 3.3. Selección simultánea de masa total y marcada

Sean \(r\ge2\), \(\beta>0\) y \(\epsilon>0\). Existen \(\gamma,C>0\) tales que, para toda familia \(r\)-uniforme \(\mathcal H\) con pesos no negativos que cumplan (3.2), y toda subfamilia marcada \(\mathcal A\subseteq\mathcal H\), hay **un mismo** emparejamiento \(\mathcal M\) que satisface
\[
\begin{aligned}
|\mathcal M|&\ge(1-\beta)\sum_{H\in\mathcal H}z_H-\epsilon|U|-C,\\
|\mathcal M\cap\mathcal A|&\ge(1-\beta)\sum_{H\in\mathcal A}z_H-\epsilon|U|-C.
\end{aligned}
\tag{3.4}
\]

**Demostración.** Ponemos \(b=\min\{\beta/2,\epsilon/2\}\) y aplicamos el Lema 3.2 con rango \(r+1\) y precisión \(b\); sean \(\gamma_0,C_0\) sus constantes. Escribamos \(u=\sum_{H\notin\mathcal A}z_H\), \(a=\sum_{H\in\mathcal A}z_H\) y \(k_0=\lceil1/\gamma_0\rceil\). Añadimos dos conjuntos disjuntos de vértices auxiliares, de tamaños
\[
p=\max\{\lceil u\rceil,k_0\},\qquad
q=\max\{\lceil a\rceil,k_0\}.
\]
Cada hiperarista no marcada se extiende de todas las maneras con un vértice del primer conjunto y recibe peso \(z_H/p\); las marcadas usan el segundo y peso \(z_H/q\). Las cargas originales no cambian. Las auxiliares son \(u/p\) y \(a/q\), a lo sumo uno. Un par original conserva su codegrado; un par original–auxiliar tiene codegrado a lo sumo \(1/p\) o \(1/q\), y un par de auxiliares distintos tiene codegrado cero. Por tanto, el Lema 3.2 se aplica tomando \(\gamma=\gamma_0\).

Proyectar el emparejamiento obtenido sobre \(U\) no identifica dos de sus miembros: si lo hiciera, sus soportes originales no vacíos se intersectarían. La proyección conserva así tanto la disjunción como la cardinalidad, y deja a lo sumo \(p\) miembros no marcados. Si \(m\) es la cardinalidad proyectada, tenemos
\[
m\ge(1-b)(u+a)-b(|U|+p+q)-C_0,
\qquad |\mathcal M\cap\mathcal A|\ge m-p.
\]
Ahora \(p\le u+1+k_0\), \(q\le a+1+k_0\), y sumar las cargas da \(r(u+a)\le|U|\). Para la primera cuota, el término \(b(p+q)\) consume a lo sumo \(b(u+a)+b(2+2k_0)\), y \(2b\le\beta\). Para la segunda, después de restar \(p\), los términos dependientes de \(u+a\) están acotados por \(2b(u+a)\le b|U|\). Junto con \(2b\le\epsilon\), ambas cuotas siguen con
\(C=C_0+1+k_0+b(2+2k_0)\).

### Lema 3.4. Selector mixto físico

Para \(0<\beta\le1\) y \(\epsilon>0\), existen \(\gamma,C,D>0\) tales que lo siguiente vale para cualquier grafo. Sea \(x\) un empaquetamiento fraccional mixto factible, sean \(t_3=\sum_Tx_T\) y \(t_4=\sum_Qx_Q\), y supongamos \(t_3\ge C\) y
\[
\sum_{K:\ e,f\in E(K)}x_K\le\gamma\qquad(e\ne f).
\tag{3.5}
\]
Entonces existe un empaquetamiento físico \(\mathcal P\) cuya ganancia satisface
\[
g(\mathcal P)\ge(1-\beta)(2t_3+5t_4-6)
 -5\epsilon\binom{n+1}{2}-5D.
\tag{3.6}
\]
La cantidad \(\binom{n+1}{2}\) es el tamaño del universo formal de parejas no ordenadas, incluidas las diagonales de peso cero. Puede usarse esa cota sin identificarla con \(e(G)\).

**Demostración.** Trabajamos sobre los recursos, es decir, las aristas. Se agrupan de dos en dos los soportes triangulares disjuntos; una pareja \(T,T'\) recibe peso \(x_Tx_{T'}/t_3\), sumando las representaciones de un mismo soporte. La masa total de las parejas es al menos \((t_3-3)/2\): para cada triángulo, la masa de los que lo intersectan es a lo sumo tres, por las capacidades de sus tres aristas. La carga de una arista no aumenta. El codegrado de las parejas se acota por el codegrado triangular original más \(3/t_3\), separando si los dos recursos pertenecen al mismo miembro de la pareja o a miembros distintos.

Se obtiene una familia 6-uniforme junto con los soportes de \(K_4\). Marcamos estos últimos. Las dos familias no se confunden: dos triángulos contenidos en un mismo \(K_4\) comparten una arista y no pueden formar una pareja disjunta. Si \(\gamma_0\) es la tolerancia del Lema 3.3 para rango seis, elegimos \(\gamma=\gamma_0/2\) y \(C=6/\gamma_0\); entonces \(3/t_3\le\gamma_0/2\). Se verifican conjuntamente las cargas y codegrados del sistema de seis recursos.

Sean \(m\) el número total de soportes seleccionados y \(b_4\) el de los marcados. Al deshacer las parejas, la ganancia es \(4m+b_4\): una pareja da dos triángulos, con ganancia cuatro; un marcado da ganancia cinco. Aplicamos cuatro veces la primera cuota de (3.4) y una vez la segunda. La masa de parejas aporta al menos \(2t_3-6\), y la masa marcada aporta \(5t_4\). Las pérdidas se suman a \(5\epsilon|U|+5D\), lo que demuestra (3.6). La proyección conserva las copias reales y la disjunción de sus aristas.

### C.1. Limpieza, selección y realización

La prueba comienza con una partición de regularidad de \(V(G)\). Se descartan las contribuciones que no admiten una realización transversal controlada: pares irregulares, pares de densidad pequeña y perfiles con masa insuficiente. Un perfil registra las clases que visita una copia. Su tipo conserva si la copia original es un triángulo o un \(K_4\).

El objeto auxiliar de selección utiliza las aristas de \(G\) como recursos. Dos copias que comparten una arista compiten por el mismo recurso, aunque sus etiquetas de perfil sean distintas. Por eso las cotas de codegrado deben verificarse para la familia conjunta; no basta redondear cada perfil por separado. Al olvidar las marcas de una selección compatible se obtiene un empaquetamiento de copias reales.

La parte algebraica puede aislarse sin perder ese significado. Sean \(S\) la ganancia retenida tras la limpieza y \(L\) su pérdida, de modo que \(w(x)-L\le S\). Si la realización proporciona
\[
(1-u-v)S-g(\mathcal P)\le\zeta n^2,
\]
con \(u+v\ge0\) y \(S\le5n^2/6\), entonces
\[
w(x)-g(\mathcal P)
\le L+\left(\zeta+\frac56(u+v)\right)n^2.
\tag{3.7}
\]
Para comprobarlo, se escribe la diferencia como
\[
\begin{aligned}
w(x)-g(\mathcal P)
={}&(w(x)-L-S)+((1-u-v)S-g(\mathcal P))\\
&+L+(u+v)S.
\end{aligned}
\]
El primer sumando es no positivo; los otros tres tienen exactamente los presupuestos de (3.7). Esta separación evita cobrar dos veces la misma limpieza.

La realización con masa triangular suficiente y el caso de masa pequeña se unen antes de fijar el umbral final. En este último paso aparecen presupuestos de la forma \(15C\) y \(13C+\zeta n^2\). Las condiciones
\[
30C\le\xi n^2,\qquad 2\zeta\le\xi
\]
controlan ambos por \(\xi n^2\). El entero \(C\) y las constantes de selección se eligen uniformemente, no a partir del grafo reducido de una instancia particular.

El paso de selección puede describirse de manera concreta. La limpieza no crea copias abstractas: para cada perfil activo \(H\) conserva una fibra de copias reales de \(G\). A esa fibra se le asigna un volumen \(\operatorname{vol}(H)\) y un presupuesto \((1+u)\operatorname{vol}(H)\). Los lemas de retención demuestran
\[
(1-v)\operatorname{vol}(H)
\le |\operatorname{cleanFiber}(H)|.
\tag{3.8}
\]
Por tanto, la masa que entra al selector ya ha pagado los patrones descartados; no se los vuelve a cobrar al final.

Sobre el único conjunto de recursos \(E(G)\) se forma entonces un hipergrafo: cada triángulo aporta sus tres aristas y cada \(K_4\), sus seis. El Lema 3.4 realiza la selección después de agrupar los soportes triangulares en parejas. Las marcas distinguen los \(K_4\), y el Lema 3.3 conserva simultáneamente las dos cuotas del sistema auxiliar. Una vez deshechas las parejas, si hay \(a\) copias físicas en total y \(b\) de ellas son \(K_4\), la ganancia puede escribirse también como
\[
2(a-b)+5b=2a+3b.
\tag{3.9}
\]
Esta identidad concuerda con \(4m+b_4\) antes de deshacer las parejas. Las variables \(a\) y \(m\) cuentan objetos diferentes; no se aplica el nibble no ponderado directamente a la unión de soportes de tamaños tres y seis.

Queda por verificar (3.5) para el empaquetamiento limpio. La derivación que sigue suma sobre perfiles antes de aplicar el Lema 3.4. Así se controla el recurso físico compartido, no sólo la contribución aislada de cada marca.

Una jerarquía explícita del desarrollo toma
\[
s=\min\{\xi/4500,1/10\},\qquad
d=u=v=s,\qquad \delta=s^{21}/2208.
\]
Después se fija el límite del número de clases de regularidad y, finalmente, un único \(N_\xi\) que absorbe todos los términos restantes. No se reemplaza \(\xi\) por \(1/n\).

El Apéndice A identifica las declaraciones correspondientes a estos pasos. La demostración probabilística de la entrada de nibble se reutiliza de Paper III [4]; los Lemas 3.3–3.4 explican la adaptación que convierte su emparejamiento en el empaquetamiento mixto de (3.1).

### C.2. Qué se descarta y por qué el umbral es uniforme

Conviene distinguir tres escalas: el orden \(n\) del grafo, el número \(k\) de clases de la partición regular y el tamaño \(t\) de cada clase no excepcional. El número de clases satisface \(k_0\le k\le B\), donde \(B\) depende de la precisión, no del grafo. Un perfil es el conjunto de tres o cuatro clases visitadas por una copia transversal. Escribamos \(\psi_H\) para la masa fraccional transferida al perfil \(H\), y
\[
S=\sum_{H\text{ activo}}g(H)\psi_H.
\]
«Activo» significa que el perfil ha superado los filtros de densidad y de masa; no se normaliza cada perfil como si dispusiera por separado de todas las aristas.

El conteo mejorado distingue las copias dañadas de los perfiles ligeros. Sean \(N_3,N_4\) los números de perfiles posibles de cada orden. Entonces
\[
w(x)-S\le L,\qquad
L=3\left(3\delta+\frac1{k_0}+d\right)n^2
  +(N_4+2N_3)\theta.
\tag{3.10}
\]
Aquí \(\delta\) es la precisión de regularidad, \(d\) el umbral de densidad y \(\theta\ge0\) el umbral de masa por perfil. La primera cuenta se obtiene sobre las aristas descartadas. Un triángulo dañado se retira y pierde ganancia dos. Si un \(K_4\) contiene exactamente una arista descartada, se conserva uno de sus triángulos que evita esa arista: la pérdida es \(5-2=3\). Si contiene al menos dos, se retira entero y se cobra \(5\le3\cdot2\). Por las capacidades, sumar estos cargos cuesta a lo sumo tres veces el número de aristas descartadas. Las copias conservadas usan subconjuntos de los recursos originales, por lo que no aumentan sus cargas.

La segunda cuenta usa una operación distinta. Un \(K_4\) de peso \(x\), perteneciente a un perfil ligero, se sustituye por sus cuatro caras triangulares de peso \(x/2\). Cada arista aparece en dos caras: su carga sigue siendo \(x\), mientras que la ganancia pasa de \(5x\) a \(4x\). El coste total es a lo sumo \(N_4\theta\). A continuación se agregan las contribuciones a cada perfil triangular y sólo después se descartan los perfiles triangulares ligeros, con coste a lo sumo \(2N_3\theta\). Agregar antes de descartar es esencial: una misma cara puede recibir masa de varios perfiles de orden cuatro.

El enlace con la realización física da, para \(\zeta>0\) y \(n\ge N_E(\zeta)\),
\[
\begin{aligned}
w(x)-g(\mathcal P)\le{}&
\left(9\delta+\frac3{k_0}+3d+\zeta
             +\frac56(u+v)\right)n^2\\
&+(N_4+2N_3)\theta .
\end{aligned}
\tag{3.11}
\]
Se suponen \(\delta,d,\theta\ge0\), \(u+v\ge0\), y \(1\le k_0\le k\). El umbral \(N_E\), definido en C.3, se elige antes del grafo. La cuenta no deja como hipótesis la existencia de un empaquetamiento favorable: el redondeador se aplica al empaquetamiento fraccional reconstruido por las dos operaciones anteriores. Puede utilizar una partición regular auxiliar; no se afirma que todas las fases físicas conserven una partición suministrada de antemano.

La mejora de (3.10) es, por tanto, parte de una cota completa de pérdida, no sólo un ahorro aislado en las copias. El calendario numérico de C.3 sigue siendo conservador: la reducción del coeficiente no implica por sí sola una reducción de la torre allí indicada.

Falta aún explicar por qué el redondeo físico puede realizarse simultáneamente. El codegrado pertinente es la masa de copias que contienen **dos aristas físicas dadas**, sumada sobre todos los perfiles y ambos tipos. Aunque cada perfil por separado tenga buen comportamiento, el mismo par de recursos podría aparecer en varios perfiles. Por eso la estimación formal se hace antes de olvidar las marcas. En la notación de la prueba, con
\[
a_3=d^3-3\delta>0,\qquad a_4=d^6-6\delta>0,
\]
el control conjunto requiere una escala de la forma
\[
k_3a_4+k_4a_3\le\gamma a_3a_4t,
\tag{3.12}
\]
donde \(k_3,k_4\) acotan los números de perfiles activos de cada tipo. Veamos la cuenta que conduce a esa condición. Todo perfil activo sirve algún par de clases. Las copias transferidas consumen aristas de ese par y sus capacidades suman a lo sumo \(t^2\); por tanto, \(\psi_H\le t^2\). No sería correcto sustituir esta cota por \(\psi_H\le1\).

El peso de cada copia limpia del perfil es \(\psi_H/b_H\), donde \(b_H=(1+u)\operatorname{vol}(H)\). Las estimaciones de conteo dan \(b_H\ge a_3t^3\) para triángulos y \(b_H\ge a_4t^4\) para \(K_4\). Fijemos dos aristas físicas distintas. En un perfil triangular hay a lo sumo una copia que las contiene. En un perfil de \(K_4\) hay a lo sumo \(t\): si las aristas comparten un extremo fijan tres vértices y sólo queda elegir el cuarto; si no, fijan los cuatro. Así, las contribuciones respectivas son a lo sumo \(1/(a_3t)\) y \(1/(a_4t)\). Sumando sobre todos los perfiles,
\[
\sum_{K:e,f\in E(K)}x_K^{\rm limpio}
\le\frac{k_3}{a_3t}+\frac{k_4}{a_4t}
=\frac{k_3a_4+k_4a_3}{a_3a_4t}\le\gamma.
\tag{3.13}
\]
Esto demuestra la condición conjunta de codegrado del Lema 3.4. La factibilidad en una arista física requiere otro argumento: una cota inferior para el volumen de la fibra no basta para acotar su carga por uno. La limpieza retira las copias que pasan por raíces con una desviación grande a cualquiera de los dos lados de su media. Aquí una raíz es una arista de un par de clases fijado, no la raíz clique de la construcción cercana.

Fijemos un perfil activo \(H\), llamemos \(\mathcal F_H\) a su fibra inicial y pongamos \(V_H=|\mathcal F_H|\). Para un par \(q\) de sus clases, sean \(E_q\) las aristas reales de ese par y \(d_q=\max\{1,|E_q|\}\). Si \(c_{H,q}(e)\) cuenta las copias iniciales que pasan por \(e\in E_q\), su valor de referencia es \(A_{H,q}=V_H/d_q\). Esta referencia depende del par. Retiramos toda copia que use una arista con \(|c_{H,q}(e)-A_{H,q}|>uA_{H,q}\), en cualquiera de los tres o seis pares del perfil.

Una arista eliminada por esta prueba no pertenece a ninguna copia superviviente. Por cualquier otra pasan a lo sumo \((1+u)A_{H,q}\) copias. Como cada copia superviviente recibe peso \(\psi_H/((1+u)V_H)\), el perfil contribuye a la carga de la arista a lo sumo \(\psi_H/d_q\). La restricción de capacidad transferida es \(\sum_{H\text{ que sirve }q}\psi_H\le d_q\); al sumar las contribuciones, la carga total es a lo sumo uno. El denominador es válido porque una fibra activa tiene volumen positivo. Ésta es la prueba de factibilidad de RC01CleanFiber, después del control bilateral de RC01DeviationCleanup.

Falta comprobar cuánto cuesta esta eliminación. Para un par, las cotas del segundo momento enraizado acotan el número \(B_q\) de raíces malas por \(B_qu^2a_3^2\le11\delta t^2\) en triángulos y \(B_qu^2a_4^2\le23\delta t^2\) en cliques de orden cuatro. Por una raíz pasan a lo sumo \(t\) triángulos iniciales o \(t^2\) cliques de orden cuatro. Sumando sobre los tres o seis pares, el número de copias retiradas es a lo sumo \(33\delta t^3/(u^2a_3^2)\) o \(138\delta t^4/(u^2a_4^2)\), respectivamente. Contar una copia más de una vez sólo aumenta estas cotas superiores. Al compararlas con las cotas inferiores de las fibras, la proporción retirada es a lo sumo \(v\) si \(33\delta\le vu^2a_3^3\) y \(138\delta\le vu^2a_4^3\).

El calendario de C.3 satisface ambas desigualdades: tomamos \(d=u=v=a\), usamos \(\delta=a^{21}/2208\) y observamos que \(a_3\ge a^3/2\), \(a_4\ge a^6/2\) para \(0<a\le1/10\). Por ejemplo, \(138\delta=a^{21}/16\le a^{21}/8\le vu^2a_4^3\). Quedan, por tanto, al menos \((1-v)V_H\) copias. Su peso total es al menos \((1-v)/(1+u)\ge1-u-v\) veces la masa transferida, como requiere (3.8). Así se verifican por separado la factibilidad, la masa retenida y el codegrado conjunto; ninguna de estas propiedades se deduce sólo de las otras dos.

El teorema marcado entrega entonces un empaquetamiento siempre que la masa triangular exceda una constante \(C\) y
\[
12+10D\le\zeta n^2,
\tag{3.14}
\]
donde \(D\) es la pérdida aditiva del selector. Si la masa triangular es menor que \(C\), la rama de masa pequeña la sustituye mediante la construcción triangular para masa pequeña; sus dos pérdidas son las cantidades \(15C\) y \(13C+\zeta n^2\) citadas arriba. Así, las ramas cubren todos los casos y el umbral final absorbe \(C,D\) una sola vez.

El orden de las elecciones importa tanto como las desigualdades. Primero se fija la precisión de salida. El lema de selección proporciona sus constantes uniformemente en el tipo de marcas y en \(n\). Después se eligen \(\delta,k_0\), se obtiene la cota de regularidad \(B\), y finalmente se toma \(N_\xi\) suficientemente grande para la regularidad, el tamaño de clase exigido por (3.12) y los términos aditivos. Éste es el contenido del ensamblaje uniforme. En particular, el número \(4\cdot10^{12}\) de la construcción cercana no controla este umbral de regularidad.

### C.3. Un calendario explícito y su propagación

Para una precisión racional \(\xi>0\), fijamos primero
\[
a=\min\{\xi/4500,1/10\},\quad
\delta=a^{21}/2208,\quad z=\min\{\xi/10,1\},\quad
k_0=\lceil1500/\xi\rceil+1.
\]
Sea \(B\) la cota del lema de regularidad con parámetros \(\delta/8,k_0\). El selector marcado, con precisión \(z\), proporciona constantes explícitas \(\gamma_*>0,C_*\ge0,D_*\ge0\). Escribamos
\[
\gamma=\frac1{\lceil1/\gamma_*\rceil},\qquad C=\lceil C_*\rceil,\qquad
a_3=a^3-3\delta,\quad a_4=a^6-6\delta.
\]
La elección de \(\delta\) garantiza \(a_3,a_4>0\). En estas expresiones, los techos son enteros no negativos. Un umbral que sirve es
\[
\begin{split}
N_E(\xi)=1+\max\biggl\{&
k_0,\ \left\lceil B/\delta\right\rceil,\
\left\lceil(12+10D_*)/z\right\rceil,\\
&\left\lceil\frac{4B^5(a_3+a_4)}{\gamma a_3a_4}\right\rceil,\
\left\lceil\frac{50(1+2C)}{\xi}\right\rceil
\biggr\}.
\end{split}
\tag{C.1}
\]
Los cinco términos tienen funciones distintas: permiten construir la partición, controlar su parte excepcional, pagar la pérdida aditiva del selector, imponer el codegrado conjunto y tratar la masa triangular pequeña. No dependen de \(G\).

Conviene explicar el enlace con la limpieza de C.2. Se aplica esa limpieza al empaquetamiento de entrada, conservando simultáneamente una cuenta de valor y otra de masa triangular. Si esta última es grande, ambas cuentas permiten utilizar el selector con las constantes de (C.1). Si es pequeña, se aplica la construcción de masa pequeña descrita después de (3.14). El calendario domina las pérdidas de ambas ramas y entrega
\[
w(x)-g(\mathcal P)\le\xi n^2
\qquad(n\ge N_E(\xi))
\tag{C.2}
\]
para todo grafo y todo empaquetamiento fraccional mixto factible. Éste es el enlace numérico que permite emplear la cuenta mejorada (3.11) sin mantener una hipótesis de realización pendiente.

Para el Corolario 3.5 se toma \(\xi=\eta/2\). Basta, por tanto, \(N_{\rm lejano}(\eta)=N_E(\eta/2)\). En la precisión usada por el ensamblaje cordal, \(\eta_0=10^{-16}\), los parámetros son
\[
a=(9\cdot10^{19})^{-1},\qquad
\delta=\frac1{2208(9\cdot10^{19})^{21}},\qquad
z=(2\cdot10^{17})^{-1},\qquad k_0=3\cdot10^{19}+1.
\]
Las tres cantidades enteras del selector que deben absorberse son
\[
G_1=\lceil1/\gamma_*\rceil,\quad G_2=\lceil C_*\rceil,\quad
G_3=\lceil2\cdot10^{17}(12+10D_*)\rceil.
\]
Para ver cómo se absorben, fijemos \(\beta_0=(64\cdot10^{18})^{-1}\). Damos el calendario explícitamente, para precisar el significado de las constantes de la Tabla C.1. Para \(r\ge2\) y \(0<\beta\le1/2\), todas las cantidades siguientes se evalúan en \((r,\beta)\), salvo que se muestre otro argumento:
\[
\begin{gathered}
a_T=(r-1)/r,\quad L_T=-\log\beta,\quad M_T=16rL_T+1,\\
\gamma_T=\min\{1/8,e^{-8M_T-1}/32\},\quad
\epsilon_T=4a_T\gamma_T,\quad q_T=1-a_T\gamma_T,\quad
T_T=\lceil M_T/\gamma_T\rceil,\\
G_T=(2+r/(\epsilon_T\gamma_T))^2,\quad
\eta_T=\frac{\beta}{8(2G_T)^{T_T}},\quad
\ell_T=\frac34q_T^{T_T}.
\end{gathered}
\]
El número de rondas es \(T_T\); \(\eta_T\) acota la fracción excepcional y \(\ell_T\) es la escala de grado conservada. Para pasar al selector, definimos
\[
\begin{gathered}
D_{0,T}=\frac{256r}{(\beta/2)^2\gamma_T}+\frac{96}{\epsilon_T}+4,\qquad
c_{0,T}=\frac{\eta_T\epsilon_T^2\gamma_T(\beta/2)^2}{16384r},\\
\mu_T=\min\{8\gamma_T,c_{0,T}\ell_T,[2(D_{0,T}+1)]^{-1},1/2\},\qquad
d_{0,T}=\max\{1,D_{0,T}/\ell_T\},\\
D_S(r,\beta)=1+\max\{\lceil d_{0,T}\rceil,\lceil4(1+r^2)/\mu_T\rceil\},\\
\gamma_R(r-1,\beta)=\min\{1/D_S(r,\beta),\mu_T/4,1\}.
\end{gathered}
\]
Son las definiciones de E18.NibbleSchedule, NibbleOracle y NibbleChain; los dos últimos usan \(\min\{\beta,1/2\}\) para una precisión positiva general, que coincide con \(\beta\) en el rango indicado. El rango aumenta de seis a siete al convertir el selector en la entrada del nibble. Sustituir \(r=7\) y \(\beta=\beta_0\) da las desigualdades registradas abajo. Son cotas demostradas para este calendario, no aproximaciones decimales ni elecciones libres de las constantes del selector.

| Paso | Cotas verificadas |
|:--|:--|
| Calendario | \(L_T(\beta_0)\le46,\quad M_T(7,\beta_0)\le5153\) |
| Cadena intermedia | \(\gamma_T(7,\beta_0)\ge2^{-59485},\quad T_T(7,\beta_0)\le2^{59498}\) |
| Selector | \(D_S(7,\beta_0)\le2^U,\quad \gamma_R(6,\beta_0)\ge2^{-U}\) |
| Tres enteros finales | \(G_1\le2^{U+2},\quad G_2\le2^{U+3},\quad G_3\le2^{U+67}\) |

**Tabla C.1.** Absorción numérica del selector. Aquí \(U=2^{59516}+191432\); las etapas corresponden a los módulos E19.ScheduleBounds, E19.ChainBounds y E19.GateBounds.

Como \(U+67\le2^{59517}\), las cuatro filas implican \(G_i\le2^{\,2^{59517}}\). La recurrencia de regularidad, iterada \(h\) veces con el valor de §6.3, domina esas tres cantidades ya tras sus dos primeras iteraciones. Al absorber después los cinco términos de (C.1), resulta
\[
N_{\rm lejano}(\eta_0)\le T(h+7).
\tag{C.3}
\]
La comparación es simbólica: no exige construir un entero con esa cantidad de cifras. Tampoco supone un resultado de diseños resolubles ni un régimen de separadores pequeños. Así, (C.3) vale para la rama lejana de **todo grafo**; la cordalidad se usa al unirla a la rama cercana en §6.

El umbral también admite una cota uniforme en el margen. Para todo racional \(0<\eta\le1\), la misma elección de parámetros satisface
\[
N_{\rm far}(\eta)\le
T\!\left(\left\lceil\frac{c_{\rm poly}}{\eta^{105}}\right\rceil\right),
\qquad c_{\rm poly}=4\cdot17664^5\cdot9000^{105}+3006.
\tag{C.4}
\]
Éste es E35.NfarE_le_tower_poly. Acota los parámetros de selección, regularidad y limpieza antes de elegir el grafo; no se permite que \(\eta\) dependa del grafo de entrada una vez fijado el umbral. La cota numérica especializada de §6.3 sigue siendo válida. La fórmula (C.4) es la comparación adicional necesaria para la banda exacta de defecto creciente del Corolario 6.6.

## Apéndice D. Grafos completos e identidades del comparador

### D.1. El grafo completo a todo orden

El objetivo sin término aditivo puede verificarse en una familia infinita sin recurrir al umbral eventual. Este complemento se formaliza en `ThreeRegime.CompleteStateAllOrders`; no interviene en la prueba de los Teoremas A y B.

**Proposición D.1.** Para todo entero \(n\ge0\), existe una partición de \(K_n\) en piezas de orden a lo sumo cuatro con a lo sumo \(M(n)\) piezas.

**Demostración.** Para \(n=0,1\) sirve la partición vacía. Para \(n\ge2\), basta construir un empaquetamiento mixto \(\mathcal P\) con
\[
n(n-2)\le3g(\mathcal P).
\tag{D.1}
\]
En efecto, su completación satisface
\[
|Q|=\binom n2-g(\mathcal P)
\le\frac{n(n-1)}2-\frac{n(n-2)}3
=\frac{n(n+1)}6.
\tag{D.2}
\]
Como \(|Q|\) es entero, se obtiene el piso \(M(n)\).

La construcción usa dos marcos de bloques sobre \((\mathbb Z/M\mathbb Z\times\mathbb Z/3\mathbb Z)\sqcup\{\infty\}\). Para \(M\) impar se emplea el marco de Bose [19]; para \(M\) par, el de Skolem [20]. El módulo `HalvingFrames` les asigna un dueño único a cada arista cubierta y demuestra que sus bloques son triángulos o \(K_4\). En el marco impar pueden sustituirse las columnas triangulares por columnas \(K_4\) que contienen \(\infty\). El ensamblaje de los seis residuos es el siguiente; los nombres indican la construcción implementada, no una atribución nueva de los diseños clásicos.

| Orden \(n\) | Bloques empleados | Paso final |
|:--|:--|:--|
| \(3M\), \(M\) impar | Bose triangular | Cubre \(K_n\) |
| \(3M-1\), \(M\) impar | Bose triangular sobre \(n+1\) vértices | Borrar un vértice y sus bloques |
| \(3M+1\), \(M\) par, \(M\ge2\) | Skolem triangular | Cubre \(K_n\) |
| \(3M\), \(M\) par, \(M\ge2\) | Skolem triangular sobre \(n+1\) vértices | Borrar un vértice y sus bloques |
| \(3M+1\), \(M\) impar | Bose con \(M\) columnas \(K_4\) | Cubre \(K_n\) |
| \(3M+2\), \(M\) impar | La construcción de la fila anterior | Añadir un vértice; completar sus aristas como \(K_2\) |

**Tabla 8.** Construcciones para el caso completo. En la última fila el vértice añadido no participa en el empaquetamiento; no es un vértice aislado del grafo completo.

Verifiquemos la ganancia que necesita el ensamblaje. Para bloques mixtos disjuntos, si \(E_{\rm cub}\) es su conjunto de aristas cubiertas y \(b_4\) su número de \(K_4\), las contribuciones dos y cinco dan
\[
3g(\mathcal P)=2|E_{\rm cub}|+3b_4.
\tag{D.3}
\]
Las filas que cubren \(K_n\) cumplen (D.1), pues \(2|E_{\rm cub}|=n(n-1)\ge n(n-2)\). Si se borra un vértice de una descomposición triangular de \(K_{n+1}\), ese vértice pertenece a \(n/2\) triángulos: sus \(n\) aristas incidentes se agrupan de dos en dos. Quedan \(n(n+1)/6-n/2=n(n-2)/6\) triángulos; su ganancia verifica (D.1) con igualdad. Finalmente, en la última fila se cubren las aristas de \(K_{3M+1}\) con \(M\) bloques \(K_4\), de modo que
\[
3g(\mathcal P)=(3M+1)3M+3M=(3M+2)3M=n(n-2).
\tag{D.4}
\]
Las seis filas agotan los residuos módulo seis para \(n\ge2\). El teorema `exists_packing` reúne estas cuentas y `complete_state_closes` aplica la completación (D.2).

Este resultado prueba \(b=0\) sobre los grafos completos, no sobre todos los cordales pequeños. En una clase de congruencia, el uso de piezas de orden cuatro es necesario.

**Proposición D.2.** Si \(n\equiv4\pmod6\), toda partición de \(K_n\) en piezas de orden a lo sumo tres tiene más de \(M(n)\) piezas.

**Demostración.** Sean \(a\) el número de piezas \(K_2\) y \(t\) el de triángulos. Contar aristas y piezas da
\[
a+3t=\binom n2,\qquad |Q|=a+t=\frac{\binom n2+2a}{3}.
\tag{D.5}
\]
Cada vértice tiene grado impar \(n-1\). Los triángulos incidentes contribuyen de dos en dos, de modo que el vértice debe pertenecer al menos a una pieza \(K_2\). Por tanto, \(2a\ge n\), y
\[
|Q|\ge\frac{\binom n2+n}{3}=\frac{n(n+1)}6.
\]
Para \(n=6r+4\), la última cantidad tiene parte fraccionaria \(1/3\). Como \(|Q|\) es entero, \(|Q|\ge M(n)+1\).

Por ejemplo, \(K_{10}\) requiere al menos 19 piezas si sólo se permiten aristas y triángulos, mientras que la Proposición D.1 da a lo sumo \(M(10)=18\) cuando también se permite \(K_4\). La restricción de orden cuatro en la cota aguda no puede reemplazarse uniformemente por orden tres. Esta obstrucción no se extiende al residuo cinco.

### D.2. Igualdad de óptimos mixtos en grafos completo-split

**Proposición D.3 (gap mixto nulo en completo-split).** Sea \(S=K_k\vee I_h\), con \(2\le k\le h\), y sea \(W(S)\) la máxima ganancia de un empaquetamiento mixto físico. Entonces
\[
W^*(S)=W(S)=2\binom k2.
\tag{D.6}
\]
Para justificar la cota fraccional, sea \(j(K)\) el número de aristas del núcleo que contiene una pieza mixta \(K\). Una clique de \(S\) tiene a lo sumo un anfitrión. Un triángulo con anfitrión tiene \(j(K)=1\) y ganancia dos; un \(K_4\) con anfitrión tiene \(j(K)=3\) y ganancia cinco. Las piezas enteramente en el núcleo también satisfacen \(g(K)\le2j(K)\). Así, para todo empaquetamiento fraccional factible \(x\),
\[
\begin{aligned}
w(x)&\le2\sum_K j(K)x_K\\
&=2\sum_{e\in E(K_k)}\sum_{K:e\in E(K)}x_K
\le2\binom k2.
\end{aligned}
\tag{D.7}
\]
La última desigualdad usa la capacidad uno de cada arista del núcleo. La construcción de la Sección 6.1 contiene un triángulo por base interna y alcanza esa ganancia. Como todo empaquetamiento entero define uno fraccional, quedan probadas las dos igualdades de (D.6). El resultado formal es `SplitMixedGap.mixed_gap_zero`, junto con la construcción acotada de `SplitCompleteSharpValue`.

La conclusión es una igualdad de valores óptimos en esta familia y bajo \(2\le k\le h\). No afirma que todos los vértices del politopo fraccional sean enteros, ni extiende el gap cero a cualquier grafo split.

### D.3. Reserva exacta por desplazamiento del núcleo

La identidad (6.3) permite conservar también el piso. Para enteros \(0\le k\le n\) con \(\binom k2\le k(n-k)\), definamos
\[
d_{n,k}=\begin{cases}n-3k,&3k\le n,\\3k-n-1,&3k>n.\end{cases}
\]
Entonces la reserva del perfil completo-split es exactamente
\[
M(n)=B_n(k)+M(d_{n,k}).
\tag{D.8}
\]
En efecto, en las dos ramas \(d_{n,k}(d_{n,k}+1)=(n-3k)(n-3k+1)\). Al sustituirlo en (6.3), dividir por seis y tomar pisos, el entero \(B_n(k)\) sale del piso y se obtiene (D.8). La hipótesis sobre \(\binom k2\) deja \(B_n(k)\) no negativo, tal como lo representa la declaración formal en naturales.

Esta forma identifica el margen disponible sin reemplazar \(M\) por su envolvente racional. En particular, la reserva es cero exactamente cuando \(d_{n,k}\le1\), lo que recupera los núcleos óptimos de (6.4). No proporciona por sí sola una partición de un cordal arbitrario: cuantifica el presupuesto del perfil con el que se compara la construcción.

## Apéndice E. La extensión a defecto fijo

El Teorema C no se obtiene sustituyendo «cordal» por «defecto \(s\)» en todos los lemas de estabilidad. Su prueba usa un terminal con grado mínimo, un constructor sobre recursos reales y un argumento que elimina una constante aditiva.

### E.1. Constructor y cuentas

La localización y la normalización producen \(V=S\sqcup H\sqcup W\): \(S\) es la región de bases, \(H\) la de anfitriones y \(W\) la de excepciones. No se exige que todas las parejas de \(S\) sean aristas. El constructor sólo hospeda las aristas reales de \(G[S]\).

Primero se absorben los vértices \(w\in W\). Para cada uno se elige un matching \(M_w\) de enlaces \(ah\) entre \(S\) y \(H\), con ambos extremos adyacentes a \(w\); cada enlace da el triángulo \(wah\). La selección equilibrada controla el consumo de radios por fila y columna. Las fases siguientes excluyen los radios ocupados.

En la primera fase, coloreamos las aristas de \(G[H]\) con \(k\) colores y equilibramos las clases para que tengan tamaño a lo sumo \(q\). Promediar desplazamientos cíclicos de su asignación a anfitriones en \(S\) da \(t_I\) bases hospedadas con \(2t_I\ge e(G[H])\). En la segunda fase, el hospedaje por listas realiza todas las aristas de \(G[S]\) usando los radios restantes. La construcción diádica aplica Galvin a problemas bipartitos auxiliares, no a un grafo arbitrario.

Entre las condiciones comprobadas antes de las fases están
\[
\begin{gathered}
d_{\max}(G[H])+1\le k,\quad |S|\le k\le2(|S|-2\sigma),\quad
q\ge\left\lceil e(G[H])/k\right\rceil,\\
3\lceil|S|/2\rceil+2\tau+4q\le |H|+2.
\end{gathered}
\tag{E.1}
\]
Aquí \(d_{\max}\) denota el grado máximo. Los parámetros \(\sigma,\tau\) acotan ausencias por fila y columna, incluidas las reservas para \(W\); no se eligen después de construir la partición. Las tres familias de triángulos son disjuntas por aristas. Su completación satisface
\[
|Q|+2\left(\sum_{w\in W}|M_w|+t_I+e(G[S])\right)=e(G).
\tag{E.2}
\]
Desarrollamos ahora esta cuenta. Escribamos \(c=|S|\), \(b=|H|\) y \(t_W=|W|\), de modo que \(n=c+b+t_W\). Para cada \(w\in W\), sean \(u_w=|N(w)\cap S|\), \(v_w=|N(w)\cap H|\), y pongamos
\[
d_W=\sum_{w\in W}\deg(w),\qquad
m_W=\sum_{w\in W}\min(u_w,v_w).
\]
Sea \(D\) una cota para el número de enlaces ausentes entre \(S\) y \(H\), y elijamos un entero \(L\ge\lfloor\sqrt D\rfloor\). La absorción da
\(\min(u_w,v_w)\le |M_w|+t_W+L\).
Además, \(e(G)\le e(G[S])+e(G[H])+cb+d_W\): las aristas dentro de \(W\) se cuentan dos veces en el último sumando, lo que es admisible en esta cota superior. Sustituir en (E.2), usando \(2t_I\ge e(G[H])\) y sumando las estimaciones de matching, da
\[
|Q|+e(G[S])+2m_W\le cb+d_W+2t_W(L+t_W).
\tag{E.2a}
\]

El papel del defecto enraizado es pagar el lado derecho de esta cuenta. La desigualdad conjunta deducida de los datos normalizados es
\[
\begin{split}
&d_W+2t_W(L+t_W)+\binom c2+\binom{s+1}2\\
&\hspace{1em}\le e(G[S])+2m_W+sc+\frac{t_W(c+b+s)}3.
\end{split}
\tag{E.2b}
\]
Sumar (E.2a) y (E.2b) cancela \(d_W\), \(2t_W(L+t_W)\), \(e(G[S])\) y \(2m_W\). Para la misma partición física \(Q\), queda
\[
|Q|+\binom c2+\binom{s+1}2
\le c(b+s)+\frac{t_W(c+b+s)}3.
\tag{E.2c}
\]
No se elige una segunda partición para satisfacer esta última desigualdad.

Explicamos el origen de (E.2b), pues no se deduce sólo de la contabilidad física. La normalización parte de una clique \(A\) de tamaño cercano a \(n/3\). Se retiran sus vértices con muchos enlaces ausentes; en el exterior, se separan los vértices de grado exterior grande de los de grado exterior pequeño. Entre los primeros, los que tienen pocos enlaces ausentes hacia la región ligera se añaden a \(S\), y los que tienen pocos enlaces ausentes hacia la raíz conservada se añaden a \(H\). Los restantes forman \(W\). Sea \(\mathcal L\subseteq H\) la región ligera. Las escalas son
\[
\rho=\frac{n}{(s+1)^2},\qquad \lambda=\frac{n}{(s+1)^4}.
\]
Para \(n\ge10^{50}(s+1)^8\), la normalización y la elección de reservas dan
\[
t_W\le\frac{4\rho}{10^{27}},\qquad
L\le\frac{\rho}{10^{13}}+1,\qquad
|\mathcal L|-\frac n3\le c+\frac{4\lambda}{10^{31}}.
\]
Desarrollemos las cuentas de estas estimaciones. Pongamos \(h=s+1\) y \(\varepsilon=1/(10^{41}h^8)\). La entrada de la normalización es una clique \(A\) con \(\bigl||A|-n/3\bigr|\le\varepsilon n\), a lo sumo \(\varepsilon n^2\) enlaces ausentes hacia su complemento y a lo sumo \(\varepsilon n^2\) aristas exteriores, junto con grado mínimo al menos \((1/3-\varepsilon)n\). Son las entradas localizadas, no consecuencias del defecto enraizado por sí solo. Observemos que \(\varepsilon n^2=\lambda^2/10^{41}\) y \(n\lambda=\rho^2\).

Retiramos de \(A\) todo vértice que omita más de \(\lambda/10^{10}\) vecinos exteriores, y llamamos \(A_0\) al conjunto conservado. Contar los enlaces ausentes por su extremo en \(A\) da \(|A\setminus A_0|\le\lambda/10^{31}\). Por tanto, \(n/3-2\lambda/10^{31}\le|A_0|\le n/3+\lambda/10^{41}\). Trasladar un vértice al exterior añade a lo sumo \(n\) aristas exteriores; el nuevo exterior \(R_0=V\setminus A_0\) tiene entonces a lo sumo \(2\rho^2/10^{31}\) aristas. Su conjunto pesado \(Y\), definido por grado al menos \(\rho/10^4\) dentro de \(R_0\), tiene tamaño a lo sumo \(4\rho/10^{27}\), por la suma de grados. El conjunto ligero es \(\mathcal L=R_0\setminus Y\).

Partimos \(Y\) en el siguiente orden. El conjunto \(Y_c\) consta de los vértices que omiten a lo sumo \(\rho/40\) vecinos en \(\mathcal L\). Entre los restantes, ponemos en \(Y_r\) los que omiten a lo sumo \(\rho/200\) vecinos en \(A_0\). Los demás forman \(W\). Así, \(S=A_0\cup Y_c\) y \(H=\mathcal L\cup Y_r\). En particular, \(t_W\le|Y|\), \(|c-n/3|\le\rho/10^{20}\) y \(m=e(G[H])\le2\rho^2/10^{31}\). Además, \(|\mathcal L|\le2n/3+2\lambda/10^{31}\) y \(c\ge n/3-2\lambda/10^{31}\), lo que da la cota mostrada para \(|\mathcal L|-n/3\).

Para un vértice ligero, el grado mínimo y la cota de su grado exterior implican a lo sumo \(\rho/10^4+2\lambda/10^{41}<\rho/200\) vecinos ausentes en \(A_0\). La definición da la misma cota \(\rho/200\) para \(Y_r\). Añadir \(Y_c\) y los \(2t_W\) radios reservados da entonces \(\sigma\le\rho/200+12\rho/10^{27}\). Del otro lado, todo vértice de \(S\) omite a lo sumo \(\rho/40\) vecinos ligeros; añadir \(Y_r\) y las reservas da \(\tau\le\rho/40+12\rho/10^{27}\). Son las cotas por fila y columna que se vuelven a usar en E.4.

Por último, sea \(D\) el número total de enlaces ausentes entre \(S\) y \(H\). Separarlos entre \(A_0\!:\!\mathcal L\), \(A_0\!:\!Y_r\) y \(Y_c\!:\!H\) da \(D\le\lambda^2/10^{41}+|Y_r|\rho/200+|Y_c|(\rho/40+|Y_r|)\le(\rho/10^{13})^2\). La elección \(L=\lfloor\sqrt D\rfloor+1\) da \(D<L^2\) y \(L\le\rho/10^{13}+1\). Estas estimaciones, demostradas en IndepAllBounds e IndepAllParams, preceden a la ejecución del constructor. En particular, las reservas no se ajustan retrospectivamente al número de piezas.

Sea \(\nu\) el máximo número de pares disjuntos de no-aristas dentro de \(S\). La condición de defecto enraizado, junto con las cotas normalizadas de vecinos comunes, implica \(\nu\le s\); el argumento se da en E.4. Es una propiedad del núcleo normalizado, no de todo subconjunto de vértices de un grafo de defecto enraizado a lo sumo \(s\). La cota extremal de matching aplicada al complemento de \(G[S]\) da
\[
M_S:=\binom c2-e(G[S])\le \nu c-\binom{\nu+1}2.
\]
Para medir la contribución de cada excepción, definamos
\[
\begin{split}
g_w&=\deg(w)-2\min(u_w,v_w)+2(L+t_W)-\frac{c+b+s}{3},\\
e_1&=4t_W+2L+\frac{4\rho}{10^{27}}.
\end{split}
\]
Así, (E.2b) equivale a
\(\sum_{w\in W}g_w+M_S+\binom{s+1}2\le sc\).
Para el argumento de estabilidad, conservemos el crédito residual
\[
R_*=E-\sum_{w\in W}g_w,\qquad
E=e(G[S])-\binom{c-s}{2}
  =e(G[S])-\binom c2-\binom{s+1}2+sc.
\]
La ecuación (E.2b) afirma \(R_*\ge0\); E.4 conservará una asignación estrictamente positiva por vértice excepcional. En todo el Apéndice E, \(t_W=|W|\) cuenta excepciones, \(t_I\) cuenta triángulos de la primera fase, y \(r\) se reserva para los vértices adicionales trasladados fuera del núcleo al extraer una clique real.
Las excepciones que pueden contribuir positivamente pertenecen a
\[
X=\{w\in W:v_w-u_w>n/3-\rho/400\},\qquad j=|X|.
\]
Fuera de \(X\), \(g_w\le0\); dentro, \(g_w\le |N(w)\cap\mathcal L|-n/3+e_1\).

La restricción de defecto suministra también una cota conjunta, no sólo cotas vértice a vértice:
\[
\sum_{w\in X'}|N(w)\cap\mathcal L|
\le (s-\nu)|\mathcal L|+\frac n9
\quad\text{si }X'\subseteq W,\quad |X'|\le2(s+1).
\tag{E.2d}
\]
Para deducir (E.2d), escribamos \(x=|X'|\le2h\) y fijemos \(\nu\) parejas disjuntas de no aristas en \(S\), con conjunto de extremos \(B\). Cada \(w\in X'\subseteq W\) omite más de \(\rho/200\) vecinos en \(A_0\). Como \(\rho\ge10^{50}h^2\), podemos escoger sucesivamente no vecinos distintos \(a_w\in A_0\setminus B\). Sea \(U_0=B\cup\{a_w:w\in X'\}\), y sea \(Z\subseteq\mathcal L\) el conjunto de vecinos comunes de \(U_0\). Toda clique de \(\mathcal L\) tiene tamaño a lo sumo \(\omega=\lceil\rho/10^4\rceil\), por la cota de grado exterior ligero.

Apliquemos el defecto enraizado con raíz vacía a inducidos sucesivos de \(U_0\cup X'\cup Z\), conservando \(U_0\). Hay tres posibilidades para el vértice que entrega esa condición. Si es \(z\in Z\), su vecindario contiene las \(\nu\) parejas ausentes fijadas y, por cada excepción vecina \(w\) que quede, la pareja ausente \(\{w,a_w\}\). Estas parejas son disjuntas. Una clique omite al menos un extremo de cada una, por lo que a \(z\) le quedan a lo sumo \(s-\nu\) excepciones vecinas. Retiramos esta fila y cargamos a lo sumo \(s-\nu\) incidencias. Si se escoge una excepción \(w\), tiene a lo sumo \(\omega+s\) vecinos en el conjunto ligero restante; la retiramos y cargamos esas incidencias. Si se escoge un vértice de \(U_0\), es vecino de todos los vértices restantes de \(Z\). Quedan entonces a lo sumo \(\omega+s\) filas y terminamos, cargando a lo sumo \((\omega+s)x\) incidencias. El procedimiento retira un vértice o se detiene, así que termina. Las tres cuentas dan \(e(Z,X')\le(s-\nu)|Z|+2(\omega+s)x\).

Restituyamos los vértices ligeros omitidos. Cada extremo de \(B\) omite a lo sumo \(\rho/40\) de ellos, y cada \(a_w\in A_0\), a lo sumo \(\lambda/10^{10}\). Luego \(|\mathcal L\setminus Z|\le2\nu\rho/40+x\lambda/10^{10}\). Cada fila restituida aporta a lo sumo \(x\) incidencias, por lo que
\[
e(\mathcal L,X')\le(s-\nu)|\mathcal L|
 +2(\omega+s)x+x\left(\frac{2\nu\rho}{40}+\frac{x\lambda}{10^{10}}\right).
\]
Para obtener el error \(n/9\) de (E.2d), usamos \(\nu\le s<h\), \(x\le2h\), \(h^2\rho=n\), \(h^2\lambda=\rho\) y \(h^2\le\rho/10^{50}\). El error mostrado es a lo sumo \(n/10+4n/10^4+4\rho/10^{10}+4\rho/10^{50}\le n/9\). Ésta es la estimación por eliminación de IndepAllPeel y su especialización numérica en IndepAllObstr. Aplicarla a \(2s+2\) excepciones grandes da además \(j\le2s+1\).

La prueba del presupuesto se divide entonces en tres casos.

1. Si \(j=0\), todas las contribuciones \(g_w\) son no positivas. Basta la identidad
   \[
   sc-\nu c-\binom{s+1}2+\binom{\nu+1}2
   =(s-\nu)\left(c-\frac{s+\nu+1}{2}\right)\ge0,
   \]
   donde se usa la cota \(c\ge s+\nu+1\) de la normalización.
2. Si \(1\le j\le s-\nu\), cada excepción de \(X\) omite más de \(\rho/40\) vecinos ligeros. Tras pagar los términos de error, esto da \(g_w\le c-\rho/80\). Por tanto,
   \[
   \sum_{w\in W}g_w+M_S+\binom{s+1}2
   \le(j+\nu)c-\frac{j\rho}{80}
        -\binom{\nu+1}2+\binom{s+1}2\le sc.
   \]
   En la última desigualdad se usan \(j+\nu\le s\) y
   \(\binom{s+1}2\le\rho/(2\cdot10^{50})\).
3. Si \(j\ge s-\nu+1\), se aplica (E.2d) a \(X\). Como \(n/3-e_1\ge0\), podemos restar al menos \((s-\nu+1)(n/3-e_1)\). Usando además la cota de \(|\mathcal L|\), resulta
   \[
   \sum_{w\in W}g_w
   \le (s-\nu)c-\frac{2n}{9}
      +\frac{4(s+1)\lambda}{10^{31}}+(s+1)e_1.
   \]
   El término negativo paga los errores restantes y \(\binom{s+1}2\):
   se sustituye \(e_1\le20\rho/10^{27}+2\rho/10^{13}+2\),
   \(n=\rho(s+1)^2\) y \(\rho\ge10^{50}(s+1)^2\).
   Junto con la cota de \(M_S\), se obtiene de nuevo (E.2b).

Estos tres casos son la desigualdad conjunta de IndepAllBudget. No afirman que la absorción, aislada del defecto enraizado, tenga siempre saldo favorable.

Finalmente, pongamos \(z=\lceil(c+b+s)/3\rceil\). La parábola del comparador entero y la suma de sus incrementos dan, cuando \(c+b\ge s+2\),
\[
\begin{gathered}
c(b+s)\le\binom c2+M(c+b+s),\\
Q_s(c+b)+t_W z\le Q_s(c+b+t_W).
\end{gathered}
\tag{E.2e}
\]
Insertar la primera desigualdad en (E.2c) da
\(|Q|\le Q_s(c+b)+t_W z\); la segunda da \(|Q|\le Q_s(n)\).
IndepAllMain combina la construcción con este paso aritmético. La interfaz adicional ConstructorBudget conserva tanto (E.2c) como la cota objetivo para una misma partición.

El constructor formal utilizado no invoca los resultados de [15] ni los módulos históricos de la construcción sustituida. La cota de listas y la ventana de capacidad de la primera fase coinciden en forma con condiciones de [15, Lema 4.1 y (4.4)]. Aquí se justifican mediante hospedaje diádico, promedio de desplazamientos cíclicos y absorción equilibrada. Esta comparación identifica los mecanismos y sus coincidencias; no reclama prioridad para esas condiciones ni deduce independencia histórica del control de dependencias de §7.

### E.2. Del terminal al teorema eventual

La prueba explícita seleccionada sigue la reducción al terminal y al grado mínimo que se describe a continuación. E34 proporciona su localización, y sus umbrales se evalúan explícitamente; el ensamblaje existencial histórico tiene la misma estructura de reducción.

Para cada \(s\), el resultado terminal proporciona \(\epsilon_s>0\) y un umbral a partir del cual todo grafo de la clase con \(\delta(G)\ge(1/3-\epsilon_s)n\) admite una partición de coste \(Q_s(n)\). Si hay margen fraccional cuadrático, se aplica el Corolario 3.5, válido para todo grafo, y \(M(n)\le Q_s(n)\) en el rango considerado. Si no, la localización para defecto fijo da los datos normalizados de E.1. El umbral local \(\lceil10^{50}(s+1)^8\rceil\) de ese terminal no es el umbral global \(N_s\), que incluye localización y redondeo.

La prueba seleccionada aquí es E34.theoremC_fully_explicit_final, con \(N_s=F_s=\mathrm{Fexp}(\mathrm{NeditE},s)\). Su paso de edición hacia un cordal se formaliza a partir de [22], con las adaptaciones registradas en el Apéndice F.5. Un ensamblaje existencial anterior utilizaba el lema de remoción inducida de Alon–Shapira [23]. Se conserva por procedencia, pero no es la prueba pública elegida aquí. El Corolario 6.6 acota \(F_s\) por una torre explícita.

Veamos por qué basta un terminal con grado mínimo. Para \(n\) suficientemente grande,
\[
Q_s(n)-Q_s(n-1)=\left\lfloor\frac{n+s+1}{3}\right\rfloor.
\tag{E.3}
\]
La clase es hereditaria para inducidos. Una primera inducción da \(c_4(G)\le Q_s(n)+K_s\), con \(K_s\) constante: los órdenes pequeños se pagan con aristas; si un vértice tiene grado no mayor que (E.3), se borra y se restauran sus aristas; si no, se aplica el terminal.

Repetir ese borrado no basta para suprimir \(K_s\). Se toma ahora \(n\) mayor aún, con \(\epsilon_s n\ge K_s+1\). Si algún vértice satisface
\[
\deg(v)+K_s\le\left\lfloor\frac{n+s+1}{3}\right\rfloor,
\tag{E.4}
\]
la cota aditiva ya demostrada para \(G-v\), junto con (E.3), da directamente \(c_4(G)\le Q_s(n)\). Si ninguno cumple (E.4), todos tienen grado al menos \((1/3-\epsilon_s)n\), y se aplica el terminal. Así se elimina la constante sin asumir la cota aguda en órdenes pequeños.

### E.3. Testigo inferior sin restricción en las piezas

Supongamos \(n\ge2s+2\) y pongamos \(k=\lfloor(n+s+1)/3\rfloor\). Tomemos conjuntos disjuntos \(C,D,H\) de tamaños \(k-s,s,n-k\). Hagamos \(C\) completo, \(D,H\) independientes y añadamos todos los enlaces entre \(C\cup D\) y \(H\), sin enlaces entre \(C\) y \(D\).

Este grafo tiene defecto enraizado a lo sumo \(s\). En cualquier inducido con raíz prescrita, un vértice de \(H\) fuera de la raíz tiene una clique de vecinos en \(C\) y a lo sumo \(s\) vecinos en \(D\). Si todos los vértices de \(H\) del inducido están en la raíz, hay a lo sumo uno, porque \(H\) es independiente; un vértice restante de \(C\) o \(D\) es entonces simplicial.

Asignemos peso \(-1\) a las aristas de \(C\) y \(+1\) a los enlaces hacia \(H\). Toda clique tiene peso a lo sumo uno: si contiene un vértice de \(D\), es a lo sumo una arista hacia \(H\); si contiene \(r\) vértices de \(C\) y uno de \(H\), pesa \(r-\binom r2\le1\); las contenidas en \(C\) tienen peso no positivo. Cualquier partición, sin restricción sobre el orden de sus piezas, necesita por tanto al menos
\[
k(n-k)-\binom{k-s}{2}
=M(n+s)-\binom{s+1}{2}=Q_s(n)
\tag{E.5}
\]
piezas. La igualdad es la identidad del comparador entero para esa elección de \(k\). Junto con la cota superior eventual, demuestra el máximo del Teorema C.

### E.4. Cuentas conservadas para la estabilidad con una misma raíz

Deducimos (6.14) bajo las hipótesis del terminal normalizado de E.1. Escribamos \(c=|S|\), \(b=|H|\), \(t_W=|W|\), \(n=c+b+t_W\), y conservemos las escalas \(\rho=n/(s+1)^2\) y \(\lambda=n/(s+1)^4\). Sea \(a=cb-e(S,H)\) el número de enlaces cruzados ausentes y \(m=e(G[H])\). Las contribuciones excepcionales \(g_w\), el exceso del núcleo \(E\) y el crédito residual \(R_*\) son los definidos en E.1. El argumento utiliza el terminal normalizado, incluidas sus cotas de grado mínimo, enlaces ausentes y grado exterior; el defecto enraizado por sí solo no proporciona estas cotas.

**Una paleta menor deja un ahorro cuantificable.** Pongamos
\[
d=\lfloor\rho/1000\rfloor,\qquad
\kappa=2(c-2\sigma)-d,\qquad
q=\lceil m/\kappa\rceil,\qquad
\theta_s=\frac1{2000(s+1)^2}.
\tag{E.6}
\]
Aquí \(\sigma,\tau\) se eligen antes de la construcción como los máximos números de enlaces ausentes en las filas y columnas respectivas, añadiendo \(2t_W\) para los radios reservados. La normalización da
\[
\begin{gathered}
|c-n/3|\le\rho/10^{20},\qquad
|b-2n/3|\le\rho/10^{20},\\
\sigma\le\rho/200+12\rho/10^{27},\qquad
\tau\le\rho/40+12\rho/10^{27},\qquad
m\le2\rho^2/10^{31}.
\end{gathered}
\]
El umbral terminal da \(\rho\ge10^{50}\), luego
\(\rho/2000\le d\le\rho/1000\). Sustituir en (E.6) da
\(c\le\kappa\le n\) y \(\kappa\ge n/2\). Más explícitamente,
\(\kappa\ge2n/3-11\rho/500\). Un anfitrión ligero tiene grado exterior a lo sumo \(\rho/10^4\); a cada uno de los demás anfitriones le faltan más de \(\rho/40\) vecinos de la región ligera, de modo que su grado dentro de \(H\) es a lo sumo \(b-\rho/40\). Ambas cotas de grado, incrementadas en uno para colorear, son a lo sumo \(\kappa\). Para la segunda comparación, la diferencia entre \(\rho/40\) y \(11\rho/500\) paga \(\rho/10^{20}+1\).

Como \(\kappa\ge n/2\) y \(\rho\le n\), la cota de aristas da \(q\le4\rho/10^{31}+1\). Las mismas estimaciones mostradas dan
\(3\lceil c/2\rceil+2\tau+4q\le b+2\).
Por tanto, todas las condiciones de capacidad y listas de (E.1) siguen cumpliéndose con esta paleta menor. Son las desigualdades establecidas en StrictParams; no se introduce una nueva hipótesis de coloración.

El paso de promedio cíclico conserva ahora \(t_I\) bases exteriores hospedadas con
\(\kappa t_I\ge m(c-2\sigma)\). Por ello, su ahorro entero \(z=2t_I-m\) satisface
\[
\kappa z\ge dm,\qquad
z\ge\frac{\rho m}{2000n}=\theta_s m.
\tag{E.7}
\]
Las fases de absorción y hospedaje siguen utilizando aristas disjuntas. En su cuenta, conservemos \(e(S,H)=cb-a\) en lugar de sustituirlo por \(cb\). Así, (E.2a) se refuerza a
\[
|Q|+e(G[S])+2m_W+a+\theta_s m
\le cb+d_W+2t_W(L+t_W).
\tag{E.8}
\]
Definamos el comparador terminal racional
\[
F=cb-\binom c2-\binom{s+1}2+sc+
       \frac{t_W(c+b+s)}3,\qquad
D_0=Q_s(n)-F.
\]
Las dos desigualdades de (E.2e) dan \(D_0\ge0\), incluido su redondeo entero. Sustituir la definición de \(R_*\) en (E.8) da
\(|Q|+a+\theta_s m+R_*\le F\).
La cota inferior para toda partición de orden a lo sumo cuatro da ahora
\[
D_0+a+\theta_s m+R_*\le\delta.
\tag{E.9}
\]
Esto prueba la primera cuenta de (6.14), una vez conservada la no negatividad de \(R_*\). La partición aquí es la partición física recién construida, no un óptimo elegido por separado.

**Las excepciones pagan sus costes de incidencia.** La prueba de (E.2b) deja margen suficiente para reemplazar cada \(g_w\) por \(\widetilde g_w=g_w+\rho/800\). Explicamos por qué se mantienen los tres casos. Fuera de \(X\), las estimaciones de grado y normalización dan
\[
g_w\le-\rho/400+\frac{10t_W}{3}+2L.
\]
Usando \(t_W\le4\rho/10^{27}\), \(L\le\rho/10^{13}+1\) y \(\rho\ge10^{50}\), el lado derecho es a lo sumo \(-\rho/800\). Por tanto, allí \(\widetilde g_w\le0\).

En \(X\), reemplacemos \(e_1\) por \(\widetilde e_1=e_1+\rho/800\). La pérdida de más de \(\rho/40\) vecinos ligeros sigue dando
\(\widetilde g_w\le c-\rho/80\): el término añadido \(\rho/800\), el error de normalización en \(|\mathcal L|-n/3-c\) y el \(e_1\) original consumen juntos menos de \(\rho/80\). Esto prueba el caso \(1\le j\le s-\nu\) como antes. En el caso \(j=0\), todas las contribuciones desplazadas son no positivas. En el caso restante, (E.2d) da
\[
\sum_{w\in W}\widetilde g_w
\le(s-\nu)c-\frac{2n}{9}+
  \frac{4(s+1)\lambda}{10^{31}}+(s+1)\widetilde e_1.
\]
Aquí \(\widetilde e_1\le20\rho/10^{27}+2\rho/10^{13}+2+\rho/800\). Como \(n=\rho(s+1)^2\), \((s+1)\lambda\le n\) y \(\binom{s+1}{2}\le\rho/(2\cdot10^{50})\), el término negativo \(2n/9\) paga estos errores y el término binomial. La misma cota de pares ausentes usada en E.1 da, por tanto,
\(\sum\widetilde g_w\le E\). Equivalentemente,
\[
R_*\ge\frac{t_W\rho}{800}\ge0,\qquad
nt_W\le800(s+1)^2R_*.
\tag{E.10}
\]
Éste es el presupuesto estricto de StrictBudget, no una hipótesis adicional sobre el constructor.

**El exceso restante del núcleo también queda pagado.** Las cotas de normalización implican
\(2(L+t_W)\le(c+b+s)/3\). Como el mínimo restado en \(g_w\) es no negativo, \(g_w\le\deg(w)\le n\). En consecuencia,
\[
E=R_*+\sum_{w\in W}g_w\le R_*+nt_W.
\tag{E.11}
\]
Ésta es la cuenta de ResidualExcess. Utiliza la cota del mismo \(L\) proporcionado por el constructor.

**Una clique real, con desplazamiento pagado.** Primero justifiquemos la restricción de pares ausentes en \(S\). Supongamos que \(s+1\) pares disjuntos de no-aristas tienen extremos \(B\subseteq S\), y sean \(U\subseteq\mathcal L\) sus vecinos ligeros comunes. Las estimaciones normalizadas de enlaces ausentes y \(|B|=2(s+1)\) dan
\[
|U|\ge\rho/10^4+s+2.
\]
Toda clique de \(\mathcal L\) tiene a lo sumo \(\rho/10^4+1\) vértices, por la cota de grado exterior ligero. En el grafo inducido por \(B\cup U\), cada vértice de \(B\) tiene entonces más de \(s\) vecinos fuera de cualquier clique de su vecindario. Cada vértice de \(U\) tiene la misma propiedad: su vecindario contiene \(B\), y una clique puede contener a lo sumo un extremo de cada par ausente. Ningún vértice de este inducido satisface la condición de defecto enraizado con raíz vacía, una contradicción. Éste es el argumento de AllInput.no_core_pairs; las estimaciones de vecinos comunes son esenciales.

Para completar la exposición, la alternativa finita del núcleo utilizada a continuación es la siguiente. Si \(c\ge20(s+1)^2\) y el complemento de \(G[S]\) no tiene un matching de tamaño \(s+1\), entonces \(S\) contiene una clique de tamaño \(c-s\), o bien
\[
c-s\le2\left(e(G[S])-\binom{c-s}{2}\right)=2E.
\tag{E.12}
\]
Se prueba por inducción en \(s\). Para \(s=0\), \(S\) es una clique. Si algún vértice tiene al menos \(2s+1\) no-vecinos en \(S\), eliminarlo deja un grafo sin matching de no-aristas de tamaño \(s\): tal matching ocuparía sólo \(2s\) vértices, dejando un no-vecino para extenderlo. Apliquemos la inducción con \(s-1\); el tamaño objetivo del núcleo sigue siendo \(c-s\), y toda cota inferior para las aristas del conjunto menor también vale en \(S\). En otro caso, el grafo de aristas ausentes tiene grado máximo a lo sumo \(2s\). Eliminar repetidamente los dos extremos de una arista ausente retira a lo sumo \(4s+1\) aristas ausentes por paso y termina tras a lo sumo \(s\) pasos. Por tanto, tiene a lo sumo \((4s+1)s\) aristas. Sustituir en \(E=e(G[S])-\binom{c-s}{2}\), usando \(c\ge20(s+1)^2\), da (E.12). Éste es CoreCliqueAlternative.

En el primer caso, elijamos la clique \(C\) de tamaño \(c-s\) y pongamos \(r=0\). En el segundo, los extremos de un matching máximo de no-aristas tocan toda arista ausente. Su complemento es una clique de tamaño al menos \(c-2s\); reduzcámosla a ese tamaño y pongamos \(r=s\). Entonces \(|C|+s+r=c\). Como \(c\ge2s\), (E.12) da \(c\le4E\) y, por tanto, \(rc\le4sE\). La normalización también da \(n\le4c\), de modo que en ambos casos
\[
rn\le16sE.
\tag{E.13}
\]
La construcción conserva \(C\) como clique del grafo original. Las cotas normalizadas de tamaño también dan \(2\le|C|\) y \(2|C|+s\le n\), como requiere la raíz final.

**Contar las ediciones sobre el conjunto original de vértices.** Partamos de la plantilla provisional con clique \(C\), conjunto independiente \(S\setminus C\), todos los enlaces entre \(S\) y \(H\), y vértices aislados \(W\). Como \(C\) ya es una clique, compararla con \(G\) cuesta a lo sumo
\[
a+m+\left(e(G[S])-\binom{|C|}{2}\right)+nt_W.
\]
Elijamos \(D\subseteq S\setminus C\) con \(|D|=s\), pongamos \(M=S\setminus(C\cup D)\), y traslademos \(M\cup W\) a la clase de anfitriones \(J=H\cup M\cup W\). Aquí \(|M|=r\). Todo par modificado en esta segunda comparación toca \(M\cup W\), por lo que cuesta a lo sumo \(n(r+t_W)\). Finalmente,
\[
e(G[S])-\binom{|C|}{2}
=E+\binom{|C|+r}{2}-\binom{|C|}{2}
\le E+rn.
\]
Combinar ambas comparaciones da
\[
d_E(G,T(C,D,J))\le a+m+E+2rn+2nt_W.
\tag{E.14}
\]
Un \(rn\) paga el tamaño reducido de la clique en la cuenta interior; el otro paga el cambio de clase de anfitrión. Análogamente, \(W\) primero se aísla y después se coloca en la clase de anfitriones. Son cotas superiores de dos ediciones sucesivas, no una afirmación de que todos los pares cargados sean distintos. TemplateDistance, RootPartition y CliqueShiftArithmetic formalizan estas comparaciones.

**Combinar las cuentas.** Las ecuaciones (E.11), (E.13) y (E.14) implican
\[
\begin{aligned}
d_E(G,T)&\le a+m+(1+32s)E+2nt_W\\
&\le a+m+(1+32s)R_*+(3+32s)nt_W\\
&\le a+m+\bigl(1+32s+800(3+32s)(s+1)^2\bigr)R_*.
\end{aligned}
\]
El coeficiente final es a lo sumo \(38000(s+1)^3\). La ecuación (E.9), con \(D_0\ge0\), paga \(a+m\) con a lo sumo \(2000(s+1)^2\delta\), y paga \(R_*\) con a lo sumo \(\delta\). Por tanto,
\[
d_E(G,T)\le40000(s+1)^3\delta.
\]
Ésta es la estimación terminal utilizada en §6.6. Su constante paga una clique real de \(G\); una comparación más barata que sólo reparara el núcleo hasta convertirlo en clique no proporcionaría la conclusión con una misma raíz del Teorema C′.

## Apéndice F. Parámetros e interfaces de prueba de las extensiones

### F.1. Parámetros explícitos para defecto fijo

Las funciones utilizadas aquí son las del módulo congelado ExplicitFixedStability. Reemplazan la elección existencial de un umbral terminal o de localización; ninguno es una entrada sin demostrar. Escribimos \(\eta_s=\mathrm{etaNF}(s)>0\), \(L_s=\mathrm{NLoc}(\mathrm{NeditE},s,\epsilon_s)\) y \(F_s=\mathrm{Fexp}(\mathrm{NeditE},s)\) para las funciones explícitas de E33.Assembly y E33.LocExplicit, con el umbral de edición cordal NeditE suministrado por E34.L11Main. El argumento de remoción formalizado en E34 sigue a de Joannis de Verclos [22]; la verificación formal no cambia su atribución matemática. La función \(N_{\rm far}\) es el umbral explícito de redondeo de E18, no un parámetro existencial adicional.

Con \(\epsilon_s,A_s\) como en (6.11), los parámetros efectivos de estabilidad son
\[
\begin{aligned}
\gamma_s&=\tfrac12\min\{1,\eta_s/4,\epsilon_s/4\},\\
N_s^{\rm deg}&=\lceil10^{50}(s+1)^8\rceil+L_s+
                    N_{\rm far}(\eta_s)+s+5,\\
N_{0,s}&=N_s^{\rm deg}+F_s+s+3+
                 \lceil1/\epsilon_s\rceil+\lceil A_s\rceil+1,\\
N_s^{\rm stab}&=2N_{0,s}+F_s+s+4.
\end{aligned}
\tag{F.1}
\]
Éstas son definiciones de funciones de umbral identificadas y demostradas, no cotas numéricamente útiles. El término local \(10^{50}(s+1)^8\) es sólo un sumando; no debe presentarse como el umbral global. La prueba de fixed_defect_stability_explicit invoca los resultados demostrados de remoción, localización, redondeo lejano y cuentas terminales conservadas. Así, (F.1) no contiene ningún realizador ni teorema de localización supuesto.

Para aclararlo, el invariante de borrado utilizado en §6.6 es
\[
0\le\delta\le\gamma_0t(t-N_{0,s}),\qquad
\gamma_0=\min\{1,\eta_s/4,\epsilon_s/4\}.
\]
Al eliminar un vértice de grado bajo, (6.15) reduce el déficit al menos en \(\epsilon_s t-1/3\). El cambio del lado derecho es \(\gamma_0(2t-1-N_{0,s})\le\epsilon_s t/2\). Como \(\epsilon_sN_{0,s}\ge1\), esto paga el cambio y deja un déficit hijo no negativo. Si el borrado alcanzara el orden inferior, el invariante forzaría déficit cero, mientras que la misma estimación de borrado forzaría un déficit hijo negativo, una contradicción. Por eso un caso finito de orden pequeño no introduce un error aditivo en la estabilidad.

### F.2. Contabilidad fraccional por estrellas y órdenes pequeños

Para \(n>0\), tomemos un dual mixto óptimo \(y\) y usemos precios con signo \(z_e=1-y_e\). Las restricciones triangulares y de \(K_4\) dan sumas con signo a lo sumo uno en las cliques. El argumento de estrella positiva máxima sobre una clique de [15, Lema 3.1], seguido de eliminación enraizada, da un entero \(c<n\) y un precio \(\alpha\) con \(0\le\alpha\le c\) tales que
\[
\begin{aligned}
F_4(G)&\le(n-2c+1)\alpha+\binom c2+
                \sum_{j=0}^{n-c-1}\min(s,j),\\
F_4(G)&\le(n-c)\alpha+\frac16\binom c2+s(n-c)
                   &&(c\ge4).
\end{aligned}
\tag{F.2}
\]
Aquí se utiliza el óptimo certificado: no se identifica un valor dual meramente factible con \(W^*(G)\).

Si \(n-c\ge s\), la primera suma de excepciones es exactamente
\[
s(n-c)-\binom{s+1}{2}.
\tag{F.3}
\]
En la rama de estrella baja \(2c\le n+1\), el coeficiente de \(\alpha\) es no negativo, por lo que se puede sustituir \(\alpha\le c\) en la primera fila. En la banda \(4s\le n\), (F.3) da entonces
\[
F_4(G)\le B_{n-s}(c)+ns-\binom{s+1}{2}
\le M(n-s)+ns-\binom{s+1}{2}.
\]
Esto utiliza una desigualdad del baseline entero antes de la comparación final, no un piso aplicado a un valor fraccional. En la rama de estrella alta, comparemos \(\alpha\) con \(5c/12\); se utiliza la segunda fila por debajo de ese valor y la primera por encima. Ambas dan la envolvente
\[
F_4(G)\le\frac{c(5n-4c-1)}{12}+s(n-c).
\tag{F.4}
\]
Las comparaciones racionales de RefinedFractionalBound y UniformFractionalBound establecen las dos bandas de la Proposición 6.4. Para \(n<8\), SmallOrderFractional comprueba dentro de Lean los rangos enteros de parámetros restantes contra esta misma envolvente. El grafo vacío y los casos que no requieren una restricción de \(K_4\) utilizan la primera fila o la cota de número de aristas. No se necesita enumeración de grafos pequeños, óptimos en punto flotante ni certificados de un solver externo para estos órdenes.

### F.3. Localización uniforme mediante edición hacia un cordal

La parte estructural del Teorema 6.5 no utiliza sólo (F.2). También necesita convertir un defecto enraizado pequeño en una edición cordal pequeña. Para cada precisión \(\xi>0\), E34 da un tamaño de muestra explícito \(m=m(\xi)\). El adaptador SublinearEdit utiliza
\[
\theta(\xi)=\frac1{16m^{m+1}+1},\qquad N(\xi)=\max\{m,1\}.
\tag{F.5}
\]
Para \(n\ge N(\xi)\) y \(s\le\theta(\xi)n\), un grafo de defecto enraizado a lo sumo \(s\) está a distancia de a lo sumo \(\xi n^2\) ediciones de aristas de un grafo cordal. La prueba de remoción subyacente es la formalizada a partir de [22].

El lema siguiente recupera una clique en el grafo original. Para un conjunto de vértices \(D\), sea \(\operatorname{ordNE}(G,D)\) el número de pares ordenados de vértices distintos y no adyacentes de \(D\), y escribamos \(x_+=\max\{x,0\}\).

**Lema F.3a (recuperación de clique con defecto aditivo).** Si \(\operatorname{rsd}(G)\le s\), todo \(D\subseteq V(G)\) contiene una clique \(C\) de \(G\) tal que
\[
(|D|-|C|-s)_+^2\le\operatorname{ordNE}(G,D).
\tag{F.5a}
\]

**Demostración.** Inducimos en \(|D|\); el conjunto vacío es inmediato. Apliquemos la condición enraizada a \(D\), con raíz prescrita vacía. Existe un vértice \(v\in D\) cuyos vecinos en \(D\) contienen una clique \(P\) con a lo sumo \(s\) vecinos fuera de \(P\). Sea \(y\) el número de no-vecinos de \(v\) en \(D\setminus\{v\}\). Retirar \(v\) elimina exactamente las dos orientaciones de esas \(y\) no-aristas, luego
\[
\operatorname{ordNE}(G,D)
=\operatorname{ordNE}(G,D\setminus\{v\})+2y.
\]
Por inducción, \(D\setminus\{v\}\) contiene una clique \(C'\) con
\(x^2\le\operatorname{ordNE}(G,D\setminus\{v\})\), donde
\(x=(|D|-1-|C'|-s)_+\).
Si \(y\ge x+1\), tomemos \(C=C'\). Entonces
\[
(|D|-|C'|-s)_+^2\le(x+1)^2
\le x^2+2y\le\operatorname{ordNE}(G,D).
\]
En otro caso, \(y\le x\), porque ambos son enteros. Tomemos \(C=P\cup\{v\}\), que es una clique. La descomposición del grado da \(|P|+s\ge |D|-1-y\), luego \((|D|-|C|-s)_+\le y\le x\). Elevar al cuadrado y usar la cota inductiva prueba (F.5a) también en este caso.

**Corolario F.3b (recuperación tras borrar aristas).** Supongamos \(\operatorname{rsd}(G)\le s\), que \(G,H\) tienen el mismo conjunto de vértices y que \(A\) es una clique de \(H\). Si \(u\ge0\) y
\[
2|E(H)\setminus E(G)|\le u^2,
\]
entonces \(A\) contiene una clique \(R\) de \(G\) con \(|A\setminus R|\le s+u\).

**Demostración.** Cada no-arista no ordenada de \(G\) dentro de \(A\) es una arista de \(H\) ausente en \(G\). En consecuencia,
\(\operatorname{ordNE}(G,A)\le2|E(H)\setminus E(G)|\).
Apliquemos (F.5a); tomar raíces cuadradas no negativas da
\((|A|-|R|-s)_+\le u\), que es la estimación requerida.

Las interfaces formales son exists_clique_additive_defect y recover_clique_from_edit. La segunda toma \(u\) racional y supone explícitamente \(u\ge0\); la prueba mostrada también vale para \(u\) real. Cuando \(s=0\), (F.5a) se reduce a la estimación de extracción de clique cordal (F.9). La pérdida en \(s\) es aditiva, no un factor que multiplica el término de raíz cuadrada.

Sea ahora \(H\) el grafo cordal obtenido arriba y pongamos \(t=d_E(G,H)\). Reparar particiones de orden acotado transfiere la cota inferior integral con déficit a lo sumo \(\delta+4t\). Apliquemos el Teorema 6.1 en \(H\). Su clique no tiene por qué ser una clique de \(G\); el Corolario F.3b retira a lo sumo \(s+u\) vértices para cualquier \(u\ge0\) con \(2t\le u^2\), produciendo una clique \(R\) en el propio \(G\). Contar aristas modificadas e incidencias da
\[
\begin{aligned}
e(G-R)+A_R&\le16\delta+65t+n(s+u),\\
M(n)-B_n(|R|)&\le\delta+4t+2n(s+u).
\end{aligned}
\tag{F.6}
\]
Éstas son las desigualdades de SublinearStabilityTransfer. Aquí \(\delta\) se mide respecto de \(M(n)\). Para partir de la hipótesis en \(n^2/6\) del Teorema 6.5, basta aumentar su déficit en \(n/6\), lo que conserva un error \(o(n^2)\). Elijamos \(\xi\), la razón de defecto y el margen de casi extremalidad suficientemente pequeños antes que \(n\) y \(G\); entonces se puede elegir \(u\) como un múltiplo pequeño de \(n\). La fórmula (F.6) prueba el control uniforme de ediciones y baseline. La parábola del comparador transforma este último en una ventana de tamaño, a una escala de precisión cuadrática. Minimizar (6.27) da entonces el enunciado secuencial con una raíz. Este orden de elecciones evita tanto un umbral oculto de \(s\) fijo como una raíz que dependa de la partición solicitada.

### F.4. Nuevas interfaces públicas y límites de esta revisión

En la tabla siguiente, el prefijo es PaperIV.SublinearResearch, salvo la entrada E32 nombrada explícitamente. Todos los archivos listados pertenecen al nuevo congelado de fuentes identificado en §7. ResearchAudit comprueba estas interfaces; FDCheck.FinalAudit y E34.Audit comprueban por separado el ensamblaje de defecto fijo y el desarrollo de remoción. E35, el adaptador público del Teorema C y la obstrucción de raíz cuadrada están incluidos en el mismo corte, con sus controles específicos indicados abajo.

| Enunciado | Declaración |
|:--|:--|
| Cotas cordales reales con una misma raíz, incluida la masa de aristas | chordal_joint_stability_real |
| Teorema C′ y (6.12)–(6.13) | fixed_defect_joint_stability_real |
| Parámetros explícitos y clasificación | FixedExplicit.fixed_defect_stability_explicit |
| Cota de edición hacia tamaño óptimo (6.17) | fixed_defect_exact_extremal_edit_real |
| Clasificación irrestricta de la igualdad | E32.cp_classification_of_theoremCPrimeC, con la clasificación demostrada arriba |
| Cota finita (6.22) | certified_shifted_fractional_bound_all_orders |
| Cota finita (6.23) | certified_refined_fractional_bound_all_orders |
| Versiones integrales uniformes | uniform_shifted_partition_bound; uniform_refined_partition_bound |
| Aproximación secuencial con órdenes arbitrarios | sequence_arbitrary_orders_partition_bound |
| Estabilidad secuencial con una raíz | sequence_arbitrary_orders_stability |

**Tabla 9.** Correspondencia de la extensión. Las interfaces finitas con una misma raíz toman déficits reales; la interfaz secuencial registra parámetros racionales de error y exceso. Esta última no se describe implícitamente como un tipo Lean elaborado distinto.

El factor diez de la desigualdad local \(\binom{a+b}{2}\le10d(a,b)\), para defecto positivo, es óptimo: el perfil \((a,b)=(3,2)\) tiene diez aristas y defecto uno. Esto no prueba la optimalidad de \(480\), \(A_s\) ni de los umbrales globales.

El Apéndice E.4 deduce las cuentas terminales conservadas utilizadas en §6.6, y F.3 demuestra la recuperación de clique. El Apéndice F.5 explica el ensamblaje de tres casos de la cota adaptada de muestras con anclajes. Estas adiciones exponen los argumentos intermedios para revisión; no son un nuevo veredicto de auditoría. Una nueva auditoría todavía debe comprobar su correspondencia con los productores formales y los lemas de remoción de nivel inferior. La compilación local no sustituye esa revisión.

### F.5. Lemas auxiliares y adaptaciones de remoción cordal

La implementación de remoción sigue a [22], pero no es una traducción literal de sus enunciados y constantes. Cuatro lemas finitos explicitan los cambios pertinentes para esta aplicación.

**Conteo de ciclos inducidos.** Si \(\operatorname{rsd}(G)\le s\), entonces para todo \(k\ge4\),
\[
\operatorname{indCopies}(C_k,G)\le2ks\,n^{k-1}.
\tag{F.7}
\]
Aquí indCopies cuenta inmersiones inducidas etiquetadas del ciclo de longitud \(k\), no conjuntos de vértices de ciclos sin etiquetar. Esta convención importa al utilizar (F.7) en la cota de la unión de eventos de la muestra. El resultado es E34.indCopies_cycle_le. Proporciona la entrada de conteo de ciclos directamente a partir del defecto enraizado.

**Cota de edición co-bipartita.** Si el conjunto de vértices es la unión de dos cliques y \(\operatorname{rsd}(G)\le s\), existe un cordal \(H\) sobre los mismos vértices con
\[
d_E(G,H)\le2\sqrt{s}\,n\sqrt n+n.
\tag{F.8}
\]
La prueba formal, E34.coBipartite_edit_le, ordena una clique, acota las inversiones en las filas de adyacencia de la otra y reemplaza cada fila por una fila umbral. Los vecindarios cruzados anidados resultantes dan un grafo cordal. La estimación se refiere a distancia de edición, no a una partición en cliques del grafo original.

**Extracción de clique por eliminación.** Si \(G[D]\) es cordal, \(d=|D|\) y \(M\) es el número de no-aristas no ordenadas en \(D\), entonces \(D\) contiene una clique \(C\) que satisface
\[
(d-|C|)^2\le2M,\qquad |C|\ge d-\sqrt{2M}.
\tag{F.9}
\]
La prueba de E34.exists_large_clique es una inducción por eliminación simplicial. El lado derecho formal utiliza no-aristas ordenadas, de ahí el factor dos. Esto reemplaza el uso de [22, Lema 4] dentro de la reparación casi simplicial; no se presenta como una nueva versión del teorema completo citado allí.

**Reparación casi simplicial.** Particionemos \(V(G)=X\sqcup Y\), supongamos que \(G[Y]\) es cordal y sea \(p_G(x)\) el número de no-aristas no ordenadas dentro de \(N_G(x)\). Si \(\varepsilon\ge0\) y \(p_G(x)\le\varepsilon n^2\) para todo \(x\in X\), existe un cordal \(H\) con
\[
d_E(G,H)\le8\sqrt{\varepsilon}\,n^2,\qquad H[Y]=G[Y].
\tag{F.10}
\]
Éste es E34.lemma3. En comparación con [22, Lema 3], la constante es ocho en vez de seis, pero no se requiere la condición \(n\ge1/\varepsilon\). Ninguna versión se describe como uniformemente más fuerte: difieren las hipótesis y las constantes.

El resto de la implementación cambia la representación y la elección numérica de parámetros de la siguiente manera.

| Paso de [22] | Implementación utilizada aquí |
|:--|:--|
| Muestreo | Las muestras son sucesiones con reemplazo. E34.transfer pasa de conteos de sucesiones a subconjuntos de vértices para la propiedad cerrada hacia arriba que se considera. |
| Representaciones con anclajes | La definición permite una aplicación que preserva caminos desde el árbol prescrito hacia otro árbol enraizado. La prueba de conteo trata esta clase ampliada de representaciones; también cambia la cota de la muestra. |
| Modelo de árbol | Aplicaciones padre finitas y conjuntos de nodos reemplazan los árboles topológicos. El parámetro \(K\) cuenta nodos, no hojas. Las secciones se indexan por nodos, por lo que no se importa la Afirmación 1 correspondiente. |
| Conteo de coloraciones por conjuntos | Los vértices afectados se cuentan explícitamente. Los casos de parámetros pequeños y degenerados se separan en lugar de importar literalmente las cotas logarítmicas publicadas. |
| Cota de muestra con anclajes | El tamaño elegido es \(m_{11}(\varepsilon,K)=\lceil2^{58}(K+1)^{15}/\varepsilon^{12}\rceil\). |
| Cota final de la unión de eventos | Se utilizan \(q=\lceil102400/\varepsilon^2\rceil^2\) pares muestreados y \(\lceil\log_2(4\,n_{\rm codes})\rceil\) bloques independientes, con \(n_{\rm codes}\) la familia de datos de compuerta contada explícitamente. |

**Tabla 10.** Adaptaciones de [22] pertinentes al umbral explícito. Las cotas de parámetros mayores no mejoran su exponente del tamaño muestral. La prueba sigue siendo una implementación de su estrategia de remoción, con estos reemplazos finitos y elecciones de parámetros.

**Ensamblaje de la cota adaptada para muestras con anclajes.** Damos los tres casos utilizados en E34.lemma11_V, pues cambiar la representación y la convención de muestreo exige comprobar el argumento de conteo, no sólo citar el lema publicado. Fijemos un árbol enraizado \(\Gamma\) con \(K\) nodos y un anclaje prescrito \(x_v\in V(\Gamma)\) para cada vértice de \(G\). Una muestra *admite los anclajes* si su grafo inducido tiene una representación por subárboles de otro árbol enraizado \(T\), junto con una aplicación que preserva caminos \(\iota:\Gamma\to T\), tal que el subárbol de \(v\) contiene \(\iota(x_v)\). Ésta es la noción ampliada de la Tabla 10.

Supongamos que \(G\) está \(\varepsilon\)-lejos de ser cordal: todo grafo cordal sobre su conjunto de vértices tiene distancia de edición mayor que \(\varepsilon n^2\). La comparación con el grafo vacío fuerza \(n\ge1\) y \(\varepsilon<1/2\); la aplicación de anclajes fuerza entonces \(K\ge1\). Para \(\varepsilon>0\), elijamos
\[
\begin{gathered}
y=\left\lceil\frac{256K^2}{\varepsilon^2}\right\rceil,\qquad
\delta_{11}=\frac1{4y^2},\qquad
B=\left\lfloor\frac{8K}{\delta_{11}}\right\rfloor,\qquad
\eta=\frac{\varepsilon}{2K},\\
m=m_{11}(\varepsilon,K)
 =\left\lceil\frac{2^{58}(K+1)^{15}}{\varepsilon^{12}}\right\rceil.
\end{gathered}
\tag{F.11}
\]
Debemos mostrar que a lo sumo la mitad de las \(n^m\) muestras ordenadas de longitud \(m\), con reemplazo, admiten los anclajes.

Una coloración por conjuntos admisible asigna a \(v\) un subárbol \(\psi(v)\) de \(\Gamma\) que contiene \(x_v\). Para una arista \(uv\), la compatibilidad requiere que el camino de \(x_u\) a \(x_v\) esté contenido en \(\psi(u)\cup\psi(v)\); para una no-arista requiere \(\psi(u)\cap\psi(v)=\varnothing\). Sea \(\operatorname{conf}(\psi)\) el número de pares ordenados incompatibles de vértices distintos. Una muestra que admite los anclajes induce una coloración por conjuntos compatible sobre su conjunto de vértices (properOn_of_pinned).

*Caso A: toda coloración admisible tiene al menos \(\delta_{11}n^2\) conflictos.* Apliquemos el teorema adaptado de conteo de coloraciones por conjuntos con tamaño muestral \(m\) y \(B\) rondas. Las condiciones numéricas son \(8K/\delta_{11}<B+1\) y la desigualdad thm2_ineq para los parámetros (F.11). Se sigue que a lo sumo la mitad de todas las muestras admiten una coloración por conjuntos compatible. Las muestras que admiten los anclajes forman un subconjunto, por lo que vale para ellas la misma cota.

*Caso B1: alguna \(\psi\) admisible tiene menos de \(\delta_{11}n^2\) conflictos, pero una sección está lejos de todo modelo de cadena.* Las secciones se indexan por los \(K\) nodos de \(\Gamma\); cada sección tiene dos clases de vértices y un modelo de rangos para sus adyacencias cruzadas. En este caso, una sección tiene más de \(\eta n^2\) discrepancias para toda asignación de rangos. El lema de conteo de secciones claim5_count acota el número de muestras de longitud \(y\) que inducen un grafo cordal por
\[
(y+1)(1-\eta)^{y-1}n^y+
y^2\operatorname{conf}(\psi)n^{y-2}.
\]
La estimación de parámetros block_ineq da \((y+1)(1-\eta)^{y-1}\le1/4\). El segundo sumando es a lo sumo \(n^y/4\), pues \(y^2\delta_{11}=1/4\). Así, a lo sumo la mitad de las muestras de longitud \(y\) son cordales. Tenemos \(y\le m\); toda muestra de longitud \(m\) que admite los anclajes induce un cordal, y también su prefijo de longitud \(y\). Cada prefijo tiene \(n^{m-y}\) extensiones. Por tanto, a lo sumo \(n^m/2\) muestras completas admiten los anclajes. Todo el argumento usa sucesiones y no supone que sus entradas sean distintas.

*Caso B2: toda sección tiene una asignación de rangos con a lo sumo \(\eta n^2\) discrepancias.* Normalicemos cada rango reemplazándolo por el número de vértices de rango estrictamente menor. Esto preserva todas las comparaciones estrictas de rangos y, por tanto, todas las discrepancias de las secciones, mientras acota cada rango por \(n\). Subdividamos el árbol prescrito usando esta cota común y peguemos los modelos de sección. El grafo resultante \(F\) es un grafo de intersección de subárboles y, por tanto, cordal. La estimación de pegado carga cada arista modificada a un conflicto o a una discrepancia de sección:
\[
\begin{aligned}
d_E(G,F)&\le\operatorname{conf}(\psi)+
             \sum_{c\in V(\Gamma)}\operatorname{mis}_c\\
&<\delta_{11}n^2+K\eta n^2
\le\varepsilon n^2.
\end{aligned}
\tag{F.12}
\]
Aquí \(\delta_{11}\le\varepsilon/2\), por (F.11). Esto contradice la distancia supuesta a la clase cordal, luego el caso B2 no puede ocurrir.

Las alternativas son exhaustivas: o toda coloración tiene muchos conflictos, o alguna tiene pocos, y sus secciones incluyen una lejana o todas admiten modelos de rangos cercanos. Las pruebas formales son l11_caseA, l11_caseB1 y l11_caseB2 de E34.L11Main. El teorema de coloración por conjuntos, el lema de conteo de secciones y el lema de pegado de subárboles conservan sus papeles en la estrategia de remoción de [22]; el argumento anterior identifica cómo encajan sus versiones adaptadas. No afirma que el Lema 11 publicado originalmente tenga el enunciado o las constantes modificadas.

El nuevo congelado de fuentes incluye los cuatro lemas finitos anteriores y E35.theoremC_tower, theoremC_tower_uniform, theoremC_tower_uniform_sMax y NfarE_le_tower_poly para (6.28)–(6.29) y (C.4). El adaptador público es PaperIV.DefectExplicitPublication; FDCheck.ASCheck comprueba las dependencias de remoción seleccionadas. La Proposición 6.3a se apoya en PaperIV.OptimalTemplateObstruction.shifted_template_witness, shifted_template_sqrt_witness y no_linear_optimal_template_bound; optimal_family_nonempty verifica que la comparación no sea vacua. Sus resultados de auditoría ejecutados de nuevo y su identidad fuente se describen en §7.

## Apéndice G. Brechas de empaquetamiento y límites de la limpieza

### G.1. La cota para todos los órdenes y las brechas de empaquetamiento

¿Vale \(c_4(G)\le M(n)\) para todo cordal y todo orden, es decir, puede tomarse \(b=0\) en el Teorema A? El umbral de esta prueba limita la demostración, no constituye evidencia de una excepción al enunciado. Para la familia completa sí se dispone de una construcción sin umbral: \(c_4(K_n)\le M(n)\) para todo \(n\ge0\), como se demuestra en el Apéndice D. A diferencia de \(\operatorname{cp}(K_n)=1\) para \(n\ge2\), esta afirmación exige controlar el tamaño de las piezas.

La demostración no necesita ni establece una cota lineal universal para el gap mixto \(W^*(G)-W(G)\), donde \(W(G)\) es la ganancia mixta entera óptima. Compara la pérdida de la construcción con el margen disponible en cada instancia. El orden de crecimiento general de ese gap se estudia por separado; no es una hipótesis de este paper.

Hay un resultado complementario para el **gap triangular** con número de clique acotado. Sean \(d\ge0\) entero y \(G\) cordal sin clique de orden \(d+2\). La biblioteca `BoundedCliqueGap`, incluida como anexo de fuentes separado y comprobada contra una compilación registrada distinta, demuestra que todo empaquetamiento fraccional triangular \(x\) satisface
\[
\sum_T x_T\le \nu_3(G)+\left(10+\frac d2\right)n.
\tag{G.1}
\]
Aquí \(\nu_3(G)\) cuenta triángulos disjuntos por aristas; el objetivo fraccional cuenta también triángulos, sin el factor de ganancia dos. Tomar el óptimo da \(\nu_3^*(G)-\nu_3(G)\le(10+d/2)n\). Para \(d\) fijo, la pérdida es lineal; no se obtiene de ello una constante uniforme cuando crece el número de clique.

El enunciado formal es `BoundedCliqueGap.chordal_gap_linear_cliqueFree`. Su prueba emplea una representación por subárboles y separa la masa de las piezas locales de la que atraviesa las uniones. Cada triángulo de esta última clase utiliza dos aristas de unión; sumar sus capacidades paga su masa con la mitad de la cuenta de esas aristas. La cota \(d\) controla esa cuenta y aporta el término \(dn/2\), además de la pérdida local \(10n\).

La misma biblioteca expresa la hipótesis mediante un árbol de cliques cuyas bolsas tienen a lo sumo \(d+1\) vértices. `exists_cliqueTree_width_le_iff_cliqueFree` demuestra, para cordales, la equivalencia con la exclusión de \(K_{d+2}\). Es la forma de anchura de árbol disponible en este desarrollo; no se afirma que Mathlib proporcione una definición general de *treewidth* utilizada aquí. El resultado (G.1) no acota el gap **mixto** de \(K_3/K_4\), ni sustituye el redondeo de la Sección 3.

### G.2. Una obstrucción cuantitativa a la limpieza de codegrado

El umbral del Teorema 3.1 procede de la construcción con regularidad del Apéndice C. Un complemento formal, separado de esa prueba, permite acotar qué puede conseguirse mediante otra interfaz de limpieza. Es necesario distinguir ambos objetos: demostrar que una limpieza basta para redondear no demuestra que todo redondeador tenga que realizarla.

Fijemos \(\varepsilon>0\), \(\gamma\le1/2\) y una constante \(C_0\). Consideremos el siguiente contrato, llamado `CleanupAtWith` en el suplemento. Para todo grafo \(G\) de orden \(n\ge N_0\) y todo empaquetamiento fraccional mixto \(x\) cuya masa triangular sea al menos \(\varepsilon n^2/30-1\), exige otro empaquetamiento \(y\) sobre el mismo grafo con masa triangular al menos \(C_0\), pérdida de ganancia a lo sumo \(\varepsilon n^2/4\) y codegrado ponderado a lo sumo \(\gamma\). Este último codegrado es la suma de pesos de las copias que contienen simultáneamente dos aristas distintas del grafo.

**Proposición G.1 (límite de ese contrato).** Si \(N_0\) satisface el contrato anterior, \(t\ge4\) y \(7\varepsilon\le e^{-t}\), entonces
\[
N_0>\exp(t^2/16).
\tag{G.2}
\]
En particular, si \(\varepsilon\le1/(7e^{34})\), se tiene \(N_0>e^{72}\). La precisión es racional en la declaración Lean; las comparaciones exponenciales se realizan en los reales.

**Demostración.** Llamemos rígido a un grafo cuyas aristas pertenecen, cada una, a un único triángulo, sin copias de \(K_4\). Si tiene \(T\) triángulos, poner peso uno sobre cada uno da ganancia \(2T\). Dos aristas de un mismo triángulo sólo pueden recibir peso conjunto a través de esa copia. Por tanto, todo \(y\) de codegrado a lo sumo \(\gamma\) le asigna peso a lo sumo \(\gamma\), y su ganancia es a lo sumo \(2\gamma T\). La pérdida forzada es al menos \(2(1-\gamma)T\). Para un orden que satisfaga la hipótesis de masa, el contrato impone
\[
2(1-\gamma)T\le\frac{\varepsilon}{4}n^2.
\tag{G.3}
\]
Así, una limpieza uniforme de este tipo controla cuantitativamente la densidad de los sistemas rígidos, un problema de tipo \((6,3)\).

La construcción tripartita de Ruzsa–Szemerédi [18], aplicada a un conjunto \(A\subseteq\{0,\ldots,M-1\}\) sin progresiones aritméticas de tres términos, da un grafo rígido de orden \(6M+3\) con al menos \((2M+1)|A|\) triángulos. La versión de la cota de Behrend [17] utilizada en Mathlib garantiza \(|A|\ge M\exp(-4\sqrt{\log M})\). Si \(7\varepsilon\le\exp(-4\sqrt{\log M})\) y \(M\ge1\), esa cuenta cumple la hipótesis de masa y contradice (G.3): el orden \(6M+3\) debe ser menor que \(N_0\).

Tomemos ahora \(M=\lfloor\exp(t^2/16)\rfloor\). Entonces \(M\ge1\), \(\log M\le t^2/16\) y \(4\sqrt{\log M}\le t\). Se aplica el párrafo anterior. Como \(\exp(t^2/16)<M+1\le6M+3\), resulta (G.2). Para \(t=34\), \(t^2/16=72.25>72\), lo que da la última afirmación. Las declaraciones `threshold_gt_exp` y `threshold_gt_exp_seventy_two`, de `FarExploration.CleanupRigidVerdict`, formalizan estas cuentas usando la cota de Behrend de Mathlib.

Para \(t=\log(1/(7\varepsilon))\), (G.2) crece más deprisa que cualquier potencia fija de \(1/\varepsilon\); `threshold_superpolynomial` ofrece también esa formulación. Esto descarta un umbral polinómico para **este contrato**, no para cualquier prueba de Erdős 81. No demuestra que regularidad sea el único método posible, ni que se necesite una torre, ni que \(e^{72}\) sea una cota inferior del umbral del Teorema 3.1. El complemento demuestra la implicación limpieza \(\Rightarrow\) redondeo; para transportar su barrera a otro redondeador haría falta la implicación inversa o un adaptador cuantitativo.

**Qué cambia si se exige cordalidad.** Tanto `CodegreeCleanupAt` como `UniformRoundingTarget` cuantifican sobre todos los grafos, mientras que el ensamblaje de la rama lejana los utiliza sobre el grafo cordal original. La familia rígida anterior no da la misma obstrucción en esa clase. En efecto, sea \(G\) cordal, sin \(K_4\), con \(n\ge2\). En un orden de eliminación perfecto, cada vértice tiene a lo sumo dos vecinos posteriores; de otro modo, él y tres de esos vecinos formarían un \(K_4\). Al contar cada arista por su extremo anterior, los primeros \(n-2\) vértices contribuyen a lo sumo dos cada uno, el penúltimo a lo sumo una y el último ninguna. Por tanto,
\[
e(G)\le2(n-2)+1=2n-3.
\tag{G.4}
\]
Si además \(G\) es rígido, sus \(T\) triángulos son disjuntos por aristas. Así, \(3T\le e(G)\), y cualquier masa triangular fraccional factible es a lo sumo \(T\). Para que se cumpla la hipótesis de masa del contrato sería necesario que
\[
\frac{\varepsilon n^2}{30}-1
\le T\le\frac{2n-3}{3}
\quad\Longrightarrow\quad n\le\frac{20}{\varepsilon}.
\tag{G.5}
\]
La cancelación de los términos constantes explica el último umbral. Por encima de él, ningún cordal rígido satisface la hipótesis de masa. En particular, las instancias densas usadas para obtener la barrera superpolinómica no pueden ser cordales. No se afirma lo mismo de cada instancia pequeña o degenerada de la construcción tripartita.

Esta cuenta delimita el alcance de la obstrucción; no demuestra una limpieza cordal ni una cota superior \(O(1/\varepsilon)\) para su umbral. Tampoco se ha formalizado aquí una versión de la implicación limpieza–redondeo restringida a cordales. Estudiar ese contrato más débil es una cuestión distinta tanto de la barrera universal como del gap triangular con clique acotada de Apéndice G.1.

## Agradecimientos

El autor está profundamente agradecido a su esposa María Paz y a sus hijos Lucas, Juan Cristóbal, Francisca, Raimundo y Benjamín por su amor, paciencia y apoyo.

## Uso de inteligencia artificial y herramientas computacionales

Se utilizaron Claude, de Anthropic, y ChatGPT/Codex, de OpenAI, para explorar argumentos, comprobarlos y preparar el manuscrito. Aristotle, de Harmonic, participó en la exploración de caminos, la búsqueda de contraejemplos, la elaboración de pruebas y su formalización y revisión en Lean; no sólo tradujo pruebas terminadas.

Certo [13], <https://github.com/jtraverso/certo-math>, y Jacobian [14], <https://github.com/morluto/jacobian>, son las herramientas computacionales usadas para explorar instancias, comprobar identidades y evaluar candidatos. Los cálculos se revisaron según su alcance; una búsqueda finita no reemplaza una prueba universal.

El autor conserva la responsabilidad por los argumentos, las citas, el código y la presentación. Ningún sistema de IA figura como autor. El borrador queda sujeto a su revisión final.

## Referencias

[1] P. Erdős, E. T. Ordman y Y. Zalcstein, «Clique partitions of chordal graphs», *Combinatorics, Probability and Computing* **2** (1993), 409–415.

[2] J. P. Traverso Gianini, *Reducción afín de perfiles para empaquetamientos fraccionales de triángulos en grafos split*, Paper I, preprint v1.3, 22 de agosto de 2026. Ediciones española e inglesa en el depósito conjunto v3, 23 de agosto de 2026. DOI de la versión consultada: <https://doi.org/10.5281/zenodo.22064657>; DOI de concepto: <https://doi.org/10.5281/zenodo.21273143>. Material complementario: <https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/main/preprints/PAPER_I>.

[3] J. P. Traverso Gianini, *Extremizadores complete-split para un funcional fraccional de cobertura de triángulos en grafos cordales*, Paper II, preprint v1.2, 22 de agosto de 2026. Ediciones española e inglesa en el depósito conjunto v3, 23 de agosto de 2026. DOI de la versión consultada: <https://doi.org/10.5281/zenodo.22064657>; DOI de concepto: <https://doi.org/10.5281/zenodo.21273143>. Material complementario: <https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/main/preprints/PAPER_II>.

[4] J. P. Traverso Gianini, *Particiones de cliques con error lineal en grafos split mediante empaquetamiento estructurado de triángulos*, Paper III, preprint v1.5, 23 de agosto de 2026. Ediciones española e inglesa en el depósito conjunto v3 de esa fecha. DOI de la versión consultada: <https://doi.org/10.5281/zenodo.22064657>; DOI de concepto: <https://doi.org/10.5281/zenodo.21273143>. Material complementario: <https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/main/preprints/PAPER_III>.

[5] Anonymous, *Clique partitions of chordal graphs with linear error*, preprint, 8 de septiembre de 2026. Versión consultada el 20 de septiembre de 2026, commit `cbde8a0a0563372b23b1b39a44180d2c0fb02f44`. Manuscrito: <https://github.com/N0zoM1z0/erdos-81/blob/cbde8a0a0563372b23b1b39a44180d2c0fb02f44/manuscript/main.pdf>. Se conserva la firma que figura en el documento; el nombre de la cuenta del repositorio no se sustituye por una atribución de autoría.

[6] P. E. Haxell y V. Rödl, «Integer and fractional packings in dense graphs», *Combinatorica* **21** (2001), 13–38.

[7] R. Yuster, «Integer and fractional packing of families of graphs», *Random Structures & Algorithms* **26** (2005), 110–118.

[8] T. F. Bloom, «Erdős Problem #81», *Erdős Problems*. Disponible en <https://www.erdosproblems.com/81>. Referencia de identificación del problema; este borrador no certifica el estado actual de revisión de las propuestas publicadas.

[9] J. P. Traverso Gianini y colaboradores de la formalización asistida, «Minimum-degree and spread matching theorems», contribución a *lean-pool*, PR #420, 2026. Disponible en <https://github.com/Vilin97/lean-pool/pull/420>; commit de fusión `d1de6d2`, 13 de septiembre de 2026. El historial y los encabezados conservan la atribución de la contribución asistida por Aristotle.

[10] L. de Moura y S. Ullrich, «The Lean 4 Theorem Prover and Programming Language», en *Automated Deduction – CADE 28*, LNCS **12699**, Springer, 2021, 625–635.

[11] The mathlib Community, «The Lean Mathematical Library», en *CPP 2020*, ACM, 2020, 367–381.

[12] J. P. Traverso Gianini, «Sum-zero triangle packing formalization», contribución de Paper III a *lean-pool*, PR #348, 2026. Disponible en <https://github.com/Vilin97/lean-pool/pull/348>; commit de fusión `540d8e3`, 25 de agosto de 2026. Véanse los créditos de formalización y de asistencia en las fuentes.

[13] J. P. Traverso Gianini, *Certo: herramientas computacionales con certificados verificables*. Disponible en <https://github.com/jtraverso/certo-math>. La versión utilizada en los experimentos debe fijarse junto con sus certificados en el suplemento.

[14] Morluto y colaboradores, *Jacobian: herramientas matemáticas componibles*. Disponible en <https://github.com/morluto/jacobian>. La atribución y las versiones de los componentes se conservan en el repositorio.

[15] O. Okechukwu, *Clique partitions and bounded simplicial defect*, arXiv:2609.20871v1, 15 de septiembre de 2026. Disponible en <https://arxiv.org/abs/2609.20871v1>. Consulta del 27 de septiembre de 2026.

[16] C. Henderson, H. Koerts, E. Roberge, S. Spirkl y R. Whitman, *Clique Partitions of Split Graphs*, proyecto anunciado en preparación en la página de investigación de R. Whitman: <https://sites.google.com/view/rebeccawhitman/research>. Consulta del 27 de septiembre de 2026; la página consultada no enlaza un manuscrito que permita comparar sus resultados.

[17] F. A. Behrend, «On Sets of Integers Which Contain No Three Terms in Arithmetical Progression», *Proceedings of the National Academy of Sciences* **32** (1946), 331–332. <https://doi.org/10.1073/pnas.32.12.331>. La constante usada en Apéndice G.2 corresponde a `Behrend.roth_lower_bound` de Mathlib v4.28.0.

[18] I. Z. Ruzsa y E. Szemerédi, «Triple systems with no six points carrying three triangles», *Combinatorics*, vol. II, Colloquia Mathematica Societatis János Bolyai **18**, North-Holland, 1978, 939–945. Registro bibliográfico del autor: <https://www.renyi.hu/~szemered/pub.html>.

[19] R. C. Bose, «On the construction of balanced incomplete block designs», *Annals of Eugenics* **9** (1939), 353–399. <https://doi.org/10.1111/j.1469-1809.1939.tb02219.x>.

[20] T. Skolem, «Some Remarks on the Triple Systems of Steiner», *Mathematica Scandinavica* **6** (1958), 273–280. <https://tidsskrift.dk/math/article/view/10551>.

[21] R. Cipollini, anuncio de prueba parcial para el problema 81 de Erdős, 10 de agosto de 2026. Resumen del autor: <https://www.erdosproblems.com/forum/thread/81/proof-claims#proof-claim-201>; manuscrito enlazado: <https://www.overleaf.com/read/thjptfhgnmxc>. Se cita por la cota anunciada con error subcuadrático, no como una entrada auditada independientemente.

[22] R. de Joannis de Verclos, *Chordal graphs are easily testable*, arXiv:1902.06135v1, 16 de febrero de 2019. Disponible en <https://arxiv.org/abs/1902.06135v1>. El argumento de remoción que sostiene el Apéndice F.3 se atribuye a este trabajo; su implementación y adaptaciones se documentan en el Apéndice F.5.

[23] N. Alon y A. Shapira, *A characterization of the (natural) graph properties testable with one-sided error*, SIAM Journal on Computing **37** (2008), 1703–1727. DOI: <https://doi.org/10.1137/06064888X>. Utilizado por el ensamblaje existencial histórico discutido en el Apéndice E.2, no como el teorema de remoción seleccionado para el Teorema C público explícito.
