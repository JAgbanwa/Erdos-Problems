# Particiones de aristas en cliques de grafos split con error lineal mediante empaquetamientos estructurados de triángulos

**Juan Pablo Traverso Gianini**  
Investigador independiente, Santiago, Chile  
[jtraverso@gmail.com](mailto:jtraverso@gmail.com)  
[ORCID: 0009-0003-6068-4096](https://orcid.org/0009-0003-6068-4096)

**Paper III de la serie**  
**Manuscrito de autor:** v0.9.5, borrador de revisión con estilo unificado (pre-preprint; consolidado editorialmente sobre v0.9.1. Los enunciados matemáticos, hipótesis, constantes, identidades desplegadas y demostraciones de §§2–9 y de los Apéndices A–D no han sido modificados. La versión v1.0 queda reservada para el primer preprint público.)  
**Fecha:** 21 de julio de 2026  
**Estado:** manuscrito de trabajo; verificación formal en curso. El proyecto Lean 4 / Mathlib v4.28.0 compila actualmente como un grafo completo de dependencias. Su núcleo elemental se ha reducido a ocho obligaciones de prueba localizadas, sin `admit`, `native_decide`, `unsafe` ni axiomas de proyecto no registrados. Los únicos axiomas matemáticos previstos son los dos insumos asintóticos externos enunciados en la Sección 2.4. Las expresiones de liberación «formalmente verificado» y «libre de `sorry`» se reservan hasta congelar el build final, el informe de axiomas y el commit. No ha sido sometido a revisión externa; la revisión bibliográfica y de novedad está incompleta.

**MSC 2020:** Primario 05C70; Secundarios 05C35, 05C72, 05C15.

---

## Resumen

Sea \(G=(K\cup I,E)\) un grafo split sobre \(n\) vértices, donde \(K\) es una clique e \(I\) es un conjunto independiente. Probamos que existe una constante absoluta \(C\) tal que

\[
|E(G)|-2\nu_3(G)
\le
\frac{n^2}{6}+Cn,
\]

donde \(\nu_3(G)\) es el número máximo de triángulos dos a dos arista-disjuntos en \(G\). En consecuencia,

\[
\operatorname{cp}(G)
\le
\frac{n^2}{6}+Cn
\]

para todo grafo split \(G\), donde \(\operatorname{cp}(G)\) es el número mínimo de cliques cuyos conjuntos de aristas particionan \(E(G)\). Esto refuerza la cota asintótica \((1/6+o(1))n^2\) hasta la escala correcta de error lineal. La constante principal es óptima.

La demostración separa tres regímenes según \(\alpha=|I|/|K|\). En el régimen bulk, un programa lineal exacto de cuatro órbitas para un perfil de vecindario común produce un margen fraccionario cuadrático uniforme; el teorema de Haxell--Rödl absorbe entonces la pérdida subcuadrática de integralidad. Cuando \(\alpha\to0\), grandes matchings arista-disjuntos anclados en los vértices independientes dejan un residuo de clique casi completo y triangularmente divisible, que se descompone exactamente mediante resultados de descomposición de grafos densos. Cuando \(\alpha\to2\), una factorización promediada cierra el corredor corto, mientras que una desigualdad de polarización con doble factor y un argumento de completación de ganancias respecto de un centro desplazado cierran el corredor mesoscópico restante.

La demostración no establece la estimación universal más fuerte \(\nu_3^*(G)-\nu_3(G)=O(n)\). Fuera del corredor extremal, una brecha de integralidad potencialmente superlineal es absorbida por la holgura fraccionaria cuadrática.

Todos los mecanismos del corredor son autocontenidos; en particular, el ingrediente de coloreo de aristas por listas se demuestra desde primeros principios en el Apéndice D. Solo quedan dos teoremas asintóticos externos, confinados a los regímenes bulk y escaso, y el teorema del corredor casi extremal (Proposición 10.1) es completamente elemental y efectivo.

**Palabras clave:** partición en cliques; grafo split; empaquetamiento de triángulos; empaquetamiento fraccionario; factorización; polarización; coloreo de aristas por listas; descomposición de grafos.

---

# 1. Introducción

## 1.1 Particiones en cliques de grafos split

Una **partición en cliques** de un grafo \(G\) es una familia de subgrafos completos cuyos conjuntos de aristas particionan \(E(G)\). Se permiten cliques de orden dos. El tamaño mínimo de una familia de este tipo se denota por \(\operatorname{cp}(G)\).

El problema de Erdős, Ordman y Zalcstein sobre particiones en cliques de grafos cordales pregunta por el orden extremal correcto de \(\operatorname{cp}(G)\) en esa clase. Su construcción complete-split —de hecho, threshold— muestra que el coeficiente \(1/6\) es inevitable. Los grafos split forman una subclase natural e importante de los grafos cordales: un grafo es split si su conjunto de vértices puede particionarse en una clique y un conjunto independiente.

Este es el tercer paper de la serie sobre el problema de Erdős--Ordman--Zalcstein de particiones en cliques (Problema de Erdős n.º 81). El Paper I prueba una cota fraccionaria finita para grafos split,
\[
|E(G)|-2\nu_3^*(G)\le n^2/6+n.
\]
El Paper II identifica la familia terminal complete-split y determina el máximo finito exacto de la funcional fraccionaria de cobertura sobre grafos cordales. Los Papers I y II son fraccionarios y están formalmente verificados en Lean 4. El presente paper es la primera entrega integral: refuerza la estimación para grafos split hasta la escala de error lineal \(n^2/6+O(n)\).

El Paper II determina exactamente el problema extremal fraccionario. Para todo \(n\),

\[
\max_{\substack{|V(G)|=n\\G\text{ cordal}}}
\bigl(|E(G)|-2\nu_3^*(G)\bigr)
=
\max_{\substack{|V(G)|=n\\G\text{ split}}}
\bigl(|E(G)|-2\nu_3^*(G)\bigr)
=
\left\lfloor\frac{(2n+1)^2}{24}\right\rfloor.
\]

Por el redondeo fraccionario-a-integral estándar, se sigue que todo grafo cordal satisface

\[
\operatorname{cp}(G)
\le
\left(\frac16+o(1)\right)n^2.
\]

El presente paper aborda una cuestión distinta y genuinamente de segundo orden: refuerza la cota integral hasta \(n^2/6+O(n)\) para grafos split arbitrarios.

## 1.2 Empaquetamientos de triángulos y objetivo de error lineal

Sea \(\nu_3(G)\) el número máximo de triángulos dos a dos arista-disjuntos en \(G\). Todo empaquetamiento de este tipo produce una partición en cliques: se conservan los triángulos empaquetados y se usa un \(K_2\) para cada arista no cubierta. Por tanto,

\[
\operatorname{cp}(G)
\le
|E(G)|-2\nu_3(G).
\tag{1.1}
\]

El teorema central de este paper es una estimación integral en la escala correcta de segundo orden.

### Teorema 1.1 — Teorema de error lineal para grafos split

Existe una constante absoluta \(C\) tal que todo grafo split \(G\) sobre \(n\) vértices satisface

\[
\boxed{
|E(G)|-2\nu_3(G)
\le
\frac{n^2}{6}+Cn.
}
\tag{1.2}
\]

Al combinar (1.1) con el Teorema 1.1 se obtiene la afirmación para particiones en cliques.

### Corolario 1.2 — Cota de error lineal para particiones en cliques

Existe una constante absoluta \(C\) tal que todo grafo split \(G\) sobre \(n\) vértices satisface

\[
\boxed{
\operatorname{cp}(G)
\le
\frac{n^2}{6}+Cn.
}
\tag{1.3}
\]

La familia complete-split —de hecho threshold— de Erdős--Ordman--Zalcstein
\[
K_p\vee\overline K_{2p},
\qquad n=3p,
\]
muestra que la constante principal \(1/6\) es óptima y que aparece de manera natural un término lineal.

![El extremizador complete-split \(K_p\vee\overline K_{2p}\). El dibujo es esquemático: el lado izquierdo representa la clique \(K_p\), el derecho un conjunto independiente de orden \(2p\), y todas las aristas cruzadas están presentes. Se destaca un triángulo para mostrar que todo triángulo contiene una arista de la clique.](paperIII_figures_bilingual_v0.9.7/fig1_complete_split_extremizer_es.png)

**Figura 1.** El grafo complete-split \(K_p\vee\overline K_{2p}\). Todas las aristas entre las dos partes están presentes y el lado independiente no tiene aristas internas. Como todo triángulo contiene una arista de la clique, un empaquetamiento de triángulos arista-disjuntos utiliza a lo sumo \(\binom p2\) triángulos; véase la Sección 10.2. La figura es ilustrativa y no se usa como premisa de la demostración.

## 1.3 Localización de obstrucciones hipotéticas

### Proposición 1.3 — Localización de obstrucciones hipotéticas

Supongamos, por contradicción, que no existe una cota absoluta con error lineal y, para cada entero positivo \(k\), escojamos un grafo split \(G_k\) de orden mínimo que satisface

\[
|E(G_k)|-2\nu_3(G_k)>\frac{|V(G_k)|^2}{6}+k|V(G_k)|.
\]

Tras pasar a una subsucesión y escribir \(|K_k|=p_k\), \(|I_k|=q_k\), toda sucesión hipotética de este tipo debe satisfacer

\[
\frac{q_k}{p_k}\longrightarrow 2.
\]

Además, si \(q_k=2p_k-s_k\), las estimaciones del régimen bulk y del corredor corto fuerzan

\[
\sqrt{p_k}\ll s_k=o(p_k).
\]

Por tanto, toda obstrucción a un término de error lineal tendría que concentrarse en el corredor mesoscópico casi extremal. La dicotomía entre dispersión alta y baja de la Sección 9 excluye ese corredor.

## 1.4 Lo que el teorema no demuestra

Sea \(\nu_3^*(G)\) el número fraccionario de empaquetamiento de triángulos. La presente demostración **no** establece

\[
\nu_3^*(G)-\nu_3(G)=O(n)
\tag{1.4}
\]

uniformemente sobre todos los grafos split.

En efecto, escribamos

\[
\Delta(G)=\nu_3^*(G)-\nu_3(G)
\]

y

\[
S(G)=\frac{n^2}{6}-\bigl(|E(G)|-2\nu_3^*(G)\bigr).
\]

Entonces

\[
|E(G)|-2\nu_3(G)
=
\frac{n^2}{6}-S(G)+2\Delta(G).
\tag{1.5}
\]

El Teorema 1.1 solo requiere

\[
2\Delta(G)\le S(G)+O(n).
\]

En el régimen bulk, \(S(G)\) es cuadrático y absorbe la pérdida general de integralidad \(o(n^2)\). Por ello, el problema de una brecha universal lineal de integralidad permanece abierto.

## 1.5 Arquitectura de la demostración

Escribamos

\[
|K|=p,
\qquad
|I|=q,
\qquad
\alpha=\frac qp.
\]

La razón \(\alpha=q/p\) determina qué fuente de holgura está disponible. Primero resolvemos \(q\ge2p-1\) mediante una factorización promediada directa, y desde entonces podemos suponer \(0\le\alpha<2\). Una sucesión hipotética de contraejemplos tiene una subsucesión en uno de tres regímenes.

1. **Bulk:** \(\alpha\) permanece alejado tanto de \(0\) como de \(2\). Un LP exacto de perfil común y un argumento de clonado fraccional producen holgura fraccionaria cuadrática. Haxell--Rödl convierte el empaquetamiento fraccionario en uno integral con pérdida \(o(n^2)\).

2. **Lado independiente escaso:** \(\alpha\to0\). Cada vértice independiente ancla un matching grande dentro de su vecindario. La clique residual es casi completa. Tras eliminar \(O(p)\) aristas para corregir divisibilidad, admite una descomposición exacta en triángulos.

3. **Corredor casi extremal:** \(\alpha\to2\). Escribimos \(q=2p-s\). La factorización promediada cierra \(s=O(\sqrt p)\). Para \(\sqrt p\ll s=o(p)\), la dispersión alta se paga mediante un término de polarización con doble factor, mientras que la dispersión baja implica cercanía a un centro común y se trata mediante completación de ganancias respecto de un centro desplazado.

La división no es meramente formal. En el bulk hay suficiente holgura fraccionaria cuadrática para absorber una pérdida general de redondeo \(o(n^2)\). En los dos extremos esa holgura desaparece, y la demostración reemplaza el redondeo genérico por construcciones adaptadas a la geometría de la presentación split.

![Mapa esquemático de los tres regímenes de la demostración sobre el eje \(\alpha=q/p\): el régimen escaso cerca de \(0\), el bulk alejado de ambos extremos y el corredor casi extremal cerca de \(2\).](paperIII_figures_bilingual_v0.9.7/fig2_alpha_regimes_es.png)

**Figura 2.** Los tres regímenes usados en la demostración. Se muestran los umbrales principales del corredor; las hipótesis completas aparecen en las Secciones 4, 8 y 9. Los regímenes extremos son asintóticos, no subintervalos rígidos de \([0,2]\).

## 1.6 Auditorías computacionales suplementarias

El paquete de cierre adjunto contiene pruebas de regresión con aritmética exacta e instancias finitas para identidades y desigualdades cuantitativas seleccionadas de la demostración.

Cada afirmación auditada se demuestra analíticamente en el manuscrito. Ningún cálculo, script, enumeración finita ni salida de solver es una premisa lógica del Teorema 1.1. El material suplementario se proporciona únicamente para verificación independiente, pruebas de regresión y reproducibilidad.

## 1.7 Organización

La Sección 2 fija la notación y los insumos externos. La Sección 3 resuelve el LP de perfil común. La Sección 4 demuestra la cota de clonado fraccional y el margen fraccionario global. La Sección 5 desarrolla el redondeo por factorización simple y doble. La Sección 6 demuestra la polarización. La Sección 7 demuestra la completación de ganancias respecto de un centro desplazado. La Sección 8 trata el régimen con lado independiente escaso. La Sección 9 ensambla los tres regímenes. La Sección 10 registra los corolarios, la Sección 11 discute la demostración y sus limitaciones, y la Sección 12 describe usos futuros y direcciones abiertas. Los apéndices contienen detalles algebraicos, la corrección de divisibilidad, material de reproducibilidad y una demostración autocontenida del teorema de coloreo de aristas por listas (Apéndice D).

---

# 2. Preliminares

## 2.1 Notación split

En todo el paper,

\[
G=(K\sqcup I,E)
\]

es un grafo split, donde \(K\) es una clique de tamaño \(p\) e \(I=\{v_1,\ldots,v_q\}\) es independiente.

Para \(v_i\in I\), escribimos

\[
N_i=N(v_i)\cap K,
\qquad
d_i=|N_i|,
\qquad
S_i=K\setminus N_i,
\qquad
m_i=|S_i|.
\]

Definimos

\[
M=\sum_i m_i,
\qquad
S_2=\sum_i m_i^2.
\]

Cuando \(q\) está cerca de \(2p\), escribimos

\[
q=2p-s.
\tag{2.1}
\]

## 2.2 Empaquetamientos de triángulos

Un empaquetamiento fraccionario de triángulos es una asignación de pesos no negativos a los triángulos de \(G\) tal que el peso total que pasa por cada arista es a lo sumo uno. Su valor máximo es \(\nu_3^*(G)\).

El dual es una cobertura fraccionaria de triángulos: una asignación de pesos no negativos a las aristas tal que cada triángulo recibe peso total al menos uno. La dualidad de programación lineal da igualdad entre ambos valores óptimos.

## 2.3 Factorizaciones de grafos completos

Adoptamos las convenciones de borde

\[
\chi'(K_0)=\chi'(K_1)=0.
\]

Para \(t\ge2\), el índice cromático del grafo completo es

\[
\chi'(K_t)
=
\begin{cases}
t-1,&t\text{ par},\\
t,&t\text{ impar}.
\end{cases}
\tag{2.2}
\]

Por tanto, \(E(K_t)\) se descompone en \(\chi'(K_t)\) matchings. Las convenciones para \(t\le1\) hacen que el mismo lenguaje sea válido para conjuntos vacíos de aristas.

## 2.4 Teoremas externos

Usamos dos insumos asintóticos externos. Versiones anteriores citaban un tercero, el teorema de coloreo de aristas por listas; el caso requerido por este paper se demuestra de manera autocontenida en el Apéndice D, por lo que las Secciones 5--7 y la Proposición 10.1 no dependen de teoremas externos.

### Teorema 2.1 — Haxell--Rödl/Yuster

Para todo grafo fijo \(H\),

\[
\nu_H^*(G)-\nu_H(G)=o(|V(G)|^2)
\]

uniformemente sobre los grafos \(G\). Lo aplicamos con \(H=K_3\).

### Teorema 2.2 — Coloreo de aristas por listas (demostrado en el Apéndice D)

Sea \(B\) un grafo bipartito de grado máximo \(\Delta(B)\). Si a cada arista \(e\) se le asigna una lista \(L(e)\) con

\[
|L(e)|\ge\Delta(B),
\]

entonces \(B\) admite un coloreo propio de aristas que elige el color de cada arista desde su lista.

Este es el caso de grado máximo del teorema de Galvin [12]. En el Apéndice D se entrega una demostración autocontenida —coloreo de König, emparejamientos estables y lema del núcleo—, por lo que no constituye una dependencia externa del paper. No se necesita el refinamiento local
\[
|L(xy)|\ge\max\{d(x),d(y)\}
\]
de Borodin, Kostochka y Woodall [2]: la hipótesis (7.2) ya acota cada lista por el grado máximo del grafo de ganancias.

### Teorema 2.3 — Descomposición densa en triángulos

Para todo \(\varepsilon>0\), todo grafo triangularmente divisible \(H\), suficientemente grande, que satisface

\[
\delta(H)\ge(0.9+\varepsilon)|V(H)|
\]

admite una descomposición en triángulos. Esto se sigue del teorema de Dross sobre descomposición fraccionaria en triángulos —grado mínimo \(0.9v\) es suficiente fraccionariamente— combinado con el teorema de absorción iterativa de Barber, Kühn, Lo y Osthus, que convierte el umbral fraccionario en un umbral de descomposición exacta para grafos triangularmente divisibles, salvo \(\varepsilon\) y para orden suficientemente grande.

---

# 3. El programa lineal de perfil común

Para enteros \(p,q,d\), sea \(H(p,q,d)\) el grafo split con clique \(K\), \(|K|=p\), conjunto independiente \(I\), \(|I|=q\), y un conjunto fijo \(N\subseteq K\), \(|N|=d\), tal que todo vértice de \(I\) tiene vecindario \(N\). Definimos \(R=K\setminus N\) y \(r=p-d\).

## 3.1 Variables simétricas de cobertura

Al promediar sobre permutaciones de \(N\), \(R\) e \(I\), podemos suponer que una cobertura fraccionaria óptima de triángulos es constante en las cuatro clases de aristas

\[
E(N),
\qquad E(N,I),
\qquad E(N,R),
\qquad E(R).
\]

Sean \(a,b,c,e\) sus respectivos pesos. Las restricciones de triángulos son

\[
a+2b\ge1,
\qquad
3a\ge1,
\tag{3.1}
\]

\[
a+2c\ge1,
\qquad
2c+e\ge1,
\qquad
3e\ge1.
\tag{3.2}
\]

Las restricciones correspondientes a tipos de triángulos vacíos pueden omitirse; la fórmula siguiente sigue siendo válida para \(p\ge3\).

La función objetivo es

\[
\binom d2a+qdb+dr\,c+\binom r2e.
\tag{3.3}
\]

## 3.2 Solución exacta

### Teorema 3.1 — Fórmula de perfil común

Para \(p\ge3\),

\[
\boxed{
\nu_3^*(H(p,q,d))
=
F(p,q,d),
}
\tag{3.4}
\]

donde

\[
\boxed{
F(p,q,d)
=
\min\left\{
\frac{\binom p2+qd}{3},
\binom d2+\binom r2,
\binom d2+\frac{dr+\binom r2}{3}
\right\}.
}
\tag{3.5}
\]

### Demostración

En un óptimo,

\[
b=\frac{1-a}{2},
\qquad
c=\frac{1-\min\{a,e\}}2,
\qquad
\frac13\le a,e\le1.
\]

Si \(a\le e\), disminuir \(e\) hasta \(a\) no puede aumentar la función objetivo. Por tanto, basta minimizar sobre

\[
\frac13\le e\le a\le1.
\]

La función objetivo es afín en este triángulo, por lo que un mínimo se alcanza en

\[
(a,e)=\left(\frac13,\frac13\right),
\qquad
(1,1),
\qquad
\left(1,\frac13\right).
\]

Los valores correspondientes son precisamente las tres expresiones de (3.5). La dualidad completa la demostración. \(\square\)

## 3.3 Interpretación de las tres coberturas

El mínimo de (3.5) se recuerda más fácilmente mediante los tres vértices del programa reducido de dos variables. Cada vértice representa una forma distinta de pagar las restricciones de triángulos.

| Patrón de cobertura | Vértice reducido \((a,e)\) | Valor | Descripción geométrica |
|---|---:|---:|---|
| **Uniforme** | \((1/3,1/3)\) | \(\bigl(\binom p2+qd\bigr)/3\) | Todas las órbitas de aristas relevantes se cubren a la tasa fraccionaria uniforme. |
| **Separada** | \((1,1)\) | \(\binom d2+\binom r2\) | Los dos bloques de clique \(N\) y \(R\) se pagan internamente, sin peso en la órbita cruzada. |
| **Vecindario caliente** | \((1,1/3)\) | \(\binom d2+\bigl(dr+\binom r2\bigr)/3\) | El vecindario común \(N\) se paga por completo, mientras la estructura residual de la clique permanece fraccionaria. |

Las etiquetas son descriptivas y no introducen nuevas definiciones. En los cálculos posteriores nos referimos a las ramas primera, segunda y tercera de \(F\). Esta tricotomía finita es la fuente del margen fraccionario global.

---

# 4. Clonado fraccional y margen fraccionario exacto

## 4.1 Clonado fraccional

La operación de clonado usada aquí es el análogo, en el lado de cobertura, de la simetrización por clones del Paper II. Allí se copian por pares vértices o clases de clones para simplificar un grafo cordal. Aquí se copia \(q\) veces un perfil del lado independiente en un único paso de promedio; el grafo \(H(p,q,d_i)\) registra el perfil común resultante.

### Lema 4.1 — Cota de clonado fraccional

Para todo grafo split con \(q\ge1\),

\[
\boxed{
\nu_3^*(G)
\ge
\frac1q\sum_{i=1}^qF(p,q,d_i).
}
\tag{4.1}
\]

### Demostración

Sea \(y\) cualquier cobertura fraccionaria de triángulos de \(G\). Definamos

\[
A=\sum_{e\in E(K)}y_e
\]

y

\[
B_i=\sum_{x\in N_i}y_{v_ix}.
\]

Reemplazamos \(v_i\) por \(q\) clones independientes, todos con vecindario \(N_i\), y damos a cada clon los pesos incidentes de \(v_i\). Junto con los pesos originales de las aristas de la clique, esto constituye una cobertura fraccionaria de \(H(p,q,d_i)\) de peso \(A+qB_i\). Por tanto,

\[
A+qB_i\ge F(p,q,d_i).
\]

Al sumar sobre \(i\), obtenemos

\[
q\left(A+\sum_iB_i\right)
\ge
\sum_iF(p,q,d_i).
\]

Minimizar sobre las coberturas demuestra el lema. \(\square\)

## 4.2 El margen exacto

Supongamos \(0<q\le2p\), definamos

\[
\alpha=\frac qp,
\]

y el umbral de empaquetamiento

\[
T(G)=\frac12\left(|E(G)|-\frac{(p+q)^2}{6}\right).
\tag{4.2}
\]

Definamos

\[
\mu(\alpha)
=
\begin{cases}
\alpha^2/12,&0\le\alpha\le2/3,\\
(2-\alpha)^2/48,&2/3\le\alpha\le2.
\end{cases}
\tag{4.3}
\]

### Teorema 4.2 — Margen fraccionario unificado

\[
\boxed{
\nu_3^*(G)
\ge
T(G)+\mu(\alpha)p^2-\frac p4.
}
\tag{4.4}
\]

### Demostración

Sea

\[
C_\alpha=\frac{2-2\alpha-\alpha^2}{12}.
\]

Para cada rama de \(F(p,q,d)\), completar cuadrados da

\[
F(p,q,d)
\ge
\frac{qd}{2}+C_\alpha p^2+\mu(\alpha)p^2-\frac p2.
\tag{4.5}
\]

Los tres mínimos residuales normalizados son

\[
\frac{\alpha^2}{12},
\qquad
\frac{(2-\alpha)^2}{48},
\]

y

\[
\begin{cases}
\alpha(8-5\alpha)/48,&\alpha\le4/3,\\
(2-\alpha)^2/12,&\alpha\ge4/3.
\end{cases}
\]

El tercero nunca está por debajo del mínimo de los dos primeros. Al promediar (4.5) mediante el Lema 4.1 obtenemos

\[
\nu_3^*(G)
\ge
\frac12\sum_i d_i+C_\alpha p^2+\mu(\alpha)p^2-\frac p2.
\]

Como

\[
T(G)=\frac12\sum_i d_i+C_\alpha p^2-\frac p4,
\]

se sigue (4.4). \(\square\)

## 4.3 Consecuencia en el bulk

Si

\[
\varepsilon\le\alpha\le2-\varepsilon,
\]

entonces \(\mu(\alpha)\ge c_\varepsilon>0\). El Teorema 4.2 y Haxell--Rödl implican

\[
\nu_3(G)\ge T(G)
\]

para todos los grafos suficientemente grandes de este régimen. Por consiguiente,

\[
|E(G)|-2\nu_3(G)
\le
\frac{n^2}{6}.
\tag{4.6}
\]

---

# 5. Redondeo por factorización cerca de \(q=2p\)

Sea

\[
r_p=\chi'(K_p).
\]

## 5.1 Promedio con un factor

### Lema 5.1

Si \(q\ge r_p\), entonces

\[
\boxed{
\nu_3(G)
\ge
\frac1q\sum_i\binom{d_i}{2}.
}
\tag{5.1}
\]

### Demostración

Factorizamos \(K_p\) en \(r_p\) matchings. Asignamos los factores inyectiva y uniformemente a los vértices de \(I\). En el factor asignado a \(v_i\), conservamos solo las aristas con ambos extremos en \(N_i\). Las aristas conservadas forman triángulos \(KKI\) válidos y arista-disjuntos.

El número esperado de aristas conservadas es

\[
\frac1q\sum_i\sum_{j=1}^{r_p}|F_j\cap E(K[N_i])|
=
\frac1q\sum_i\binom{d_i}{2}.
\]

Alguna asignación alcanza al menos la esperanza. \(\square\)

Al escribir \(q=2p-s\), la sustitución da

\[
\Phi(G)
\le
\frac{n^2}{6}+\frac p2-\frac{s^2}{6}
+
\frac{(s-1)M-S_2}{q}.
\tag{5.2}
\]

Usando \(S_2\ge M^2/q\) y maximizando la parábola resultante se obtiene

\[
\boxed{
\Phi(G)
\le
\frac{n^2}{6}+\frac p2+\frac{s^2-6s+3}{12}.
}
\tag{5.3}
\]

Así, \(s=O(\sqrt p)\) queda cerrado con error lineal.

## 5.2 Redondeo con doble factor

Para una arista \(e=xy\) de la clique, sea

\[
b_e=|\{i:\{x,y\}\not\subseteq N_i\}|.
\]

Definamos

\[
h=\min\{r_p,q-r_p\},
\qquad
\delta=\frac h{r_p}.
\]

Elegimos uniformemente al azar el conjunto de \(h\) factores que reciben dos vértices independientes distintos, damos un vértice independiente a cada factor restante y asignamos los vértices independientes a las posiciones resultantes de manera uniforme e inyectiva. Todas las esperanzas siguientes se toman respecto de ambas elecciones aleatorias; alguna elección determinista alcanza al menos la ganancia esperada.

### Lema 5.2 — Desigualdad de doble factor

Si \(q\ge r_p\), entonces

\[
\boxed{
\begin{aligned}
\Phi(G)
\le{}&
\frac{n^2}{6}+\frac p2-\frac{s^2}{6}
+
\frac{(s-1)M-S_2}{q}\\
&-
\frac{2\delta V}{q(q-1)},
\end{aligned}
}
\tag{5.4}
\]

donde

\[
V=\sum_{e\in E(K)}b_e(q-b_e).
\tag{5.5}
\]

### Demostración

Si el factor que contiene \(e\) recibe un vértice, \(e\) se pierde con probabilidad \(b_e/q\). Si recibe dos vértices, se pierde solo cuando ambos son malos, con probabilidad

\[
\frac{b_e(b_e-1)}{q(q-1)}.
\]

Por tanto, el número esperado \(U\) de aristas perdidas de la clique es

\[
U
=
\frac1q\sum_e b_e
-
\frac{\delta}{q(q-1)}\sum_e b_e(q-b_e).
\]

Como cada factor es un matching, cada arista conservada puede asignarse a uno de sus vértices admisibles sin crear una colisión de aristas. La sustitución da (5.4). \(\square\)

---

# 6. Polarización cuantitativa

Para cada \(i\), definimos

\[
\mathcal B_i=\{e\in E(K):e\cap S_i\ne\varnothing\}.
\]

Entonces

\[
V=\sum_{i,j}|\mathcal B_i\setminus\mathcal B_j|.
\tag{6.1}
\]

Sea

\[
m=\max_i|S_i|.
\]

### Lema 6.1 — Desigualdad de polarización

Si \(2p-3m-1\ge0\), entonces

\[
\boxed{
V
\ge
\frac{2p-3m-1}{4}
\sum_{i,j}|S_i\triangle S_j|.
}
\tag{6.2}
\]

### Demostración

Sea

\[
a_{ij}=|S_i\setminus S_j|.
\]

Las aristas de \(\mathcal B_i\setminus\mathcal B_j\) son precisamente las aristas de \(K_p-S_j\) que inciden en \(S_i\setminus S_j\). Por tanto,

\[
|\mathcal B_i\setminus\mathcal B_j|
=
\frac{a_{ij}\bigl(2(p-|S_j|)-a_{ij}-1\bigr)}2.
\]

Como \(|S_j|\le m\) y \(a_{ij}\le m\),

\[
|\mathcal B_i\setminus\mathcal B_j|
\ge
\frac{2p-3m-1}{2}|S_i\setminus S_j|.
\]

Sumamos sobre pares ordenados y usamos

\[
\sum_{i,j}|S_i\setminus S_j|
=
\frac12\sum_{i,j}|S_i\triangle S_j|.
\]

Esto demuestra (6.2). \(\square\)

---

# 7. Completación de ganancias respecto de un centro desplazado

Fijemos \(R\subseteq K\). Definamos

\[
\rho=|R|,
\qquad
Q=K\setminus R,
\qquad
b=|Q|.
\]

Para cada \(i\), definimos

\[
T_i=S_i\setminus R,
\qquad
t_i=|T_i|,
\]

y

\[
G_i=R\setminus S_i,
\qquad
g_i=|G_i|.
\]

Sea

\[
A_R=\sum_i t_i,
\qquad
A_{2,R}=\sum_i t_i^2,
\qquad
B_R=\sum_i g_i.
\]

Definimos

\[
r_b=\chi'(K_b),
\qquad
u=q-r_b.
\]

Supongamos

\[
b\ge2,
\qquad
q\ge r_b,
\qquad
b\ge\chi'(K_\rho),
\tag{7.1}
\]

y

\[
b-t_i\ge\max\{\rho,u\}
\qquad
\text{para todo }i.
\tag{7.2}
\]

Definimos

\[
\theta_R=\frac{\max\{\rho-1,0\}}{b}
\]

y

\[
\kappa_R
=
1-2(1-\theta_R)\frac{u}{q}.
\tag{7.3}
\]

## 7.1 Empaquetamiento dentro de \(Q\)

Reservamos un conjunto \(U\subseteq I\) de \(u\) vértices; obsérvese que \(|I\setminus U|=q-u=r_b\) exactamente. Asignamos biyectivamente los \(r_b\) vértices restantes a una factorización de \(K[Q]\).

Para \(v_i\), el número de aristas no disponibles de \(K[Q]\) es

\[
\beta_i
=
\binom b2-\binom{b-t_i}{2}.
\tag{7.4}
\]

Para \(U\) fijo, el promedio sobre las asignaciones da al menos

\[
\binom b2-\frac1{r_b}\sum_{i\notin U}\beta_i
\tag{7.5}
\]

triángulos \(QQI\) arista-disjuntos.

## 7.2 El grafo de ganancias

Construimos un grafo bipartito con partes \(U\) y \(R\), uniendo \(v_i\) con \(r\) cuando \(r\in G_i\). Asignamos la lista

\[
L(v_ir)=N_i\cap Q.
\]

Por (7.2), toda lista satisface

\[
|L(v_ir)|=b-t_i
\ge
\max\{\rho,u\}
\ge
\Delta,
\]

donde \(\Delta\) es el grado máximo del grafo de ganancias, pues \(d(v_i)=g_i\le\rho\) y \(d(r)\le|U|=u\). El Teorema 2.2, demostrado de manera autocontenida en el Apéndice D, proporciona un coloreo propio de aristas por listas. Si \(v_ir\) recibe el color \(z\in Q\), tomamos el triángulo \(v_irz\). Esto produce

\[
B_U=\sum_{i\in U}g_i
\]

triángulos \(IRQ\) arista-disjuntos.

## 7.3 Completación dentro de \(R\)

Para cada \(z\in Q\), sea \(U_z\subseteq R\) el conjunto de vértices \(r\) para los cuales \(rz\) fue usado por un triángulo \(IRQ\).

Si \(\rho\le1\), el grafo \(K[R]\) no tiene aristas, por lo que esta completación no aporta triángulos \(RRQ\). Supongamos entonces \(\rho\ge2\). Factorizamos \(K[R]\), inyectamos sus factores en los colores \(z\in Q\) y eliminamos del factor asignado a \(z\) toda arista incidente en \(U_z\). El promedio sobre las inyecciones pierde a lo sumo

\[
\frac{\rho-1}{b}\sum_z|U_z|
=
\theta_RB_U
\]

aristas. Por consiguiente, en todos los casos obtenemos al menos

\[
\binom\rho2-\theta_RB_U
\]

triángulos \(RRQ\) adicionales.

Las tres familias \(QQI\), \(IRQ\) y \(RRQ\) son arista-disjuntas. En particular, la eliminación por colores prohibidos evita que un triángulo \(IRQ\) y uno \(RRQ\) compartan una arista \(rz\).

## 7.4 La desigualdad centrada

Elegimos \(U\), \(|U|=u\), que maximice

\[
\sum_{i\in U}
\left(
\frac{2\beta_i}{r_b}+2(1-\theta_R)g_i
\right).
\]

La suma de los mejores \(u\) términos es al menos \(u/q\) veces la suma total. Usando

\[
2\sum_i\beta_i
=(2b-1)A_R-A_{2,R},
\]

obtenemos el lema local principal.

### Lema 7.1 — Desigualdad de ganancias reservadas respecto de un centro desplazado

Bajo (7.1)--(7.2),

\[
\boxed{
\begin{aligned}
\Phi(G)
\le{}&
\frac{n^2}{6}+\frac p2-\frac{s^2}{6}
+s\rho-2\rho^2\\
&+
\kappa_RB_R
+
\frac{(s-2\rho-1)A_R-A_{2,R}}q.
\end{aligned}
}
\tag{7.6}
\]

---

# 8. Régimen con lado independiente escaso

Supongamos \(q=o(p)\). Demostramos la cota requerida de manera directa e integral.

## 8.1 Cota de grado para un contraejemplo mínimo

En el argumento global por contradicción, un contraejemplo mínimo con penalización \(kn\) satisface, para todo \(v\in I\),

\[
d(v)>
\frac{2n-1}{6}+k.
\tag{8.1}
\]

Como \(q=o(p)\), esto implica eventualmente

\[
d(v)\ge2q+2.
\tag{8.2}
\]

## 8.2 Matchings sucesivos

Ordenamos \(I=\{v_1,\ldots,v_q\}\). Elegimos sucesivamente matchings arista-disjuntos

\[
M_i\subseteq K[N_i]
\]

de tamaño \(\lfloor d_i/2\rfloor\).

Antes de elegir \(M_i\), cada vértice ha perdido a lo sumo \(i-1\) aristas incidentes, por lo que el grafo disponible sobre \(N_i\) tiene grado mínimo al menos

\[
d_i-i\ge d_i/2.
\]

El teorema de Dirac proporciona un ciclo hamiltoniano y, por tanto, un matching del tamaño requerido.

Sea

\[
F=\bigcup_iM_i.
\]

Entonces

\[
|F|
\ge
\frac12\sum_i d_i-\frac q2,
\qquad
\Delta(F)\le q.
\tag{8.3}
\]

Las aristas de \(M_i\) producen \(|M_i|\) triángulos \(KKI\) arista-disjuntos con ápice \(v_i\).

## 8.3 Corrección de divisibilidad

El grafo residual sobre la clique

\[
R_0=K_p-F
\]

satisface

\[
\delta(R_0)
\ge
p-1-q
=(1-o(1))p.
\tag{8.4}
\]

En particular, para todos los miembros suficientemente grandes de la sucesión, \(\delta(R_0)>p/2\). El teorema de Dirac da entonces un ciclo hamiltoniano y, por tanto, un camino hamiltoniano

\[
P=x_1x_2\cdots x_p
\]

contenido en \(R_0\). Sea \(O\) el conjunto de vértices de grado impar de \(R_0\). Por el lema del apretón de manos, \(|O|\) es par. Definimos el subgrafo del camino \(J\subseteq P\) mediante

\[
x_jx_{j+1}\in E(J)
\quad\Longleftrightarrow\quad
|O\cap\{x_1,\ldots,x_j\}|\text{ es impar}.
\tag{8.5}
\]

Para un vértice interno \(x_j\), la paridad de su grado en \(J\) es el cambio de paridad del prefijo entre las posiciones \(j-1\) y \(j\), y por tanto es \(1\) exactamente cuando \(x_j\in O\). La misma conclusión vale en los dos extremos porque \(|O|\) es par. En consecuencia,

\[
\operatorname{Odd}(J)=O,
\qquad
|E(J)|\le p-1,
\qquad
\Delta(J)\le2.
\tag{8.6}
\]

Así,

\[
R_1:=R_0-J
\]

tiene todos sus grados pares, y

\[
\delta(R_1)\ge p-1-q-2.
\tag{8.7}
\]

Como \(q=o(p)\), eventualmente \(\delta(R_1)>3p/4\). Por el teorema de Turán, \(R_1\) contiene una copia de \(K_5\). Elegimos un \(C_4\) y un \(C_5\) dentro de este \(K_5\) fijo. Según

\[
|E(R_1)|\equiv0,1,2\pmod3,
\]

eliminamos, respectivamente, nada, el \(C_4\) o el \(C_5\). Sea \(C\) el ciclo eliminado, permitiendo \(C=\varnothing\), y definamos

\[
H:=R_1-E(C).
\]

Cada vértice pierde cero o dos aristas incidentes cuando se elimina un ciclo, por lo que todos los grados de \(H\) siguen siendo pares. Además, \(|E(C)|\equiv |E(R_1)|\pmod3\), y por tanto

\[
|E(H)|\equiv0\pmod3.
\]

Luego \(H\) es triangularmente divisible. La pérdida total de grado al pasar de \(R_0\) a \(H\) es a lo sumo cuatro, de modo que

\[
\delta(H)\ge p-1-q-4.
\tag{8.8}
\]

Para aplicar el Teorema 2.3 con un parámetro fijo, tomemos por ejemplo \(\varepsilon_0=1/100\). Como \(q=o(p)\), eventualmente \(q\le p/20\), y entonces, para \(p\) suficientemente grande,

\[
\delta(H)\ge p-1-q-4\ge0.91p=(0.9+\varepsilon_0)|V(H)|.
\tag{8.9}
\]

El Teorema 2.3 da ahora una descomposición exacta de \(H\) en triángulos. Obsérvese que el teorema de descomposición se aplica sobre el conjunto original de \(p\) vértices: no se elimina ningún vértice durante la corrección. La corrección completa elimina a lo sumo \(p+4\) aristas.

## 8.4 Tamaño del empaquetamiento

El empaquetamiento combinado tiene tamaño

\[
\begin{aligned}
\nu_3(G)
&\ge
|F|+\frac{\binom p2-|F|-O(p)}3\\
&=
\frac13\binom p2+\frac23|F|-O(p)\\
&\ge
\frac13\binom p2+\frac13\sum_i d_i-O(p+q).
\end{aligned}
\tag{8.10}
\]

En consecuencia,

\[
\begin{aligned}
\Phi(G)
&\le
\frac13\binom p2+\frac13\sum_i d_i+O(p+q)\\
&\le
\frac13\binom p2+\frac{pq}{3}+O(p+q)\\
&=
\frac{(p+q)^2}{6}-\frac{p+q^2}{6}+O(p+q).
\end{aligned}
\tag{8.11}
\]

Esto es a lo sumo \(n^2/6+O(n)\).

---

# 9. Demostración del teorema principal

Demostramos ahora el Teorema 1.1 por contradicción.

Supongamos que ninguna constante absoluta funciona. Para cada entero positivo \(k\), elegimos un grafo split \(G_k\), mínimo en su número \(n_k\) de vértices, tal que

\[
\Phi(G_k)
>
\frac{n_k^2}{6}+kn_k.
\tag{9.1}
\]

Necesariamente \(n_k\to\infty\). Para todo \(v\in I(G_k)\), la minimalidad da

\[
\Phi(G_k)
\le
\Phi(G_k-v)+d(v),
\]

y por tanto

\[
\boxed{
d(v)>
\frac{2n_k-1}{6}+k.
}
\tag{9.2}
\]

Primero, si \(q_k\ge2p_k-1\), el Lema 5.1 da

\[
\Phi(G_k)
\le
\frac{n_k^2}{6}+\frac{p_k}{2},
\]

lo que contradice (9.1) para \(k\) grande. Podemos entonces suponer \(q_k<2p_k-1\) y pasar a una subsucesión según

\[
\alpha_k=\frac{q_k}{p_k}\in[0,2).
\]

## 9.1 Régimen bulk

Supongamos que para algún \(\varepsilon>0\),

\[
\varepsilon\le\alpha_k\le2-\varepsilon.
\]

El Teorema 4.2 da

\[
\nu_3^*(G_k)
\ge
T(G_k)+c_\varepsilon p_k^2-O(p_k).
\]

Haxell--Rödl da

\[
\nu_3(G_k)
\ge
\nu_3^*(G_k)-o(n_k^2).
\]

Para \(k\) suficientemente grande, el margen cuadrático domina la pérdida de integralidad, de modo que \(\nu_3(G_k)\ge T(G_k)\), en contradicción con (9.1).

## 9.2 El extremo \(\alpha_k\to0\)

Este caso se cierra mediante la Sección 8, que da una constante absoluta \(C_0\) tal que

\[
\Phi(G_k)
\le
\frac{n_k^2}{6}+C_0n_k.
\]

Para \(k>C_0\), esto contradice (9.1).

## 9.3 El extremo \(\alpha_k\to2\)

Escribimos

\[
q=2p-s,
\qquad
s=o(p).
\]

Si \(s=O(\sqrt p)\), la desigualdad (5.3) da la cota de error lineal requerida. Supongamos desde ahora

\[
\sqrt p\ll s=o(p).
\tag{9.3}
\]

Para todos los miembros suficientemente grandes de la sucesión,

\[
p\ge2304,
\qquad
6\sqrt p\le s\le\frac p8,
\qquad
k\ge1.
\tag{9.4}
\]

Por (9.2),

\[
m_i=|S_i|
<
\frac s3+\frac16-k
\le
\frac s3-\frac56.
\]

Como cada \(m_i\) es entero, si \(m=\max_i m_i\), entonces

\[
\boxed{3m\le s-3.}
\tag{9.5}
\]

Para \(x\in K\), sea

\[
a_x=|\{i:x\in S_i\}|
\]

y

\[
D=\sum_{x\in K}a_x(q-a_x).
\tag{9.6}
\]

Entonces

\[
\sum_{i,j}|S_i\triangle S_j|=2D.
\tag{9.7}
\]

### Dispersión alta

Supongamos

\[
D\ge\frac{qs^2}{12}.
\tag{9.8}
\]

Por (9.5),

\[
2p-3m-1\ge2p-s+2=q+2.
\]

El Lema 6.1 y (9.7) dan entonces

\[
V
\ge
\frac{q+2}{2}D
\ge
\frac q2D.
\tag{9.9}
\]

El coeficiente de doble factor del Lema 5.2 satisface

\[
\boxed{\delta\ge\frac78.}
\tag{9.10}
\]

En efecto, si \(p\) es impar, entonces \(r_p=p\) y

\[
\delta=\frac{p-s}{p}\ge\frac78,
\]

mientras que si \(p\) es par, entonces \(r_p=p-1\) y

\[
\delta=\frac{p+1-s}{p-1}\ge\frac78.
\]

Además, \(S_2\ge M^2/q\), y (9.5) implica \(M/q\le m\le(s-3)/3\). Como la parábola resultante es creciente en este intervalo,

\[
\frac{(s-1)M-S_2}{q}
\le
\frac{2s(s-3)}9.
\tag{9.11}
\]

Al sustituir (9.8)--(9.11) en el Lema 5.2, obtenemos

\[
\Phi(G)-\frac{n^2}{6}
\le
\frac p2-\frac{5s^2}{288}-\frac{2s}{3}.
\tag{9.12}
\]

Como \(s^2\ge36p\),

\[
\Phi(G)-\frac{n^2}{6}
\le
-\frac p8-\frac{2s}{3}<0,
\]

una contradicción.

### Dispersión baja

Supongamos

\[
D<\frac{qs^2}{12}.
\tag{9.13}
\]

Por (9.7), existe algún \(j\) tal que

\[
\sum_i|S_i\triangle S_j|
<
\frac{s^2}{6}.
\tag{9.14}
\]

Definimos

\[
R=S_j,
\qquad
\rho=|R|.
\]

Entonces

\[
A_R+B_R<\frac{s^2}{6},
\qquad
\rho\le m\le\frac{s-3}{3}.
\tag{9.15}
\]

Verificamos explícitamente las hipótesis del Lema 7.1. Como \(s\le p/8\),

\[
q=2p-s\ge\frac{15p}{8},
\qquad
b=p-\rho\ge p-\frac s3.
\]

Por tanto \(b\ge2\), \(q\ge r_b\) y \(b\ge\chi'(K_\rho)\). Además \(r_b\ge b-1\), luego

\[
u=q-r_b\le p-s+\rho+1.
\]

Para todo \(i\),

\[
2\rho+t_i+1
\le
3m+1
\le
s-2.
\]

En consecuencia,

\[
b-t_i\ge\max\{\rho,u\},
\]

y el Lema 7.1 se aplica.

Si \(\rho=0\), entonces \(B_R=0\). Si \(\rho\ge1\), entonces

\[
\theta_R
\le
\frac{\rho}{p-\rho}
\le
\frac{8s}{23p}.
\]

Usando \(u=q-r_b\), \(r_b\le b\) y \(q\ge15p/8\), obtenemos

\[
\kappa_R
=1-2(1-\theta_R)\frac uq
\le
\frac sq+2\theta_R
\le
\frac{5s}{4p}.
\tag{9.16}
\]

Del mismo modo,

\[
\frac{(s-2\rho-1)_+}{q}
\le
\frac{5s}{4p}.
\tag{9.17}
\]

Por (9.15), la desviación positiva total de (7.6) es entonces a lo sumo

\[
\frac{5s}{4p}(A_R+B_R)
<
\frac{5s^3}{24p}
\le
\frac{5s^2}{192}.
\tag{9.18}
\]

Mientras tanto,

\[
\frac{s^2}{6}-s\rho+2\rho^2
=
2\left(\rho-\frac s4\right)^2+\frac{s^2}{24}
\ge
\frac{s^2}{24}.
\tag{9.19}
\]

El Lema 7.1 da ahora

\[
\Phi(G)-\frac{n^2}{6}
\le
\frac p2-\frac{s^2}{64}.
\tag{9.20}
\]

Como \(s^2\ge36p\), el lado derecho es a lo sumo \(-p/16\), nuevamente una contradicción.

Todas las subsucesiones posibles son imposibles. Se sigue el Teorema 1.1. \(\square\)

---

# 10. Corolarios

## 10.1 Particiones en cliques

El Corolario 1.2 se sigue inmediatamente de

\[
\operatorname{cp}(G)
\le
|E(G)|-2\nu_3(G).
\]

## 10.2 Optimalidad del término principal

La familia

\[
K_p\vee\overline K_{2p}
\]

tiene \(n=3p\). Una factorización de \(K_p\) asignada a vértices independientes empaqueta toda arista de la clique en un triángulo \(KKI\). La expresión resultante del empaquetamiento es

\[
|E|-2\nu_3
=
\frac{n^2}{6}+\frac n6.
\tag{10.1}
\]

La construcción de Erdős--Ordman--Zalcstein para particiones en cliques sobre esta familia muestra que el coeficiente \(1/6\) no puede mejorarse.

## 10.3 Localización de sucesiones difíciles

La Proposición 1.3 registra la localización proporcionada por la demostración. Debe entenderse como una descripción estructural de un fallo hipotético de toda estimación con error lineal, no como un teorema extremal adicional posterior al Teorema 1.1. El margen bulk excluye razones acotadas lejos de \(0\) y \(2\), la construcción escasa excluye \(|I|/|K|\to0\), y la factorización promediada excluye el corredor corto cerca de \(|I|=2|K|\). La única ubicación restante es el corredor mesoscópico

\[
|I|=2|K|-s,
\qquad
\sqrt{|K|}\ll s=o(|K|),
\]

que se elimina mediante la dicotomía de dispersión.

## 10.4 Valor fraccionario exacto de perfil común

El Teorema 3.1 es útil por sí mismo: da el empaquetamiento fraccionario exacto de triángulos para todo grafo split en el que todos los vértices independientes tienen un vecindario común, incluido el régimen con demasiado pocos vértices independientes para colorear integralmente todas las aristas del vecindario. Lo enunciamos como corolario independiente.

### Corolario 10.4 — Empaquetamiento exacto con vecindario común

Para todos los enteros \(p\ge3\), \(q\ge0\) y \(0\le d\le p\), el grafo \(H(p,q,d)\) —clique de orden \(p\); \(q\) vértices independientes, cada uno con el mismo vecindario de tamaño \(d\)— satisface

\[
\nu_3^*(H(p,q,d))=F(p,q,d)=\min\left\{\tfrac{\binom p2+qd}{3},\ \binom d2+\binom{p-d}2,\ \binom d2+\tfrac{d(p-d)+\binom{p-d}2}{3}\right\}.
\]

Esta es una fórmula cerrada exacta para el número fraccionario de empaquetamiento de triángulos de una familia completa de un parámetro, válida para todo \(d\), incluido el régimen de \(q\) pequeño donde ninguna factorización integral cubre el vecindario; puede tener interés independiente fuera del problema de particiones en cliques.

### Corolario 10.4b — Grafos threshold

Como \(K_p\vee\overline K_{2p}\) es un grafo threshold y todo grafo threshold es split, el Teorema 1.1 da, en particular, la cota de error lineal

\[
\operatorname{cp}(G)\le n^2/6+Cn
\]

para todos los grafos threshold, con la misma constante principal óptima atestiguada dentro de esa subclase.

## 10.5 Efectividad localizada cerca de \(q=2p\)

### Proposición 10.1 — Cotas explícitas para el corredor

Sea \(q=2p-s\) y \(n=p+q\).

1. Si
   \[
   p\ge36,
   \qquad
   0\le s\le6\sqrt p,
   \]
   entonces
   \[
   \boxed{
   \Phi(G)\le\frac{n^2}{6}+2n.
   }
   \tag{10.2}
   \]

2. Si
   \[
   p\ge2304,
   \qquad
   6\sqrt p\le s\le\frac p8,
   \]
   y todo \(v\in I\) satisface
   \[
   d(v)>\frac{2n-1}{6}+1,
   \]
   entonces
   \[
   \boxed{
   \Phi(G)\le\frac{n^2}{6}.
   }
   \tag{10.3}
   \]

En consecuencia, para todo \(C\ge2\), un contraejemplo de orden mínimo a

\[
\Phi(G)\le\frac{n^2}{6}+Cn
\]

no puede satisfacer

\[
p\ge2304,
\qquad
0\le s\le\frac p8.
\]

### Demostración

Para el corredor corto, (5.3) y \(s^2\le36p\) dan

\[
\Phi(G)-\frac{n^2}{6}
\le
\frac{7p}{2}+\frac14
\le
2n,
\]

porque \(p\ge36\) implica \(s\le p\) y, por tanto, \(n=3p-s\ge2p\).

La afirmación mesoscópica es exactamente el cálculo cuantitativo de dispersión alta/baja de la Sección 9.3. La consecuencia final se sigue de la desigualdad de grado obtenida al eliminar un vértice independiente de un contraejemplo de orden mínimo. \(\square\)

---

# 11. Discusión

## 11.1 De la asintótica fraccionaria a un teorema integral con error lineal

La dificultad central es que el teorema general

\[
\nu_3^*(G)-\nu_3(G)=o(n^2)
\]

no proporciona una tasa lineal. La presente demostración evita exigir un único mecanismo uniforme de redondeo.

- En el bulk, el LP de perfil común produce holgura cuadrática.
- Cerca de \(q=2p\), las estructuras explícitas de factorización reemplazan el redondeo general.
- Cerca de \(q=0\), la clique residual se vuelve suficientemente densa para una descomposición exacta.

Esta estrategia dependiente del régimen es más débil que un teorema universal de brecha lineal de integralidad, pero basta para el problema extremal de particiones en cliques.

## 11.2 Por qué el grado máximo residual no es el invariante correcto

Los primeros trabajos exploratorios intentaron probar que un empaquetamiento óptimo deja un residuo de clique de grado máximo acotado. El comportamiento numérico dependía fuertemente del algoritmo de empaquetamiento, y la demostración final no necesita ninguna propiedad de este tipo.

Los invariantes efectivos son, en cambio:

- el margen fraccionario de perfil común;
- el término de varianza \(S_2\);
- la energía de polarización \(V\);
- las desviaciones centradas \(A_R,B_R\);
- la divisibilidad del residuo denso.

## 11.3 Efectividad localizada y no efectividad restante

La Proposición 10.1 muestra que todo el corredor casi extremal tratado mediante factorización, polarización y completación respecto de un centro desplazado es cuantitativamente efectivo. Se puede tomar

\[
C_{\mathrm{corr}}=2,
\qquad
p_0=2304,
\qquad
s_0(p)=6\sqrt p,
\qquad
\eta_0=\frac18.
\]

La constante global \(C\) sigue siendo no efectiva por dos razones independientes.

1. El teorema de Haxell--Rödl se usa mediante una afirmación asintótica \(o(n^2)\) en el bulk.
2. Los teoremas de descomposición densa en triángulos se invocan con umbrales no especificados de «suficientemente grande» en el régimen escaso.

Así, no queda no efectividad oculta en las Secciones 5--7; proviene únicamente de los dos insumos asintóticos externos anteriores. Además, después del Apéndice D, las Secciones 5--7 son autocontenidas: la Proposición 10.1 no depende de ningún teorema externo.

## 11.4 Relación con el teorema extremal fraccionario

El teorema extremal complete-split determina el máximo fraccionario global de

\[
|E(G)|-2\nu_3^*(G)
\]

tanto sobre grafos split como sobre grafos cordales. El LP de perfil común del presente paper cumple otro propósito: es una cota inferior local, sensible al perfil, para el grafo replicado, y su holgura cuantitativa absorbe la pérdida de integralidad fuera del corredor extremal.

Por tanto, el cálculo extremal fraccionario global y el cálculo local de perfil común son compatibles, pero lógicamente distintos. La presente demostración es autocontenida salvo por los teoremas externos enunciados en la Sección 2.

**Observación (clonado a través de la serie).** El Lema 4.1 y el paso de simetrización por clones del Paper II usan la misma operación subyacente en funciones distintas. El Paper II usa clonado por pares para llevar un grafo cordal hacia un grafo terminal complete-split. El Lema 4.1 usa clonado \(q\)-fold en el lado de cobertura para comparar un perfil arbitrario con un grafo de perfil común. Se conserva entonces el término compartido *clonado*, mientras que el calificativo *fraccional* distingue la desigualdad presente.

## 11.5 Relación con el problema cordal de error lineal

La reducción complete-split establece la cota cordal asintóticamente óptima

\[
\operatorname{cp}(G)
\le
\left(\frac16+o(1)\right)n^2.
\]

La estimación más fuerte

\[
\operatorname{cp}(G)
\le
\frac{n^2}{6}+O(n)
\]

permanece abierta para grafos cordales generales. Los mecanismos desarrollados aquí sugieren un programa concreto de tres partes.

1. **Estabilidad del teorema extremal fraccionario.** Reforzar el teorema fraccionario cordal exacto del Paper II hasta una afirmación de estabilidad: todo grafo cordal cuyo valor está a distancia \(\delta n^2\) del máximo fraccionario está a distancia de edición \(\varepsilon n^2\) de un grafo complete-split maximizador. Fuera de la casi extremalidad, la holgura fraccionaria cuadrática absorbe la pérdida general de integralidad exactamente como en la Sección 4.

2. **Mecanismos robustos del corredor.** Extender los argumentos de factorización, polarización y centro desplazado de las Secciones 5--7 desde grafos split a perturbaciones de \(\varepsilon n^2\) de grafos complete-split, para aplicarlos a los grafos casi extremales producidos por estabilidad.

3. **Ensamblaje mediante el árbol de cliques.** Parchar las estimaciones locales a través del árbol de cliques mediante un ledger de propiedad de aristas que preserve las capacidades de los separadores, en el espíritu de la completación respecto de un centro desplazado, de modo que ninguna arista se cargue dos veces.

Una demostración cordal con error lineal todavía tendría que preservar la propiedad y las capacidades de los separadores a lo largo del árbol de cliques; el ledger del paso 3 está pensado precisamente para ese propósito.

Un paper compañero en preparación investiga este programa. Su recursión prevista por separadores-clique usa el teorema split demostrado aquí como caso base y está diseñada para que los regímenes cordales reflejen los ingredientes correspondientes de las Secciones 3--9: evaluación de perfil común, clonado fraccional, factorización y análisis del corredor. Hasta que ese argumento compañero esté completo, este párrafo registra la interfaz propuesta y no un teorema del presente paper.

## 11.6 Perímetro y estado actual de la verificación formal

Los Papers I y II de la serie están formalmente verificados en Lean 4 con Mathlib. El Paper III se está verificando bajo el mismo protocolo de liberación. El proyecto Lean del presente manuscrito usa Mathlib v4.28.0 y compila actualmente como un grafo completo de dependencias.

El desarrollo formal separa dos capas.

- **Capa X** contiene exactamente los dos insumos asintóticos externos, los Teoremas 2.1 y 2.3, retenidos como axiomas nombrados con sus hipótesis enunciadas explícitamente.
- **Capa E** contiene el núcleo matemático finito: Teoremas 3.1 y 4.2; Lemas 4.1--7.1; la corrección de divisibilidad del Apéndice B; el desarrollo de coloreo de aristas por listas del Apéndice D; las cadenas cuantitativas de las Secciones 9.3 y 10.5; la Proposición 10.1; y el ensamblaje final.

A la fecha de este borrador, el proyecto tiene ocho obligaciones localizadas de tipo `sorry`. Están confinadas a: los pequeños casos degenerados del LP de perfil común; el bloque de redondeo con uno y dos factores de la Sección 5; la conclusión del corredor medio de la Proposición 10.1; un helper de matching en el desarrollo autocontenido de Galvin/König; la construcción de empaquetamiento con tres familias que subyace a la Sección 7.2; y la estimación de empaquetamiento del régimen escaso que invoca el Teorema 2.3. El enunciado y el ensamblaje de dependencias del Teorema 1.1 ya compilan, pero el teorema permanece transitivamente abierto hasta cerrar estas hojas.

Ningún cálculo ni script de regresión es una premisa de la demostración. Las comprobaciones de aritmética exacta y programación entera son auditorías suplementarias. Bajo una convención única de conteo, comprenden 46,390 comprobaciones exactas de aritmética y LP, y 91 comprobaciones exactas de ILP, para un total de 46,481, sin discrepancias reportadas.

La línea de estado del preprint público se actualizará solo después de congelar todos los siguientes elementos: un build con cero `sorry`, el informe de axiomas, el toolchain y manifest de Lean, y el commit de liberación. Por tanto, la afirmación final prevista ya está delimitada, pero no se declara en este borrador.

---

# 12. Usos potenciales y direcciones futuras

## 12.1 Brecha universal lineal de integralidad

### Problema 12.1

¿Existe una constante absoluta \(C\) tal que

\[
\nu_3^*(G)-\nu_3(G)
\le C|V(G)|
\]

para todo grafo split \(G\)?

El presente paper proporciona estructuras de apoyo cerca del corredor extremal, pero no resuelve el régimen bulk sin holgura cuadrática.

## 12.2 Constantes globales efectivas

### Problema 12.2

Encontrar una constante global explícita \(C\) en el Teorema 1.1.

El corredor casi extremal ya es efectivo por la Proposición 10.1. Un teorema global completamente cuantitativo requiere entonces solo tasas explícitas en el paso fraccionario-a-integral, o un reemplazo estructurado de Haxell--Rödl en el bulk, junto con umbrales efectivos de descomposición densa en el régimen con lado independiente escaso.

## 12.3 Empaquetamiento algorítmico

La demostración contiene piezas implementables en tiempo polinomial:

- factorizaciones de grafos completos;
- selección ponderada de vértices reservados;
- coloreo bipartito de aristas por listas;
- extracción de matchings;
- algoritmos de descomposición densa implícitos en la absorción iterativa.

Es natural buscar un algoritmo polinomial que produzca una partición en cliques de tamaño

\[
\frac{n^2}{6}+O(n)
\]

con una constante explícita. Los pasos de factorización, coloreo por listas y matchings de las Secciones 5--7 son individualmente polinomiales; ensamblarlos en un solo algoritmo de aproximación con garantía demostrada queda para trabajo futuro.

### Corolario 12.2 — Algoritmo efectivo en el corredor

En el corredor casi extremal cubierto por la Proposición 10.1 —con \(p_0,s_0\) explícitos—, la demostración es constructiva: las factorizaciones simples y dobles de \(K_p\), la selección de vértices reservados, el coloreo de aristas por listas —Apéndice D, cuya demostración mediante núcleos y emparejamientos estables es a su vez un algoritmo— y la extracción de matchings se ejecutan todos en tiempo polinomial. Por tanto, existe un algoritmo determinista de tiempo polinomial que, para grafos split en el corredor efectivo, produce una partición en cliques de tamaño \(n^2/6+2n\), con la constante explícita de la Proposición 10.1. Fuera del corredor, la garantía actual depende del insumo no constructivo del bulk —Teorema 2.1—; un algoritmo global completamente efectivo queda para trabajo futuro.

## 12.4 Estabilidad y clasificación extremal

### Problema 12.3

Caracterizar los grafos split que satisfacen

\[
\operatorname{cp}(G)
\ge
\frac{n^2}{6}-o(n^2).
\]

La demostración sugiere que los grafos casi extremales deben satisfacer \(|I|=(2+o(1))|K|\) y tener perfiles de ausencias de baja dispersión cercanos a un centro común.

Dos evidencias apoyan una afirmación de estabilidad de tipo Simonovits. Primero, una enumeración exhaustiva para \(n=9\) —todos los grafos split con \(|K|=3\)— muestra que los grafos a distancia aditiva constante del máximo están a distancia de edición acotada de la familia complete-split, mientras que los perfiles genuinamente dispersos quedan una cantidad lineal por debajo del máximo. Segundo, el margen fraccionario del Teorema 4.2 ya da una cota de conjunto de nivel: lejos de la casi extremalidad, la holgura cuadrática \(\mu(\alpha)p^2\) es estrictamente positiva, por lo que todo casi maximizador debe tener \(\alpha\) cerca de la razón extremal y pequeña dispersión de perfiles. Un teorema completo de estabilidad aún requeriría cuantificar la ganancia de un único paso de simetrización y controlar las direcciones a lo largo de las cuales \(\Phi^*\) es plana; lo dejamos como problema abierto, formulado de manera natural en la métrica de corte —graphon— para absorber la elección del grafo complete-split más cercano.

## 12.5 Empaquetamiento con cliques mayores y error lineal

La reducción complete-split determina el problema extremal fraccionario y la asintótica integral de primer orden para particiones en \(K_r\) fijos y aristas individuales. El análogo natural para cliques mayores es la siguiente pregunta de error lineal.

Para \(r\ge3\) fijo, ¿satisface todo grafo split

\[
\pi_r(G)
\le
\frac{r-1}{4r}n^2+O_r(n),
\]

donde \(\pi_r(G)\) es el número mínimo de partes en una partición de aristas en copias de \(K_r\) y aristas individuales?

Las ideas de perfil común y clonado sugieren una posible vía, pero los programas locales por órbitas y los mecanismos de redondeo integral relevantes se vuelven sustancialmente más complicados. Los métodos de diseños y descomposición, como los desarrollados por Keevash [10] y el marco de rebanadas regulares de Allen, Böttcher, Cooley y Mycroft [11], pueden ser herramientas útiles; no son ingredientes de la presente demostración.

## 12.6 Aplicaciones cordales y a árboles de cliques

La completación respecto de un centro desplazado fue diseñada para separar aristas propias de la clique de aristas protegidas de interfaz. Una versión paramétrica puede ser útil en un futuro teorema cordal con error lineal, donde los separadores son compartidos entre cliques maximales vecinas.

## 12.7 Principio reutilizable de demostración

El paper ilustra una estrategia más amplia:

> Usar LP simétricos exactos para crear holgura lejos de la extremalidad, y reservar el redondeo combinatorio explícito solo para el corredor donde la holgura desaparece.

Este principio puede aplicarse a otros problemas estructurados de empaquetamiento y cobertura en los que un teorema general de regularidad es demasiado débil en segundo orden.

---

# 13. Reproducibilidad

El paquete de liberación de trabajo para este borrador se organiza como sigue.

```text
01_MANUSCRIPT/
    PAPER_III_split_lineal_v0.9.5_review_es.md
02_PROOF_CONTROL/
    LEDGER.md
    LEDGER_INCREMENTAL_v0.9.2_formalization_draft.md
    AUDIT_PAPER_C.md
03_FORMALIZATION/
    lean/                         (fuentes Lean 4 / Mathlib v4.28.0)
    lakefile.toml
    lean-toolchain
    lake-manifest.json
    BUILD_STATUS.md               (temporal hasta congelar el build de liberación)
04_SUPPLEMENTARY_REGRESSION/
    audit_c_fast.py
    audit_c_ilp.py
    audit_c_ilp_results.txt
```

El manuscrito es la fuente matemática de verdad. `LEDGER.md` es la especificación autoritativa de dependencias para el desarrollo Lean; el ledger incremental registra únicamente la transición desde v0.9.1 a este borrador. El paquete final de liberación añadirá el commit congelado, el log de build, el informe de axiomas y el manifiesto SHA-256.

La demostración misma está contenida en el manuscrito. La optimización de perfil común se prueba en el Teorema 3.1; el margen fraccionario se prueba en el Teorema 4.2 y el Apéndice A; las desigualdades de factorización, polarización y centro desplazado se prueban en los Lemas 5.1--7.1; la corrección de divisibilidad se prueba en la Sección 8.3 y el Apéndice B; y las constantes explícitas casi extremales se prueban algebraicamente en las Secciones 9.3 y 10.5.

El script incluido es una prueba suplementaria de regresión para las constantes explícitas del corredor. Su salida no se usa como hipótesis, reducción ni paso de demostración en ninguna parte del manuscrito. Los cálculos exploratorios históricos no forman parte del paquete lógico de la demostración.

---

# Apéndice A. Álgebra del margen fraccionario

Sea \(x=d/p\) y \(\alpha=q/p\). Ignorando temporalmente los términos lineales exactos, las tres ramas normalizadas de \(F\) son

\[
f_1(x)=\frac16+\frac{\alpha x}{3},
\]

\[
f_2(x)=x^2-x+\frac12,
\]

y

\[
f_3(x)=\frac16+\frac{x^2}{3}.
\]

Al restar la contribución afín objetivo se obtienen los mínimos

\[
\min_x\left(f_1(x)-\frac{\alpha x}{2}-C_\alpha\right)
=
\frac{\alpha^2}{12},
\]

\[
\min_x\left(f_2(x)-\frac{\alpha x}{2}-C_\alpha\right)
=
\frac{(2-\alpha)^2}{48},
\]

y

\[
\min_x\left(f_3(x)-\frac{\alpha x}{2}-C_\alpha\right)
=
\begin{cases}
\alpha(8-5\alpha)/48,&\alpha\le4/3,\\
(2-\alpha)^2/12,&\alpha\ge4/3.
\end{cases}
\]

La tercera rama está dominada por la envolvente inferior de las dos primeras. Al restituir la contribución exacta \(-p/2\) en cada estimación puntual y promediar, se produce el término \(-p/4\) del Teorema 4.2.

---

# Apéndice B. Corrección de divisibilidad

Sea \(P=x_1\cdots x_p\) un camino y sea \(O\subseteq V(P)\) de cardinalidad par. Definimos

\[
J=\{x_jx_{j+1}:|O\cap\{x_1,\ldots,x_j\}|\text{ es impar}\}.
\]

Todo vértice interno \(x_j\) cambia la paridad del prefijo exactamente cuando \(x_j\in O\). Por tanto,

\[
\operatorname{Odd}(J)=O.
\]

Además, \(|E(J)|\le p-1\) y \(\Delta(J)\le2\).

Después de corregir la paridad, el grado mínimo ha disminuido a lo sumo en dos. En el régimen con lado independiente escaso sigue siendo mayor que \(3p/4\) para todo \(p\) suficientemente grande, de modo que el teorema de Turán proporciona un \(K_5\). Eliminar un \(C_4\) dentro de ese \(K_5\) cambia el número de aristas en \(1\pmod3\), mientras que eliminar un \(C_5\) lo cambia en \(2\pmod3\). Todo grado afectado cambia en dos, por lo que la paridad se preserva. La pérdida total de grado debida al subgrafo del camino y al ciclo corrector es a lo sumo cuatro. Así, cuando \(q=o(p)\), el grafo final tiene grado mínimo al menos \(p-1-q-4\), que eventualmente excede \((0.9+\varepsilon_0)p\) para todo \(0<\varepsilon_0<0.1\) fijo.

---

# Apéndice C. Auditorías computacionales

## C.1 LP exacto de perfil común

`verify_common_profile_lp.py` enumera los vértices del poliedro simetrizado de coberturas mediante eliminación gaussiana racional exacta y compara el óptimo con (3.5).

## C.2 Margen fraccionario exacto

`verify_fractional_margin.py` comprueba el Teorema 4.2 para

\[
3\le p\le80,
\qquad
1\le q\le2p,
\qquad
0\le d\le p
\]

usando aritmética racional exacta.

## C.3 Auditorías ILP pequeñas

`verify_factor_rounding.py` y `verify_shifted_center.py` calculan empaquetamientos integrales exactos de triángulos en instancias pequeñas mediante un ILP binario de capacidad de aristas. Verifican las cotas superiores declaradas para \(\Phi(G)\).

## C.4 Polarización

`verify_polarization.py` realiza comprobaciones exhaustivas de perfiles pequeños y comprobaciones aleatorias con enteros exactos del Lema 6.1.

## C.5 Divisibilidad

`verify_divisibility_correction.py` verifica exhaustivamente la construcción de paridad sobre caminos hasta orden dieciocho, comprueba exactamente el umbral fijo de grado mínimo y sigue la corrección completa de paridad y módulo tres sobre residuos densos aleatorios.

---

# Apéndice D. Coloreo de aristas por listas autocontenido

Este apéndice demuestra el teorema de coloreo de aristas por listas usado en la Sección 7.2 —enunciado como Teorema 2.2—, de modo que el argumento del corredor no dependa de ningún teorema externo de coloreo. El resultado es el caso de grado máximo del teorema de Galvin [12]; el grafo de ganancias de la Sección 7.2 es simple y bipartito, que es el caso probado aquí.

## D.1 Núcleos

Un **núcleo** de un dígrafo \(D\) es un conjunto independiente \(K\) de vértices tal que todo vértice fuera de \(K\) tiene un vecino de salida en \(K\). El dígrafo \(D\) es **perfecto por núcleos** si todo subdígrafo inducido tiene un núcleo. Un núcleo de un dígrafo no vacío es no vacío.

### Lema D.1 — Lema de coloreo por núcleos

Sea \(D\) un dígrafo perfecto por núcleos en el que cada vértice \(v\) tiene una lista \(L(v)\) con \(|L(v)|\ge d^+_D(v)+1\). Entonces el grafo subyacente de \(D\) admite un coloreo propio que elige cada color desde la lista correspondiente.

### Demostración

Elegimos cualquier color \(c\) que aparezca en alguna lista, definimos \(S=\{v:c\in L(v)\}\) y sea \(K\) un núcleo de \(D[S]\). Coloreamos todos los vértices de \(K\) con \(c\); el coloreo es propio sobre \(K\) porque \(K\) es independiente. Eliminamos \(K\) de \(D\) y eliminamos \(c\) de la lista de todo vértice de \(S\setminus K\). Cada \(v\in S\setminus K\) perdió un color, pero también al menos un vecino de salida, a saber, su vecino de salida en \(K\), de modo que la hipótesis \(|L(v)|\ge d^+(v)+1\) se preserva; los vértices fuera de \(S\) conservan sus listas y sus grados de salida no aumentan. Repetimos. Todo vértice no coloreado mantiene siempre una lista no vacía, y cada ronda con \(S\ne\varnothing\) colorea el conjunto no vacío \(K\), por lo que finalmente todos los vértices quedan coloreados. \(\square\)

## D.2 Emparejamientos estables

Sea \(B\) un grafo bipartito con partes \(U\) y \(R\) en el que cada vértice \(z\) tiene un orden lineal de preferencia \(>_z\) sobre sus aristas incidentes. Un matching \(M\subseteq E(B)\) es **estable** si toda arista \(f\notin M\) tiene un extremo \(z\) cubierto por una arista \(e\in M\) con \(e>_zf\).

### Lema D.2 — Gale--Shapley [13]

Para todo sistema de preferencias existe un matching estable.

### Demostración

Ejecutamos aceptación diferida. Mientras exista algún \(u\in U\) no emparejado que todavía no haya propuesto a lo largo de todas sus aristas, hacemos que \(u\) proponga por su arista no intentada más preferida, digamos \(f\), con extremo \(r\in R\). Si \(r\) no está emparejado, o prefiere \(f\) a la arista que mantiene actualmente, entonces \(r\) acepta \(f\), liberando a su pareja anterior, si existe; en caso contrario, \(r\) rechaza \(f\). Cada arista recibe a lo sumo una propuesta, de modo que el proceso termina, y termina en un matching \(M\).

Sea \(f=ur\notin M\). Supongamos primero que \(u\) propuso a lo largo de \(f\) en algún momento. Entonces \(r\) rechazó \(f\) inmediatamente o la aceptó y más tarde la liberó; en ambos casos, en ese momento \(r\) mantenía o recibió una arista que prefiere estrictamente a \(f\). Como la arista mantenida por \(r\) solo mejora durante el proceso, la arista final \(e\in M\) en \(r\) satisface \(e>_rf\). Supongamos ahora que \(u\) nunca propuso a lo largo de \(f\). Un vértice no emparejado de \(U\) sigue proponiendo mientras queden aristas no intentadas, por lo que al terminar \(u\) está emparejado, digamos con \(e\in M\); como \(u\) propone en orden decreciente de preferencia y nunca llegó a \(f\), se tiene \(e>_uf\). En ambos casos, \(f\) tiene un extremo cuya arista emparejada se prefiere a \(f\). \(\square\)

## D.3 El teorema de coloreo

### Teorema D.3 — Galvin, caso de grado máximo

Sea \(B\) un grafo bipartito simple de grado máximo \(\Delta\), y supongamos que cada arista \(e\) lleva una lista \(L(e)\) con \(|L(e)|\ge\Delta\). Entonces \(B\) admite un coloreo propio de aristas que elige cada color desde la lista correspondiente.

### Demostración

**Paso 1: un coloreo propio de aristas con \(\Delta\) colores.** Por el teorema de coloreo de aristas de König [14], \(B\) admite un coloreo propio de aristas \(\varphi:E(B)\to\{1,\ldots,\Delta\}\). Para completar el argumento, procedemos por inducción en el número de aristas. Eliminamos una arista \(e=ur\) y coloreamos el resto. A lo sumo \(\Delta-1\) colores aparecen en \(u\) y a lo sumo \(\Delta-1\) en \(r\), de modo que a \(u\) le falta un color \(\alpha\) y a \(r\) un color \(\beta\). Si les falta un color común, se lo asignamos a \(e\). En caso contrario, consideramos el camino maximal \(P\) que parte de \(u\) y cuyas aristas están coloreadas alternadamente \(\beta,\alpha\). El camino \(P\) no puede terminar en \(r\): como a \(r\) le falta \(\beta\), tal camino terminaría con una arista de color \(\alpha\) y tendría longitud par, mientras todo camino entre los vértices adyacentes \(u\) y \(r\) de un grafo bipartito tiene longitud impar. Intercambiamos los colores \(\alpha\) y \(\beta\) a lo largo de \(P\); por maximalidad de \(P\), el coloreo sigue siendo propio, \(r\) no se altera y ahora a \(u\) le falta \(\beta\). Asignamos \(\beta\) a \(e\).

**Paso 2: la orientación.** Definimos preferencias a partir de \(\varphi\): cada \(u\in U\) prefiere sus aristas incidentes con color \(\varphi\) **mayor**, y cada \(r\in R\) prefiere color \(\varphi\) **menor**. Definimos un dígrafo \(D\) sobre el conjunto de vértices \(E(B)\): para aristas distintas \(e,f\) que comparten un extremo \(z\), ponemos un arco \(e\to f\) exactamente cuando \(f>_ze\).

Grados de salida: sea \(e=ur\) con \(\varphi(e)=c\). Los vecinos de salida de \(e\) son las aristas en \(u\) con color mayor que \(c\) —a lo sumo \(\Delta-c\), pues los colores en \(u\) son dos a dos distintos— y las aristas en \(r\) con color menor que \(c\) —a lo sumo \(c-1\). Por tanto,

\[
d^+_D(e)\le(\Delta-c)+(c-1)=\Delta-1.
\]

**Paso 3: perfección por núcleos.** Un subdígrafo inducido de \(D\) es \(D[S]\) para un conjunto \(S\) de aristas de \(B\). Un núcleo de \(D[S]\) es exactamente un matching estable del subgrafo \((V(B),S)\) con las preferencias heredadas: independencia en \(D\) significa que dos aristas del núcleo no comparten extremo, pues dos aristas en un mismo vértice siempre están unidas por un arco; y la condición de dominación pide que todo \(f\in S\setminus K\) tenga un arco hacia \(K\), es decir, un extremo \(z\) y una arista \(e\in K\) en \(z\) con \(e>_zf\), que es precisamente estabilidad. El Lema D.2 proporciona un matching estable, de modo que \(D\) es perfecto por núcleos.

**Paso 4: conclusión.** Toda arista satisface \(|L(e)|\ge\Delta\ge d^+_D(e)+1\), de modo que el Lema D.1 da un coloreo propio del grafo subyacente de \(D\) desde las listas; esto es, un coloreo propio de aristas por listas de \(B\). \(\square\)

### Observación D.4 — Aplicación

El grafo de ganancias de la Sección 7.2 es simple y bipartito, y la hipótesis (7.2) da para toda lista

\[
b-t_i\ge\max\{\rho,u\}\ge\Delta
\]

del grafo de ganancias. Por tanto, el Teorema D.3 se aplica literalmente. La versión para multigrafos del teorema de Galvin también es válida [12], pero no se necesita aquí.

---

## Agradecimientos

El autor agradece profundamente a su esposa María Paz y a sus hijos Lucas, Juan Cristóbal, Francisca, Raimundo y Benjamín por su amor, paciencia y apoyo.

---

## Uso de herramientas asistidas por IA

Se utilizaron herramientas asistidas por IA durante las etapas exploratoria, computacional, adversarial, organizativa y editorial, incluidos sistemas de Anthropic, Google y OpenAI. Estas herramientas apoyaron la prueba de argumentos candidatos, las comprobaciones exactas de regresión, la organización de la demostración, la preparación de auditorías y la redacción. El autor revisó el contenido matemático, seleccionó los argumentos finales y conserva la responsabilidad exclusiva por las afirmaciones, citas, código y presentación. Ningún sistema de IA figura como autor.

---

## Referencias

[1] B. Barber, D. Kühn, A. Lo, and D. Osthus, “Edge-decompositions of graphs with high minimum degree,” *Advances in Mathematics* **288** (2016), 337–385.

[2] O. V. Borodin, A. V. Kostochka, and D. R. Woodall, “List edge and list total colourings of multigraphs,” *Journal of Combinatorial Theory, Series B* **71** (1997), no. 2, 184–204.

[3] G.-T. Chen, P. Erdős, and E. T. Ordman, “Clique partitions of split graphs,” in *Combinatorics, Graph Theory, Algorithms and Applications* (Beijing, 1993), World Scientific, 1994, pp. 21–30.

[4] G. A. Dirac, “Some theorems on abstract graphs,” *Proceedings of the London Mathematical Society* (3) **2** (1952), 69–81.

[5] F. Dross, “Fractional triangle decompositions in graphs with large minimum degree,” *SIAM Journal on Discrete Mathematics* **30** (2016), no. 1, 36–42.

[6] P. Erdős, E. T. Ordman, and Y. Zalcstein, “Clique partitions of chordal graphs,” *Combinatorics, Probability and Computing* **2** (1993), no. 4, 409–415.

[7] P. E. Haxell and V. Rödl, “Integer and fractional packings in dense graphs,” *Combinatorica* **21** (2001), 13–38.

[8] J. P. Traverso Gianini, “Complete-split extremizers for a fractional triangle-cover functional on chordal graphs” (Paper II in the series), preprint v1.0, July 2026.

[9] R. Yuster, “Integer and fractional packing of families of graphs,” *Random Structures & Algorithms* **26** (2005), 110–118.

[10] P. Keevash, “The existence of designs,” arXiv:1401.3665, revised 2018.

[11] P. Allen, J. Böttcher, O. Cooley, and R. Mycroft, “Tight cycles and regular slices in dense hypergraphs,” *Journal of Combinatorial Theory, Series A* **149** (2017), 30–100.

[12] F. Galvin, “The list chromatic index of a bipartite multigraph,” *Journal of Combinatorial Theory, Series B* **63** (1995), no. 1, 153–158.

[13] D. Gale and L. S. Shapley, “College admissions and the stability of marriage,” *The American Mathematical Monthly* **69** (1962), no. 1, 9–15.

[14] D. König, “Über Graphen und ihre Anwendung auf Determinantentheorie und Mengenlehre,” *Mathematische Annalen* **77** (1916), 453–465.

[15] J. P. Traverso Gianini, “Affine profile reduction for fractional triangle packings in split graphs” (Paper I in the series), preprint v1.0, July 2026.
