# Reducción afín de perfiles para empaquetamientos fraccionales de triángulos en grafos split

**Juan Pablo Traverso Gianini**  
Investigador independiente, Santiago, Chile  
[jtraverso@gmail.com](mailto:jtraverso@gmail.com)  
[ORCID: 0009-0003-6068-4096](https://orcid.org/0009-0003-6068-4096)

**Manuscrito preprint:** v1.0  
**Fecha:** 6 de julio de 2026  
**Estado:** lanzamiento de preprint; el teorema fraccional finito está congelado internamente, auditado adversarialmente con asistencia de IA y verificado formalmente en Lean 4 con Mathlib v4.28.0. El enunciado del Teorema 1.1 está verificado por máquina, no contiene `sorry`, y su reporte de axiomas contiene solo los axiomas fundacionales estándar de Lean (`propext`, `Classical.choice`, `Quot.sound`), sin axiomas específicos del proyecto; véanse la Sección 10 y el Apéndice C. No ha sido revisado externamente por pares; la revisión bibliográfica y de novedad está incompleta.

**MSC 2020:** Primario 05C70; secundarios 05C35, 05C72.

---

## Resumen

Estudiamos empaquetamientos fraccionales de triángulos en grafos split. Una presentación split \(V(G)=K\sqcup I\) permite empaquetar explícitamente los triángulos que intersectan el conjunto independiente. Las capacidades no usadas en las aristas del clique llevan, por dualidad finito-dimensional de programación lineal, a un problema de cobertura de triángulos sobre un único politopo fijo. El vector objetivo de ese problema de cobertura depende afínmente de los tipos de vecindarios que aparecen en \(I\).

El mínimo de un objetivo lineal sobre un politopo fijo es cóncavo como función del vector objetivo. Esta observación reduce la tarea de probar una cota inferior uniforme para una mezcla arbitraria de vecindarios del conjunto independiente al análisis de perfiles puros de vecindario. Después de promediar sobre el estabilizador del perfil puro, el problema residual de cobertura se convierte en un programa lineal de tres variables. La solución de ese programa da una cota inferior cuadrática uniforme para el valor residual.

Como consecuencia, todo grafo split \(G\) con \(n\) vértices satisface

\[
\boxed{
|E(G)|-2\nu_3^*(G)\le \frac{n^2}{6}+n,
}
\]

donde \(\nu_3^*(G)\) es el valor máximo de un empaquetamiento fraccional de triángulos. La constante principal \(1/6\) es la que aparece en el Problema #81 de Erdős sobre particiones en cliques de grafos cordales; el resultado presente trata el problema fraccional finito para la subclase de grafos split. La prueba es finita y analítica. No se usa ningún teorema de transferencia asintótica.

**Palabras clave:** grafo split; empaquetamiento fraccional de triángulos; cobertura fraccional de triángulos; programación lineal; reducción afín; simetrización.

---

## 1. Introducción

Un grafo split es un grafo cuyo conjunto de vértices puede particionarse en un clique y un conjunto independiente. Esta clase es un laboratorio natural para preguntas sobre particiones en cliques: conserva un núcleo completo rígido y, al mismo tiempo, permite muchos patrones distintos de vecindarios fuera del núcleo. Erdős, Ordman y Zalcstein [1] exhibieron ejemplos cordales que requieren asintóticamente \(n^2/6\) cliques y probaron que \((1-c)n^2/4\) cliques bastan para alguna constante absoluta \(c>0\). Para grafos split, Chen, Erdős y Ordman [2] probaron la cota más aguda \(\frac{3}{16}n^2+O(n)\). Este artículo estudia, en cambio, el déficit de empaquetamiento fraccional de triángulos \(|E(G)|-2\nu_3^*(G)\), para el cual el resultado de abajo tiene constante principal \(1/6\). Para un contexto más amplio sobre particiones y coberturas por cliques, véase Cavers [5].

El presente artículo aísla un mecanismo fraccional relacionado con el lado split del Problema #81 de Erdős. En lugar de intentar escoger directamente triángulos disjuntos en aristas, primero construimos un empaquetamiento fraccional a partir de los triángulos que intersectan el conjunto independiente. La capacidad que no usa este primer empaquetamiento queda en las aristas del clique, y esas capacidades residuales soportan un segundo empaquetamiento formado enteramente por triángulos del clique. La dualidad transforma entonces este problema residual de empaquetamiento en un problema de cobertura fraccional de triángulos sobre el clique.

El punto estructural principal es que el politopo factible de cobertura no depende del perfil de vecindarios del conjunto independiente. Solo cambia el vector objetivo. Como el óptimo de un problema de minimización sobre un politopo fijo es cóncavo en el vector objetivo, un perfil mixto de vecindarios queda acotado inferiormente por la combinación convexa correspondiente de valores de perfiles puros, y por tanto por el menor de esos valores. Esto no identifica un perfil mixto con uno puro; muestra que una cota inferior uniforme puede probarse considerando perfiles puros. El caso puro tiene entonces suficiente simetría para reducirse a tres variables de órbitas.

**Rol dentro del programa más amplio.** Este artículo es autocontenido salvo por el teorema estándar de dualidad fuerte finito-dimensional de programación lineal, citado y aplicado en el Apéndice B. Su propósito principal es aislar el mecanismo de reducción afín de perfiles en el contexto de grafos split y dar una aplicación fraccional finita. Dentro de un programa más amplio sobre el Problema #81 de Erdős, este mecanismo sirve como punto de partida metodológico para desarrollos fraccionales e integrales posteriores. Ningún resultado de esas etapas posteriores se usa aquí.

La prueba resultante tiene la siguiente forma:

\[
\begin{aligned}
\text{empaquetamiento explícito}
&\longrightarrow
\text{politopo residual fijo}\\
&\longrightarrow
\text{reducción afín de perfiles}\\
&\longrightarrow
\text{optimización de tres órbitas}.
\end{aligned}
\]

Nuestro teorema principal es finito.

#### Teorema 1.1

Para todo grafo split \(G\) con \(n\) vértices,

\[
|E(G)|-2\nu_3^*(G)
\le
\frac{n^2}{6}+n.
\]

**Verificación formal.** El Teorema 1.1 está formalizado en Lean 4 con Mathlib v4.28.0 como `paperI_main`. En el desarrollo formal, el enunciado es `Phi ≤ n^2/6 + n`, donde `Phi = |E| − 2·nu3star` y `nu3star` es el supremo de los valores factibles de empaquetamientos fraccionales de triángulos. Por lo tanto, el enunciado Lean es la desigualdad del Teorema 1.1. La prueba no contiene `sorry`. Su reporte de axiomas lista solo los axiomas fundacionales estándar de Lean, `propext`, `Classical.choice` y `Quot.sound`, y ningún axioma específico del proyecto. La Proposición B.1 también está formalizada: la dualidad finita de empaquetamiento-cobertura usada allí se deriva en `FiniteLPDuality.lean` a partir de la infraestructura finita de Farkas y conos cerrados de Mathlib, en vez de postularse. Las fuentes Lean, el archivo de toolchain, la configuración y el manifiesto de Lake, el log de compilación y el reporte de axiomas están incluidos en el repositorio público [8], en `PAPER_I/05_formalization/lean`.

La notación y todos los cálculos usados en la prueba se registran en el archivo acompañante `CALCULATION_LEDGER_FINITE_FRACTIONAL_preprint_v1.0.md`. El artículo enfatiza las ideas matemáticas y mantiene visible, aunque compacto, el álgebra rutinaria.

---

## 2. Notación para grafos split

Fijemos una presentación split

\[
V(G)=K\sqcup I,
\]

donde \(K\) es un clique e \(I\) es independiente. Escribimos

\[
p:=|K|.
\]

Para \(v\in I\), sea

\[
d_v:=|N(v)|.
\]

Separamos los vértices independientes en

\[
I_{\ge2}:=\{v\in I:d_v\ge2\},
\qquad
I_1:=\{v\in I:d_v=1\},
\qquad
I_0:=\{v\in I:d_v=0\}.
\]

Ponemos

\[
q:=|I_{\ge2}|,
\qquad
b_1:=|I_1|,
\qquad
b_{\ge2}:=\sum_{v\in I_{\ge2}}d_v.
\]

Como no hay aristas dentro de \(I\),

\[
|E(G)|
=
\binom{p}{2}+b_{\ge2}+b_1.
\tag{2.1}
\]

Además,

\[
n=p+q+b_1+|I_0|.
\tag{2.2}
\]

Sea \(\nu_3^*(G)\) el valor máximo de un empaquetamiento fraccional de triángulos: se asigna un peso no negativo \(w(T)\) a cada triángulo \(T\), con la condición de que el peso total de los triángulos que contienen una arista fija sea a lo más uno.

---

## 3. La carga agregada sobre el clique

Para una arista \(e\in E(K)\) del clique, definimos

\[
\kappa_e
:=
\sum_{\substack{v\in I_{\ge2}\\ e\subseteq N(v)}}
\frac{1}{d_v-1}.
\tag{3.1}
\]

La normalización se escoge para que cada vértice independiente activo contribuya en total la mitad de su grado.

#### Lema 3.1

\[
\sum_{e\in E(K)}\kappa_e
=
\frac{b_{\ge2}}2.
\]

#### Prueba

Intercambiando el orden de sumación,

\[
\begin{aligned}
\sum_{e\in E(K)}\kappa_e
&=
\sum_{v\in I_{\ge2}}
\frac{\binom{d_v}{2}}{d_v-1}\\
&=
\frac12
\sum_{v\in I_{\ge2}}d_v\\
&=
\frac{b_{\ge2}}2.
\end{aligned}
\]

---

## 4. Un empaquetamiento fraccional en dos fases

### 4.1 Fase I

Para cada arista \(e\) del clique, definimos

\[
\lambda_e
:=
\begin{cases}
1,&\kappa_e=0,\\[1mm]
\min\{1,\kappa_e^{-1}\},&\kappa_e>0.
\end{cases}
\]

Para cada triángulo \(vxy\) con \(v\in I_{\ge2}\) y \(x,y\in N(v)\), asignamos

\[
w_1(vxy)
:=
\frac{\lambda_{xy}}{d_v-1}.
\tag{4.1}
\]

La carga sobre una arista \(e\) del clique es

\[
\lambda_e\kappa_e
=
\min\{\kappa_e,1\}.
\tag{4.2}
\]

Una arista cruzada \(vx\) pertenece a lo más a \(d_v-1\) de estos triángulos, cada uno con peso a lo más \(1/(d_v-1)\). Por tanto, \(w_1\) es factible.

Definimos

\[
H:=\{e:\kappa_e\ge1\},
\qquad
L:=\{e:\kappa_e<1\}.
\]

Cada triángulo positivo de Fase I contiene exactamente una arista del clique. Por lo tanto,

\[
|w_1|
=
|H|+\sum_{e\in L}\kappa_e.
\tag{4.3}
\]

### 4.2 Fase II

La capacidad residual sobre una arista del clique es

\[
r_e:=\max\{1-\kappa_e,0\}.
\tag{4.4}
\]

Sea \(w_2\) un empaquetamiento fraccional óptimo de triángulos del clique bajo estas capacidades residuales. La dualidad finita de empaquetamiento-cobertura usada aquí se registra explícitamente en el Apéndice B.

Después de truncar a uno las variables duales de cobertura, sustituimos

\[
y_e:=1-x_e.
\]

Las restricciones de cobertura de triángulos se convierten en

\[
\sum_{e\in E(T)}y_e\le2.
\]

Los coeficientes \(1-\kappa_e\) son no positivos sobre \(H\), de modo que el vector maximizador puede tomarse nulo allí. Una segunda sustitución,

\[
z_e:=1-y_e,
\]

lleva al politopo fijo

\[
\mathcal P_p
:=
\left\{
z\in[0,1]^{E(K)}:
\sum_{e\in E(T)}z_e\ge1
\text{ para todo triángulo }T\subseteq K
\right\}.
\tag{4.5}
\]

Definimos

\[
M(\kappa)
:=
\min_{z\in\mathcal P_p}
\sum_{e\in E(K)}(1-\kappa_e)z_e.
\tag{4.6}
\]

Sea

\[
w_{\mathrm{com}}:=w_1+w_2,
\qquad
V_{\mathrm{com}}:=|w_{\mathrm{com}}|.
\]

Aquí \(M(\kappa)\) es el valor de un problema residual de cobertura, no el valor de un empaquetamiento adicional. Su región factible depende solo del tamaño \(p\) del clique, mientras que toda la información de los vecindarios del conjunto independiente entra por los coeficientes objetivos \(1-\kappa_e\).

El cálculo dual y el Lema 3.1 dan la identidad exacta

\[
\boxed{
V_{\mathrm{com}}
=
\frac{b_{\ge2}}2+M(\kappa).
}
\tag{4.7}
\]

El empaquetamiento es factible: en una arista del clique, las cargas de Fase I y residual suman a lo más

\[
\min\{\kappa_e,1\}
+
\max\{1-\kappa_e,0\}
=
1.
\]

Por consiguiente,

\[
V_{\mathrm{com}}\le\nu_3^*(G).
\tag{4.8}
\]

Combinando (2.1) y (4.7), se obtiene

\[
\boxed{
|E(G)|-2V_{\mathrm{com}}
=
\binom{p}{2}-2M(\kappa)+b_1.
}
\tag{4.9}
\]

Esta cancelación es el puente entre la construcción de empaquetamiento y el problema de perfiles.

---

## 5. Reducción afín a un vecindario puro

Para todo conjunto \(S\subseteq K\) con \(|S|\ge2\), definimos

\[
a_e^S
:=
\frac{\mathbf1_{\{e\subseteq S\}}}{|S|-1}.
\tag{5.1}
\]

Sea \(n_S\) el número de vértices \(v\in I_{\ge2}\) con \(N(v)=S\). Entonces

\[
\kappa=\sum_Sn_Sa^S.
\tag{5.2}
\]

Supongamos primero que \(q>0\), y pongamos

\[
\lambda_S:=\frac{n_S}{q},
\qquad
\kappa^S:=qa^S.
\]

Entonces

\[
\kappa=\sum_S\lambda_S\kappa^S,
\qquad
\lambda_S\ge0,
\qquad
\sum_S\lambda_S=1.
\tag{5.3}
\]

La reducción sigue de un hecho elemental de concavidad.

#### Lema 5.1

Sea \(P\) no vacío y defínase

\[
\Phi(c):=\min_{x\in P}\langle c,x\rangle.
\]

Si \(c=\sum_i\lambda_ic^{(i)}\) es una combinación convexa, entonces

\[
\Phi(c)
\ge
\sum_i\lambda_i\Phi(c^{(i)})
\ge
\min_i\Phi(c^{(i)}).
\]

#### Prueba

Para todo \(x\in P\),

\[
\langle c,x\rangle
=
\sum_i\lambda_i\langle c^{(i)},x\rangle
\ge
\sum_i\lambda_i\Phi(c^{(i)}).
\]

Tomamos el mínimo sobre \(x\in P\).

Aplicamos el lema a los vectores objetivo \(1-\kappa^S\) sobre el politopo fijo \(\mathcal P_p\). La conclusión es una reducción para cotas inferiores: un perfil mixto no tiene por qué coincidir con ningún perfil puro, pero su valor residual es al menos el promedio correspondiente de los valores de perfiles puros. Obtenemos

\[
\boxed{
M(\kappa)
\ge
\sum_S\lambda_SM(\kappa^S)
\ge
\min_SM(\kappa^S).
}
\tag{5.4}
\]

Resta controlar un perfil puro.

---

## 6. El programa orbital de perfil puro

Fijemos \(S\subseteq K\), y escribamos

\[
s:=|S|,
\qquad
o:=p-s.
\]

Para el perfil puro,

\[
\kappa_e^S
=
\begin{cases}
q/(s-1),&e\subseteq S,\\
0,&\text{en otro caso}.
\end{cases}
\tag{6.1}
\]

Promediamos una cobertura óptima sobre el estabilizador de \(S\). Tanto el politopo de cobertura como el objetivo de perfil puro son invariantes bajo este grupo. Por lo tanto, el promedio preserva factibilidad y valor objetivo. La cobertura promediada es constante en las tres órbitas de aristas:

\[
SS,\qquad
S(K\setminus S),\qquad
(K\setminus S)(K\setminus S).
\]

Llamamos a los valores correspondientes

\[
\alpha,\qquad\beta,\qquad\gamma.
\]

El objetivo es

\[
A\alpha+B\beta+C\gamma,
\tag{6.2}
\]

donde

\[
A:=\frac{s(s-1-q)}2,
\qquad
B:=so,
\qquad
C:=\frac{o(o-1)}2.
\tag{6.3}
\]

Los tipos de triángulos existentes imponen

\[
3\alpha\ge1,
\qquad
\alpha+2\beta\ge1,
\qquad
2\beta+\gamma\ge1,
\qquad
3\gamma\ge1,
\tag{6.4}
\]

omitiendo toda restricción cuyo tipo de triángulo no exista.

La región factible es ahora un politopo tridimensional. Sus puntos extremos relevantes dan las coberturas uniforme, separada y de conjunto caliente; cuando algunos tipos de triángulos no existen, los regímenes de frontera correspondientes deben tratarse por separado. Resolver este programa de tres variables da

\[
M(\kappa^S)
=
\begin{cases}
\min\{U,D\},&o\le2,\\[1mm]
\min\{U,D,H\},&o\ge3,
\end{cases}
\tag{6.5}
\]

donde

\[
U:=\frac{A+B+C}{3},
\qquad
D:=A+C,
\qquad
H:=A+\frac{B+C}{3}.
\tag{6.6}
\]

Los tres valores corresponden a la cobertura uniforme, la cobertura separada y la cobertura de conjunto caliente.

---

## 7. Una cota inferior uniforme para la cobertura residual

Definimos

\[
R(p,q)
:=
\frac{2p^2-2pq-q^2}{12}.
\tag{7.1}
\]

Comparamos cada candidato de (6.5) con \(R(p,q)\).

Para el candidato uniforme, usando \(o=p-s\),

\[
12(U-R)
=
q(2o+q)-2p.
\tag{7.2}
\]

Como \(q,o\ge0\),

\[
U-R\ge-\frac p6.
\tag{7.3}
\]

Para el candidato separado,

\[
12(D-R)
=
12o^2-6o(2p-q)+(2p-q)^2-6p.
\tag{7.4}
\]

La parte cuadrática es no negativa porque

\[
12u^2-6uv+v^2
=
12\left(u-\frac v4\right)^2+\frac{v^2}{4}.
\]

Así,

\[
D-R\ge-\frac p2.
\tag{7.5}
\]

Para el candidato de conjunto caliente,

\[
12(H-R)
=
(2s-q)^2+2q(p-s)-2p-4s.
\tag{7.6}
\]

Los dos primeros términos son no negativos, y \(s\le p\), luego

\[
H-R\ge-\frac p2.
\tag{7.7}
\]

En consecuencia,

\[
M(\kappa^S)
\ge
R(p,q)-\frac p2
\]

para todo perfil puro. Por (5.4),

\[
\boxed{
M(\kappa)
\ge
R(p,q)-\frac p2.
}
\tag{7.8}
\]

Cuando \(q=0\), la misma estimación se obtiene directamente. Si \(p\le2\), entonces \(M(0)=0\). Si \(p\ge3\), la cobertura constante \(z_e=1/3\) es factible. Para ver que es óptima, se suman las restricciones de cobertura sobre todos los triángulos del clique: cada arista del clique aparece en exactamente \(p-2\) de esos triángulos, lo que da la cota inferior correspondiente. Por lo tanto,

\[
M(0)=\frac{p(p-1)}6.
\]

---

## 8. Prueba del teorema principal

Partimos de (4.9):

\[
|E(G)|-2V_{\mathrm{com}}
=
\binom p2-2M(\kappa)+b_1.
\]

Insertamos (7.8):

\[
|E(G)|-2V_{\mathrm{com}}
\le
\binom p2-2R(p,q)+p+b_1.
\tag{8.1}
\]

Una simplificación directa da

\[
\binom p2-2R(p,q)+p
=
\frac{(p+q)^2}{6}+\frac p2.
\tag{8.2}
\]

Por tanto,

\[
|E(G)|-2V_{\mathrm{com}}
\le
\frac{(p+q)^2}{6}+\frac p2+b_1.
\tag{8.3}
\]

Por (2.2), los vértices contados por \(p+q\) forman solo una parte de \(V(G)\), de modo que

\[
p+q\le n
\]

y el término cuadrático puede agrandarse en consecuencia. Asimismo, los vértices del clique y los vértices independientes de grado uno son disjuntos, y por tanto

\[
\frac p2+b_1
\le
p+b_1
\le
n.
\]

Así,

\[
|E(G)|-2V_{\mathrm{com}}
\le
\frac{n^2}{6}+n.
\tag{8.4}
\]

Finalmente, \(V_{\mathrm{com}}\le\nu_3^*(G)\). Luego

\[
|E(G)|-2\nu_3^*(G)
\le
|E(G)|-2V_{\mathrm{com}}
\le
\frac{n^2}{6}+n.
\]

Esto prueba el Teorema 1.1.

---

## 9. Discusión

Tres ideas elementales impulsan la prueba. Primero separamos el empaquetamiento en una parte soportada en triángulos que intersectan el conjunto independiente y una parte residual soportada enteramente en el clique. Luego formulamos el problema residual sobre un único politopo fijo de cobertura. La simetría se usa solo después de que el problema de cota inferior ha sido reducido a perfiles puros.

El rasgo estructural central es el politopo fijo. La concavidad aplica porque la región factible no cambia cuando cambia el perfil de vecindarios; solo cambia el vector objetivo. Si las restricciones mismas dependieran del perfil, la reducción de la Sección 5 ya no se seguiría del mismo argumento. El promedio orbital es un paso separado: usa la simetría de un perfil puro y no es necesario para la reducción afín en sí.

Las cantidades intermedias \(p\), \(q\) y \(\kappa\) dependen de la presentación split elegida. La estimación final no. Una vez ensamblados los términos, la conclusión se expresa solo en función de \(n=|V(G)|\).

El término aditivo \(+n\) en el Teorema 1.1 no está optimizado. Para la familia complete-split \(K_p\vee\overline{K}_{2p}\), con \(p\ge2\) y \(n=3p\), todo triángulo usa al menos una arista del clique, así que \(\nu_3^*(G)\le\binom p2\), mientras que la construcción de Fase I alcanza igualdad. En consecuencia, el lado izquierdo del Teorema 1.1 es igual a \(n^2/6+n/6\) en esta familia. Determinar el término lineal óptimo queda fuera del alcance de este argumento.

El artículo se limita intencionalmente a la desigualdad fraccional finita. Cualquier paso a empaquetamientos integrales de triángulos, particiones en cliques, consecuencias asintóticas o clases más amplias de grafos requiere resultados adicionales y pertenece a otra etapa.

El valor del argumento presente reside principalmente en el mecanismo de reducción, que se pretende reutilizable independientemente de la cota finita particular probada aquí.

---

## 10. Reproducibilidad y registro de prueba

La prueba es analítica. Durante el desarrollo se usaron experimentos computacionales para buscar contraejemplos y detectar errores de transcripción, pero ningún cálculo computacional es una premisa lógica del teorema. Por esa razón, el material de regresión computacional se mantiene fuera del artículo en vez de incluirse como un segundo apéndice.

El archivo acompañante `CALCULATION_LEDGER_FINITE_FRACTIONAL_preprint_v1.0.md` registra:

- toda identidad exacta;
- toda dirección de desigualdad;
- la contabilidad completa de pérdidas;
- la rama \(q=0\);
- los regímenes orbitales;
- la conversión final a \(n\).

El teorema, su cota cuantitativa y el ensamblaje completo han recibido auditoría adversarial interna. Esta afirmación describe el registro de validación del autor; no es una afirmación de revisión externa por pares.

### Verificación formal en Lean

El Teorema 1.1 está formalizado y verificado por máquina en Lean 4 con Mathlib v4.28.0 [6,7]. La declaración correspondiente es `paperI_main`. Su enunciado formal es `Phi ≤ n^2/6 + n`; bajo las definiciones usadas en el desarrollo Lean, `Phi = |E| − 2·nu3star`, y `nu3star` es el supremo de los valores factibles de empaquetamientos fraccionales de triángulos. Esta es la misma desigualdad que el Teorema 1.1, escrita en la notación de la formalización; el Apéndice C registra la declaración Lean exacta.

El desarrollo no contiene `sorry`. El reporte de axiomas registrado para `paperI_main` contiene solo los axiomas fundacionales estándar de Lean, `propext`, `Classical.choice` y `Quot.sound`. No se usa ningún axioma específico del proyecto. Estos axiomas son parte de la fundación lógica ordinaria usada en Mathlib, no supuestos matemáticos adicionales introducidos por este artículo.

La dualidad finito-dimensional de empaquetamiento-cobertura usada en la Proposición B.1 también está formalizada. En Lean aparece como `residual_duality`, una aplicación del teorema general `covering_packing_duality`. Ese teorema general se prueba a partir de un lema finito de Farkas y de la infraestructura de conos cerrados de Mathlib; por tanto, la dualidad se deriva dentro del desarrollo formal, no se postula como axioma externo. La cita a Schrijver [4, Corolario 7.1g] sigue siendo la referencia clásica para la prueba matemática escrita.

El artefacto público de formalización se distribuye con el preprint a través del repositorio del proyecto [8], en `PAPER_I/05_formalization/lean`. El paquete de lanzamiento contiene las fuentes Lean `FiniteLPDuality.lean` y `PaperI_Statement.lean`, el archivo de toolchain, la configuración y el manifiesto de Lake, instrucciones exactas de compilación, un log de compilación registrado y el reporte de axiomas registrado para el Teorema 1.1 y la Proposición B.1. Estos archivos hacen que las afirmaciones de verificación formal sean reejecutables y auditables de manera independiente.

---

## Apéndice A. El programa de tres órbitas y sus casos de frontera

Este apéndice registra la solución del programa de órbitas usado en la Sección 6. La región factible depende de cuáles tipos de triángulos existen. Escribimos \(o=p-s\).

### A.1 El caso interior \(s\ge3\) y \(o\ge3\)

Todos los tipos de triángulos existen, y las restricciones son

\[
3\alpha\ge1,\qquad
\alpha+2\beta\ge1,\qquad
2\beta+\gamma\ge1,\qquad
3\gamma\ge1,
\qquad
0\le\alpha,\beta,\gamma\le1.
\]

Los candidatos relevantes para minimizar el objetivo lineal

\[
A\alpha+B\beta+C\gamma
\]

son

\[
U=\frac{A+B+C}{3},
\qquad
D=A+C,
\qquad
H=A+\frac{B+C}{3}.
\]

Corresponden respectivamente a:

\[
(\alpha,\beta,\gamma)=\left(\frac13,\frac13,\frac13\right),
\]

\[
(\alpha,\beta,\gamma)=(1,0,1),
\]

y

\[
(\alpha,\beta,\gamma)=\left(1,0,\frac13\right).
\]

La verificación de los demás vértices del politopo muestra que ninguno mejora a estos candidatos para los signos de coeficientes que aparecen en el problema. Esta es una enumeración finita de vértices de un politopo tridimensional. El cálculo detallado está registrado en el ledger de cálculo.

### A.2 El caso \(s=2\)

No hay triángulos \(SSS\). La restricción \(3\alpha\ge1\) se omite. La variable \(\alpha\) aparece con coeficiente

\[
A=\frac{s(s-1-q)}2=1-q.
\]

Si \(q\ge1\), entonces \(A\le0\), y el mínimo empuja \(\alpha\) hacia su valor máximo permitido por la caja. Si \(q=0\), no hay vértices activos de \(I_{\ge2}\), y el caso se cubre en la rama \(q=0\) de la Sección 7.

Los mismos candidatos \(U,D,H\), con las restricciones inexistentes omitidas, dan la fórmula usada en (6.5).

### A.3 Los casos \(o=0,1,2\)

Cuando \(o\le2\), no existen triángulos \(OOO\), y para \(o\le1\) tampoco existen triángulos \(SOO\). Los candidatos de conjunto caliente que dependen de la restricción \(3\gamma\ge1\) desaparecen. La fórmula resultante es

\[
M(\kappa^S)=\min\{U,D\}.
\]

En particular, si \(o=0\), entonces \(B=C=0\), y el problema se reduce a minimizar \(A\alpha\) bajo las restricciones existentes sobre triángulos \(SSS\). Si \(s\ge3\), la restricción \(3\alpha\ge1\) da

\[
\min_{\alpha\in[1/3,1]}A\alpha
=
\min\left\{\frac A3,A\right\}
=
\min\{U,D\}.
\]

Si \(s=2\), no hay triángulos del clique, la restricción \(3\alpha\ge1\) no existe y \(A=1-q\le0\) en la rama activa; el óptimo es \(D=A\). Estos son precisamente los valores usados en la prueba principal.

---

## Apéndice B. Dualidad finita de empaquetamiento-cobertura

Para completitud, registramos el par dual finito de empaquetamiento-cobertura usado en la Sección 4.

Sea \(F\) un conjunto finito de aristas y sea \(\mathcal T\) una familia finita de triángulos sobre \(F\). Dadas capacidades \(r_e\ge0\), consideramos

\[
\begin{aligned}
\text{maximizar}\quad
&\sum_{T\in\mathcal T}w_T\\
\text{sujeto a}\quad
&w_T\ge0,\\
&\sum_{T\ni e}w_T\le r_e
\qquad(e\in F).
\end{aligned}
\tag{B.1}
\]

El dual es

\[
\begin{aligned}
\text{minimizar}\quad
&\sum_{e\in F}r_ex_e\\
\text{sujeto a}\quad
&x_e\ge0,\\
&\sum_{e\in E(T)}x_e\ge1
\qquad(T\in\mathcal T).
\end{aligned}
\tag{B.2}
\]

#### Proposición B.1

Los valores óptimos de (B.1) y (B.2) son iguales.

#### Prueba

La dualidad débil es inmediata:

\[
\sum_Tw_T
\le
\sum_Tw_T\sum_{e\in E(T)}x_e
=
\sum_er_e x_e.
\]

Ambos programas son finitos, factibles y acotados cuando \(0\le r_e\le1\). La dualidad fuerte finito-dimensional de programación lineal, en la forma de Schrijver [4, Corolario 7.1g], se aplica directamente a este par primal-dual. Por lo tanto, los valores óptimos coinciden.

En la aplicación de la Sección 4, \(F=E(K)\), \(\mathcal T\) es el conjunto de triángulos del clique, y \(r_e=\max\{1-\kappa_e,0\}\).

**Nota de formalización.** La Proposición B.1 también está verificada en Lean como `residual_duality`, una instancia del teorema general de dualidad fuerte finita `covering_packing_duality`. Este último se prueba a partir de un lema finito de Farkas, usando la cerradura de un cono convexo finitamente generado y el teorema de separación por hiperplanos para conos convexos cerrados. Así, la dualidad usada aquí se deriva dentro del desarrollo formal, no se postula como axioma específico del proyecto. Schrijver sigue siendo la referencia clásica para el argumento escrito. Las fuentes correspondientes, el log de compilación y el reporte de axiomas están incluidos en el artefacto público [8], en `PAPER_I/05_formalization/lean`.

---

## Apéndice C. Enunciado formalizado

El enunciado del Teorema 1.1 verificado por máquina es la siguiente declaración de Lean 4:

```lean
theorem paperI_main (G : Split) :
    G.Phi ≤ (G.n : ℝ) ^ 2 / 6 + (G.n : ℝ)
```

Aquí `Split` empaqueta los datos de un grafo split usados en la prueba: un clique de tamaño `p`, un tipo de vértices independientes y los vecindarios de los vértices independientes dentro del clique. El campo `n` es el número total de vértices. La cantidad `Phi` se define como `|E| − 2·nu3star`, donde `nu3star` es el supremo de los valores factibles de empaquetamientos fraccionales de triángulos. Con estas definiciones, `paperI_main` es precisamente

\[
|E(G)|-2\nu_3^*(G)\le \frac{n^2}{6}+n,
\]

la desigualdad enunciada en el Teorema 1.1.

La verificación no contiene `sorry`. El reporte de axiomas registrado es:

```text
PaperI.paperI_main depends on axioms: [propext, Classical.choice, Quot.sound]
```

Estos son los tres axiomas fundacionales estándar de Lean y Mathlib. No se usa ningún axioma específico del proyecto.

## Agradecimientos

El autor agradece profundamente a su esposa María Paz y a sus hijos Lucas, Juan Cristóbal, Francisca, Raimundo y Benjamín por su amor, paciencia y apoyo.

---

## Uso de herramientas asistidas por IA

Se usaron herramientas asistidas por IA durante las etapas exploratorias, computacionales, adversariales y editoriales, incluidos sistemas de Anthropic, Google y OpenAI. Estas herramientas apoyaron la prueba de argumentos candidatos, chequeos exactos de regresión, organización de pruebas y redacción. El autor revisó el contenido matemático, seleccionó los argumentos finales y es el único responsable de las afirmaciones, citas, artefactos de código y presentación. Ningún sistema de IA figura como autor.

---

## Referencias

1. P. Erdős, E. T. Ordman, and Y. Zalcstein, “Clique partitions of chordal graphs,” *Combinatorics, Probability and Computing* **2** (1993), no. 4, 409–415.

2. G.-T. Chen, P. Erdős, and E. T. Ordman, “Clique partitions of split graphs,” in *Combinatorics, Graph Theory, Algorithms and Applications* (Beijing, 1993), World Scientific, 1994, pp. 21–30.

3. T. F. Bloom, “Erdős Problem #81,” *Erdős Problems*, https://www.erdosproblems.com/81, accessed 2026-07-06.

4. A. Schrijver, *Theory of Linear and Integer Programming*, Wiley-Interscience Series in Discrete Mathematics and Optimization, John Wiley & Sons, Chichester, 1986.

5. M. S. Cavers, *Clique Partitions and Coverings of Graphs*, M.Math. essay, University of Waterloo, 2005.

6. L. de Moura and S. Ullrich, “The Lean 4 Theorem Prover and Programming Language,” in *Automated Deduction – CADE 28*, Lecture Notes in Computer Science **12699**, Springer, 2021, pp. 625–635, https://doi.org/10.1007/978-3-030-79876-5_37.

7. The mathlib Community, “The Lean Mathematical Library,” in *Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs (CPP 2020)*, ACM, 2020, pp. 367–381, https://doi.org/10.1145/3372885.3373824.

8. J. P. Traverso Gianini, *Erdős #81 Chordal Clique Partitions: Public Preprints and Formalization Artifacts*, public project repository, 2026, https://github.com/jtraverso/erdos-81-chordal-clique-partitions, accessed July 7, 2026.
