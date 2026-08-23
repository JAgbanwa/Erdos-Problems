# Auditoria de PAPER C (split lineal, ex-v1.0.4) — track C, 2026-07-20

**Alcance:** manuscrito completo. Tres capas: (1) cadena logica y constantes a mano,
(2) verificacion numerica exacta de los teoremas de carga, (3) auditoria ILP de los
lemas de redondeo. **Veredicto anticipado: APTO PARA PUBLICAR** con 3 observaciones
menores de exposicion (ninguna afecta la correccion).

## Capa 1 — verificacion a mano (COMPLETA, sin errores encontrados)

### Estructura logica global (Sec. 9)
Contradiccion sobre secuencia minimal + subsecuencias por regimen. Verificado:
- (9.2) d(v) > (2n-1)/6 + k: correcto (Phi(G) <= Phi(G-v)+d(v) + minimalidad).
- Caso q >= 2p-1 despachado por Lema 5.1 antes de los regimenes. OK.
- Los tres regimenes cubren [0,2) tras subsecuencia. OK.

### Cadena de constantes de 9.3 (el corazon efectivo) — TODAS verificadas:
- (9.5) 3m <= s-3: de (9.2) con k>=1, m_i < s/3 - 5/6, entero. OK.
- (9.9) 2p-3m-1 >= q+2 y V >= qD/2 via Lema 6.1. OK.
- (9.10) delta >= 7/8 en ambas paridades de p (p impar: (p-s)/p; p par: (p-s+1)/(p-1);
  ambos >= 7/8 sii s <= p/8, con margen). OK.
- (9.11) (s-1)M/q - S2/q <= 2s(s-3)/9: parabola creciente hasta M/q=(s-1)/2 >= (s-3)/3. OK.
- (9.12) -s^2/6 + 2s^2/9 = s^2/18; s^2/18 - (7/96)s^2 = -5s^2/288. OK. Con s^2>=36p: <= -p/8. OK.
- (9.16) kappa_R <= s/q + 2*theta_R: verificado algebraicamente
  (kappa = -1 + 2r_b/q + theta(2-2r_b/q); r_b <= p da -1+2r_b/q <= s/q). Luego
  8s/15p + 16s/23p = (424/345)(s/p) ~ 1.229 s/p <= 1.25 s/p. OK con margen.
- (9.18) 5s^3/24p <= 5s^2/192 usando s <= p/8. OK.
- (9.19) identidad de cuadrados 2(rho-s/4)^2 + s^2/24. OK.
- (9.20) s^2/24 - 5s^2/192 = 3s^2/192 = s^2/64; con s^2 >= 36p: <= -p/16. OK.
- Consistencia del umbral: 6*sqrt(p) <= p/8 sii p >= 2304 — exactamente la constante
  declarada en (9.4). OK (el umbral es exacto, no holgado).

### Hipotesis de Lema 7.1 en el punto de uso (punto que habia flagueado): RESUELTO.
b - t_i - u >= s - 2rho - t_i - 1 >= s - (3m+1) >= 2 > 0 usando (9.5). La hipotesis
(7.2) se cumple con holgura 2. El caso rho<=1 (sin edges en K[R]) esta tratado
explicitamente en 7.3. Sin gap.

### Lemas individuales
- Teorema 3.1: LP simetrizado correcto; los 5 tipos de triangulo cubiertos
  (NNN, NNI, NNR, NRR, RRR; no existen INR ni IRR ni III). Reduccion afin al
  triangulo de vertices (1/3,1/3),(1,1),(1,1/3) correcta. Dualidad OK.
- Lema 4.1 (replicacion): la clonacion de pesos da cobertura valida de H(p,q,d_i)
  con valor A + qB_i; suma y promedio correctos. OK.
- Identidad T(G) = (1/2)Sum d_i + C_alpha p^2 - p/4: verificada
  (3-(1+alpha)^2 = 2-2alpha-alpha^2). OK.
- (5.2)-(5.3): algebra verificada a mano paso a paso, incluida
  pq - C(p,2) = n^2/6 - s^2/6 + p/2 y el maximo de la parabola (s-1)^2/4. OK.
- Lema 5.2: probabilidades de perdida correctas (1 apice: b_e/q; 2 apices:
  b_e(b_e-1)/q(q-1)); identidad U = M/q - delta*V/(q(q-1))... verificada en la forma
  (1/q)Sum b_e - (delta/q(q-1)) Sum b_e(q-b_e). OK.
- Lema 6.1: conteo |B_i\B_j| = a_ij(2(p-|S_j|)-a_ij-1)/2 y la cota. OK.
- Seccion 7: disjuncion de las tres familias QQI/IRQ/RRQ verificada (I-vertices
  reservados vs asignados; borrado de aristas rz incidentes a U_z). Colores/listas:
  |L| = b - t_i >= max grados via (7.2). Perdida esperada en RRQ <= (rho-1)/b por
  vertice usando que r esta emparejado en <= rho-1 factores. OK.
- Seccion 8: Dirac aplicable (d_i - i >= d_i/2 pues d_i >= 2q+2 > 2i); correccion de
  divisibilidad (App. B) correcta (paridad por prefijos, C4/C5 dentro de K5, perdida
  de grado <= 4); umbral (8.9) con eps_0 = 1/100 y q <= p/20. OK.
- Nitidez (10.1): Phi(K_p v bar-K_2p) = n^2/6 + n/6 verificado (nu_3 = C(p,2) optimo
  pues todo triangulo usa >= 1 arista de clique). OK.

## Capa 2 — numerica exacta (COMPLETA, 0 fallas)
Script: audit_c_fast.py
- Teorema 3.1 vs LP directo de triangulos: p<=9, q<=5, todos los d: **245/245**.
  (Cubre los casos degenerados d<3, r<3: la formula es valida alli tambien.)
- Teorema 4.2 (cada rama >= qd/2 + (C_a+mu)p^2 - p/2), aritmetica de fracciones:
  p<=40, q<=2p, todo d: **45,904/45,904**.
- Dominancia de la tercera rama residual (App. A): 241 puntos racionales, 0 fallas.

## Capa 3 — ILP de lemas de redondeo (COMPLETA, 0 fallas)
Script: audit_c_ilp.py -> audit_c_ilp_results.txt. Contra nu_3 exacto por ILP:
- Lema 5.1 (cota de factorizacion): 16/16.
- Lema 5.2/(5.4) con energia de polarizacion V exacta: 27/27.
- Lema 7.1/(7.6) en instancias cumpliendo (7.1)-(7.2): 48/48.

## Observaciones (menores, de exposicion — no afectan correccion)
1. **Lema 5.2:** el argumento promedia sobre la eleccion de los h factores dobles Y
   sobre la asignacion inyectiva de vertices; el texto dice "choose h factors" y luego
   usa delta = h/r_p como peso uniforme por arista. Sugerencia: una frase explicitando
   que la eleccion de los h factores tambien se promedia (o se sortea uniforme).
2. **Teorema 2.3:** el enunciado 0.9+eps combina Dross (fraccionario 9/10) + BKLO
   (absorcion iterativa). Correcto, pero conviene citar el enunciado combinado con
   precision de fuente (la conversion BKLO requiere delta >= (0.9+o(1))|V|; la forma
   usada esta bien). Nota: solo afecta la NO-efectividad ya declarada en 11.3.
3. **Seccion 7.1:** "Assign the remaining r_b vertices bijectively" — implicita que
   |I \ U| = r_b exactamente (u = q - r_b); una palabra lo aclara.

## Veredicto
- Cadena logica: sin gaps encontrados.
- Constantes: todas correctas; el umbral p>=2304 es exacto (6*sqrt(p) = p/8).
- Numerica: 46,149 verificaciones exactas, 0 fallas (capas 2 y 3 cerradas: 46,240 verificaciones, 0 fallas).
- Los dos puntos que este auditor habia flagueado a priori ((9.16) y rho=0/(7.2))
  quedan RESUELTOS a favor del manuscrito.

**Recomendacion: publicar como Paper III de la linea oficial** tras incorporar las
3 observaciones de exposicion. El resultado es el mas fuerte de la serie hasta hoy
y su maquinaria de corredor es insumo directo del cierre chordal.
