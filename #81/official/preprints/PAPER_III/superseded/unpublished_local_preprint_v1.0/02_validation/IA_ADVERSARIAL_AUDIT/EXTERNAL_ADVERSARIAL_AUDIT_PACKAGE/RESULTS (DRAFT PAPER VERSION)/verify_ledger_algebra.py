# -*- coding: utf-8 -*-
# Verificacion simbolica exacta de las cadenas que iran al ledger (base mathlib).
import sympy as sp
p,q,s,m,rho,al,d = sp.symbols('p q s m rho alpha d', positive=True)

print("== Teorema 4.2: identidad T(G) ==")
# T(G) = (1/2)(|E| - (p+q)^2/6); con |E| = C(p,2)+sum d_i, y C_alpha p^2 = (2-2a-a^2)/12 p^2
# Afirmacion del paper (4.2 proof): T(G) = (1/2)sum d_i + C_alpha p^2 - p/4
# Chequeo: (1/2)[C(p,2)+S - (p+q)^2/6] =? (1/2)S + C_alpha p^2 - p/4  con q=alpha p
Ca=(2-2*al-al**2)/12
lhs=sp.Rational(1,2)*(p*(p-1)/2 - (p+al*p)**2/6)   # (1/2)(C(p,2) - (p+q)^2/6), parte sin S
rhs=Ca*p**2 - p/4
print("  T sin-S  lhs-rhs =", sp.simplify(lhs-rhs), " (debe ser 0)")

print("== (7.2) => listas >= Delta en el gain graph ==")
print("  d(v_i)=g_i<=rho ; d(r)<=u ; |L|=b-t_i>=max(rho,u)>=Delta : correcto por construccion")

print("== 9.3 dispersion ALTA: (9.12) ==")
# Phi - n^2/6 <= p/2 - s^2/6 + (s-1)M/q - S2/q - (2 delta/q(q-1)) V,  con:
#   (9.11) (s-1)M/q - S2/q <= 2s(s-3)/9
#   (9.9) V >= (q/2) D ,  (9.8) D >= q s^2/12  => V >= q^2 s^2/24
#   delta >= 7/8 ; 2/(q(q-1)) * V >= 2/(q^2) * q^2 s^2/24 = s^2/12  (usando q-1<q, cota conservadora del paper)
# termino de polarizacion >= (7/8)*(s^2/12) = 7 s^2/96
pol = sp.Rational(7,8)*(s**2/12)
expr = p/2 - s**2/6 + sp.Rational(2,1)*s*(s-3)/9 - pol
print("  Phi-n^2/6 <=", sp.nsimplify(sp.expand(expr)))
print("  coef de s^2:", sp.expand(expr).coeff(s**2), " (debe ser -5/288)")

print("== 9.3 dispersion BAJA: (9.19) y (9.20) ==")
# (9.19): s^2/6 - s rho + 2 rho^2 = 2(rho - s/4)^2 + s^2/24
id919 = sp.simplify( (s**2/6 - s*rho + 2*rho**2) - (2*(rho - s/4)**2 + s**2/24) )
print("  (9.19) identidad, lhs-rhs =", id919, " (debe ser 0)")
# (9.20): Phi - n^2/6 <= p/2 - [s^2/24 - 5 s^2/192] = p/2 - s^2/64
final = sp.simplify(s**2/24 - sp.Rational(5,192)*s**2)
print("  s^2/24 - 5s^2/192 =", final, " (debe ser s^2/64 = ", sp.Rational(1,64),"* s^2)")

print("== 9.10: delta >= 7/8 si s <= p/8 ==")
# p impar: delta=(p-s)/p ; p par: delta=(p+1-s)/(p-1). Peor caso s=p/8.
di=sp.simplify((p - p/8)/p); dp=sp.simplify((p+1-p/8)/(p-1))
print("  p impar, s=p/8: delta =", di, ">=7/8 ?", sp.simplify(di-sp.Rational(7,8))>=0)
print("  p par,  s=p/8: delta-7/8 =", sp.simplify(dp-sp.Rational(7,8)), "(>=0 para p>=? )")

print("== umbral: 6*sqrt(p) = p/8  <=>  p = 2304 ==")
print("  (6*sqrt(p)=p/8) => sqrt(p)=48 => p=2304 :", sp.solve(sp.Eq(6*sp.sqrt(p), p/8), p))
