# Audit Record

Audit ID: ERDOZ81-P1-3ORBIT-SOLVE-01-AUD-001  
Gate ID: ERDOZ81-P1-3ORBIT-SOLVE-01  
Statement version: 0.1  
Audit type: SELF_AUDIT  
Independence level: same agent, separate adversarial pass  
Auditor: Researcher  
Materials supplied: exact gate statement, corrected orbit program, proof candidate  
Materials withheld: historical claimed solution was not used as authority  
Protocol version: 1.0

## Scope

Attempt to reject the exact formula for the orbit optimum, with emphasis
on missing boundary vertices, negative \(A\), and the exceptional case
\(s=2\).

## Claims Checked

C-3SOLVE-01 through C-3SOLVE-06.

## Adversarial Checks

### 1. Missing constraints by existence regime

The audit rechecked that \(H\) is used only when \(o\ge3\), where
\(\gamma\ge1/3\) is a genuine \(OOO\)-triangle constraint. No nonexistent
constraint is reintroduced.

Verdict: PASS.

### 2. Sign of \(A\)

No step assumes \(A\ge0\). All remaining objectives are affine in
\(\alpha\), so both signs are covered by endpoint minimization.

Verdict: PASS.

### 3. Exceptional case \(s=2\)

When \(s=2\), \(\alpha\) may lie below \(1/3\). The proof separately
checks this interval. Since \(q\ge1\):

- for \(o=0\), \(A=1-q\le0\);
- for \(o=1\), the slope is \(-q<0\);
- for \(o=2\), the slope is \(-q<0\);
- for \(o\ge3\) and \(\alpha\le1/3\), the slope is \(1-q-o<0\).

Thus no extra optimum occurs at \(\alpha=0\) or in
\(0<\alpha<1/3\).

Verdict: PASS.

### 4. Fixed-\(\alpha\) minimization for \(o=2\)

The coefficient controlling movement along
\(\gamma=1-2\beta\) is

\[
B-2C=2s-2>0.
\]

Hence the least feasible \(\beta\), not \(\beta=1/2\), is optimal.
The adjoining branch \(\gamma=0,\beta\ge1/2\) cannot improve it.

Verdict: PASS.

### 5. Fixed-\(\alpha\) minimization for \(o\ge3\)

The feasible lower boundary has exactly two linear segments meeting at
\((\beta,\gamma)=(1/3,1/3)\). Their slopes are controlled by
\(B-2C\) and \(B\), respectively. Since \(B>0\), no point with
\(\beta>1/3\) can improve the junction. No third branch is omitted.

Verdict: PASS.

### 6. Exhaustiveness

The proof does not rely on enumerating vertices. For every fixed
\(\alpha\), it minimizes over every feasible \((\beta,\gamma)\); it then
minimizes the resulting affine function over the full feasible interval
for \(\alpha\). This covers the entire polytope.

Verdict: PASS.

### 7. Candidate comparisons

When \(B-2C\ge0\),

\[
H-D=(B-2C)/3\ge0.
\]

When \(B-2C\le0\),

\[
D-H=(2C-B)/3\ge0.
\]

Thus the inactive candidate cannot undercut the two active endpoints.

Verdict: PASS.

### 8. Degenerate equality \(B=2C\)

Both lower-bound segments have equal cost and the formulas
\(\min\{U,D\}\) and \(\min\{U,H\}\) agree because \(D=H\).

Verdict: PASS.

## Falsification Performed

Checked symbolically:

- \(s=2\) in every \(o\)-regime;
- \(o=0,1,2,3\);
- \(A<0\), \(A=0\), and \(A>0\);
- \(B-2C<0\), \(=0\), and \(>0\);
- boundary points \(\alpha=0,1/3,1\);
- junction \(\beta=\gamma=1/3\);
- separated point \((\alpha,\beta,\gamma)=(1,0,1)\).

No counterexample was found.

## Material Objections

None.

## Exclusions

- No audit of the future comparison with \(R(p,q)\).
- No independent audit.
- No admission decision for upstream evidence.

## Verdict

`PROVISIONAL_PASS / SELF_AUDITED`.

## Required Actions

- Derive and audit the quantitative comparison with the target
  expression \(R(p,q)\).
- Preserve the \(o\le2\) versus \(o\ge3\) distinction in all downstream
  statements.
- Obtain the required later independent audit before freeze.
