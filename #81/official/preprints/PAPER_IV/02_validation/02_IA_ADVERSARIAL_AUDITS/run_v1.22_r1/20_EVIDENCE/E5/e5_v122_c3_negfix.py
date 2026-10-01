"""Corrected negative control for C3m (added after run 1; original result kept in E5_V122_C3.json).
The original control '(R*16^R)^6 <= 2^(29R)' is TRUE (R^6 <= 2^(5R)), so it could not discriminate.
Corrected control: '(R*16^R)^6 <= 2^(24R)' must FAIL (R^6 > 1 for R >= 2)."""
import json
neg = all((R * 16**R)**6 <= 2**(24 * R) for R in range(1, 51))
json.dump({'id': 'C3m-negfix', 'corrected_negative': '(R*16^R)^6 <= 2^(24R) on R=1..50', 'negative_holds': neg, 'negative_rejected': not neg}, open('E5_V122_C3_negfix.json', 'w'), indent=1)
print('negative rejected:', not neg)
