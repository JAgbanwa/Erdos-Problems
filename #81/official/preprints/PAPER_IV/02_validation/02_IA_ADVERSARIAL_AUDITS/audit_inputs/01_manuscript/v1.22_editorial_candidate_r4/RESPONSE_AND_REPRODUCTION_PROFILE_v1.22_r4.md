# Respuesta al informe r3 y perfil de reproducción r4

El informe externo r3 concluyó PASS_WITH_FINDINGS. Su única acción nueva, NEW-05, son las dos expresiones españolas corregidas aquí. No se atribuye al informe un PASS global que todavía no ha emitido.

| Punto | Respuesta y estado actual |
| --- | --- |
| NEW-05, A.2 y F.4 | Corregido localmente en MD/TeX/PDF; pendiente de confirmación externa. Véanse CHANGES_es.diff y TERMINOLOGY_DELTA.json. |
| NEW-04 y E8-02 | Cerrados en r3; no se reabren mediante cambios adicionales. |
| X-28 | Defecto histórico del runner conservado en el registro; acción de control mitigada en r3. El verificador suplementario sigue siendo obligatorio e idéntico. |
| Observaciones aceptadas | Se conservan X17, X18, X19, X22, X24, X29 y R01, sin convertirlas en acciones nuevas. |
| Independencia | Declarar el modelo y la continuidad real de sesión. No afirmar revisión ciega o independencia de familia que no exista. |
| Revisión humana | Hito posterior independiente, fuera de E0–E8. Puede recomendarse; su ausencia no impide PASS si se cumplen todos los criterios de este encargo. |

## Reproducción limitada

1. Verificar el objetivo r4, sus hashes y su manifiesto, y contrastar los antecedentes r3.
2. Ejecutar `python check_r4.py` sólo en una copia de trabajo si se desea reproducir el control editorial: el script escribe su resultado, por lo que no se debe ejecutar sobre el paquete sellado. No ejecuta Lean.
3. Confirmar por hashes que `verify_frozen_logs.py` y `LOG_INVENTORY.json` son idénticos a r3. Mantener el verificador como parte obligatoria del perfil de reproducción; sus pruebas, controles corruptos y resultados completos se heredan del paquete externo r3. Si se repite, usar una carpeta de salida propia y la interfaz ya documentada allí.
4. Consolidar E0–E8, no sólo el delta. Distinguir controles nuevos de los heredados por identidad. No repetir el build ni instalar Mathlib.

La identidad formal es `piv-v12-fb459343d234`. El inglés no cambia. La compilación española se ejecutó sólo con recursos existentes. Los párrafos históricos de estado del manuscrito siguen describiendo los informes anteriores con su revisión: no se reescriben como si r4 ya hubiera sido aprobado.

## Solicitud al auditor

Aplicar `EXTERNAL_ADVERSARIAL_REVALIDATION_v1.22_r4.md`. Si NEW-05 queda cerrado y no existe otra acción correctiva abierta dentro de E0–E8, emitir PASS para ese alcance, con límites e historia explícitos. Si encuentra un defecto, conservarlo y precisar el criterio incumplido. No se pide ocultar observaciones ni garantizar de antemano un resultado.

El nuevo informe consolidado y su paquete deben quedar en `02_validation/02_IA_ADVERSARIAL_AUDITS/run_v1.22_r4/`, con hashes, matriz de trazabilidad y todos los PASS históricos justificados. La preparación de este paquete no inicia la auditoría ni autoriza publicar.
