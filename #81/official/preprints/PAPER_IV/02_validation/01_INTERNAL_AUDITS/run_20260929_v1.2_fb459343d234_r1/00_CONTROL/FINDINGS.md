# Hallazgos y correcciones de la auditoría interna v1.2

No se encontró un defecto matemático bloqueante en el alcance revisado. Se preservan los siguientes incidentes; ninguno cambia una fuente Lean ni un manuscrito congelado.

| ID | Clase | Resultado |
|---|---|---|
| I-01 | Verificador de identidad | Una comparación inicial por basename confundía miembros homónimos del ZIP. Se corrigió a la ruta completa; intento conservado en G0_INTEGRITY/attempts. Reejecución correcta. |
| I-02 | Inventario | Se corrigió la extracción de nombres Lean con apóstrofo; la fuente formal no cambió. Inventario final sin ambigüedades. |
| I-03 | Regresión de 6.3a | La primera transcripción del control usó d(q-1-d), que no era la diferencia de aristas del manuscrito. Se sustituyó por d(4q-4s-d-1)/2. El script original queda en attempts/extension_001. En q=3,s=0,d=1, la expresión incorrecta daba 1; la correcta da 5. La nueva regresión pasa. |
| I-04 | Alcance del anexo | El primer verificador intentó vincular todas las fuentes históricas de un build de 579 módulos, incluidas las no distribuidas. Se corrigió conforme al README del anexo: verificar su cierre real y leer los demás logs solo como historial. Script original en attempts/annex_001. No se atribuye a 579 fuentes un cotejo inexistente. |
| I-05 | Referencia editorial menor | A.2, fila de fibras, dice '§3.2 and C.2' en EN y equivalente ES. No existe una sección 3.2: el destino es Lema 3.2 y C.1-C.2. Esta aclaración es la errata del expediente, sin cambio semántico. Los archivos congelados permanecen intactos; aplicar al texto exigiría nueva identidad de manuscrito. |
| I-06 | Orden de ejecución | Se ejecutaron regresiones finitas ligeras antes de cerrar toda G1. No se tomó su éxito como aprobación semántica. La revisión G1/E.4/F.5 se completó antes del dictamen final. Desviación documentada, no relajación del criterio. |
| I-07 | Producción de informes | El generador tuvo una colisión local de nombre antes de compilar; corregida. La primera plantilla requería una métrica de fuente no almacenada en caché. Se conservó el fallo en attempts/report_font_001 y se usaron las fuentes OpenType Latin Modern ya utilizadas por el manuscrito. No se instaló ni descargó nada; se recompilaron los informes y se revisaron los PDF. |

Las salidas previas con estado pendiente no se borran: los archivos de aceptación finales identifican qué revisión posterior las cierra. Las fuentes compiladas, los manuscritos y las huellas del corte no se alteran. No se emite un PASS externo ni de b=0.
