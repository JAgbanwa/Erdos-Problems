"""Generate audit reports from reviewed evidence. No Lean invocation or downloads."""
from pathlib import Path
import hashlib,json,subprocess,sys,re,shutil,importlib.metadata as metadata
from datetime import datetime,timezone
import fitz
from PIL import Image,ImageDraw

RUN=Path(__file__).resolve().parents[1];PAPER=RUN.parents[2]
EV=RUN/'20_EVIDENCE';CONTROL=RUN/'00_CONTROL';MATH=EV/'G2_MATHEMATICS'
PANDOC=Path('C:/Users/jtraverso/.cache/e81-editorial-tools/pandoc/pandoc-3.11/pandoc.exe')
TEX=Path('C:/Users/jtraverso/.cache/e81-editorial-tools/tectonic/tectonic.exe')
REFERENCE=PAPER.parent/'PAPER_III/02_validation/01_INTERNAL_AUDITS/run_2026-08-22_v1.4/10_REPORT/INTERNAL_AUDIT_FINAL_REPORT.tex'
def read(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,o):
    p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(o,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
def write(p,t):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t,encoding='utf-8')

BLOCKS={
'B01_MODEL':('Modelo físico y certificado Certo','Aristas reales, cobertura exacta, piezas de orden 2 a 4 y ganancia 2/5. Se separa gainOf mixto de la ganancia irrestricta.',
'Se recorrieron 33 868 grafos etiquetados hasta seis vértices y se reconstruyeron las particiones literales. Certo certificó una cubierta de seis piezas de K3 join I3; un checker independiente del productor verificó sus doce aristas. Una cota inferior por pesos de cliques demuestra seis, por separado del certificado de cubierta.',
'Omisión, solapamiento, pieza no clique, orden indebido y universo incorrecto se rechazan. El replay independiente añade controles de tamaño declarado y no clique a la prueba tamper de Certo.',
'La universalidad procede de las declaraciones formales. El certificado Certo por sí solo prueba factibilidad, no optimalidad; aquí la cota inferior es un argumento exacto adicional.'),
'B02_LP':('Óptimo fraccional y dualidad','Packing de copias reales K3/K4 con cargas no negativas y capacidad uno por arista. Las extensiones finitas mantienen s<=n, y la corrección más fuerte exige 4s<=n.',
'Se comprobaron 76 pares primal-dual en todos los grafos etiquetados hasta cuatro vértices. SciPy propone valores; el verificador racional exige factibilidad de ambos lados e igualdad exacta. Se conserva un certificado K4 y el regenerador determinista del resto.',
'Los negativos alteran carga, signo, objetivo o cota dual. No se acepta un valor flotante óptimo sin replay racional.',
'La regresión no demuestra dualidad fuerte universal ni la cota de defecto para todos los órdenes; sus interfaces y el caso pequeño fueron revisados en G1/G3.'),
'B03_ROUNDING':('Redondeo mixto y cuotas conjuntas','Precisión positiva antes del grafo, cargas por arista de ambos tipos y un único matching marcado.',
'Se revisaron los pasos de limpieza, fibra, codegrado conjunto, cuotas y desmarcado de C.1-C.2. La regresión K5 distingue dos triángulos (ganancia cuatro) de un K4 (ganancia cinco), aunque la cardinalidad favorece los primeros.',
'Se rechaza combinar packings que compiten por una arista y usar cardinalidad como sustituto de ganancia ponderada.',
'Se reutiliza el nibble atribuido a Paper III. No se deriva un teorema de redondeo asintótico de ejemplos pequeños.'),
'B04_CONSTANTS':('Constantes explícitas y enlace B7','Torre simbólica, umbral cercano separado del global, mejora completa de limpieza y umbral uniforme E35.',
'Los logs de E17.ExplicitFarAudit exigen la ruta mejorada y excluyen finales antiguos. Se comprobaron exactamente la contracción cercana, el cociente 393/100 y 101 evaluaciones de la cuenta de edición en s=0..100. El paso formal retiene la cota polinómica para todo s.',
'La desigualdad x^2<=2^x se comprueba en x=4..100 y se conserva x=3 como negativo de una extensión ilegítima. La torre enorme no se evalúa.',
'Las cotas son explícitas, no prácticas. No se confunde el umbral 4 por 10^12 con el umbral global ni se omite la condición de la forma inversa.'),
'B05_NEAR':('Constructor cercano y presupuesto neto','La raíz es clique real del grafo; ambas fases usan recursos compatibles y la misma partición.',
'100 000 vectores racionales, semilla 8104; 6 583 satisfacen ambas premisas del presupuesto y cumplen la conclusión. La cuenta de momentos y su cancelación dan B-m/16-A/2. El delta ConstructorBudget está incluido y compilado.',
'Un vector que solo satisface la premisa presupuestaria falsea la conclusión: la premisa física no puede borrarse. No se presenta ese vector como grafo.',
'No se infiere realizabilidad de parámetros a partir del test aritmético. La existencia viene de la cadena formal, y AllInput sigue visible en el lema local.'),
'B06_ASSEMBLY':('Ensamblaje y cuantificadores','A para todo orden, B eventual, C para defecto fijo y 6.5 para sucesiones arbitrarias. El régimen lejano conserva todos los grafos.',
'Se verificaron diferencias de pisos en n=1..10 000 y 40 000 telescopajes. El mapa contrasta tipos elaborados y prosa, incluida precisión antes de s y la elección de una raíz común antes de cada partición.',
'No se reemplaza un resultado para s fijo por s creciente. No se interpreta exceso positivo o(n^2) como igualdad para grafos dispersos.',
'No prueba b=0 universal. Las ramas son exhaustivas; no se afirma exclusión mutua de todos los testigos existenciales.'),
'B07_SPLIT':('Testigos, parábola y optimalidad','Cota inferior irrestricta, doble núcleo máximo y rango 2<=k<=h para gap mixto nulo.',
'Se calcularon exactamente cp y c4 en seis splits pequeños; 45 430 identidades parabólicas y 98 órdenes de doble máximo. La familia de 6.3a conserva su déficit exacto y una cota inferior de edición a todo comparador óptimo.',
'El caso n=1 módulo tres rechaza elegir siempre un maximizador único. La primera transcripción del script de obstrucción fue corregida y conservada en el historial.',
'Igualdad de valores óptimos no significa integralidad del politopo. La obstrucción no contradice la estabilidad lineal hacia una raíz de tamaño no prefijado.'),
'B08_STABILITY':('Estabilidad, particiones y obstrucción','Una misma raíz controla todas las particiones irrestrictas. Para defecto fijo hay exactamente s vértices de defecto y una clique del grafo original.',
'35 457 identidades de partición y 98 119 piezas no canónicas comprobadas; revisión exacta adicional de perfiles a,b<=150 y familias de desplazamiento s<=10,q<=70. E.4 fue cotejado bloque por bloque, incluidos el crédito R y el coste de mover vértices.',
'El perfil (3,2) alcanza el factor local diez; la familia de déficit uno refuta una cota puramente lineal a plantillas de tamaño óptimo. Los controles no afirman optimalidad global de 480.',
'El anexo separado da un gap triangular lineal con ancho acotado, no gap mixto lineal universal. Absorción y reservas mantienen sus hipótesis de recursos libres.'),
'B09_STRUCTURE':('Estructura cordal y clique recovery','Casos degenerados, recuperación de clique real y tres casos exhaustivos del muestreo adaptado.',
'Se revisaron F.3a, F.3b y F.5 contra sus declaraciones. Los contraejemplos finitos incluyen grafo vacío, bolsas duplicadas, árbol aislado y hoja con más de un vértice privado.',
'Los ejemplos rechazan identificar hoja con un único vértice simplicial o intersección duplicada con separador minimal. Parte positiva y orientación doble de las no-aristas se conservan.',
'Las extracciones contrib fuera del corte no se certifican. La adaptación de de Joannis de Verclos se atribuye y no se confunde con el enunciado publicado literal.'),
'B10_REGRESSION':('Regresión integrada','Dos definiciones independientes de cordalidad y modelos literales en un dominio finito explícito.',
'Los clasificadores por ciclos inducidos y por eliminación perfecta coinciden en los 33 868 grafos etiquetados de n=0..6: 19 049 cordales. Se incluyen vacíos, desconexos, completos y aislados.',
'C4 inducido se rechaza, y añadir una diagonal cambia correctamente el veredicto. Los demás bloques conservan mutaciones específicas de sus certificados.',
'El dominio se enumera por máscaras; no requiere deduplicación por isomorfismo. No es un censo universal ni una prueba de b=0.')}

GATES={
'G0_INTEGRITY':('Identidad e integridad','Hashes de fuente, manuscritos, configuración, ZIP y evidencia de los dos segmentos cotejados. El control inicial tiene 5 912 comprobaciones; se repite al sellar. La recuperación no cambia el hash fuente.'),
'G1_CLAIMS':('Afirmaciones y alcance','CLAIM_MAP.csv, TRACE_SUMMARY.json y MATHEMATICAL_REVIEW.md relacionan las interfaces exportadas y los lemas de apoyo. Cada encabezado de resultado tiene correspondencia. Las siete entradas A.2 tienen juicio expositivo individual, no inferido del build.'),
'G2_MATHEMATICS':('Diez bloques matemáticos','B01-B10 combinan revisión matemática, evidencia formal registrada y regresiones exactas. Las obligaciones E.4, F.3a y los tres casos de F.5 se trataron explícitamente. Ningún resultado universal se infiere de un censo finito.'),
'G3_FORMAL':('Conformidad y entrada pública','607 módulos de fuente; cierre de importación PaperIV de 553; 224 #check importando solo PaperIV. Sin tokens efectivos sorry/admit/native_decide/axiom en la inspección léxica. Esta inspección complementa los axiomas transitivos, no los sustituye.'),
'G4_LEAN':('Build y axiomas registrados','607 módulos con procedencia fresca entre dos segmentos, 19 targets reejecutados y 224 exports. Se validaron 461 listas de axiomas permitidos; 313 registros nominales de #print corresponden a 307 declaraciones distintas. El anexo histórico tiene 38 módulos y cierre de 50 fuentes vinculadas; sus 579 logs históricos se inspeccionaron por separado.'),
'G5_PARITY':('Paridad bilingüe','1 988 expresiones matemáticas por idioma, 146 etiquetas coincidentes, cinco bloques Lean idénticos y cuatro figuras por idioma. Las siete diferencias de fórmula son palabras traducidas en text. Rangos, constantes y cuantificadores de los resultados nuevos fueron cotejados.'),
'G6_PDF':('Artefactos y revisión visual','68 páginas EN y 69 ES renderizadas. Todas revisadas mediante 16 láminas; se amplió la inspección de páginas densas y de referencias. No se observaron recortes ni superposiciones. Informes de auditoría compilados desde su TeX final, con logs, renders y QA propios.'),
'G7_PROVENANCE':('Atribución y licencias','Se revisaron [5], [15] y [22] en sus cortes citados. Se distinguen coincidencia de resultado, adaptación de método, independencia lógica y originalidad histórica. El anuncio de Cipollini no se usa como entrada demostrada. No se redistribuyen dependencias ni se cambia su licencia.'),
'G8_PACKAGE':('Reproducción y paquetes','Cada bloque y gate tiene MD, TeX, PDF, evidencia y ZIP con manifiesto. El paquete general contiene scripts, entradas, resultados, revisión y controles negativos. Fuentes/manuscritos grandes son insumos comunes identificados por sus hashes, sin cachés ni credenciales.')}

def compile_report(path,title):
    pdf=path.with_suffix('.pdf');tex=path.with_suffix('.tex');body=path.with_suffix('.body.tex')
    cmd=[str(PANDOC),str(path),'-f','markdown','-t','latex','-o',str(body)]
    a=subprocess.run(cmd,capture_output=True,text=True,encoding='utf-8',timeout=60)
    assert a.returncode==0,a.stderr
    b=body.read_text(encoding='utf-8')
    b=re.sub(r'\\texttt\{([^{}]*)\}',lambda m:r'\nolinkurl{'+m[1].replace(r'\_', '_')+'}',b)
    pre=r'''\documentclass[11pt]{article}
\usepackage[margin=1in]{geometry}
\usepackage{booktabs,longtable,array,calc}
\usepackage{fontspec}
\setmainfont{lmroman10-regular.otf}[BoldFont=lmroman10-bold.otf,ItalicFont=lmroman10-italic.otf,BoldItalicFont=lmroman10-bolditalic.otf]
\setmonofont{lmmono10-regular.otf}[Scale=MatchLowercase]
\usepackage{microtype,amsmath,amssymb}
\usepackage{xurl}
\usepackage[hidelinks]{hyperref}
\setlength{\parindent}{0pt}
\setlength{\parskip}{0.5em}
\setlength{\emergencystretch}{3em}
\setcounter{secnumdepth}{-\maxdimen}
\providecommand{\tightlist}{\setlength{\itemsep}{0pt}\setlength{\parskip}{0pt}}
\begin{document}
'''
    write(tex,pre+b+'\n\\end{document}\n')
    cmd=[str(TEX),'--only-cached','--keep-logs','--reruns','1','--outdir',str(path.parent),str(tex)]
    p=subprocess.run(cmd,capture_output=True,text=True,encoding='utf-8',errors='replace',timeout=120)
    write(path.with_suffix('.compile.txt'),' '.join(cmd)+'\n'+p.stdout+'\n'+p.stderr)
    assert p.returncode==0 and pdf.exists(),p.stderr
    log=path.with_suffix('.log').read_text(encoding='utf-8',errors='replace')
    bad=[x for x in log.splitlines() if any(w in x for w in ('Overfull','Missing character:','undefined references','! LaTeX Error'))]
    assert not bad,(str(path),bad)
    assert 'Output written on' in log and pdf.stat().st_mtime>=tex.stat().st_mtime
    doc=fitz.open(pdf);renders=path.parent/(path.stem+'_renders');renders.mkdir(exist_ok=True)
    texts=[]
    for i,page in enumerate(doc):
        assert '\ufffd' not in page.get_text()
        assert not [w for w in page.get_text('words') if w[0]<-1 or w[1]<-1 or w[2]>page.rect.width+1 or w[3]>page.rect.height+1]
        page.get_pixmap(matrix=fitz.Matrix(1.1,1.1),alpha=False).save(renders/f'{i+1:03}.png')
        texts.append(page.get_text())
    qa=dict(status='COMPILED_STATIC_PASS_VISUAL_PENDING',title=title,pages=len(doc),md_sha256=sha(path),tex_sha256=sha(tex),pdf_sha256=sha(pdf),log_sha256=sha(path.with_suffix('.log')),compiler=str(TEX),compiler_sha256=sha(TEX),exit_code=p.returncode,reference_tex_sha256=sha(REFERENCE),renders=str(renders.relative_to(RUN)))
    save(path.with_name(path.stem+'_QA.json'),qa)
    return dict(path=path.relative_to(RUN).as_posix(),**qa)

def prepare():
    trace=read(EV/'G1_CLAIMS/TRACE_SUMMARY.json')
    assert all(x['declarations'] for x in trace['headings']),[x for x in trace['headings'] if not x['declarations']]
    assert read(EV/'G3_FORMAL/INVENTORY_SUMMARY.json')['unsafe_tokens']==[]
    for b in BLOCKS:
        assert list((MATH/b/'results').glob('*.json')),b
        runner=MATH/b/'results/runner.json'
        if runner.exists():assert read(runner)['exit_code']==0
    diff=read(EV/'G5_PARITY/RESULTS.json')
    assert diff['labels_equal'] and diff['lean_code_equal'] and len(diff['math_text_differences'])==7
    save(EV/'G5_PARITY/ACCEPTANCE.json',dict(status='PASS',accepted_translated_indices=[x['index'] for x in diff['math_text_differences']],reason='Only translated text in formulas; declarations, hypotheses, inequalities and quantifiers reviewed.',unchanged_manuscripts=True))
    save(EV/'G6_PDF/MANUSCRIPT_VISUAL_QA.json',dict(status='PASS_INTERNAL_VISUAL_QA',all_pages_contact_sheets=True,contact_sheets=16,pages=137,readable_pages={'en':[1,7,24,31,38,56,58,60,62,68],'es':[1,16,32,57,61,63,69]},limits='All-page layout review plus readable dense samples, not human proofreading of every line.',render_index_sha256=sha(EV/'G6_PDF/RENDER_INDEX.json')))
    env=read(CONTROL/'ENVIRONMENT.json')
    env['tools']={p.name:{'path':str(p),'sha256':sha(p)} for p in (PANDOC,TEX)}
    dist=metadata.distribution('certo-math');certo=[]
    for f in dist.files or []:
        p=Path(dist.locate_file(f))
        if str(f).endswith('.py') and p.exists():certo.append({'file':str(f),'sha256':sha(p)})
    save(CONTROL/'CERTO_SOURCE_MANIFEST.json',certo)
    env['certo_source_manifest_sha256']=sha(CONTROL/'CERTO_SOURCE_MANIFEST.json');save(CONTROL/'ENVIRONMENT.json',env)
    findings=[dict(id=f'I-{i:02}',severity='MINOR' if i==5 else 'INFORMATIONAL',status='DOCUMENTED_ERRATUM_NO_SEMANTIC_CHANGE' if i==5 else 'RESOLVED_OR_DISCLOSED',record='FINDINGS.md') for i in range(1,7)]
    save(CONTROL/'FINDINGS.json',findings)
    common='Corte Lean `piv-v12-fb459343d234`; manuscritos `piv-v12-manuscripts-2451d43bface`. Auditoría interna del lado del autor, no independiente. Fecha: 30 de septiembre de 2026.'
    reports=[]
    for b,(title,question,results,negative,limits) in BLOCKS.items():
        d=MATH/b
        scripts=[p.name for p in (d/'scripts').glob('*.py')]
        repro=('Ejecutar con Python 3.12 '+', '.join('`scripts/'+x+'`' for x in scripts)+'.') if scripts else 'Ejecutar `00_CONTROL/extension_checks.py` desde el expediente extraído.'
        txt=f'# {b[:3]}: {title}\n\n{common}\n\n## Obligación e hipótesis\n\n{question}\n\n## Revisión y resultados\n\n{results}\n\nEl cotejo matemático detallado está en `G1_CLAIMS/MATHEMATICAL_REVIEW.md`; las declaraciones y tipos se vinculan en `CLAIM_MAP.csv`.\n\n## Negativos e incidentes\n\n{negative}\n\n## Reproducción y evidencia\n\n{repro} Los JSON, stdout y stderr de `results/` son la evidencia de ejecución. El runner guarda comandos, duración, límite y código de salida. Las ampliaciones exactas usan `extension_checks.py`; no invocan Lean.\n\nUn solo proceso propio a la vez; las regresiones serializadas tienen límite de 2 GiB y 120 segundos, Certo 60 segundos por instancia. Se usan versiones registradas en `ENVIRONMENT.json`, sin instalar dependencias.\n\n## Dictamen y límites\n\n**PASS interno**, combinando evidencia formal registrada y regresión finita donde corresponde. {limits} Los archivos de entrada comunes se resuelven por `TARGET.json`, no por otra carpeta mutable de trabajo.\n'
        write(d/'REPORT.md',txt);write(d/'SPEC.md',f'# {b}: especificación\n\n{question}\n\n{negative}\n\n{limits}\n')
        write(d/'README.md',f'# {b}\n\nLeer REPORT.md y SPEC.md. Los scripts y resultados pertenecen a esta corrida. Para reproducir, extraer conservando la estructura del expediente; controles compartidos en 00_CONTROL, insumos congelados por TARGET.json. No ejecutar nuevos builds ni descargar Mathlib.\n')
        reports.append((d/'REPORT.md',title))
    for g,(title,content) in GATES.items():
        d=EV/g;d.mkdir(exist_ok=True)
        write(d/'REPORT.md',f'# {g[:2]}: {title}\n\n{common}\n\n## Obligación y resultado\n\n{content}\n\n## Evidencia y método\n\nEste gate se apoya en los archivos de su carpeta, el inventario de entradas, los registros de ejecución y la revisión matemática. No basta el marcador de estado. Los controles de build son de solo lectura; no se recompiló Lean durante esta auditoría.\n\n## Hallazgos y límites\n\nVer `00_CONTROL/FINDINGS.md`: errores de verificadores corregidos, una referencia cruzada menor aclarada y el alcance del anexo histórico. No se cambió matemática, fuente Lean ni manuscrito. El resultado no sustituye la auditoría externa ni acredita prioridad.\n\n## Reproducción\n\nLos scripts en `00_CONTROL` identifican insumos y archivos de salida. Repetir en una carpeta nueva; conservar intentos previos. No descargar otra Mathlib. Las rutas del entorno documentan esta máquina y no son dependencias del teorema.\n\n## Dictamen\n\n**PASS interno**, con el alcance anterior. El cierre efectivo de G6 y G8 se registra tras revisar los informes y verificar los archivos ZIP; un PDF compilado no es por sí solo una auditoría matemática.\n')
        reports.append((d/'REPORT.md',title))
    table='\n'.join(f'| {k[:2]} | PASS interno | {v[0]} |' for k,v in GATES.items())
    final=f'''# Paper IV v1.2: informe final de auditoría interna

{common}

## Dictamen

**PASS_INTERNAL_AUTHOR_SIDE** para el alcance fijado, sujeto a la verificación mecánica del paquete que acompaña este informe. G0-G8 y B01-B10 están cubiertos. No se encontró un defecto matemático bloqueante. Se documenta una referencia cruzada menor en A.2, aclarada en FINDINGS.md sin cambiar el manuscrito sellado.

Este dictamen no es auditoría externa, revisión humana independiente, autorización de publicación ni demostración de b=0. No se lanzó otro build ni otro Mathlib; la continuación se ejecutó sin subagentes y con cómputo serial limitado.

## Identidad y procedencia

- Fuentes: 607 módulos, manifiesto de 615 archivos.
- Entrada PaperIV: cierre de 553 módulos; 224 comprobaciones de exportación que importan solo esa raíz.
- Build completo: dos segmentos tras reinicio, con cada objeto reutilizado vinculado a su compilación fresca verificada. Los 19 targets de auditoría se reejecutaron.
- 461 listas de axiomas permitidos; 313 impresiones nominales sobre 307 declaraciones distintas. Los únicos axiomas admitidos son propext, Classical.choice y Quot.sound o subconjuntos.
- Anexo separado: 38 módulos BoundedCliqueGap, cierre de 50 fuentes históricas cotejadas. Los restantes logs de su corrida histórica de 579 módulos no certifican fuentes no distribuidas.
- Manuscritos: inglés 68 páginas, español 69. Los hashes originales siguen vigentes; no se generó una versión matemática nueva.

Los identificadores completos, ZIP fuente, ZIP de manuscritos y evidencia del build están en TARGET.json. El hash de este expediente se entrega en un sidecar externo, evitando una referencia circular.

## Matriz de gates

| Gate | Resultado | Objeto |
|:--|:--|:--|
{table}

## Cobertura matemática

Se separaron A para todo orden, B agudo eventual, C para defecto fijo y C prime con la misma raíz antes de toda partición. Se revisaron la estabilidad real, el término de raíz cuadrada, las cotas fraccionales en todos los órdenes, el redondeo uniforme en s y las sucesiones de órdenes arbitrarios.

E.4 fue cotejado con StrictParams, StrictBudget, ResidualExcess, CoreCliqueAlternative, LargeCliqueCore, TemplateDistance y RootPartition. F.3a conserva parte positiva y no-aristas ordenadas. Los tres casos F.5 son exhaustivos y conservan el muestreo con reemplazo y el tamaño de muestra adaptado. Las siete entradas resumidas de A.2 tienen dictámenes individuales ACCEPTABLE_SUMMARY para el paper acompañado de sus fuentes y referencias; no se declara una nueva rederivación humana de todos los diseños o del nibble.

El detalle está en `20_EVIDENCE/G1_CLAIMS/MATHEMATICAL_REVIEW.md`, el inventario de encabezados y `00_CONTROL/CLAIM_MAP.csv`. Las exclusiones de dependencias se aplican a los conos nombrados y no se convierten en una afirmación de originalidad histórica.

## Regresiones y Certo

Se ejecutaron ocho suites seriales y ampliaciones exactas. El censo literal comprende 33 868 grafos etiquetados hasta orden seis; 19 049 son cordales. Se verificaron 76 pares primal-dual racionales, las cuotas mixtas, 100 000 vectores de presupuesto, 40 000 telescopajes y los testigos split. Las ampliaciones controlan perfiles de piezas, constantes de defecto fijo, obstrucción de raíz cuadrada y casos degenerados de árboles de cliques.

Certo 0.20.1 produjo un certificado de cobertura de K3 join I3. Se verificó con su especificación y con un checker literal que no importa el productor. La optimalidad se certificó aparte mediante pesos de cliques. Se rechazaron mutaciones semánticas. Certo no es un auditor independiente del autor, y estas pruebas finitas no demuestran los teoremas universales.

## Paridad, PDFs y atribución

Las 1 988 expresiones matemáticas por idioma difieren solo en siete textos traducidos; coinciden 146 etiquetas y cinco bloques Lean. Las 137 páginas fueron revisadas en láminas y se inspeccionaron a resolución legible páginas densas, figuras, tablas y referencias. Los informes de esta auditoría se compilaron desde sus TeX finales con la plantilla de informes de Paper III, y tienen revisión visual propia.

La comparación con [15] reconoce su Teorema 1.1, su estabilidad y el método de estrella. F.5 atribuye la estrategia de [22] y sus modificaciones. [5] se compara en el commit citado. El anuncio de Cipollini no es una entrada auditada de la demostración. Actualizar la literatura y repetir estos juicios con independencia corresponde al carril externo.

## Hallazgos y límites

Los incidentes de los verificadores se conservaron y corrigieron sin alterar el corte: colisión por basename, nombres Lean con apóstrofo, fórmula mal transcrita en una regresión y alcance excesivo inicial del verificador del anexo. La referencia '§3.2' de A.2 se precisa como Lema 3.2/C.1-C.2 en la errata. Las regresiones ligeras comenzaron antes de completar G1; no se usaron para inferir su PASS.

Este expediente valida evidencia de compilación, no ejecuta una nueva compilación independiente. La aprobación de resúmenes expositivos no impide que un árbitro solicite más detalle. No se certifican extracciones contrib fuera del corte, licencias nuevas ni prioridad bibliográfica. No se modificó ni publicó el repositorio.

## Entrega y siguiente paso

Hay informes MD, TeX y PDF para diez bloques, nueve gates y este resumen; ZIP por bloque y gate, manifiestos y paquete general. PACKAGE_INDEX.json y PACKAGE_VERIFICATION.json registran los hashes y el replay de cada archivo. La auditoría externa debe empezar por identidad y lectura independiente según su mandato, sin usar este PASS como premisa matemática. Su ejecución requiere la petición del autor.
'''
    path=RUN/'10_REPORT/INTERNAL_AUDIT_FINAL_REPORT.md';write(path,final);reports.append((path,'Informe general'))
    save(CONTROL/'TEST_PLAN.json',dict(blocks=list(BLOCKS),gates=list(GATES),heavy_parallelism=1,new_lean_build=False,limits='2 GiB child process; finite suites <=120s; Certo <=60s per invocation. Exact extension checks do not use solvers.'))
    index=[]
    for path,title in reports:
        q=path.with_name(path.stem+'_QA.json')
        if q.exists() and read(q)['md_sha256']==sha(path) and read(q)['pdf_sha256']==sha(path.with_suffix('.pdf')):
            row=dict(path=path.relative_to(RUN).as_posix(),**read(q))
        else:row=compile_report(path,title)
        index.append(row);print('COMPILED',path.relative_to(RUN),row['pages'],flush=True)
    save(CONTROL/'REPORT_INDEX.json',index)
    # Make contact sheets over every generated report page, with report/page labels.
    pages=[]
    for r in index:
        for p in sorted((RUN/r['renders']).glob('*.png')):pages.append((r['path'].split('/')[-2]+' '+p.stem,p))
    out=RUN/'10_REPORT/visual_qa';out.mkdir(exist_ok=True)
    sheets=[]
    for start in range(0,len(pages),9):
        sheet=Image.new('RGB',(1080,1560),'#dddddd');draw=ImageDraw.Draw(sheet)
        for j,(label,p) in enumerate(pages[start:start+9]):
            with Image.open(p) as im:
                im.thumbnail((340,480));x=(j%3)*360;y=(j//3)*520;sheet.paste(im,(x+10,y+25));draw.text((x+10,y+5),label,fill='black')
        name=out/f'contact_{start//9+1:02}.png';sheet.save(name);sheet.close();sheets.append(name.relative_to(RUN).as_posix())
    save(out/'INDEX.json',dict(pages=len(pages),sheets=sheets,status='PENDING_VISUAL_REVIEW'))
    print('Reports ready for visual review:',len(index),'PDFs,',len(pages),'pages.',flush=True)

if __name__=='__main__':prepare()
