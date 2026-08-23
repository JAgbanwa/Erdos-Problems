[CmdletBinding()]
param(
    [Parameter(Mandatory = $false)]
    [string]$WorkRoot = 'C:\p3build'
)

$ErrorActionPreference = 'Stop'
$ProgressPreference = 'SilentlyContinue'

$KitRoot = $PSScriptRoot
$SourceProject = Join-Path $KitRoot 'PROJECT'
$WorkRootFull = [IO.Path]::GetFullPath($WorkRoot)
$ProjectRoot = Join-Path $WorkRootFull 'P3'
$ResultsRoot = Join-Path $WorkRootFull 'RESULTS'
$LogsRoot = Join-Path $ResultsRoot 'logs'
$EvidenceRoot = Join-Path $ResultsRoot 'evidence'
$StartedUtc = [DateTime]::UtcNow
$FailureMessage = $null

function Write-Utf8Lf {
    param([string]$Path, [string[]]$Lines)
    $content = ($Lines -join "`n") + "`n"
    [IO.File]::WriteAllText($Path, $content, [Text.UTF8Encoding]::new($false))
}

function Get-RelativeUnixPath {
    param([string]$Root, [string]$Path)
    return $Path.Substring($Root.Length + 1).Replace('\', '/')
}

function Write-HashManifest {
    param([string]$Root, [string]$Destination, [string[]]$ExcludePaths = @())
    $excluded = @{}
    foreach ($item in $ExcludePaths) {
        $excluded[[IO.Path]::GetFullPath($item)] = $true
    }
    $lines = Get-ChildItem -LiteralPath $Root -Recurse -File -Force |
        Where-Object { -not $excluded.ContainsKey([IO.Path]::GetFullPath($_.FullName)) } |
        Sort-Object FullName |
        ForEach-Object {
            $hash = (Get-FileHash -LiteralPath $_.FullName -Algorithm SHA256).Hash.ToLowerInvariant()
            $relative = Get-RelativeUnixPath -Root $Root -Path $_.FullName
            "$hash  $relative"
        }
    Write-Utf8Lf -Path $Destination -Lines $lines
}

function Test-HashManifest {
    param([string]$Root, [string]$Manifest)
    $failures = [Collections.Generic.List[string]]::new()
    foreach ($line in [IO.File]::ReadAllLines($Manifest)) {
        if ($line -notmatch '^([0-9a-f]{64})  (.+)$') {
            $failures.Add("Malformed manifest line: $line")
            continue
        }
        $expected = $Matches[1]
        $path = Join-Path $Root $Matches[2].Replace('/', '\')
        if (-not (Test-Path -LiteralPath $path -PathType Leaf)) {
            $failures.Add("Missing: $($Matches[2])")
            continue
        }
        $actual = (Get-FileHash -LiteralPath $path -Algorithm SHA256).Hash.ToLowerInvariant()
        if ($actual -ne $expected) {
            $failures.Add("Hash mismatch: $($Matches[2])")
        }
    }
    if ($failures.Count -gt 0) {
        throw "Source-manifest verification failed:`n$($failures -join "`n")"
    }
}

function Invoke-LakeLogged {
    param([string]$Name, [string[]]$Arguments)
    $log = Join-Path $LogsRoot "$Name.log"
    $exitRecord = Join-Path $LogsRoot "$Name.exit.txt"
    $start = [DateTime]::UtcNow
    @(
        "start_utc=$($start.ToString('o'))"
        "cwd=$ProjectRoot"
        "command=lake $($Arguments -join ' ')"
    ) | Set-Content -LiteralPath $log -Encoding utf8
    Push-Location $ProjectRoot
    try {
        & lake @Arguments 2>&1 | Tee-Object -FilePath $log -Append
        $code = $LASTEXITCODE
    }
    finally {
        Pop-Location
    }
    $end = [DateTime]::UtcNow
    Write-Utf8Lf -Path $exitRecord -Lines @(
        "exit_code=$code"
        "start_utc=$($start.ToString('o'))"
        "end_utc=$($end.ToString('o'))"
        "duration_seconds=$([math]::Round(($end - $start).TotalSeconds, 3))"
    )
    if ($code -ne 0) {
        throw "Command failed ($code): lake $($Arguments -join ' ')"
    }
}

function Get-ModuleMap {
    param([string]$Root)
    $map = @{}
    foreach ($file in Get-ChildItem -LiteralPath $Root -Recurse -File -Filter '*.lean') {
        $relative = Get-RelativeUnixPath -Root $Root -Path $file.FullName
        $module = $relative.Substring(0, $relative.Length - 5).Replace('/', '.')
        $map[$module] = $file.FullName
    }
    return $map
}

function Get-ImportClosure {
    param([hashtable]$ModuleMap, [string[]]$Roots)
    $seen = @{}
    $stack = [Collections.Generic.Stack[string]]::new()
    foreach ($root in $Roots) { $stack.Push($root) }
    while ($stack.Count -gt 0) {
        $module = $stack.Pop()
        if ($seen.ContainsKey($module)) { continue }
        $seen[$module] = $true
        if (-not $ModuleMap.ContainsKey($module)) { continue }
        foreach ($line in [IO.File]::ReadAllLines($ModuleMap[$module])) {
            if ($line -match '^\s*import\s+(.+?)\s*$') {
                foreach ($imported in ($Matches[1] -split '\s+')) {
                    if ($imported) { $stack.Push($imported) }
                }
            }
        }
    }
    return $seen
}

function Write-EnvironmentEvidence {
    $os = Get-CimInstance Win32_OperatingSystem
    $cpu = Get-CimInstance Win32_Processor | Select-Object -First 1
    $computer = Get-CimInstance Win32_ComputerSystem
    $envRecord = [ordered]@{
        captured_utc = [DateTime]::UtcNow.ToString('o')
        computer_name = $env:COMPUTERNAME
        os = $os.Caption
        os_version = $os.Version
        cpu = $cpu.Name
        logical_processors = $cpu.NumberOfLogicalProcessors
        memory_bytes = [int64]$computer.TotalPhysicalMemory
        powershell = $PSVersionTable.PSVersion.ToString()
        git = (& git --version 2>&1 | Out-String).Trim()
        lake = (& lake --version 2>&1 | Out-String).Trim()
        lean = (& lean --version 2>&1 | Out-String).Trim()
    }
    $envRecord | ConvertTo-Json -Depth 4 |
        Set-Content -LiteralPath (Join-Path $EvidenceRoot 'ENVIRONMENT.json') -Encoding utf8
}

if (-not (Test-Path -LiteralPath $SourceProject -PathType Container)) {
    throw "PROJECT directory missing from kit: $SourceProject"
}
if (-not (Test-Path -LiteralPath (Join-Path $KitRoot 'PROJECT_MANIFEST.sha256') -PathType Leaf)) {
    throw 'PROJECT_MANIFEST.sha256 is missing from the kit.'
}
if (Test-Path -LiteralPath $WorkRootFull) {
    throw "WorkRoot already exists; choose a new empty path: $WorkRootFull"
}

Test-HashManifest -Root $KitRoot -Manifest (Join-Path $KitRoot 'PROJECT_MANIFEST.sha256')
New-Item -ItemType Directory -Path $ProjectRoot, $LogsRoot, $EvidenceRoot | Out-Null
Copy-Item -Path (Join-Path $SourceProject '*') -Destination $ProjectRoot -Recurse -Force

try {
    $unexpectedLake = Get-ChildItem -LiteralPath $ProjectRoot -Recurse -Directory -Force |
        Where-Object { $_.Name -eq '.lake' }
    $compiledExtensions = @('.olean', '.ilean', '.o', '.c', '.bc', '.dll', '.so', '.dylib')
    $compiled = Get-ChildItem -LiteralPath $ProjectRoot -Recurse -File -Force |
        Where-Object { $compiledExtensions -contains $_.Extension.ToLowerInvariant() }
    if ($unexpectedLake -or $compiled) {
        throw 'Delivered PROJECT is not clean: .lake or compiled project artifacts found.'
    }

    Write-EnvironmentEvidence

    $configNames = @('lakefile.toml', 'lake-manifest.json', 'lean-toolchain')
    $configBefore = foreach ($name in $configNames) {
        $path = Join-Path $ProjectRoot $name
        [ordered]@{ file = $name; sha256 = (Get-FileHash $path -Algorithm SHA256).Hash.ToLowerInvariant() }
    }
    $configBefore | ConvertTo-Json | Set-Content (Join-Path $EvidenceRoot 'CONFIG_HASHES_BEFORE.json') -Encoding utf8

    $moduleMap = Get-ModuleMap -Root $ProjectRoot
    $rootClosure = Get-ImportClosure -ModuleMap $moduleMap -Roots @('PaperIII')
    $publicClosure = Get-ImportClosure -ModuleMap $moduleMap -Roots @('PaperIII.PublicAPI')
    $canonicalRoots = @(
        'PaperIII',
        'BKLO.MainDenseUnconditional',
        'Nibble.AX1Closed',
        'PaperIII.CanonicalTrianglePacking',
        'PaperIII.Obstructions',
        'PaperIII.PaperImprovementsGate',
        'PaperIII.PublicAPI',
        'PaperIII.Theorem_1_1_Final'
    )
    $canonicalClosure = Get-ImportClosure -ModuleMap $moduleMap -Roots $canonicalRoots
    $closureAssertions = [ordered]@{
        paperIII_reaches_final = $rootClosure.ContainsKey('PaperIII.Theorem_1_1_Final')
        paperIII_reaches_public_api = $rootClosure.ContainsKey('PaperIII.PublicAPI')
        public_api_reaches_final = $publicClosure.ContainsKey('PaperIII.Theorem_1_1_Final')
        canonical_reaches_archived_wlog = $canonicalClosure.ContainsKey('Ax2.PartA.Wlog')
        canonical_reaches_archived_axioms = $canonicalClosure.ContainsKey('Ax2.PartB.Axioms')
        paperIII_closure_modules = $rootClosure.Count
        canonical_closure_modules = $canonicalClosure.Count
        project_lean_files = $moduleMap.Count
    }
    $closureAssertions | ConvertTo-Json |
        Set-Content (Join-Path $EvidenceRoot 'IMPORT_CLOSURE.json') -Encoding utf8
    if (-not $closureAssertions.paperIII_reaches_final -or
        -not $closureAssertions.paperIII_reaches_public_api -or
        -not $closureAssertions.public_api_reaches_final -or
        $closureAssertions.canonical_reaches_archived_wlog -or
        $closureAssertions.canonical_reaches_archived_axioms) {
        throw 'Import-closure release gate failed.'
    }

    Get-ChildItem -LiteralPath $ProjectRoot -Recurse -File -Filter '*.lean' |
        Select-String -Pattern '\bsorry\b|\badmit\b|\bnative_decide\b|^\s*axiom\s+' |
        ForEach-Object { "$($_.Path):$($_.LineNumber):$($_.Line)" } |
        Set-Content (Join-Path $EvidenceRoot 'RAW_ESCAPE_HATCH_SCAN.txt') -Encoding utf8

    Write-Utf8Lf -Path (Join-Path $EvidenceRoot 'PRE_CACHE_CLEAN_STATE.txt') -Lines @(
        'project_dot_lake_present=false'
        'compiled_project_artifacts=0'
        "lean_source_files=$($moduleMap.Count)"
    )

    Invoke-LakeLogged -Name '01_cache_get' -Arguments @('exe', 'cache', 'get')
    if (Test-Path -LiteralPath (Join-Path $ProjectRoot '.lake\build')) {
        throw 'Project .lake/build exists immediately after cache get.'
    }

    $manifest = Get-Content -Raw (Join-Path $ProjectRoot 'lake-manifest.json') | ConvertFrom-Json
    $dependencyRecords = foreach ($package in $manifest.packages) {
        $packagePath = Join-Path $ProjectRoot ".lake\packages\$($package.name)"
        if (-not (Test-Path -LiteralPath $packagePath -PathType Container)) {
            throw "Dependency checkout missing: $($package.name)"
        }
        $actualRevision = (& git -C $packagePath rev-parse HEAD 2>&1 | Out-String).Trim()
        $status = (& git -C $packagePath status --porcelain 2>&1 | Out-String).Trim()
        if ($actualRevision -ne $package.rev -or $status) {
            throw "Dependency mismatch or dirty tree: $($package.name)"
        }
        [ordered]@{
            name = $package.name
            expected_revision = $package.rev
            actual_revision = $actualRevision
            clean = -not [bool]$status
        }
    }
    $dependencyRecords | ConvertTo-Json -Depth 4 |
        Set-Content (Join-Path $EvidenceRoot 'DEPENDENCIES.json') -Encoding utf8
    if (@($dependencyRecords).Count -ne 9) {
        throw "Expected 9 dependencies, found $(@($dependencyRecords).Count)."
    }

    Invoke-LakeLogged -Name '02_build_public_root_clean' -Arguments @('build', 'PaperIII')

    $finalObject = Get-ChildItem (Join-Path $ProjectRoot '.lake\build') -Recurse -File -Filter 'Theorem_1_1_Final.olean'
    $publicObject = Get-ChildItem (Join-Path $ProjectRoot '.lake\build') -Recurse -File -Filter 'PublicAPI.olean'
    if (@($finalObject).Count -lt 1 -or @($publicObject).Count -lt 1) {
        throw 'Public-root build did not produce the final theorem and PublicAPI object files.'
    }
    Write-Utf8Lf -Path (Join-Path $EvidenceRoot 'PUBLIC_ROOT_OBJECTS.txt') -Lines @(
        "Theorem_1_1_Final_objects=$(@($finalObject).Count)"
        "PublicAPI_objects=$(@($publicObject).Count)"
        ($finalObject.FullName | ForEach-Object { "final=$_" })
        ($publicObject.FullName | ForEach-Object { "public_api=$_" })
    )

    Invoke-LakeLogged -Name '03_build_query_roots_incremental' -Arguments @(
        'build',
        'BKLO.MainDenseUnconditional',
        'Nibble.AX1Closed',
        'PaperIII.CanonicalTrianglePacking',
        'PaperIII.Obstructions',
        'PaperIII.PaperImprovementsGate',
        'PaperIII.PublicAPI',
        'PaperIII.Theorem_1_1_Final'
    )

    $queryFiles = @(
        'FreezeAxioms.lean',
        'FreezeAxiomsAuditClosure.lean',
        'FreezeAxiomsAX1.lean',
        'FreezeAxiomsAX1Closure.lean',
        'FreezeAxiomsAX2.lean',
        'FreezeAxiomsByproducts.lean',
        'FreezeAxiomsCanonical.lean',
        'FreezeAxiomsObstructions.lean'
    )
    $queryIndex = 0
    foreach ($query in $queryFiles) {
        $queryIndex++
        $stem = [IO.Path]::GetFileNameWithoutExtension($query)
        Invoke-LakeLogged -Name ("axioms_{0:D2}_{1}" -f $queryIndex, $stem) -Arguments @('env', 'lean', $query)
    }

    $axiomLogs = Get-ChildItem $LogsRoot -File -Filter 'axioms_*.log'
    $axiomText = ($axiomLogs | Get-Content -Raw) -join "`n"
    if ($axiomText -match 'sorryAx') {
        throw 'Axiom output contains sorryAx.'
    }
    $axiomLines = [regex]::Matches($axiomText, '(?m)^.*depends on axioms:\s*\[([^\]]*)\].*$')
    if ($axiomLines.Count -ne 42) {
        throw "Expected 42 axiom surfaces, found $($axiomLines.Count)."
    }
    $allowed = @{
        'propext' = $true
        'Classical.choice' = $true
        'Quot.sound' = $true
    }
    $unexpectedAxioms = [Collections.Generic.List[string]]::new()
    foreach ($match in $axiomLines) {
        foreach ($axiom in ($match.Groups[1].Value -split ',')) {
            $name = $axiom.Trim()
            if ($name -and -not $allowed.ContainsKey($name)) {
                $unexpectedAxioms.Add($name)
            }
        }
    }
    if ($unexpectedAxioms.Count -gt 0) {
        throw "Unexpected axioms: $($unexpectedAxioms -join ', ')"
    }
    if ($axiomText -notmatch 'PaperIII\.Theorem_1_1 depends on axioms:') {
        throw 'Headline theorem axiom output is missing.'
    }
    Write-Utf8Lf -Path (Join-Path $EvidenceRoot 'AXIOM_GATE_SUMMARY.txt') -Lines @(
        'result=PASS_FOUNDATIONAL_ONLY'
        'query_files=8'
        'surfaces=42'
        'sorryAx=0'
        'allowed_axioms=propext,Classical.choice,Quot.sound'
        'headline_surface=PaperIII.Theorem_1_1'
    )

    $configAfter = foreach ($name in $configNames) {
        $path = Join-Path $ProjectRoot $name
        [ordered]@{ file = $name; sha256 = (Get-FileHash $path -Algorithm SHA256).Hash.ToLowerInvariant() }
    }
    $configAfter | ConvertTo-Json | Set-Content (Join-Path $EvidenceRoot 'CONFIG_HASHES_AFTER.json') -Encoding utf8
    for ($i = 0; $i -lt $configBefore.Count; $i++) {
        if ($configBefore[$i].sha256 -ne $configAfter[$i].sha256) {
            throw "Configuration changed during build: $($configBefore[$i].file)"
        }
    }
}
catch {
    $FailureMessage = $_.Exception.Message
}
finally {
    $EndedUtc = [DateTime]::UtcNow
    $summary = [ordered]@{
        paper = 'Paper III'
        version = '1.4-candidate'
        result = $(if ($FailureMessage) { 'FAIL' } else { 'PASS' })
        failure = $FailureMessage
        machine = $env:COMPUTERNAME
        started_utc = $StartedUtc.ToString('o')
        ended_utc = $EndedUtc.ToString('o')
        duration_seconds = [math]::Round(($EndedUtc - $StartedUtc).TotalSeconds, 3)
        clean_public_root_build = -not [bool]$FailureMessage
        expected_axiom_query_files = 8
        expected_axiom_surfaces = 42
    }
    $summary | ConvertTo-Json -Depth 4 |
        Set-Content -LiteralPath (Join-Path $ResultsRoot 'RUN_SUMMARY.json') -Encoding utf8
    $resultManifest = Join-Path $ResultsRoot 'RESULTS_MANIFEST.sha256'
    Write-HashManifest -Root $ResultsRoot -Destination $resultManifest -ExcludePaths @($resultManifest)
    $stamp = [DateTime]::UtcNow.ToString('yyyyMMdd_HHmmss')
    $safeMachine = ($env:COMPUTERNAME -replace '[^A-Za-z0-9_-]', '_')
    $zip = Join-Path $WorkRootFull "PAPER_III_v1.4_CLEAN_BUILD_RESULTS_${safeMachine}_${stamp}.zip"
    Compress-Archive -LiteralPath $ResultsRoot -DestinationPath $zip -CompressionLevel Optimal
    $zipHash = (Get-FileHash -LiteralPath $zip -Algorithm SHA256).Hash.ToLowerInvariant()
    Write-Utf8Lf -Path "$zip.sha256" -Lines @("$zipHash  $([IO.Path]::GetFileName($zip))")
    Write-Output "Result package: $zip"
    Write-Output "Result hash: $zipHash"
}

if ($FailureMessage) {
    Write-Error $FailureMessage
    exit 1
}

Write-Output 'PAPER III v1.4 CLEAN BUILD: PASS'
exit 0
