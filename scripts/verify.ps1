param([switch]$SupportingOnly)

# resolve paths once so the checks work from another shell directory.
$ErrorActionPreference = 'Stop'
$projectRoot = Split-Path -Parent $PSScriptRoot

# reject any theorem dependency beyond lean's ordinary foundational axioms.
function Assert-OrdinaryAxioms([string]$LogPath, [string[]]$ExpectedDeclarations) {
    $logText = Get-Content -LiteralPath $LogPath -Raw
    if ($logText -match 'sorryAx') { throw 'an audited theorem depends on an admitted proof' }
    $reportedDeclarations = @([regex]::Matches($logText,
        "'([^']+)' (?:depends on axioms:|does not depend on any axioms)") |
        ForEach-Object { $_.Groups[1].Value })
    if ($ExpectedDeclarations.Count -eq 0 -or $reportedDeclarations.Count -ne $ExpectedDeclarations.Count) {
        throw 'the compiler log does not contain every required axiom audit'
    }
    foreach ($declaration in $ExpectedDeclarations) {
        if ($declaration -cnotin $reportedDeclarations) { throw "missing axiom audit: $declaration" }
    }
    $matches = [regex]::Matches($logText, 'depends on axioms:\s*\[([^\]]*)\]')
    foreach ($match in $matches) {
        foreach ($name in ($match.Groups[1].Value -split ',')) {
            if ($name.Trim() -cnotin @('propext', 'Classical.choice', 'Quot.sound')) {
                throw "unexpected axiom dependency: $($name.Trim())"
            }
        }
    }
}

Push-Location -LiteralPath $projectRoot
try {
    New-Item -ItemType Directory -Path 'audit' -Force | Out-Null
    & lake build 2>&1 | Tee-Object -FilePath 'audit/build.log'
    if ($LASTEXITCODE -ne 0) { throw 'the supporting library did not build' }

    # scan the complete authored library rather than the unbuilt reference checkout.
    $sources = @((Get-Item -LiteralPath 'KumarNivat.lean')) +
        @(Get-ChildItem -LiteralPath 'KumarNivat' -File -Recurse -Filter '*.lean')
    $blocked = $sources | Select-String -Pattern '\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b'
    if ($blocked) { throw 'a prohibited proof admission or trust extension occurs in the library' }

    # inspect elaborated axiom dependencies, not just source keywords.
    & lake env lean 'scripts/Audit.lean' 2>&1 | Tee-Object -FilePath 'audit/axioms.log'
    if ($LASTEXITCODE -ne 0) { throw 'the supporting theorem audit failed' }
    $expectedAuditNames = @([regex]::Matches((Get-Content -LiteralPath 'scripts/Audit.lean' -Raw),
        '(?m)^#print axioms (\S+)') | ForEach-Object { $_.Groups[1].Value })
    if (@($expectedAuditNames | Select-Object -Unique).Count -ne $expectedAuditNames.Count) {
        throw 'the supporting audit contains a duplicate declaration'
    }
    Assert-OrdinaryAxioms 'audit/axioms.log' $expectedAuditNames

    if ($SupportingOnly) {
        Write-Output 'supporting checks passed; the full target check was skipped'
        exit 0
    }

    # a successful helper build cannot satisfy the full requested endpoint.
    & lake env lean 'scripts/FullTarget.lean' 2>&1 | Tee-Object -FilePath 'audit/full-target.log'
    if ($LASTEXITCODE -ne 0) {
        Write-Output 'the full requested conjecture failed its acceptance check'
        exit 1
    }
    Assert-OrdinaryAxioms 'audit/full-target.log' @('KumarNivat.nivat')
    Write-Output 'the full target acceptance check passed'
}
finally {
    Pop-Location
}
