#!/usr/bin/env python3
"""Read-only product-success audit for the Lean LCA exact-category challenge."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


PROJECT_REQUIRED = [
    "LeanLCAExactChallenge/ExactCategory/Basic.lean",
    "LeanLCAExactChallenge/ExactCategory/Conflation.lean",
    "LeanLCAExactChallenge/LCA/Basic.lean",
    "LeanLCAExactChallenge/LCA/StrictExact.lean",
    "LeanLCAExactChallenge/LCA/ExactCategory.lean",
    "LeanLCAExactChallenge/Ext/Yoneda.lean",
    "LeanLCAExactChallenge/Derived/Bounded.lean",
    "audit/RequiredDeclarations.lean",
    "audit/ProductSuccessDeclarations.lean",
    "audit/external_audit.py",
    "docs/research/sources.md",
    "docs/research/reference_route_log.md",
    "docs/research/mathlib_gap_analysis.md",
]

ROOT_REQUIRED = [
    "README_FOR_REVIEW.md",
]

REQUIRED_COMMANDS = [
    "lake build",
    "scripts/audit_no_generated_files.sh",
    "scripts/audit_no_forbidden_lean_tokens.sh LeanLCAExactChallenge audit",
    "scripts/build_lean_audit_dependencies.sh",
    "lake env lean audit/RequiredDeclarations.lean",
    "lake env lean audit/ProductSuccessDeclarations.lean",
    "lake env lean audit/OriginalFourTaskCompletionDeclarations.lean",
    "PYTHONDONTWRITEBYTECODE=1 python3 audit/external_audit.py --root .",
    "git diff --check",
]

POSITIVE_COMPLETION_SYMBOLS = [
    "OriginalFourTaskProductSuccess",
    "originalFourTaskProductSuccess",
    "originalFourTaskProductSuccess_quillenExactCategory",
    "originalFourTaskProductSuccess_metrizableLCAExactCategory",
    "originalFourTaskProductSuccess_yonedaExt",
    "originalFourTaskProductSuccess_boundedDerivedInfinityCategory",
]

FINAL_FALSE_COMPLETION_MARKERS = [
    "originalFourTaskContractCompletion_productSuccessClaimed",
    "originalFourTaskContractCompletion.productSuccessClaimed = false",
    "productSuccessClaimed := false",
]

ALLOWED_NONTERMINAL_OUTCOMES = {
    "nonterminal_recovery_baseline",
    "nonterminal_checkpoint_pushed",
    "mathematical_frontier_nonterminal",
    "source_patch_needed_handoff",
    "failed",
    "nonterminal",
}

ALLOWED_VERIFICATION_STATUSES = {"passed", "failed_expected"}
UNRESOLVED_VERIFICATION_STATUSES = {
    "pending",
    "queued",
    "running",
    "not_run",
    "todo",
    "unknown",
}

FORBIDDEN_LEAN_RE = re.compile(r"\b(sorry|admit|axiom|unsafe)\b")
HEX64_RE = re.compile(r"\b[0-9a-fA-F]{64}\b")
JAPANESE_RE = re.compile(r"[\u3040-\u30ff\u3400-\u9fff]")
ENGLISH_WORD_RE = re.compile(r"\b[A-Za-z][A-Za-z0-9'_-]*\b")
GENERATED_ARTIFACT_NAMES = {"manifest.json"}
GENERATED_ARTIFACT_PREFIXES = (
    ".lake/",
    "run/",
    "terminal_outcome/",
    "packets/",
    "__pycache__/",
)
GENERATED_ARTIFACT_SUFFIXES = (
    ".pyc",
    ".log",
    ".exit",
    ".err",
    ".status",
    ".tsv",
    ".olean",
    ".ilean",
    ".c",
    ".o",
)
PRODUCT_PLACEHOLDER_RE = re.compile(
    r"StrictExactQuillenAxioms|SourcePatch|ConstructionAssumption|ProductAssumption|"
    r"\bsource[- ]patch\b|\bblocker\b|\bfrontier\b|\bgap\b",
    flags=re.IGNORECASE,
)

DERIVED_STABLE_MARKER_RE = re.compile(
    r"StableBoundedDerivedInfinityCategory|stableInfinity|finiteLimits|finiteColimits|"
    r"suspensionEquivalence|loopSuspensionEquivalence|pushoutPullbackSquare",
    flags=re.IGNORECASE,
)

STABLE_CERTIFICATE_PLACEHOLDER_RE = re.compile(
    r"StableBoundedDerivedInfinityCategory|StableInfinityAudit\.CertificateShape|"
    r"StableInfinityAudit\.DboundedCertificateInput|DboundedCertificateInput",
    flags=re.IGNORECASE,
)

STABLE_CERTIFICATE_FIELD_EVIDENCE_RE = re.compile(
    r"finiteLimitObligation|finiteColimitObligation|"
    r"suspensionLoopEquivalenceObligation|pushoutPullbackCompatibilityObligation|"
    r"\bfiniteLimits\b|\bfiniteColimits\b|"
    r"\bsuspensionLoopEquivalence\b|\bpushoutPullbackCompatibility\b|"
    r"\bsuspensionEquivalence\b|\bloopSuspensionEquivalence\b|"
    r"\bpushoutPullbackSquare\b",
    flags=re.IGNORECASE,
)

ORDINARY_NERVE_RE = re.compile(
    r"BoundedDerivedInfinityCategory[\s\S]{0,500}"
    r"CategoryTheory\.nerve\s*\(\s*BoundedDerivedCategory\s+C\s*\)",
    flags=re.MULTILINE,
)


def strip_lean_comments_and_strings(text: str) -> str:
    """Remove Lean comments and string contents before marker-only regex scans."""

    out: list[str] = []
    i = 0
    n = len(text)
    block_depth = 0
    in_line_comment = False
    in_string = False

    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""

        if in_line_comment:
            if ch == "\n":
                in_line_comment = False
                out.append(ch)
            else:
                out.append(" ")
            i += 1
            continue

        if block_depth:
            if ch == "/" and nxt == "-":
                block_depth += 1
                out.extend("  ")
                i += 2
                continue
            if ch == "-" and nxt == "/":
                block_depth -= 1
                out.extend("  ")
                i += 2
                continue
            out.append("\n" if ch == "\n" else " ")
            i += 1
            continue

        if in_string:
            if ch == "\\":
                out.append(" ")
                if i + 1 < n:
                    out.append("\n" if nxt == "\n" else " ")
                    i += 2
                else:
                    i += 1
                continue
            if ch == '"':
                in_string = False
                out.append(" ")
            else:
                out.append("\n" if ch == "\n" else " ")
            i += 1
            continue

        if ch == "-" and nxt == "-":
            in_line_comment = True
            out.extend("  ")
            i += 2
            continue
        if ch == "/" and nxt == "-":
            block_depth = 1
            out.extend("  ")
            i += 2
            continue
        if ch == '"':
            in_string = True
            out.append(" ")
            i += 1
            continue

        out.append(ch)
        i += 1

    return "".join(out)


def fail(message: str) -> None:
    print(f"external_audit: FAIL: {message}", file=sys.stderr)
    raise SystemExit(1)


def load_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        fail(f"missing JSON file: {path}")
    except json.JSONDecodeError as exc:
        fail(f"invalid JSON in {path}: {exc}")


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def project_root_for(root: Path) -> Path:
    nested = root / "input" / "workdir"
    if (nested / "LeanLCAExactChallenge").exists():
        return nested
    return root


def iter_project_source_files(project_root: Path) -> list[Path]:
    roots = [
        project_root / "LeanLCAExactChallenge",
        project_root / "audit",
        project_root / "docs" / "research",
    ]
    files: list[Path] = []
    for base in roots:
        if not base.exists():
            continue
        for path in base.rglob("*"):
            if (
                path.is_file()
                and ".lake" not in path.parts
                and "__pycache__" not in path.parts
                and path.suffix != ".pyc"
            ):
                files.append(path)
    return sorted(files)


def source_tree_hash(project_root: Path) -> str:
    h = hashlib.sha256()
    for path in iter_project_source_files(project_root):
        rel = path.relative_to(project_root).as_posix()
        h.update(rel.encode("utf-8"))
        h.update(b"\0")
        h.update(sha256_file(path).encode("ascii"))
        h.update(b"\n")
    return h.hexdigest()


def is_generated_artifact_path(rel: str) -> bool:
    return (
        rel in GENERATED_ARTIFACT_NAMES
        or rel.startswith(GENERATED_ARTIFACT_PREFIXES)
        or rel.endswith(GENERATED_ARTIFACT_SUFFIXES)
    )


def check_no_tracked_generated_files(root: Path) -> None:
    if not (root / ".git").exists():
        return
    proc = subprocess.run(
        ["git", "ls-files", "-z"],
        cwd=root,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        fail(f"git ls-files failed while checking tracked artifacts: {proc.stderr.strip()}")
    offenders = sorted(
        rel for rel in proc.stdout.split("\0") if rel and is_generated_artifact_path(rel)
    )
    if offenders:
        fail("generated or transient artifacts are tracked: " + ", ".join(offenders))


def check_required(
    root: Path, project_root: Path, terminal_outcome: Path, *, require_terminal: bool
) -> None:
    missing = []
    for rel in PROJECT_REQUIRED:
        if not (project_root / rel).is_file():
            missing.append(str(project_root / rel))
    for rel in ROOT_REQUIRED:
        if not (root / rel).is_file():
            missing.append(str(root / rel))
    if require_terminal and not terminal_outcome.is_file():
        missing.append(str(terminal_outcome))
    if missing:
        fail("missing required files: " + ", ".join(missing))


def check_forbidden_lean(project_root: Path) -> None:
    for path in sorted((project_root / "LeanLCAExactChallenge").rglob("*.lean")) + sorted(
        (project_root / "audit").rglob("*.lean")
    ):
        text = path.read_text(encoding="utf-8")
        match = FORBIDDEN_LEAN_RE.search(text)
        if match:
            fail(f"forbidden Lean token {match.group(1)!r} in {path}")


def japanese_char_count(text: str) -> int:
    return len(JAPANESE_RE.findall(text))


def require_english_text(label: str, text: str, minimum: int = 20) -> None:
    count = japanese_char_count(text)
    if count:
        fail(f"{label} contains {count} Japanese/CJK characters; write review prose in English")
    if substantive_english_word_count(text) < minimum:
        fail(f"{label} must contain substantive English prose")


def substantive_english_word_count(text: str) -> int:
    return len(ENGLISH_WORD_RE.findall(text))


def require_substantive_text(label: str, text: str, minimum: int = 20) -> None:
    count = japanese_char_count(text)
    if count:
        fail(f"{label} contains {count} Japanese/CJK characters; write outcome prose in English")
    if substantive_english_word_count(text) >= minimum:
        return
    fail(f"{label} must contain substantive prose")


def check_reference_route_log(project_root: Path) -> None:
    path = project_root / "docs" / "research" / "reference_route_log.md"
    text = path.read_text(encoding="utf-8")
    require_english_text("docs/research/reference_route_log.md", text, minimum=80)
    required_patterns = {
        "references": r"B[üu]hler|Hoffmann|Spitzweck|Schneiders|references?",
        "source_searches": r"rg|source search|searches?",
        "library_apis": r"mathlib|API|ShortComplex|Abelian\.Ext|DerivedCategory",
        "shortcut": r"shortcut|reused|existing API",
        "local_vs_adapted": r"local|existing API|adapted|custom",
        "false_leads": r"false lead|not found|did not find|unsuitable",
    }
    for label, pattern in required_patterns.items():
        if not re.search(pattern, text, flags=re.IGNORECASE):
            fail(f"reference_route_log.md does not explain required route-log item: {label}")


def check_english_deliverables(
    root: Path, project_root: Path, terminal_outcome_path: Path | None
) -> None:
    for rel, base in [
        ("README_FOR_REVIEW.md", root),
        ("docs/research/sources.md", project_root),
        ("docs/research/mathlib_gap_analysis.md", project_root),
    ]:
        require_english_text(rel, (base / rel).read_text(encoding="utf-8"), minimum=40)
    check_reference_route_log(project_root)

    if terminal_outcome_path is None or not terminal_outcome_path.exists():
        return

    outcome = load_json(terminal_outcome_path)
    summary = outcome.get("summary")
    if not isinstance(summary, str):
        fail("terminal_outcome.summary must be a string")
    require_substantive_text("terminal_outcome.summary", summary, minimum=12)
    known_gaps = outcome.get("known_gaps")
    if not isinstance(known_gaps, list):
        fail("terminal_outcome.known_gaps must be a list")
    for index, gap in enumerate(known_gaps):
        if not isinstance(gap, str):
            fail(f"terminal_outcome.known_gaps[{index}] must be a string")
        require_substantive_text(f"terminal_outcome.known_gaps[{index}]", gap, minimum=4)
    if outcome.get("reference_route_log") != "docs/research/reference_route_log.md":
        fail("terminal_outcome.reference_route_log must point to docs/research/reference_route_log.md")


def check_no_product_placeholders(project_root: Path) -> None:
    hits: list[str] = []
    for path in sorted((project_root / "LeanLCAExactChallenge").rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        for lineno, line in enumerate(text.splitlines(), start=1):
            match = PRODUCT_PLACEHOLDER_RE.search(line)
            if match:
                rel = path.relative_to(project_root).as_posix()
                hits.append(f"{rel}:{lineno}:{match.group(0)!r}")
    if hits:
        fail("product-facing Lean sources contain placeholder markers: " + ", ".join(hits))


def terminal_claims_product_success(terminal_outcome_path: Path) -> bool:
    if not terminal_outcome_path.exists():
        return False
    outcome = load_json(terminal_outcome_path)
    return outcome.get("outcome") == "product_success" or outcome.get("product_complete") is True


def current_git_head(root: Path) -> str | None:
    if not (root / ".git").exists():
        return None
    proc = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=root,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        check=False,
    )
    if proc.returncode != 0:
        return None
    return proc.stdout.strip()


def positive_witness_present(product_audit_text: str, original_audit_text: str) -> bool:
    combined = product_audit_text + "\n" + original_audit_text
    return all(symbol in combined for symbol in POSITIVE_COMPLETION_SYMBOLS)


def final_false_witness_present(project_root: Path, product_audit_text: str, original_audit_text: str) -> bool:
    final_source = strip_lean_comments_and_strings(
        (project_root / "LeanLCAExactChallenge/Derived/OriginalFourTaskContractCompletion.lean").read_text(
            encoding="utf-8"
        )
        if (project_root / "LeanLCAExactChallenge/Derived/OriginalFourTaskContractCompletion.lean").is_file()
        else ""
    )
    final_surface = product_audit_text + "\n" + original_audit_text + "\n" + final_source
    if "originalFourTaskContractCompletion" in product_audit_text + "\n" + original_audit_text:
        return any(marker in final_surface for marker in FINAL_FALSE_COMPLETION_MARKERS)
    return False


def check_positive_witness_source_gate(
    root: Path, project_root: Path, terminal_outcome_path: Path
) -> None:
    if not terminal_claims_product_success(terminal_outcome_path):
        return
    outcome = load_json(terminal_outcome_path)
    head = current_git_head(root)
    if head is not None and outcome.get("git_head") != head:
        fail("terminal_outcome.git_head does not match current HEAD while claiming product success")
    product_audit = strip_lean_comments_and_strings(
        (project_root / "audit/ProductSuccessDeclarations.lean").read_text(encoding="utf-8")
    )
    original_audit = strip_lean_comments_and_strings(
        (project_root / "audit/OriginalFourTaskCompletionDeclarations.lean").read_text(
            encoding="utf-8"
        )
        if (project_root / "audit/OriginalFourTaskCompletionDeclarations.lean").is_file()
        else ""
    )
    if not positive_witness_present(product_audit, original_audit):
        fail("product_success lacks a positive OriginalFourTaskProductSuccess Lean witness")
    if final_false_witness_present(project_root, product_audit, original_audit):
        fail("product_success imports a final witness proving productSuccessClaimed=false")


def check_derived_infinity_product_contract(
    project_root: Path, terminal_outcome_path: Path, require_product_contract: bool
) -> None:
    """Reject a product-success claim that only exposes an ordinary localization nerve."""

    if not require_product_contract:
        return

    derived = project_root / "LeanLCAExactChallenge" / "Derived" / "Bounded.lean"
    product_audit = project_root / "audit" / "ProductSuccessDeclarations.lean"
    derived_text = strip_lean_comments_and_strings(derived.read_text(encoding="utf-8"))
    audit_text = strip_lean_comments_and_strings(product_audit.read_text(encoding="utf-8"))
    stable_text = derived_text + "\n" + audit_text

    if ORDINARY_NERVE_RE.search(derived_text):
        fail(
            "BoundedDerivedInfinityCategory is still the nerve of the ordinary localized "
            "category; this cannot satisfy the stable bounded derived infinity-category "
            "product contract"
        )

    if not DERIVED_STABLE_MARKER_RE.search(derived_text):
        fail(
            "Derived/Bounded.lean lacks a stable infinity-category certificate marker "
            "(finite limits, finite colimits, suspension equivalence, or equivalent local API)"
        )

    if not DERIVED_STABLE_MARKER_RE.search(audit_text):
        fail(
            "ProductSuccessDeclarations.lean does not check any stable infinity-category "
            "certificate for Dbounded"
        )

    if STABLE_CERTIFICATE_PLACEHOLDER_RE.search(stable_text) and not (
        STABLE_CERTIFICATE_FIELD_EVIDENCE_RE.search(stable_text)
    ):
        fail(
            "stable bounded derived infinity-category product success cites a certificate "
            "name without concrete finite-limit, finite-colimit, suspension/loop, or "
            "pushout/pullback field evidence"
        )


def command_status_map(verification: dict[str, Any]) -> dict[str, str]:
    out: dict[str, str] = {}
    for item in verification.get("commands", []):
        if isinstance(item, dict):
            cmd = item.get("command")
            status = item.get("status")
            if isinstance(cmd, str) and isinstance(status, str):
                out[cmd] = status.strip().lower()
    return out


def check_verification_entries_resolved(
    verification: dict[str, Any], *, product_success: bool = False
) -> None:
    commands = verification.get("commands")
    if not isinstance(commands, list):
        fail("run/verification.json commands must be a list")
    for index, item in enumerate(commands):
        if not isinstance(item, dict):
            fail(f"run/verification.json commands[{index}] must be an object")
        command = item.get("command")
        status = item.get("status")
        evidence = item.get("evidence")
        if not isinstance(command, str) or not command.strip():
            fail(f"run/verification.json commands[{index}].command must be a nonempty string")
        if not isinstance(status, str):
            fail(f"run/verification.json command {command!r} status must be a string")
        normalized = status.strip().lower()
        if normalized in UNRESOLVED_VERIFICATION_STATUSES:
            fail(f"run/verification.json command {command!r} has unresolved status {status!r}")
        if normalized not in ALLOWED_VERIFICATION_STATUSES:
            fail(f"run/verification.json command {command!r} has unsupported status {status!r}")
        if product_success and normalized == "failed_expected":
            fail(
                f"run/verification.json command {command!r} has failed_expected status "
                "inside product_success evidence"
            )
        if not isinstance(evidence, str) or not evidence.strip():
            fail(f"run/verification.json command {command!r} must include nonempty evidence")


def check_verification_fixture_resolved(root: Path, terminal_outcome: Path) -> None:
    verification_path = root / "run" / "verification.json"
    if verification_path.exists():
        check_verification_entries_resolved(
            load_json(verification_path),
            product_success=terminal_claims_product_success(terminal_outcome),
        )


def check_verification(root: Path, project_root: Path, terminal_outcome: Path) -> None:
    verification = load_json(root / "run" / "verification.json")
    check_verification_entries_resolved(
        verification, product_success=terminal_claims_product_success(terminal_outcome)
    )
    statuses = command_status_map(verification)
    for cmd in REQUIRED_COMMANDS:
        if statuses.get(cmd) != "passed":
            fail(f"missing passing verification evidence for command: {cmd}")
    recorded_hash = verification.get("source_tree_hash")
    current_hash = source_tree_hash(project_root)
    if recorded_hash != current_hash:
        fail("stale verification evidence: source_tree_hash mismatch")


def has_authoritative_zip_sha(obj: Any, path: str = "$") -> str | None:
    if isinstance(obj, dict):
        for key, value in obj.items():
            lower = key.lower()
            if "zip" in lower and "sha256" in lower:
                return f"{path}.{key}"
            found = has_authoritative_zip_sha(value, f"{path}.{key}")
            if found:
                return found
    elif isinstance(obj, list):
        for index, value in enumerate(obj):
            found = has_authoritative_zip_sha(value, f"{path}[{index}]")
            if found:
                return found
    return None


def check_no_internal_zip_sha(root: Path, terminal_outcome: Path | None) -> None:
    for rel in ["manifest.json"]:
        path = root / rel
        if path.exists():
            found = has_authoritative_zip_sha(load_json(path))
            if found:
                fail(f"packet-internal JSON treats final zip SHA256 as authoritative at {rel}:{found}")
    readme = root / "README_FOR_REVIEW.md"
    if readme.exists():
        text = readme.read_text(encoding="utf-8")
        if "zip" in text.lower() and HEX64_RE.search(text):
            fail("README_FOR_REVIEW.md appears to contain a final zip SHA256")
    if terminal_outcome is not None and terminal_outcome.exists():
        found = has_authoritative_zip_sha(load_json(terminal_outcome))
        if found:
            fail(f"terminal outcome treats final zip SHA256 as authoritative at {found}")


def check_negative_fixture(root: Path) -> None:
    def run_fixture(rel: str, expected_failure: str) -> None:
        fixture = root / "audit" / "negative_fixtures" / rel
        if not fixture.exists():
            fail(f"missing negative fixture: {fixture}")
        proc = subprocess.run(
            [
                sys.executable,
                str(Path(__file__).resolve()),
                "--root",
                str(fixture),
                "--terminal-outcome",
                str(fixture / "terminal_outcome.json"),
                "--self-check-only",
            ],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            check=False,
        )
        if proc.returncode == 0:
            fail(f"{rel} negative fixture was accepted; expected {expected_failure}")

    run_fixture(
        "self_referential_zip_sha_authoritative",
        "self-referential zip SHA failure",
    )
    run_fixture(
        "ordinary_nerve_claimed_product_success",
        "derived infinity contract failure",
    )
    run_fixture(
        "comment_only_stable_marker_claimed_product_success",
        "comment-only stable marker failure",
    )
    run_fixture(
        "string_literal_only_stable_marker_claimed_product_success",
        "string-literal-only stable marker failure",
    )
    run_fixture(
        "pending_verification_evidence",
        "unresolved verification status failure",
    )
    run_fixture(
        "failed_expected_product_success",
        "failed_expected product-success verification failure",
    )
    run_fixture(
        "stable_certificate_name_without_field_evidence",
        "stable certificate placeholder without field evidence failure",
    )
    run_fixture(
        "final_witness_productSuccessClaimed_false",
        "final false witness contradiction failure",
    )
    run_fixture(
        "product_success_without_positive_lean_witness",
        "missing positive Lean witness failure",
    )
    run_fixture(
        "symbol_only_completion_check",
        "symbol-only completion check failure",
    )
    run_fixture(
        "metadata_only_w1426_promotion",
        "metadata-only product-success promotion failure",
    )
    run_fixture(
        "terminal_git_head_stale",
        "stale terminal git_head product-success failure",
    )


def check_terminal_outcome(root: Path, terminal_outcome_path: Path, packet_mode: bool) -> None:
    outcome = load_json(terminal_outcome_path)
    terminal = outcome.get("outcome")
    if terminal != "product_success":
        if terminal not in ALLOWED_NONTERMINAL_OUTCOMES:
            fail(f"unsupported terminal_outcome.outcome: {terminal!r}")
        if outcome.get("product_success") is True:
            fail("nonterminal outcome must not set product_success=true")
        if outcome.get("product_complete") is True:
            fail("nonterminal outcome must not set product_complete=true")
        if outcome.get("update_goal_allowed") is True:
            fail("nonterminal outcome must not set update_goal_allowed=true")
        known_gaps = outcome.get("known_gaps")
        remaining_work = outcome.get("remaining_work")
        if not isinstance(known_gaps, list) or not known_gaps:
            fail("nonterminal outcome must record known_gaps")
        if not isinstance(remaining_work, list) or not remaining_work:
            fail("nonterminal outcome must record remaining_work")
        return
    product_complete = outcome.get("product_complete")
    update_goal_allowed = outcome.get("update_goal_allowed")
    if product_complete is not True or update_goal_allowed is not True:
        fail("product_success must set product_complete and update_goal_allowed true")
    known_gaps = outcome.get("known_gaps")
    if known_gaps != []:
        fail("product_success must have known_gaps = []")

    commands = outcome.get("verified_commands", [])
    if not isinstance(commands, list):
        fail("terminal_outcome.verified_commands must be a list")
    for cmd in REQUIRED_COMMANDS:
        if cmd not in commands:
            fail(f"terminal outcome omits verified command: {cmd}")

    if not packet_mode:
        packet_zip = outcome.get("packet_zip")
        sidecar = outcome.get("packet_sha256_sidecar")
        if packet_zip or sidecar:
            if not isinstance(packet_zip, str) or not isinstance(sidecar, str):
                fail("packet_zip and packet_sha256_sidecar must be strings")
            zip_path = root / packet_zip
            sidecar_path = root / sidecar
            if not zip_path.is_file():
                fail(f"missing packet zip: {zip_path}")
            if not sidecar_path.is_file():
                fail(f"missing packet SHA256 sidecar: {sidecar_path}")
            expected = sidecar_path.read_text(encoding="utf-8").split()[0]
            actual = sha256_file(zip_path)
            if expected != actual:
                fail("packet sidecar SHA256 mismatch")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", required=True)
    parser.add_argument("--terminal-outcome", default=None)
    parser.add_argument("--self-check-only", action="store_true")
    args = parser.parse_args()

    root = Path(args.root).resolve()
    terminal_outcome_arg = args.terminal_outcome or "terminal_outcome/terminal_outcome.json"
    terminal_outcome = Path(terminal_outcome_arg)
    if not terminal_outcome.is_absolute():
        terminal_outcome = root / terminal_outcome

    if args.self_check_only:
        check_no_internal_zip_sha(root, terminal_outcome)
        check_verification_fixture_resolved(root, terminal_outcome)
        project_root = project_root_for(root)
        check_derived_infinity_product_contract(
            project_root, terminal_outcome, terminal_claims_product_success(terminal_outcome)
        )
        check_positive_witness_source_gate(root, project_root, terminal_outcome)
        print("external_audit: self-check passed")
        return

    project_root = project_root_for(root)
    packet_mode = project_root != root
    require_terminal = packet_mode or args.terminal_outcome is not None
    terminal_for_checks = terminal_outcome if require_terminal else None
    terminal_product_success = (
        terminal_for_checks is not None and terminal_claims_product_success(terminal_for_checks)
    )
    check_required(root, project_root, terminal_outcome, require_terminal=require_terminal)
    check_no_tracked_generated_files(root)
    check_forbidden_lean(project_root)
    check_english_deliverables(
        root,
        project_root,
        terminal_for_checks,
    )
    check_no_product_placeholders(project_root)
    check_derived_infinity_product_contract(
        project_root, terminal_outcome, terminal_product_success
    )
    if terminal_for_checks is not None:
        check_positive_witness_source_gate(root, project_root, terminal_for_checks)
    check_no_internal_zip_sha(root, terminal_for_checks)
    if terminal_for_checks is not None and terminal_for_checks.exists():
        if not (root / "run" / "verification.json").is_file():
            fail("terminal outcome audit requires run/verification.json")
        check_verification(root, project_root, terminal_for_checks)
    check_negative_fixture(root)
    if terminal_for_checks is not None and terminal_for_checks.exists():
        check_terminal_outcome(root, terminal_for_checks, packet_mode)
    print("external_audit: passed")


if __name__ == "__main__":
    main()
