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
    "manifest.json",
    "terminal_outcome/terminal_outcome.json",
    "run/verification.json",
]

REQUIRED_COMMANDS = [
    "lake build",
    "scripts/audit_no_forbidden_lean_tokens.sh LeanLCAExactChallenge",
    "lake env lean audit/RequiredDeclarations.lean",
    "lake env lean audit/ProductSuccessDeclarations.lean",
    "git diff --check",
]

FORBIDDEN_LEAN_RE = re.compile(r"\b(sorry|admit|axiom|unsafe)\b")
HEX64_RE = re.compile(r"\b[0-9a-fA-F]{64}\b")
JAPANESE_RE = re.compile(r"[\u3040-\u30ff\u3400-\u9fff]")
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

ORDINARY_NERVE_RE = re.compile(
    r"BoundedDerivedInfinityCategory[\s\S]{0,500}"
    r"CategoryTheory\.nerve\s*\(\s*BoundedDerivedCategory\s+C\s*\)",
    flags=re.MULTILINE,
)


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


def check_required(root: Path, project_root: Path, terminal_outcome: Path) -> None:
    missing = []
    for rel in PROJECT_REQUIRED:
        if not (project_root / rel).is_file():
            missing.append(str(project_root / rel))
    for rel in ROOT_REQUIRED:
        if not (root / rel).is_file():
            missing.append(str(root / rel))
    if not terminal_outcome.is_file():
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


def require_japanese_text(label: str, text: str, minimum: int = 20) -> None:
    if japanese_char_count(text) < minimum:
        fail(f"{label} must contain substantive Japanese prose")


def check_reference_route_log(project_root: Path) -> None:
    path = project_root / "docs" / "research" / "reference_route_log.md"
    text = path.read_text(encoding="utf-8")
    require_japanese_text("docs/research/reference_route_log.md", text, minimum=80)
    required_patterns = {
        "references": r"B[üu]hler|Hoffmann|Spitzweck|Schneiders|文献|参照",
        "source_searches": r"rg|source search|検索",
        "library_apis": r"mathlib|API|ShortComplex|Abelian\.Ext|DerivedCategory",
        "shortcut": r"近道|shortcut|楽にした",
        "local_vs_adapted": r"ローカル|既存API|自作|適応",
        "false_leads": r"失敗|false lead|見つからなかった",
    }
    for label, pattern in required_patterns.items():
        if not re.search(pattern, text, flags=re.IGNORECASE):
            fail(f"reference_route_log.md does not explain required route-log item: {label}")


def check_japanese_deliverables(root: Path, project_root: Path, terminal_outcome_path: Path) -> None:
    for rel, base in [
        ("README_FOR_REVIEW.md", root),
        ("docs/research/sources.md", project_root),
        ("docs/research/mathlib_gap_analysis.md", project_root),
    ]:
        require_japanese_text(rel, (base / rel).read_text(encoding="utf-8"), minimum=40)
    check_reference_route_log(project_root)

    outcome = load_json(terminal_outcome_path)
    summary = outcome.get("summary")
    if not isinstance(summary, str):
        fail("terminal_outcome.summary must be a string")
    require_japanese_text("terminal_outcome.summary", summary, minimum=12)
    known_gaps = outcome.get("known_gaps")
    if not isinstance(known_gaps, list):
        fail("terminal_outcome.known_gaps must be a list")
    for index, gap in enumerate(known_gaps):
        if not isinstance(gap, str):
            fail(f"terminal_outcome.known_gaps[{index}] must be a string")
        require_japanese_text(f"terminal_outcome.known_gaps[{index}]", gap, minimum=4)
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


def check_derived_infinity_product_contract(
    project_root: Path, terminal_outcome_path: Path, require_product_contract: bool
) -> None:
    """Reject a product-success claim that only exposes an ordinary localization nerve."""

    if not require_product_contract:
        return

    derived = project_root / "LeanLCAExactChallenge" / "Derived" / "Bounded.lean"
    product_audit = project_root / "audit" / "ProductSuccessDeclarations.lean"
    derived_text = derived.read_text(encoding="utf-8")
    audit_text = product_audit.read_text(encoding="utf-8")

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


def command_status_map(verification: dict[str, Any]) -> dict[str, str]:
    out: dict[str, str] = {}
    for item in verification.get("commands", []):
        if isinstance(item, dict):
            cmd = item.get("command")
            status = item.get("status")
            if isinstance(cmd, str) and isinstance(status, str):
                out[cmd] = status
    return out


def check_verification(root: Path, project_root: Path) -> None:
    verification = load_json(root / "run" / "verification.json")
    statuses = command_status_map(verification)
    for cmd in REQUIRED_COMMANDS:
        if statuses.get(cmd) != "passed":
            fail(f"missing passing verification evidence for command: {cmd}")
    recorded_hash = verification.get("source_tree_hash")
    current_hash = source_tree_hash(project_root)
    if recorded_hash != current_hash:
        fail("stale verification evidence: source_tree_hash mismatch")


def check_manifest(root: Path) -> None:
    manifest = load_json(root / "manifest.json")
    files = manifest.get("files")
    if not isinstance(files, list):
        fail("manifest.json must contain a files list")
    tree = hashlib.sha256()
    for item in files:
        if not isinstance(item, dict):
            fail("manifest file entries must be objects")
        rel = item.get("path")
        expected = item.get("sha256")
        expected_bytes = item.get("bytes")
        if not isinstance(rel, str) or not isinstance(expected, str):
            fail("manifest file entry requires path and sha256")
        if rel == "manifest.json":
            fail("manifest must not hash itself")
        path = root / rel
        if not path.is_file():
            fail(f"manifest lists missing file: {rel}")
        actual = sha256_file(path)
        if actual != expected:
            fail(f"manifest hash mismatch for {rel}")
        if isinstance(expected_bytes, int) and path.stat().st_size != expected_bytes:
            fail(f"manifest byte-size mismatch for {rel}")
        tree.update(rel.encode("utf-8"))
        tree.update(b"\0")
        tree.update(expected.encode("ascii"))
        tree.update(b"\n")
    expected_tree = manifest.get("content_hash_tree")
    if expected_tree != tree.hexdigest():
        fail("manifest content_hash_tree mismatch")


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


def check_no_internal_zip_sha(root: Path, terminal_outcome: Path) -> None:
    for rel in ["manifest.json", "terminal_outcome/terminal_outcome.json"]:
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
    if terminal_outcome.exists():
        found = has_authoritative_zip_sha(load_json(terminal_outcome))
        if found:
            fail(f"terminal outcome treats final zip SHA256 as authoritative at {found}")


def check_negative_fixture(root: Path) -> None:
    fixture = root / "audit" / "negative_fixtures" / "self_referential_zip_sha_authoritative"
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
        fail("negative fixture was accepted; expected self-referential zip SHA failure")

    fixture = root / "audit" / "negative_fixtures" / "ordinary_nerve_claimed_product_success"
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
        fail("ordinary-nerve negative fixture was accepted; expected derived infinity contract failure")


def check_terminal_outcome(root: Path, terminal_outcome_path: Path, packet_mode: bool) -> None:
    outcome = load_json(terminal_outcome_path)
    terminal = outcome.get("outcome")
    if terminal != "product_success":
        fail(f"terminal_outcome.outcome must be product_success for this Goal, got {terminal!r}")
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
    parser.add_argument("--terminal-outcome", required=True)
    parser.add_argument("--self-check-only", action="store_true")
    args = parser.parse_args()

    root = Path(args.root).resolve()
    terminal_outcome = Path(args.terminal_outcome)
    if not terminal_outcome.is_absolute():
        terminal_outcome = root / terminal_outcome

    if args.self_check_only:
        check_no_internal_zip_sha(root, terminal_outcome)
        project_root = project_root_for(root)
        check_derived_infinity_product_contract(
            project_root, terminal_outcome, terminal_claims_product_success(terminal_outcome)
        )
        print("external_audit: self-check passed")
        return

    project_root = project_root_for(root)
    packet_mode = project_root != root
    check_required(root, project_root, terminal_outcome)
    check_forbidden_lean(project_root)
    check_japanese_deliverables(root, project_root, terminal_outcome)
    check_no_product_placeholders(project_root)
    check_derived_infinity_product_contract(
        project_root, terminal_outcome, terminal_claims_product_success(terminal_outcome)
    )
    check_no_internal_zip_sha(root, terminal_outcome)
    check_manifest(root)
    check_verification(root, project_root)
    check_negative_fixture(root)
    check_terminal_outcome(root, terminal_outcome, packet_mode)
    print("external_audit: passed")


if __name__ == "__main__":
    main()
