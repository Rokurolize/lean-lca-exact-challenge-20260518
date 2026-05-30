#!/usr/bin/env python3
"""Read-only audit for the immutable Lean LCA original four-task contract."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


EXPECTED_CONTRACT_SHA256 = "a7c9f6493dfd369bae9d18196e8379635f958630306f5272fad3faea1f8edfd1"
EXPECTED_POSITIVE_WITNESS_CONTRACT_SHA256 = (
    "3120c014b83e0c7c8f8160ca90447a1a73588096a354ace109e2fca4e4eab5ec"
)
ORIGINAL_COMPLETION_SYMBOL = "originalFourTaskContractCompletion"
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
REQUIRED_NEGATIVE_FIXTURES = [
    "self_referential_zip_sha_authoritative",
    "ordinary_nerve_claimed_product_success",
    "stable_certificate_name_without_field_evidence",
    "semantic_input_claimed_product_success",
    "prop_field_wrapper_claimed_product_success",
    "final_witness_productSuccessClaimed_false",
    "product_success_without_positive_lean_witness",
    "symbol_only_completion_check",
    "metadata_only_w1426_promotion",
    "terminal_git_head_stale",
]


def fail(message: str) -> None:
    print(f"original_four_task_contract_audit: failed: {message}", file=sys.stderr)
    raise SystemExit(1)


def load_json(path: Path) -> dict[str, Any]:
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError:
        fail(f"missing JSON file: {path}")
    except json.JSONDecodeError as exc:
        fail(f"invalid JSON in {path}: {exc}")
    if not isinstance(data, dict):
        fail(f"JSON root must be an object: {path}")
    return data


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def read_text_if_present(path: Path) -> str:
    if not path.is_file():
        return ""
    return path.read_text(encoding="utf-8")


def strip_lean_comments_and_strings(text: str) -> str:
    out: list[str] = []
    i = 0
    depth = 0
    in_line_comment = False
    in_string = False
    while i < len(text):
        ch = text[i]
        nxt = text[i + 1] if i + 1 < len(text) else ""
        if in_line_comment:
            if ch == "\n":
                in_line_comment = False
                out.append(ch)
            else:
                out.append(" ")
            i += 1
            continue
        if depth:
            if ch == "/" and nxt == "-":
                depth += 1
                out.extend("  ")
                i += 2
                continue
            if ch == "-" and nxt == "/":
                depth -= 1
                out.extend("  ")
                i += 2
                continue
            out.append("\n" if ch == "\n" else " ")
            i += 1
            continue
        if in_string:
            if ch == "\\":
                out.append(" ")
                if i + 1 < len(text):
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
            depth = 1
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


def terminal_claims_product_success(outcome: dict[str, Any]) -> bool:
    return (
        outcome.get("outcome") == "product_success"
        or outcome.get("product_success") is True
        or outcome.get("product_complete") is True
        or outcome.get("update_goal_allowed") is True
    )


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
        if path.is_file():
            found = has_authoritative_zip_sha(load_json(path))
            if found:
                fail(f"packet-internal JSON treats final zip SHA256 as authoritative at {rel}:{found}")
    if terminal_outcome.is_file():
        found = has_authoritative_zip_sha(load_json(terminal_outcome))
        if found:
            fail(f"terminal outcome treats final zip SHA256 as authoritative at {found}")


def product_success_blockers(root: Path, outcome: dict[str, Any]) -> list[str]:
    derived_text = strip_lean_comments_and_strings(
        read_text_if_present(root / "LeanLCAExactChallenge/Derived/Bounded.lean")
    )
    product_audit_text = strip_lean_comments_and_strings(
        read_text_if_present(root / "audit/ProductSuccessDeclarations.lean")
    )
    original_audit_text = strip_lean_comments_and_strings(
        read_text_if_present(root / "audit/OriginalFourTaskCompletionDeclarations.lean")
    )
    terminal_text = json.dumps(outcome, ensure_ascii=True)
    blockers: list[str] = []

    structure_match = re.search(
        r"structure\s+BoundedDerivedInfinityCategory\b[\s\S]{0,900}", derived_text
    )
    if structure_match:
        block = structure_match.group(0)
        prop_fields = [
            "finiteLimits : Prop",
            "finiteColimits : Prop",
            "suspensionLoopEquivalence : Prop",
            "pushoutPullbackCompatibility : Prop",
        ]
        if all(field in block for field in prop_fields):
            blockers.append("BoundedDerivedInfinityCategory is still a four-Prop wrapper")

    if re.search(
        r"BoundedDerivedInfinityCategory[\s\S]{0,600}CategoryTheory\.nerve\s*\(",
        derived_text + "\n" + product_audit_text,
    ):
        blockers.append("ordinary nerve is still presented as bounded derived infinity-category evidence")

    final_surface_text = product_audit_text + "\n" + original_audit_text + "\n" + terminal_text
    forbidden_final_inputs = [
        "MetrizableOrdinaryStableSemanticInput",
        "StableFourProjectionCertificate",
        "AcceptedStableBoundedDerivedInfinityCategory",
        "boundedDerivedInfinityCategoryOfMetrizableOrdinaryInput",
    ]
    for name in forbidden_final_inputs:
        if name in final_surface_text:
            blockers.append(f"final product surface still references {name}")

    if "#check BoundedDerivedInfinityCategory" in product_audit_text or (
        "#check (BoundedDerivedInfinityCategory" in product_audit_text
    ):
        if ORIGINAL_COMPLETION_SYMBOL not in original_audit_text:
            blockers.append("ProductSuccessDeclarations only checks the bounded-derived name without an original-four-task completion witness")

    if not original_audit_text:
        blockers.append("audit/OriginalFourTaskCompletionDeclarations.lean is missing")
    elif ORIGINAL_COMPLETION_SYMBOL not in original_audit_text:
        blockers.append("OriginalFourTaskCompletionDeclarations lacks the original-four-task completion witness")

    if terminal_claims_product_success(outcome):
        head = current_git_head(root)
        recorded_head = outcome.get("git_head")
        if head is not None and recorded_head != head:
            blockers.append(
                "terminal_outcome.git_head does not match current HEAD while claiming product success"
            )
        if not positive_witness_present(product_audit_text, original_audit_text):
            blockers.append("product_success lacks a positive OriginalFourTaskProductSuccess Lean witness")
        if final_false_witness_present(root, product_audit_text, original_audit_text):
            blockers.append("product_success imports a final witness proving productSuccessClaimed=false")
        if ORIGINAL_COMPLETION_SYMBOL in product_audit_text and not positive_witness_present(
            product_audit_text, original_audit_text
        ):
            blockers.append(
                "ProductSuccessDeclarations symbol-checks completion without positive Lean content"
            )

    packet_root = root / "packets/lean_lca_exact_category_challenge"
    if not packet_root.is_dir():
        blockers.append("review packet directory is missing")
    else:
        for rel in [
            "manifest.json",
            "README_FOR_REVIEW.md",
        ]:
            if not (packet_root / rel).is_file():
                blockers.append(f"review packet missing {rel}")
        for name in REQUIRED_NEGATIVE_FIXTURES:
            if not (packet_root / "negative_fixtures" / name).exists():
                blockers.append(f"review packet missing negative fixture {name}")

    return blockers


def check_nonterminal_outcome(outcome: dict[str, Any]) -> None:
    if outcome.get("product_success") is True:
        fail("nonterminal outcome must not set product_success=true")
    if outcome.get("product_complete") is True:
        fail("nonterminal outcome must not set product_complete=true")
    if outcome.get("update_goal_allowed") is True:
        fail("nonterminal outcome must not set update_goal_allowed=true")
    gaps = outcome.get("known_gaps")
    remaining = outcome.get("remaining_work")
    if not isinstance(gaps, list) or not gaps:
        fail("nonterminal outcome must record known_gaps")
    if not isinstance(remaining, list) or not remaining:
        fail("nonterminal outcome must record remaining_work")
    combined = json.dumps({"summary": outcome.get("summary"), "known_gaps": gaps}, ensure_ascii=True)
    if "original four" not in combined.lower() and "four-task" not in combined.lower():
        fail("nonterminal outcome must mention the original four-task contract")


def check_negative_fixtures(root: Path, contract: Path, terminal_outcome_rel: str) -> None:
    fixture_root = root / "audit/negative_fixtures"
    for name in REQUIRED_NEGATIVE_FIXTURES:
        fixture = fixture_root / name
        if not fixture.exists():
            fail(f"missing negative fixture: audit/negative_fixtures/{name}")
        terminal = fixture / "terminal_outcome.json"
        if not terminal.exists():
            terminal = fixture / terminal_outcome_rel
        proc = subprocess.run(
            [
                sys.executable,
                str(Path(__file__).resolve()),
                "--root",
                str(fixture),
                "--contract",
                str(contract),
                "--terminal-outcome",
                str(terminal),
                "--self-check-only",
            ],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            check=False,
        )
        if proc.returncode == 0:
            fail(f"negative fixture {name} was accepted")


def check_contract(contract: Path) -> str:
    if not contract.is_file():
        fail(f"missing immutable contract: {contract}")
    actual = sha256_file(contract)
    if actual != EXPECTED_CONTRACT_SHA256:
        fail(
            "immutable contract SHA256 changed: "
            f"expected {EXPECTED_CONTRACT_SHA256}, got {actual}"
        )
    return actual


def check_positive_witness_contract(contract: Path | None) -> str | None:
    if contract is None:
        return None
    if not contract.is_file():
        fail(f"missing positive-witness contract: {contract}")
    actual = sha256_file(contract)
    if actual != EXPECTED_POSITIVE_WITNESS_CONTRACT_SHA256:
        fail(
            "positive-witness contract SHA256 changed: "
            f"expected {EXPECTED_POSITIVE_WITNESS_CONTRACT_SHA256}, got {actual}"
        )
    return actual


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


def final_false_witness_present(root: Path, product_audit_text: str, original_audit_text: str) -> bool:
    final_source = strip_lean_comments_and_strings(
        read_text_if_present(root / "LeanLCAExactChallenge/Derived/OriginalFourTaskContractCompletion.lean")
    )
    final_surface = product_audit_text + "\n" + original_audit_text + "\n" + final_source
    if ORIGINAL_COMPLETION_SYMBOL in product_audit_text + "\n" + original_audit_text:
        return any(marker in final_surface for marker in FINAL_FALSE_COMPLETION_MARKERS)
    return False


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", required=True)
    parser.add_argument("--contract", required=True)
    parser.add_argument("--positive-witness-contract")
    parser.add_argument("--terminal-outcome", default="terminal_outcome/terminal_outcome.json")
    parser.add_argument("--self-check-only", action="store_true")
    args = parser.parse_args()

    root = Path(args.root).resolve()
    contract = Path(args.contract).resolve()
    terminal_outcome = Path(args.terminal_outcome)
    if not terminal_outcome.is_absolute():
        terminal_outcome = root / terminal_outcome

    contract_sha = check_contract(contract)
    positive_contract_sha = check_positive_witness_contract(
        Path(args.positive_witness_contract).resolve()
        if args.positive_witness_contract
        else None
    )
    outcome = load_json(terminal_outcome)
    check_no_internal_zip_sha(root, terminal_outcome)

    blockers = product_success_blockers(root, outcome)
    if terminal_claims_product_success(outcome):
        if blockers:
            fail("; ".join(blockers))
        if outcome.get("known_gaps") != []:
            fail("product_success must record known_gaps=[]")
    else:
        check_nonterminal_outcome(outcome)

    if not args.self_check_only:
        check_negative_fixtures(root, contract, args.terminal_outcome)

    result = {
        "audit": "original_four_task_contract_audit",
        "status": "passed",
        "root": str(root),
        "contract": str(contract),
        "contract_sha256": contract_sha,
        "positive_witness_contract": str(Path(args.positive_witness_contract).resolve())
        if args.positive_witness_contract
        else None,
        "positive_witness_contract_sha256": positive_contract_sha,
        "terminal_claims_product_success": terminal_claims_product_success(outcome),
        "blockers": blockers,
    }
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
