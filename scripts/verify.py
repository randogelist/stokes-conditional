#!/usr/bin/env python3
"""Build the recovered sources and audit every declaration in their actual modules.

No prior receipt is treated as a proof. Lake decides which unchanged compiled
modules can be reused; every successful invocation audits the loaded environment
and writes a new receipt bound to source, dependencies, toolchain, and artifacts.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import subprocess
import sys
import zipfile
from contextlib import ExitStack
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parents[1]
TOOLCHAIN = "leanprover/lean4:v4.33.0"
MATHLIB = "db584cd6d46c92f209a44c0f1c829460d327499d"
GENERATED = {"All.lean", "lakefile.lean"}
FORBIDDEN = re.compile(r"\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|extern|opaque)\b")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def json_hash(value: object) -> str:
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def lean_code(source: str) -> str:
    """Remove nested Lean comments and string literals, preserving line positions."""
    out = []
    i = 0
    depth = 0
    state = "code"
    while i < len(source):
        c, pair = source[i], source[i:i + 2]
        if state == "line":
            if c == "\n":
                state = "code"
            out.append("\n" if c == "\n" else " ")
        elif state == "block":
            if pair == "/-":
                depth += 1
                out.extend("  ")
                i += 1
            elif pair == "-/":
                depth -= 1
                out.extend("  ")
                i += 1
                if depth == 0:
                    state = "code"
            else:
                out.append("\n" if c == "\n" else " ")
        elif state == "string":
            if c == "\\" and i + 1 < len(source):
                out.extend("  ")
                i += 1
            elif c == '"':
                state = "code"
                out.append(" ")
            else:
                out.append("\n" if c == "\n" else " ")
        elif pair == "--":
            state = "line"
            out.extend("  ")
            i += 1
        elif pair == "/-":
            state, depth = "block", 1
            out.extend("  ")
            i += 1
        elif c == '"':
            state = "string"
            out.append(" ")
        else:
            out.append(c)
        i += 1
    if state in {"block", "string"}:
        raise ValueError("Unterminated Lean comment or string")
    return "".join(out)


def sources(root: Path = ROOT) -> dict[str, Path]:
    paths = [p for p in root.glob("*.lean") if p.name not in GENERATED]
    for directory in ("Fefferman", "NSE"):
        paths.extend((root / directory).rglob("*.lean"))
    return {p.relative_to(root).with_suffix("").as_posix().replace("/", "."): p
            for p in sorted(paths)}


def imported_modules(code: str) -> list[str]:
    result = []
    for line in code.splitlines():
        match = re.match(r"\s*(?:(?:public|private|meta)\s+)?import\s+(.*)$", line)
        if match:
            result.extend(token.strip("«»") for token in match[1].split() if token != "all")
    return result


def check_sources(modules: dict[str, Path]) -> dict[str, list[str]]:
    graph = {}
    for name, path in modules.items():
        code = lean_code(path.read_text(encoding="utf-8-sig"))
        match = FORBIDDEN.search(code)
        if match:
            line = code[:match.start()].count("\n") + 1
            raise ValueError(f"Proof escape or new axiom token: {path}:{line}: {match[0]}")
        if re.search(r"\b(elab|macro|syntax|run_tac)\b", code):
            raise ValueError(f"Unreviewed metaprogramming command in {path}")
        if "run_cmd" in code and name != "NSE.Audit":
            raise ValueError(f"Unreviewed run_cmd in {path}")
        if "skipKernelTC" in code or "debug.skip" in code:
            raise ValueError(f"Kernel check override in {path}")
        graph[name] = [n for n in imported_modules(code) if n in modules]
    if "LayerA_Mathematics" not in graph:
        raise ValueError("Missing mathematical Layer A")
    pending, seen = ["LayerA_Mathematics"], set()
    while pending:
        name = pending.pop()
        if name in seen:
            continue
        seen.add(name)
        if name == "LayerB_Physics" or name.startswith("Fefferman.Physics"):
            raise ValueError(f"Mathematical Layer A depends on physics: {name}")
        pending.extend(graph[name])
    return graph


def repository_path(root: Path, relative: str) -> Path:
    path = root / relative
    if Path(relative).is_absolute() or ".." in Path(relative).parts or not path.resolve().is_relative_to(root.resolve()):
        raise ValueError(f"Provenance path escapes repository: {relative}")
    return path


def apply_recorded_repair(original: bytes, record: dict, label: str) -> bytes:
    """Replay an explicitly recorded UTF-8 patch against an immutable original."""
    if "repair" not in record:
        if "original_sha256" in record:
            raise ValueError(f"Original hash without a recorded repair: {label}")
        return original
    if hashlib.sha256(original).hexdigest() != record.get("original_sha256"):
        raise ValueError(f"Repaired source original hash mismatch: {label}")
    repair = record["repair"]
    if not isinstance(repair, dict) or not isinstance(repair.get("reason"), str) or not repair["reason"].strip():
        raise ValueError(f"Missing repair reason: {label}")
    edits = repair.get("edits")
    if not isinstance(edits, list) or not edits:
        raise ValueError(f"Missing exact repair edits: {label}")
    result = original
    for edit in edits:
        old, new = edit.get("old"), edit.get("new")
        if not isinstance(old, str) or not old or not isinstance(new, str) or edit.get("occurrences") != 1:
            raise ValueError(f"Repair must specify a nonempty old text and exactly one occurrence: {label}")
        before, after = old.encode("utf-8"), new.encode("utf-8")
        if result.count(before) != 1:
            raise ValueError(f"Recorded repair old text does not occur exactly once: {label}")
        result = result.replace(before, after, 1)
    if hashlib.sha256(result).hexdigest() != record["sha256"]:
        raise ValueError(f"Recorded repair result hash mismatch: {label}")
    return result


def verify_provenance(modules: dict[str, Path], root: Path = ROOT) -> dict[str, str]:
    """Verify immutable archives and exact active/reference source origins."""
    catalog_path = root / "provenance/sources.json"
    active_path = root / "provenance/active_source_origins.json"
    rocq_path = root / "provenance/rocq_origins.json"
    catalog = json.loads(catalog_path.read_text(encoding="utf-8"))
    active = json.loads(active_path.read_text(encoding="utf-8"))
    rocq = json.loads(rocq_path.read_text(encoding="utf-8"))
    tracked = {p.relative_to(root).as_posix() for p in modules.values()}
    if set(active) != tracked:
        raise ValueError("Active source provenance inventory differs from the compiled module inventory")
    archives = {}
    records = catalog["sources"]
    for record in records:
        relative = record["archive"]
        if relative in archives:
            raise ValueError(f"Duplicate source archive in provenance: {relative}")
        path = repository_path(root, relative)
        actual = sha256(path)
        if actual != record["sha256"]:
            raise ValueError(f"Historical archive integrity mismatch: {relative}")
        archives[relative] = actual
    actual_archives = {p.relative_to(root).as_posix() for p in (root / "provenance/archives").glob("*.zip")}
    if set(archives) != actual_archives:
        raise ValueError("Historical archive inventory differs from provenance catalog")
    with ExitStack() as stack:
        opened = {name: stack.enter_context(zipfile.ZipFile(repository_path(root, name))) for name in archives}

        def origin_bytes(origin: dict[str, str]) -> bytes:
            if origin["archive"] not in opened:
                raise ValueError(f"Origin archive absent from catalog: {origin['archive']}")
            member = origin["member"]
            if member.startswith("/") or ".." in member.replace("\\", "/").split("/"):
                raise ValueError(f"Unsafe archive member: {member}")
            return opened[origin["archive"]].read(member)

        for relative, record in active.items():
            content = repository_path(root, relative).read_bytes()
            if hashlib.sha256(content).hexdigest() != record["sha256"]:
                raise ValueError(f"Active source integrity mismatch: {relative}")
            if not record["origins"]:
                raise ValueError(f"Active source has no historical origin: {relative}")
            for origin in record["origins"]:
                if apply_recorded_repair(origin_bytes(origin), record, relative) != content:
                    raise ValueError(f"Active source differs from its historical archive member: {relative}")
        actual_rocq = {p.name for p in (root / "reference/rocq").glob("*.v")}
        if set(rocq) != actual_rocq:
            raise ValueError("Rocq reference inventory differs from provenance catalog")
        for filename, origins in rocq.items():
            content = repository_path(root, "reference/rocq/" + filename).read_bytes()
            if not origins:
                raise ValueError(f"Rocq reference has no origin: {filename}")
            digest = hashlib.sha256(content).hexdigest()
            for origin in origins:
                if digest != origin["sha256"] or origin_bytes(origin) != content:
                    raise ValueError(f"Rocq reference differs from historical archive: {filename}")
        containment_path = root / "provenance/concrete_containment.json"
        if containment_path.exists():
            containment = json.loads(containment_path.read_text(encoding="utf-8"))
            target = repository_path(root, containment["target"]).read_bytes()
            if hashlib.sha256(target).hexdigest() != containment["target_sha256"]:
                raise ValueError("Concrete atlas hash differs from containment receipt")
            by_identity = {r["identity"]: r["archive"] for r in records}
            for record in containment["records"]:
                archive = opened[by_identity[record["source_package"]]]
                matches = [name for name in archive.namelist() if name.endswith("/" + record["module"] + ".lean")]
                if len(matches) != 1:
                    raise ValueError(f"Ambiguous concrete precursor origin: {record['source_package']}")
                precursor = archive.read(matches[0])
                if hashlib.sha256(precursor).hexdigest() != record["sha256"] or not target.startswith(precursor):
                    raise ValueError(f"Concrete precursor is not an exact prefix: {record['module']}")
    manifests = {p.relative_to(root).as_posix(): sha256(p) for p in (catalog_path, active_path, rocq_path)}
    if (root / "provenance/concrete_containment.json").exists():
        manifests["provenance/concrete_containment.json"] = sha256(root / "provenance/concrete_containment.json")
    return {**archives, **manifests}


def lean_name(name: str) -> str:
    return ".".join(part if re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", part) else f"«{part}»"
                    for part in name.split("."))


def write_if_changed(path: Path, contents: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if not path.exists() or path.read_text(encoding="utf-8") != contents:
        path.write_text(contents, encoding="utf-8", newline="\n")


def prepare(modules: dict[str, Path]) -> None:
    names = sorted(modules)
    expected_theorems = {
        name: len(re.findall(r"(?m)^\s*(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma)\s+",
                             lean_code(path.read_text(encoding="utf-8-sig"))))
        for name, path in modules.items()
    }
    write_if_changed(ROOT / "lean-toolchain", TOOLCHAIN + "\n")
    write_if_changed(ROOT / "All.lean", "-- Generated by scripts/verify.py; imports every active source module.\n"
                     + "".join(f"import {lean_name(name)}\n" for name in names))
    globs = ",\n    ".join(".one `" + lean_name(name) for name in ["All", *names])
    write_if_changed(ROOT / "lakefile.lean", f'''import Lake
open Lake DSL

package nseFeffermanABCD where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "{MATHLIB}"

@[default_target]
lean_lib NSEFefferman where
  roots := #[`All]
  globs := #[
    {globs}
  ]
''')
    module_names = ",\n    ".join("`" + lean_name(name) for name in names)
    module_thresholds = ",\n    ".join(f"(`{lean_name(name)}, {expected_theorems[name]})" for name in names)
    write_if_changed(ROOT / "scripts" / "KernelAudit.lean", f'''-- Generated by scripts/verify.py. Audit mechanism, not a theorem source.
import All
import Lean.Util.CollectAxioms
import Lean.Elab.Command

open Lean Elab Command

set_option maxRecDepth 10000
set_option maxHeartbeats 0

run_cmd do
  let env ← getEnv
  let projectModules : Array Name := #[
    {module_names}
  ]
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let expectedTheorems : Array (Name × Nat) := #[
    {module_thresholds}
  ]
  for mod in projectModules do
    unless (env.getModuleIdx? mod).isSome do
      throwError "Missing project module in audit environment: {{mod}}"
  let mut declarations : Nat := 0
  let mut theorems : Nat := 0
  let mut perModule : Std.HashMap Name Nat := {{}}
  for (name, ci) in env.constants do
    if let some idx := env.getModuleIdxFor? name then
      if projectModules.contains env.header.moduleNames[idx]! then
        declarations := declarations + 1
        if ci.isUnsafe then
          throwError "Unsafe project declaration: {{name}}"
        if let .axiomInfo _ := ci then
          throwError "Custom axiom declaration: {{name}}"
        let axioms ← collectAxioms name
        for ax in axioms do
          unless allowed.contains ax do
            throwError "Unexpected axiom in {{name}}: {{ax}}"
        if let .thmInfo _ := ci then
          theorems := theorems + 1
          let mod := env.header.moduleNames[idx]!
          perModule := perModule.insert mod (perModule[mod]?.getD 0 + 1)
          logInfo m!"PROJECT_THEOREM_AXIOMS|{{name}}|{{axioms}}"
  for (mod, minimum) in expectedTheorems do
    let actual := perModule[mod]?.getD 0
    if actual < minimum then
      throwError "Theorem audit coverage too small for {{mod}}: {{actual}} < {{minimum}}"
  if theorems < {sum(expected_theorems.values())} then
    throwError "Theorem audit is smaller than the source declaration inventory"
  if declarations == 0 || theorems == 0 then
    throwError "Audit scope was empty"
  logInfo m!"PROJECT_MODULES_CHECKED={{projectModules.size}}"
  logInfo m!"PROJECT_DECLARATIONS_CHECKED={{declarations}}"
  logInfo m!"PROJECT_THEOREMS_CHECKED={{theorems}}"
  logInfo "PROJECT_AXIOM_ALLOWLIST=PASS"
  logInfo "UNCONDITIONAL_FEFFERMAN_ENDPOINTS=NOT_ESTABLISHED"
''')


def run(command: list[str], log: Path) -> str:
    log.parent.mkdir(parents=True, exist_ok=True)
    print("RUN " + " ".join(command), flush=True)
    with log.open("w", encoding="utf-8", newline="\n") as stream:
        proc = subprocess.Popen(command, cwd=ROOT, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, text=True,
                                encoding="utf-8", errors="replace")
        assert proc.stdout is not None
        for line in proc.stdout:
            stream.write(line)
            stream.flush()
            print(line, end="", flush=True)
        result = proc.wait()
    text = log.read_text(encoding="utf-8")
    if result:
        raise RuntimeError(f"Command exited {result}; see {log.relative_to(ROOT)}")
    return text


def verify_manifest() -> None:
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    mathlib = [p for p in manifest.get("packages", []) if p.get("name") == "mathlib"]
    if len(mathlib) != 1 or mathlib[0].get("rev") != MATHLIB:
        raise ValueError("Mathlib lockfile is not pinned to the audited revision")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prepare-only", action="store_true", help="Generate build/audit files and scan sources")
    parser.add_argument("--fetch-cache", action="store_true", help="Download compatible Mathlib cached artifacts before building")
    args = parser.parse_args()
    out = ROOT / "artifacts"
    receipt_path = out / "anchor-receipt.json"
    if not args.prepare_only and receipt_path.exists():
        receipt_path.unlink()  # A failed new verification must not leave an old PASS receipt.
    modules = sources()
    if len(modules) < 59:
        raise ValueError(f"Expected at least 59 recovered modules, found {len(modules)}")
    graph = check_sources(modules)
    provenance_hashes = verify_provenance(modules)
    prepare(modules)
    print(f"PROJECT_SOURCES_SCANNED={len(modules)}")
    print("LAYER_A_PHYSICS_FIREWALL=PASS")
    print("HISTORICAL_ARCHIVES_AND_SOURCE_ORIGINS=PASS")
    if args.prepare_only:
        return 0
    out.mkdir(exist_ok=True)
    version = run(["lean", "--version"], out / "lean-version.log").strip()
    if not re.search(r"\bversion 4\.33\.0(?:,|\s|\))", version):
        raise ValueError(f"Expected Lean 4.33.0, received {version}")
    if not (ROOT / "lake-manifest.json").exists():
        run(["lake", "update"], out / "dependencies.log")
    verify_manifest()
    if args.fetch_cache:
        run(["lake", "exe", "cache", "get"], out / "mathlib-cache.log")
    run(["lake", "build"], out / "build.log")
    audit = run(["lake", "env", "lean", "scripts/KernelAudit.lean"], out / "axioms.log")
    if "PROJECT_AXIOM_ALLOWLIST=PASS" not in audit:
        raise ValueError("Environment axiom audit produced no success marker")
    counts = {}
    for key in ("MODULES", "DECLARATIONS", "THEOREMS"):
        found = re.findall(rf"PROJECT_{key}_CHECKED=(\d+)", audit)
        if len(found) != 1:
            raise ValueError(f"Missing or duplicate audit count for {key}")
        counts[key.lower()] = int(found[0])
    if counts["modules"] != len(modules):
        raise ValueError("Compiled audit module coverage mismatch")
    printed = len(re.findall(r"PROJECT_THEOREM_AXIOMS\|", audit))
    if printed != counts["theorems"]:
        raise ValueError("Theorem audit output coverage mismatch")
    src_hashes = {p.relative_to(ROOT).as_posix(): sha256(p) for p in modules.values()}
    settings = {p: sha256(ROOT / p) for p in ("lean-toolchain", "lakefile.lean", "lake-manifest.json",
                                              "All.lean", "scripts/verify.py", "scripts/KernelAudit.lean")}
    artifacts = {}
    for name in modules:
        p = ROOT / ".lake/build/lib/lean" / Path(*name.split(".")).with_suffix(".olean")
        if not p.is_file() or p.stat().st_size == 0:
            raise ValueError(f"Missing compiled module artifact: {p}")
        artifacts[p.relative_to(ROOT).as_posix()] = sha256(p)
    receipt = {
        "schema": 1,
        "anchor": "NSE_FEFFERMAN_ABCD_RECOVERED_v0_1_0",
        "created_at": datetime.now(timezone.utc).isoformat(),
        "status": "COMPILED_AXIOM_AUDITED_CONDITIONAL_ARCHITECTURE",
        "physical_endpoints": {x: "OPEN" for x in "ABCD"},
        "lean_version": version,
        "platform": {"system": platform.system(), "machine": platform.machine()},
        "mathlib_revision": MATHLIB,
        "counts": counts,
        "allowed_axioms": ["propext", "Classical.choice", "Quot.sound"],
        "source_sha256": src_hashes,
        "settings_sha256": settings,
        "provenance_sha256": provenance_hashes,
        "dependency_graph": graph,
        "compiled_artifact_sha256": artifacts,
        "logs_sha256": {p.name: sha256(p) for p in (out / "build.log", out / "axioms.log")},
    }
    receipt["integrity_fingerprint"] = json_hash({"sources": src_hashes, "settings": settings,
                                                  "provenance": provenance_hashes,
                                                  "lean": version, "platform": receipt["platform"]})
    receipt_path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print("ANCHOR_RECEIPT=artifacts/anchor-receipt.json")
    print("PROJECT_BUILD=PASS")
    print("PROJECT_AXIOM_AUDIT=PASS")
    print("FEFFERMAN_A_B_C_D_PHYSICAL_ENDPOINTS=OPEN")
    return 0


if __name__ == "__main__":
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    try:
        raise SystemExit(main())
    except (OSError, ValueError, RuntimeError) as exc:
        print(f"VERIFICATION_FAILED={exc}", file=sys.stderr)
        raise SystemExit(1)
