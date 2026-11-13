#!/usr/bin/env python3
"""Offline FS4 release integrity check, with opt-in capture and Lean replay.

Why: bind the published interface to complete source coverage and raw Lean output.
Criterion: exact pinned dependencies, four signatures, and foundational axioms only.
Known false positives: unusual Lean output formatting and commented-out forbidden
source tokens (comments and strings are lexically removed before source checks).
This standalone public-release audit is not registered in AImath run_checks.

Evidence schema version 1 (UTF-8 JSON): version, created_utc (UTC ISO timestamp),
toolchain, lean_version, mathlib_rev, mathlib_manifest_sha256,
mathlib_manifest (the nested manifest object), mathlib_manifest_raw (its exact
UTF-8 text, permitting offline hash verification), dependencies_at_run (package name
-> {rev, clean}), source_sha256 (relative POSIX path -> SHA256), output_sha256
(the two log paths -> SHA256), commands ([{argv, returncode, output}]),
signatures (exact FQN -> whitespace-normalized #check text), axioms (exact FQN
-> sorted unique axiom names). output is raw combined stdout/stderr decoded as
strict UTF-8; log hashes cover original bytes. No cryptographic authenticity is
claimed: this checks consistency, not provenance against a trusted signature.

Usage: python audit/check_fs4_release.py [--self-test | --capture | --lean]
Default is offline (no subprocesses). Capture requires FS4_STAGING_SERVER=1.
Replay copies inputs into ignored build/fs4-replay and never writes frozen logs
or evidence. Both live modes require installed, pinned dependency git checkouts.
"""

import argparse
import copy
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

MATHLIB_REV = "852d20a84581aeba8527bd01d0be361d8c0e71c0"
TOOLCHAIN = "leanprover/lean4:v4.34.0-rc2"
PREFIX = "Pphi2Clean.Continuum."
NAMES = tuple(PREFIX + name for name in (
    "fs4PhysicalFiniteMarginal_eq_resolventTarget",
    "fs4HminusFour_probabilityMeasure_ext_of_real_finite_marginals",
    "fs4Periodic_subsequence_limit_eq_free",
    "fs4PeriodicFixedVolume_weak_tendsto_free",
))
ALLOWLIST = {"propext", "Classical.choice", "Quot.sound"}
QUERY = "audit/fs4_periodic_raw_lift_interface.lean"
EVIDENCE = "docs/fs4/release_evidence.json"
LOGS = ("docs/fs4/build.log", "docs/fs4/theorems.log")
INPUTS = ("AImathPPhi2Clean.lean", "lakefile.lean", "lake-manifest.json", "lean-toolchain", QUERY)
HEX = re.compile(r"[0-9a-f]{40}\Z")
HASH = re.compile(r"[0-9a-f]{64}\Z")


class Invalid(ValueError):
    """A failed release invariant."""


def require(condition, message):
    if not condition:
        raise Invalid(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def load_json(path):
    return json.loads(path.read_text(encoding="utf-8"))


def normalized(text):
    return " ".join(text.split())


def lean_code(text, keep_strings=False):
    """Remove Lean nested comments and strings while retaining token boundaries."""
    out = []
    i = 0
    depth = 0
    while i < len(text):
        pair = text[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                i += 2
            elif pair == "-/":
                depth -= 1
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif pair == "/-":
            depth = 1
            out.append(" ")
            i += 2
        elif pair == "--":
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
            out.append(" ")
        elif text[i] == '"':
            start = i
            i += 1
            while i < len(text) and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            require(i < len(text), "unterminated Lean string")
            i += 1
            out.append(text[start:i] if keep_strings else " ")
        else:
            out.append(text[i])
            i += 1
    require(depth == 0, "unterminated Lean comment")
    return "".join(out)


def check_source(text, path):
    code = lean_code(text)
    require(not re.search(r"(?<![\w'])\b(?:axiom|sorry|sorryAx|admit)\b", code),
            "custom axiom or incomplete proof in " + path)


def source_hashes(root):
    library = root / "AImathPPhi2Clean"
    require(library.is_dir(), "missing AImathPPhi2Clean source directory")
    sources = sorted(p.relative_to(root).as_posix() for p in library.rglob("*.lean"))
    require(sources, "empty Lean library")
    paths = sources + list(INPUTS)
    result = {}
    for relative in paths:
        data = (root / relative).read_bytes()
        if relative.endswith(".lean") and relative != "lakefile.lean":
            check_source(data.decode("utf-8"), relative)
        result[relative] = digest(data)
    return result


def package_revs(manifest):
    require(isinstance(manifest, dict) and isinstance(manifest.get("packages"), list),
            "invalid Lake manifest")
    result = {}
    for package in manifest["packages"]:
        require(isinstance(package, dict), "invalid dependency record")
        name, rev = package.get("name"), package.get("rev")
        require(isinstance(name, str) and re.fullmatch(r"[A-Za-z0-9_-]+", name),
                "unsafe dependency name")
        require(name not in result and isinstance(rev, str) and HEX.fullmatch(rev),
                "dependency must have unique name and full git revision: " + name)
        require(package.get("type") == "git", "non-git dependency: " + name)
        result[name] = rev
    require(result.get("mathlib") == MATHLIB_REV, "Mathlib manifest pin mismatch")
    return result


def check_nested(nested, project):
    require(isinstance(nested, dict) and isinstance(nested.get("packages"), list),
            "invalid Mathlib nested manifest")
    seen = set()
    for package in nested["packages"]:
        name, rev = package.get("name"), package.get("rev")
        require(name not in seen and name in project and project[name] == rev,
                "Mathlib nested dependency mismatch: " + str(name))
        seen.add(name)


def check_query(text):
    code = lean_code(text)
    checks = re.findall(r"#check\s+@([\w.]+)", code)
    prints = re.findall(r"#print\s+axioms\s+([\w.]+)", code)
    require(len(checks) == 4 and set(checks) == set(NAMES), "query #check FQNs mismatch")
    require(len(prints) == 4 and set(prints) == set(NAMES), "query #print axioms FQNs mismatch")
    require(len(re.findall(r"#check\b", code)) == 4 and
            len(re.findall(r"#print\b", code)) == 4, "unexpected query commands")
    require(re.search(r"\bexample\b[\s\S]*?:[\s\S]+?:=", code),
            "query lacks a typed example")
    example = code[code.rfind("example"):]
    require(NAMES[-1] in example or NAMES[-1].split(".")[-1] in example,
            "final example does not invoke final theorem")


def parse_transcript(text):
    require(not re.search(r"\bsorryAx\b|\bsorry\b|\berror\s*:|\bpanic\b", text, re.I),
            "Lean transcript contains errors or sorry")
    # #check @FQN emits the fully qualified constant followed by its entire type;
    # #print axioms emits a quoted FQN and possibly a multiline bracketed list.
    ax_pattern = re.compile(
        r"['\u2018]([\w.]+)['\u2019]\s+(?:depends on axioms:\s*\[([^\]]*)\]|"
        r"does not depend on any axioms)", re.S)
    ax_records = list(ax_pattern.finditer(text))
    require(len(ax_records) == 4, "expected exactly four axiom records")
    axioms = {}
    for match in ax_records:
        name = match.group(1)
        require(name in NAMES and name not in axioms, "missing/duplicate/unexpected axiom FQN")
        names = [item.strip() for item in (match.group(2) or "").split(",") if item.strip()]
        require(len(names) == len(set(names)), "duplicate axiom in footprint")
        require(set(names) <= ALLOWLIST, "non-foundational axioms for " + name)
        axioms[name] = sorted(names)
    masked = ax_pattern.sub("\n", text)
    starts = list(re.finditer(r"(?m)^@?((?:Pphi2Clean\.)[\w.]+)(?=\s|\.{)", masked))
    require(len(starts) == 4, "expected exactly four #check signatures")
    signatures = {}
    for i, start in enumerate(starts):
        name = start.group(1)
        require(name in NAMES and name not in signatures, "missing/duplicate/unexpected signature FQN")
        end = starts[i + 1].start() if i + 1 < len(starts) else len(masked)
        signature = normalized(masked[start.start():end]).lstrip("@")
        require(signature.startswith(name) and ":" in signature and len(signature) > len(name) + 3,
                "empty or malformed signature: " + name)
        signatures[name] = signature
    require(set(signatures) == set(axioms) == set(NAMES), "incomplete theorem records")
    return signatures, axioms


def validate_records(evidence, transcript):
    signatures, axioms = parse_transcript(transcript)
    require(evidence.get("signatures") == signatures, "signature evidence differs from transcript")
    require(evidence.get("axioms") == axioms, "axiom evidence differs from transcript")


def check_hashes(recorded, current):
    require(isinstance(recorded, dict) and recorded == current,
            "source coverage or hash mismatch (missing, added, or altered input)")


def configuration(root):
    require((root / "lean-toolchain").read_text(encoding="utf-8").strip() == TOOLCHAIN,
            "toolchain mismatch")
    raw = lean_code((root / "lakefile.lean").read_text(encoding="utf-8"), keep_strings=True)
    require(re.search(r'\brequire\s+mathlib\b[\s\S]*?\bfrom\s+git\s+"[^"\n]+"\s*@\s*"' + MATHLIB_REV + r'"', raw),
            "lakefile must require Mathlib at exact revision")
    check_query((root / QUERY).read_text(encoding="utf-8"))
    return package_revs(load_json(root / "lake-manifest.json"))


def expected_commands(lake):
    return [[lake, "build", "AImathPPhi2Clean"],
            [lake, "env", "lean", QUERY], [lake, "env", "lean", "--version"]]


def verify(root):
    project = configuration(root)
    evidence = load_json(root / EVIDENCE)
    require(evidence.get("version") == 1, "unsupported evidence version")
    created = datetime.fromisoformat(evidence["created_utc"].replace("Z", "+00:00"))
    require(created.utcoffset() is not None and created.utcoffset().total_seconds() == 0,
            "created_utc must be UTC")
    require(evidence.get("toolchain") == TOOLCHAIN and evidence.get("mathlib_rev") == MATHLIB_REV,
            "evidence toolchain or Mathlib mismatch")
    require(re.search(r"\b4\.34\.0-rc2\b", evidence.get("lean_version", "")),
            "Lean version mismatch")
    deps = evidence.get("dependencies_at_run")
    require(isinstance(deps, dict) and set(deps) == set(project), "dependency coverage mismatch")
    for name, rev in project.items():
        require(deps[name] == {"rev": rev, "clean": True}, "unpinned/dirty dependency: " + name)
    nested = evidence.get("mathlib_manifest")
    check_nested(nested, project)
    nested_hash = evidence.get("mathlib_manifest_sha256", "")
    require(isinstance(nested_hash, str) and HASH.fullmatch(nested_hash), "invalid nested manifest hash")
    nested_raw = evidence.get("mathlib_manifest_raw")
    require(isinstance(nested_raw, str) and digest(nested_raw.encode("utf-8")) == nested_hash,
            "frozen Mathlib nested manifest hash mismatch")
    require(json.loads(nested_raw) == nested, "frozen Mathlib nested manifest object mismatch")
    nested_path = root / ".lake/packages/mathlib/lake-manifest.json"
    if nested_path.is_file():
        require(digest(nested_path.read_bytes()) == nested_hash, "Mathlib nested manifest hash mismatch")
        require(load_json(nested_path) == nested, "Mathlib nested manifest content mismatch")
    check_hashes(evidence.get("source_sha256"), source_hashes(root))
    outputs = {path: (root / path).read_bytes() for path in LOGS}
    require(evidence.get("output_sha256") == {p: digest(b) for p, b in outputs.items()},
            "output hash mismatch")
    commands = evidence.get("commands")
    require(isinstance(commands, list) and len(commands) == 3, "expected build/query/version commands")
    require(isinstance(commands[0].get("argv"), list) and commands[0]["argv"], "invalid command argv")
    expected = expected_commands(commands[0]["argv"][0])
    for i, command in enumerate(commands):
        require(command.get("argv") == expected[i] and command.get("returncode") == 0,
                "command or returncode mismatch")
        expected_output = outputs[LOGS[i]].decode("utf-8") if i < 2 else evidence["lean_version"]
        require(command.get("output") == expected_output, "raw command output mismatch")
    require(not re.search(r"\bsorryAx\b|\berror\s*:", outputs[LOGS[0]].decode("utf-8"), re.I),
            "build log contains error/sorryAx")
    validate_records(evidence, outputs[LOGS[1]].decode("utf-8"))
    return evidence


def run(argv, root):
    process = subprocess.run(argv, cwd=root, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                             check=False)
    output = process.stdout.decode("utf-8")
    require(process.returncode == 0,
            "command failed: " + repr(argv) + "\n" + output)
    return {"argv": argv, "returncode": process.returncode, "output": output}, process.stdout


def installed_dependencies(root, project):
    result = {}
    for name, rev in project.items():
        path = root / ".lake/packages" / name
        top, _ = run(["git", "rev-parse", "--show-toplevel"], path)
        require(Path(top["output"].strip()).resolve() == path.resolve(),
                "dependency is not its own git checkout: " + name)
        head, _ = run(["git", "rev-parse", "HEAD"], path)
        status, _ = run(["git", "status", "--porcelain", "--untracked-files=all"], path)
        require(head["output"].strip() == rev, "installed dependency HEAD mismatch: " + name)
        require(not status["output"].strip(), "dirty installed dependency: " + name)
        result[name] = {"rev": rev, "clean": True}
    nested_path = root / ".lake/packages/mathlib/lake-manifest.json"
    nested = load_json(nested_path)
    check_nested(nested, project)
    return result, nested, digest(nested_path.read_bytes())


def lake_executable():
    lake = os.environ.get("LAKE") or shutil.which("lake")
    require(bool(lake), "lake unavailable: set LAKE or add lake to PATH")
    return lake


def capture(root):
    require(os.environ.get("FS4_STAGING_SERVER") == "1",
            "capture is staging-server only; set FS4_STAGING_SERVER=1 explicitly there")
    project = configuration(root)
    sources = source_hashes(root)
    dependencies, nested, nested_hash = installed_dependencies(root, project)
    commands, outputs = [], []
    for argv in expected_commands(lake_executable()):
        record, raw = run(argv, root)
        commands.append(record)
        outputs.append(raw)
    require(source_hashes(root) == sources, "sources changed during capture")
    require(installed_dependencies(root, project) == (dependencies, nested, nested_hash),
            "dependencies changed during capture")
    signatures, axioms = parse_transcript(commands[1]["output"])
    require(re.search(r"\b4\.34\.0-rc2\b", commands[2]["output"]), "actual Lean version mismatch")
    evidence = {
        "version": 1, "created_utc": datetime.now(timezone.utc).isoformat(),
        "toolchain": TOOLCHAIN, "lean_version": commands[2]["output"],
        "mathlib_rev": MATHLIB_REV, "mathlib_manifest_sha256": nested_hash,
        "mathlib_manifest": nested,
        "mathlib_manifest_raw": (root / ".lake/packages/mathlib/lake-manifest.json").read_bytes().decode("utf-8"),
        "dependencies_at_run": dependencies,
        "source_sha256": sources,
        "output_sha256": {path: digest(raw) for path, raw in zip(LOGS, outputs)},
        "commands": commands, "signatures": signatures, "axioms": axioms,
    }
    for path, raw in zip(LOGS, outputs):
        (root / path).parent.mkdir(parents=True, exist_ok=True)
        (root / path).write_bytes(raw)
    (root / EVIDENCE).write_bytes((json.dumps(evidence, indent=2, ensure_ascii=True) + "\n").encode("utf-8"))
    verify(root)


def replay(root):
    frozen = verify(root)
    paths = list(frozen["source_sha256"]) + list(LOGS) + [EVIDENCE]
    before = {path: digest((root / path).read_bytes()) for path in paths}
    project = configuration(root)
    dependencies = installed_dependencies(root, project)
    destination = root / "build/fs4-replay"
    ignored = subprocess.run(["git", "check-ignore", "--quiet", "build/fs4-replay/"], cwd=root,
                             check=False)
    require(ignored.returncode == 0, "build/fs4-replay must be git-ignored before replay")
    require(not destination.is_symlink(), "replay directory must not be a symlink")
    destination.mkdir(parents=True, exist_ok=True)
    require(destination.resolve().is_relative_to(root.resolve()), "replay directory escapes checkout")
    # Start each replay in a new subdirectory; never delete an earlier replay.
    import tempfile
    workspace = Path(tempfile.mkdtemp(prefix="run-", dir=destination))
    try:
        for path in frozen["source_sha256"]:
            target = workspace / path
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(root / path, target)
        (workspace / ".lake").mkdir(exist_ok=True)
        os.symlink((root / ".lake/packages").resolve(), workspace / ".lake/packages", target_is_directory=True)
        for index, argv in enumerate(expected_commands(lake_executable())):
            record, raw = run(argv, workspace)
            (workspace / ("build.log", "theorems.log", "lean-version.log")[index]).write_bytes(raw)
            if index == 1:
                validate_records(frozen, record["output"])
            if index == 2:
                require(record["output"] == frozen["lean_version"], "replay Lean version differs")
        require(installed_dependencies(root, project) == dependencies, "dependencies changed during replay")
    finally:
        after = {path: digest((root / path).read_bytes()) for path in paths}
        require(before == after, "frozen inputs or evidence changed during replay")
    verify(root)
    print("Replay outputs: " + str(workspace))


def self_test():
    transcript = "\n".join(
        name + "\n  (x : Nat) : x = x\n'" + name +
        "' depends on axioms: [propext,\n Classical.choice, Quot.sound]" for name in NAMES)
    signatures, axioms = parse_transcript(transcript)
    evidence = {"signatures": signatures, "axioms": axioms}
    validate_records(evidence, transcript)
    check_source('/- axiom hidden /- sorry -/ -/ def x := "sorry" -- axiom\n', "control")
    controls = []
    bad = copy.deepcopy(evidence)
    bad["signatures"][NAMES[0]] += " altered"
    controls.append(("altered signature", lambda: validate_records(bad, transcript)))
    controls.append(("custom axiom footprint", lambda: parse_transcript(transcript.replace("propext", "Custom.bad", 1))))
    controls.append(("missing FQN", lambda: parse_transcript(transcript.replace(NAMES[0], "Other.missing"))))
    controls.append(("custom source axiom", lambda: check_source("axiom fake : False", "control")))
    controls.append(("sorry source", lambda: check_source("theorem fake : False := by sorry", "control")))
    controls.append(("missing source", lambda: check_hashes({"A.lean": "a"}, {"A.lean": "a", "B.lean": "b"})))
    controls.append(("transcript error", lambda: parse_transcript(transcript + "\nerror: bad")))
    for name, action in controls:
        try:
            action()
        except Invalid:
            print("PASS negative control: " + name)
        else:
            raise Invalid("negative control accepted: " + name)
    print("PASS parser positive controls and all negative controls")


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    modes = parser.add_mutually_exclusive_group()
    modes.add_argument("--capture", action="store_true", help="capture fresh evidence on staging only")
    modes.add_argument("--lean", action="store_true", help="isolated Lean replay; leave frozen evidence unchanged")
    modes.add_argument("--self-test", action="store_true", help="run synthetic positive and mutation-negative controls")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    try:
        if args.self_test:
            self_test()
        elif args.capture:
            capture(root)
            print("PASS fresh release evidence captured and verified")
        elif args.lean:
            replay(root)
            print("PASS Lean replay and frozen evidence integrity")
        else:
            verify(root)
            print("PASS offline release integrity (no Lean execution)")
    except (Invalid, OSError, ValueError, KeyError, TypeError, AttributeError) as error:
        print("FAIL: " + str(error), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
