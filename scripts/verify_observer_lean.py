"""Recheck the observer interface against Paper I's local compiled imports."""
from pathlib import Path
import os
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
BUILD = ROOT / "build"
SOURCE = ROOT / "observer/Rule110Observer.lean"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def main():
    required = (ROOT / "lean-toolchain").read_text().strip().split(":v")[-1]
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    if not re.search(r"\bversion " + re.escape(required) + r"[,)]", version):
        raise SystemExit(f"Expected Lean {required}, got {version}")
    expected = re.findall(r"^#print axioms (\w+)$", SOURCE.read_text(), re.M)
    if len(set(expected)) != 11 or len(expected) != 11:
        raise SystemExit("Expected eleven distinct observer declarations")
    env = dict(os.environ, LEAN_PATH=str(BUILD))
    run = subprocess.run(["lean", "-j1", str(SOURCE)], cwd=ROOT, env=env,
                         text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    BUILD.mkdir(exist_ok=True)
    log = BUILD / "observer-axioms.log"
    log.write_text(version + "\n" + run.stdout)
    run.check_returncode()
    found = re.findall(r"^'Rule110Observer\.(\w+)' depends on axioms: \[([^\]]*)\]$",
                       run.stdout, re.M)
    if [name for name, _ in found] != expected or "sorryAx" in run.stdout:
        raise SystemExit(f"Unexpected observer axiom reports in {log}")
    for name, axioms in found:
        if set(filter(None, axioms.split(", "))) - ALLOWED:
            raise SystemExit(f"Unexpected axiom for {name}: {axioms}")
    print(f"Checked {len(found)} observer axiom reports against {required}. See {log}")


if __name__ == "__main__":
    main()
