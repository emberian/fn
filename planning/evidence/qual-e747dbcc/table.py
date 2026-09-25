import hashlib, re, sys
from pathlib import Path
L = Path("/tank/fn/scratch/qual-e747dbcc/logs")
for p in sorted(L.glob("*.log")):
    t = p.read_text("utf-8", "replace")
    ran = re.search(r"^Ran (\d+) tests? in ([\d.]+)s", t, re.M)
    n = int(ran.group(1)) if ran else 0
    wall = re.search(r"# rc=(-?\d+) wall=([\d.]+)", t)
    fail = sum(int(x) for x in re.findall(r"failures=(\d+)", t.splitlines()[-3] if False else " ".join(re.findall(r"^FAILED \(([^)]*)\)", t, re.M))))
    errs = sum(int(x) for x in re.findall(r"errors=(\d+)", " ".join(re.findall(r"^FAILED \(([^)]*)\)", t, re.M))))
    skips = sum(int(x) for x in re.findall(r"skipped=(\d+)", " ".join(re.findall(r"^(?:OK|FAILED) \(([^)]*)\)", t, re.M))))
    failing_tests = len(set(re.findall(r"^(?:FAIL|ERROR): (\S+) \(", t, re.M)))
    sha = hashlib.sha256(p.read_bytes()).hexdigest()[:16]
    rc = wall.group(1) if wall else "?"
    print("| {} | {} | {} | {} | {} | {} | {} | `{}` |".format(
        p.name[:-4], n, n - failing_tests - skips if n else 0, "{} ({} f, {} e)".format(failing_tests, fail, errs) if failing_tests else 0,
        skips, wall.group(2) if wall else "-", rc, sha))
