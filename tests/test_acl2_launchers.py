"""Every ACL2 fn starts goes through the machine's pool (PKT-162).

`tools/acl2_slots.py` is the one launch path: `run` and `popen` take this
process tree's slot and give the child the certification environment and
the heap cap.  On dev at 483987b1 eleven launchers started a bare `acl2`
outside it -- the auth-secret, stx and reader sessions, host_check, the
simulator, the certificate-alist reader, the proof-artifact loader, and four
test drivers (the campaign model bridge, the owner feed-connection check,
the feed-journal BookBridge, the auth-admin fidelity driver) -- each with
SBCL's 32,000 MB dynamic space on the laptop unless the shell exported a
cap; tests/interop_cbor.py capped its heap and took no slot
(harness-repair, 2026-09-25).

The rule is read from the code: a `subprocess` launch whose program is an
ACL2 executable (its first argv element names `acl2`) is refused unless it
is `acl2_slots.run`/`acl2_slots.popen` or sits inside `with
acl2_slots.tree_slot(...)`.  `tools/acl2` (the `ld` wrapper) takes its slot
itself and is the pool's own implementation.  Native images (`fn-host`,
`FN_NATIVE_HOST`) are not ACL2 sessions and run on hbox under a cgroup
memory limit; this rule does not cover them.  Its blind spot: a program
held in a variable whose spelling does not say `acl2` (interop_cbor's
`executable` was one; it now uses `acl2_slots.popen`).
"""

from __future__ import annotations

import ast
import fcntl
import os
from pathlib import Path
import re
import stat
import subprocess
import sys
import tempfile
import textwrap
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
import acl2_slots  # noqa: E402

LAUNCHES = {"run", "Popen", "check_output", "call", "check_call"}
POOLED_CONTEXTS = {"tree_slot", "slot"}
# The pool's own implementation launches ACL2 after taking its slot.
IMPLEMENTATION = {"tools/acl2", "tools/acl2_slots.py"}


def _pooled_with(node: ast.With) -> bool:
    for item in node.items:
        expression = item.context_expr
        if (isinstance(expression, ast.Call) and isinstance(expression.func, ast.Attribute)
                and expression.func.attr in POOLED_CONTEXTS
                and isinstance(expression.func.value, ast.Name)
                and expression.func.value.id == "acl2_slots"):
            return True
    return False


def _assignments(tree: ast.AST) -> dict[str, list[ast.expr]]:
    """Every value assigned to each plain name anywhere in the module."""
    values: dict[str, list[ast.expr]] = {}
    for node in ast.walk(tree):
        if isinstance(node, ast.Assign):
            for target in node.targets:
                if isinstance(target, ast.Name):
                    values.setdefault(target.id, []).append(node.value)
        elif isinstance(node, (ast.AnnAssign, ast.NamedExpr)) and node.value is not None \
                and isinstance(node.target, ast.Name):
            values.setdefault(node.target.id, []).append(node.value)
    return values


def _argv_list(expression: ast.expr, values, depth: int = 0) -> ast.List | None:
    """The literal list an argv expression is, through names and `list + x`."""
    if depth > 4:
        return None
    if isinstance(expression, ast.List):
        return expression
    if isinstance(expression, ast.BinOp) and isinstance(expression.op, ast.Add):
        return _argv_list(expression.left, values, depth + 1)
    if isinstance(expression, ast.Name):
        for value in values.get(expression.id, []):
            found = _argv_list(value, values, depth + 1)
            if found is not None and found.elts:
                return found
    return None


def _program_texts(element: ast.expr, values, depth: int = 0) -> list[str]:
    """The program element's own text and what each name in it is assigned."""
    texts = [ast.unparse(element)]
    if depth < 4:
        # Every name the element reads (`program`, `str(binary)`,
        # `Path(exe).resolve()`), judged by what the module assigns it.
        for name in {node.id for node in ast.walk(element) if isinstance(node, ast.Name)}:
            for value in values.get(name, []):
                texts += _program_texts(value, values, depth + 1)
    return texts


def _is_acquire(call: ast.Call, acquirers: set[str]) -> bool:
    function = call.func
    if (isinstance(function, ast.Attribute) and function.attr == "acquire_tree_slot"
            and isinstance(function.value, ast.Name) and function.value.id == "acl2_slots"):
        return True
    return isinstance(function, ast.Name) and function.id in acquirers


def _slot_acquirers(tree: ast.AST) -> set[str]:
    """Names that are acl2_slots.acquire_tree_slot: an alias or a function calling it."""
    names: set[str] = set()
    for node in ast.walk(tree):
        if (isinstance(node, ast.Assign) and isinstance(node.value, ast.Attribute)
                and node.value.attr == "acquire_tree_slot"
                and isinstance(node.value.value, ast.Name) and node.value.value.id == "acl2_slots"):
            names |= {target.id for target in node.targets if isinstance(target, ast.Name)}
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and any(
                isinstance(call, ast.Call) and _is_acquire(call, names)
                for call in ast.walk(node)):
            names.add(node.name)
    return names


def _acquires(function: ast.AST, acquirers: set[str]) -> bool:
    """A function that takes the tree slot itself (acquire/release, not `with`)."""
    return any(isinstance(call, ast.Call) and _is_acquire(call, acquirers)
               for call in ast.walk(function))


def unpooled_launches(source: str, filename: str = "<source>") -> list[tuple[int, str]]:
    """(line, program) for every ACL2 launch outside the pool.

    The argv may be a literal list or a name bound to one (`command = [...]`,
    `command = [...] + args`); its first element may be a literal or a name,
    and a name is judged by every value the module assigns it, so an ACL2
    path held in `program = os.environ["FN_ACL2"]` is caught (PKT-258).
    """
    tree = ast.parse(source, filename)
    found: list[tuple[int, str]] = []
    values = _assignments(tree)
    acquirers = _slot_acquirers(tree)

    def visit(node: ast.AST, pooled: bool) -> None:
        if isinstance(node, ast.With) and _pooled_with(node):
            pooled = True
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)) and _acquires(node, acquirers):
            pooled = True
        if isinstance(node, ast.Call) and not pooled:
            function = node.func
            name = (function.attr if isinstance(function, ast.Attribute)
                    else function.id if isinstance(function, ast.Name) else "")
            through_pool = (isinstance(function, ast.Attribute)
                            and isinstance(function.value, ast.Name)
                            and function.value.id == "acl2_slots")
            argv = _argv_list(node.args[0], values) if (name in LAUNCHES and not through_pool
                                                          and node.args) else None
            if argv is not None and argv.elts:
                texts = _program_texts(argv.elts[0], values)
                if any(re.search(r"acl2", text, re.IGNORECASE) and "tools" not in text
                       for text in texts):
                    found.append((node.lineno, " = ".join(dict.fromkeys(texts))))
        for child in ast.iter_child_nodes(node):
            visit(child, pooled)

    visit(tree, False)
    return found


def python_sources() -> list[Path]:
    paths = [ROOT / "tools" / "acl2"]
    for directory in ("tools", "tests", "bin"):
        paths.extend(sorted((ROOT / directory).rglob("*.py")))
    return [path for path in paths if path.is_file()]


class LauncherRuleTests(unittest.TestCase):
    def test_no_acl2_starts_outside_the_pool(self):
        offenders = []
        for path in python_sources():
            relative = path.relative_to(ROOT).as_posix()
            if relative in IMPLEMENTATION:
                continue
            try:
                source = path.read_text(encoding="utf-8")
                launches = unpooled_launches(source, relative)
            except (SyntaxError, UnicodeDecodeError):
                continue
            offenders.extend(f"{relative}:{line}: {program}" for line, program in launches)
        self.assertEqual(offenders, [])

    def test_the_rule_finds_every_spelling_of_a_bare_launch(self):
        # Teeth: the shapes the eleven launchers had at 483987b1.
        for source in (
                'subprocess.Popen([env.get("FN_ACL2", "acl2")], stdin=PIPE)',
                "subprocess.run([str(acl2)], input=b'')",
                "result = run([str(acl2)], cwd=root)",
                "subprocess.run([str(ACL2)], input=driver)"):
            self.assertEqual(len(unpooled_launches(source)), 1, source)

    def test_an_acl2_path_in_a_variable_is_caught(self):
        # PKT-258: the program, or the whole argv, held in a name that does
        # not say acl2.
        for source in (
                'program = os.environ["FN_ACL2"]\nsubprocess.Popen([program], stdin=PIPE)',
                'exe = shutil.which("acl2")\ncommand = [exe, "--quiet"]\nsubprocess.run(command)',
                'binary = Path(os.environ.get("FN_ACL2", "saved_acl2"))\n'
                'argv = [str(binary)] + extra\nsubprocess.check_call(argv)',
                'def start(cfg):\n    image = cfg.acl2_image\n    return subprocess.Popen([image])'):
            self.assertEqual(len(unpooled_launches(source)), 1, source)

    def test_an_explicit_tree_slot_acquisition_pools_its_function(self):
        # run_store's bridge takes the slot with an alias, not a `with`.
        pooled = ('_take = acl2_slots.acquire_tree_slot\n'
                  'def start(env):\n    _take("bridge")\n'
                  '    command = [str(resolve_acl2(env))]\n    return subprocess.Popen(command)')
        self.assertEqual(unpooled_launches(pooled), [])
        direct = ('def start(env):\n    acl2_slots.acquire_tree_slot("x")\n'
                  '    return subprocess.Popen([env["FN_ACL2"]])')
        self.assertEqual(unpooled_launches(direct), [])
        elsewhere = ('_take = acl2_slots.acquire_tree_slot\n'
                     'def other():\n    _take("x")\n'
                     'def start(env):\n    command = [str(resolve_acl2(env))]\n'
                     '    return subprocess.Popen(command)')
        self.assertEqual(len(unpooled_launches(elsewhere)), 1)

    def test_the_pooled_spellings_pass(self):
        for source in (
                'acl2_slots.popen([os.environ.get("FN_ACL2", "acl2")], "label")',
                "acl2_slots.run([str(acl2)], 'label', input=b'')",
                "with acl2_slots.tree_slot('x'):\n    completed = run([str(acl2)], cwd=root)",
                "subprocess.run([sys.executable, str(ROOT / 'tools/acl2')])",
                "subprocess.run(['git', 'status'])"):
            self.assertEqual(unpooled_launches(source), [], source)


FAKE_ACL2 = textwrap.dedent("""\
    #!/bin/sh
    printf 'SBCL_USER_ARGS=%s\\n' "${SBCL_USER_ARGS-unset}"
    printf 'ACL2_CUSTOMIZATION=%s\\n' "${ACL2_CUSTOMIZATION-unset}"
    printf 'ACL2_SYSTEM_BOOKS=%s\\n' "${ACL2_SYSTEM_BOOKS-unset}"
    printf 'HOLDER=%s\\n' "${FN_ACL2_SLOT_HOLDER-unset}"
    """)


class LaunchPathTests(unittest.TestCase):
    """`acl2_slots.run` and `popen` hold the slot and pass the environment."""

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix="fn-launchers-")
        root = Path(self.temp.name)
        self.fake = root / "acl2"
        self.fake.write_text(FAKE_ACL2)
        self.fake.chmod(self.fake.stat().st_mode | stat.S_IXUSR)
        self.saved = {name: os.environ.get(name) for name in (
            "FN_ACL2_SLOT_DIR", "FN_ACL2_SLOTS", "FN_ACL2_DYNAMIC_SPACE_MB",
            "ACL2_SYSTEM_BOOKS", "SBCL_USER_ARGS", acl2_slots.SLOT_HOLDER_VARIABLE)}
        os.environ["FN_ACL2_SLOT_DIR"] = str(root / "slots")
        os.environ["FN_ACL2_SLOTS"] = "1"
        os.environ["FN_ACL2_DYNAMIC_SPACE_MB"] = "1234"
        os.environ["ACL2_SYSTEM_BOOKS"] = "/elsewhere"
        os.environ.pop(acl2_slots.SLOT_HOLDER_VARIABLE, None)
        # The login shell may export its own cap; the pool's is under test.
        os.environ.pop("SBCL_USER_ARGS", None)

    def tearDown(self):
        for name, value in self.saved.items():
            if value is None:
                os.environ.pop(name, None)
            else:
                os.environ[name] = value
        self.temp.cleanup()

    def pool_is_free(self) -> bool:
        """The one slot can be locked now (never waits)."""
        path = acl2_slots.slot_directory() / "slot-000"
        descriptor = os.open(path, os.O_RDWR | os.O_CREAT, 0o644)
        try:
            fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except OSError:
            return False
        finally:
            os.close(descriptor)
        return True

    def test_run_holds_the_slot_and_passes_the_environment(self):
        result = acl2_slots.run([str(self.fake)], "launcher test",
                                stdout=subprocess.PIPE, text=True, check=True)
        lines = dict(line.split("=", 1) for line in result.stdout.splitlines())
        self.assertEqual(lines["SBCL_USER_ARGS"], "--dynamic-space-size 1234")
        self.assertEqual(lines["ACL2_CUSTOMIZATION"], "NONE")
        self.assertEqual(lines["ACL2_SYSTEM_BOOKS"], "unset")
        self.assertEqual(lines["HOLDER"], str(os.getpid()))
        self.assertNotIn(acl2_slots.SLOT_HOLDER_VARIABLE, os.environ)
        self.assertTrue(self.pool_is_free())

    def test_popen_holds_the_slot_until_released(self):
        process = acl2_slots.popen([str(self.fake)], "launcher test",
                                   stdout=subprocess.PIPE)
        process.communicate(timeout=30)
        # Still counted: the session's close() is what returns it.
        self.assertEqual(os.environ.get(acl2_slots.SLOT_HOLDER_VARIABLE), str(os.getpid()))
        acl2_slots.release_tree_slot()
        self.assertNotIn(acl2_slots.SLOT_HOLDER_VARIABLE, os.environ)
        self.assertTrue(self.pool_is_free())

    def test_a_failed_start_returns_the_slot(self):
        with self.assertRaises(OSError):
            acl2_slots.popen([str(Path(self.temp.name) / "missing")], "launcher test")
        self.assertNotIn(acl2_slots.SLOT_HOLDER_VARIABLE, os.environ)
        self.assertTrue(self.pool_is_free())


if __name__ == "__main__":
    unittest.main()
