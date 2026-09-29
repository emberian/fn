"""The input tracer tools/check_steps.py puts on a `make check` step's PYTHONPATH.

Inert unless FN_CHECK_TRACE names a directory.  Then this process (and every
Python child that inherits the environment) appends, one JSON line per new
observation, what it read and wrote to FN_CHECK_TRACE/<pid>.jsonl:

    ["r", path]        a file opened for reading (imports included)
    ["w", path]        a file opened for writing, created, removed or renamed
    ["l", path]        a directory listed (listdir, scandir, walk, glob)
    ["s", path]        a path stat'ed (exists, is_file, is_dir, getmtime)
    ["g", cwd, argv]   a git command (check_steps replays it to key the step)
    ["x", why]         something the trace cannot see into (a non-Python,
                       non-git child; a Python child without this tracer):
                       the step is never cached

The step's declared inputs are therefore what it actually touched, not a list
kept by hand beside the tool: a hand list goes stale the day a tool reads one
more file, and a stale list is a false green.  An existing sitecustomize
further down sys.path still runs.
"""
from __future__ import annotations

import os
import sys


def _chain() -> None:
    """Run the sitecustomize this one shadows, if there is one."""
    here = os.path.dirname(os.path.abspath(__file__))
    saved = sys.path[:]
    sys.path[:] = [p for p in sys.path if os.path.abspath(p or ".") != here]
    module = sys.modules.pop("sitecustomize", None)
    try:
        import importlib
        try:
            importlib.import_module("sitecustomize")
        except ImportError:
            pass
    finally:
        sys.path[:] = saved
        if module is not None:
            sys.modules["sitecustomize"] = module


def _install(directory: str) -> None:
    import json

    state = {"file": None, "pid": None, "cwd": os.getcwd(), "busy": False}
    seen: set = set()
    skip = tuple(sorted({os.path.realpath(p) + os.sep for p in
                         (sys.prefix, sys.base_prefix, sys.exec_prefix, directory,
                          "/dev", "/proc", "/sys") if p}))
    write_flags = os.O_WRONLY | os.O_RDWR | os.O_CREAT | os.O_TRUNC | os.O_APPEND

    def emit(record: list) -> None:
        key = tuple(record) if record[0] != "g" else (record[0], record[1], tuple(record[2]))
        if key in seen:
            return
        seen.add(key)
        state["busy"] = True
        try:
            if state["pid"] != os.getpid():
                state["pid"] = os.getpid()
                state["file"] = open(os.path.join(directory, f"{os.getpid()}.jsonl"), "a",
                                     encoding="utf-8")
            state["file"].write(json.dumps(record) + "\n")
            state["file"].flush()
        finally:
            state["busy"] = False

    def norm(path) -> str | None:
        if isinstance(path, int) or path is None:
            return None if isinstance(path, int) else state["cwd"]
        try:
            path = os.fsdecode(os.fspath(path))
        except TypeError:
            return None
        path = os.path.normpath(os.path.join(state["cwd"], path))
        if (path + os.sep).startswith(skip) or "/__pycache__/" in path:
            return None
        return path

    def hook(event: str, args: tuple) -> None:
        if state["busy"]:
            return
        if event == "open":
            path, mode, flags = args
            path = norm(path)
            if path is None:
                return
            writing = (isinstance(mode, str) and any(c in mode for c in "wax+")) or \
                (mode is None and isinstance(flags, int) and flags & write_flags)
            emit(["w" if writing else "r", path])
        elif event in ("os.listdir", "os.scandir"):
            path = norm(args[0] if args else None)
            if path is not None:
                emit(["l", path])
        elif event == "os.chdir":
            state["cwd"] = os.path.normpath(os.path.join(state["cwd"], os.fsdecode(args[0])))
        elif event in ("os.remove", "os.rmdir", "os.mkdir", "os.truncate", "os.symlink",
                       "os.link", "shutil.rmtree", "shutil.copyfile", "shutil.move",
                       "os.utime", "os.chmod"):
            path = norm(args[0])
            if path is not None:
                emit(["w", path])
            if event == "shutil.copyfile" and len(args) > 1:
                dst = norm(args[1])
                if dst is not None:
                    emit(["w", dst])
        elif event in ("os.rename", "os.replace"):
            for p in args[:2]:
                path = norm(p)
                if path is not None:
                    emit(["w", path])
        elif event == "subprocess.Popen":
            executable, argv, cwd, env = args
            argv = [os.fsdecode(a) for a in (argv if isinstance(argv, (list, tuple)) else [argv])]
            program = os.path.basename(os.fsdecode(executable or argv[0]))
            where = norm(cwd) if cwd is not None else state["cwd"]
            if program == "git":
                emit(["g", where, argv[1:]])
            elif program.startswith("python") or os.path.realpath(
                    os.fsdecode(executable or argv[0])) == os.path.realpath(sys.executable):
                if env is not None and "FN_CHECK_TRACE" not in env:
                    emit(["x", f"python child without the tracer: {' '.join(argv)[:120]}"])
                elif any(a in ("-I", "-S", "-E") for a in argv[1:3]):
                    emit(["x", f"python child isolated from the tracer: {' '.join(argv)[:120]}"])
            else:
                emit(["x", f"child process {program}"])
        elif event in ("os.system", "os.posix_spawn", "os.spawn", "os.exec", "os.fork"):
            if event != "os.fork":
                emit(["x", f"{event}"])

    real_stat, real_lstat = os.stat, os.lstat

    def traced_stat(path, *a, **k):
        if not state["busy"] and not isinstance(path, int):
            p = norm(path)
            if p is not None:
                emit(["s", p])
        return real_stat(path, *a, **k)

    def traced_lstat(path, *a, **k):
        if not state["busy"] and not isinstance(path, int):
            p = norm(path)
            if p is not None:
                emit(["s", p])
        return real_lstat(path, *a, **k)

    os.stat, os.lstat = traced_stat, traced_lstat
    sys.addaudithook(hook)


_chain()
if os.environ.get("FN_CHECK_TRACE"):
    _install(os.environ["FN_CHECK_TRACE"])
