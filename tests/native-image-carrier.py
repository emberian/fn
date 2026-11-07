#!/usr/bin/env python3
"""One file-backed measurement session, checked by WIRE and ENVELOPE.

Run after certifying sim/seeded-store.lisp and sim/check-wire.lisp.
"""
from pathlib import Path
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tests.surface.fn2_native_session import Fn2NativeSession


def main():
    directory = ROOT / "build" / f"image-carrier-{time.time_ns()}"
    directory.mkdir()
    session = Fn2NativeSession(log=directory / "session.log")
    (directory / "launcher.pid").write_text(f"{session.proc.pid}\n")
    try:
        assert Path(session.image).stat().st_size == 33554432
        ident, greeting = session.open()
        assert greeting == b"201 fn-nntp experimental reader ready\r\n", greeting
        group, closed = session.send(ident, b"GROUP local.test\r\n")
        assert not closed and group == b"211 3 1 3 local.test\r\n", group
        article, closed = session.send(ident, b"ARTICLE 1\r\n")
        assert not closed and article.startswith(b"220 1 <a@example.invalid> article follows\r\n"), article
        assert b"\r\n..dotted\r\n" in article and article.endswith(b"\r\n.\r\n"), article
        session.close(ident)
        verdicts = session.stop()
        assert verdicts == {ident: "ok"}, verdicts
    finally:
        if session.proc.poll() is None:
            session.proc.stdin.close()  # let the raw REPL exit after TERM stops serving
            session.proc.terminate()  # recorded launcher forwards TERM to its child
            session.proc.wait(timeout=30)
    print(f"NATIVE IMAGE CARRIER PASS: file image; ARTICLE; WIRE/ENVELOPE; {directory}")


if __name__ == "__main__":
    main()
