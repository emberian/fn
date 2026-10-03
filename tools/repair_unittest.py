#!/usr/bin/env python3
"""Verifier-owned unittest observer. Run unchanged against base and head.

JSON is separate from test output: exits and printed words are not assertions.
This is an observation harness, not a sandbox against malicious test code.
"""
import json
import hashlib
import inspect
from pathlib import Path
import sys
import unittest


class Result(unittest.TextTestResult):
    def __init__(self, *args):
        super().__init__(*args)
        self.executed = []
        self.assertions = []
        self.sources = {}

    def startTest(self, test):
        self.executed.append(test.id())
        source = inspect.getsourcefile(type(test))
        if source:
            p = Path(source).resolve()
            try:
                self.sources[p.relative_to(Path.cwd()).as_posix()] = hashlib.sha256(p.read_bytes()).hexdigest()
            except ValueError:
                self.sources[str(p)] = "outside-worktree"
        super().startTest(test)

    def addFailure(self, test, err):
        self.assertions.append({"test": test.id(), "type": err[0].__name__,
                                "message": str(err[1])})
        super().addFailure(test, err)

    def addSubTest(self, test, subtest, err):
        if err is not None and issubclass(err[0], test.failureException):
            self.assertions.append({"test": test.id(), "type": err[0].__name__,
                                    "message": str(err[1]), "subtest": subtest.id()})
        super().addSubTest(test, subtest, err)


def main():
    output, *names = sys.argv[1:]
    sys.path.insert(0, str(Path.cwd()))
    suite = unittest.defaultTestLoader.loadTestsFromNames(names)
    result = unittest.TextTestRunner(resultclass=Result, verbosity=2).run(suite)
    data = {"executed": result.executed, "assertions": result.assertions,
            "errors": [test.id() for test, _ in result.errors],
            "skips": [(test.id(), why) for test, why in result.skipped],
            "expected_failures": [test.id() for test, _ in result.expectedFailures],
            "unexpected_successes": [test.id() for test in result.unexpectedSuccesses],
            "tests_run": result.testsRun}
    data["sources"] = result.sources
    data["python"] = sys.version
    Path(output).write_text(json.dumps(data))
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    sys.exit(main())
