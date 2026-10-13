"""tools/build_native_host.sh refuses a build whose log carries an ACL2 error.

A fake ACL2 (FN_ACL2) prints one marker line and the ready marker and makes
the image files, so the only thing between it and "built" is the log check
at build_native_host.sh's grep (PKT-284's refusal; PKT-305 owed its test).
Every path is in a temporary directory: FN_NATIVE_IMAGE and FN_NATIVE_LOG.
"""
import os
import pathlib
import platform
import re
import subprocess
import tempfile
import sys
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools import profile_limits  # noqa: E402
from tools.extract import core_launcher  # noqa: E402
TLS = profile_limits.get("run-tls-limit")
SCRIPT = ROOT / "tools" / "build_native_host.sh"
FAKE = """#!/bin/sh
cat > /dev/null
printf '%s\\n' "$FAKE_LINE"
echo "mldsa=$FN_MLDSA_LIBRARY openssl=${FN_OPENSSL_PREFIX:-unset}"
echo FN_NATIVE_BUILD_LOADED
echo "FN_NATIVE_TLS_LIMIT $FAKE_TLS"
echo "FN_NATIVE_STACK_KIB 1024"
echo FN_NATIVE_WORLD_STRIPPED
echo 'fn-world-deps 2' > "$FN_NATIVE_IMAGE.world-deps"
cat > "$FN_NATIVE_IMAGE" <<'IMG'
#!/bin/sh
if [ "$1" = --fn ]; then
    echo "$SBCL_USER_ARGS $*" > "$0.probe"
    echo "init: profile=small sizing=explicit reservation=1068 MB budget=1068 MB within-budget=yes"
    exit 0
fi
exec "/sbcl" --tls-limit 16384 --dynamic-space-size 32000 --control-stack-size 64 --core "c"
IMG
chmod +x "$FN_NATIVE_IMAGE"
echo core > "$FN_NATIVE_IMAGE.core"
exit "${FAKE_EXIT:-0}"
"""
MARKERS = ("ACL2 Error [Failure] in ( DEFUN FNN-X ...)",
           "HARD ACL2 ERROR in FMT: bad directive",
           "ABORTING from raw Lisp for (INCLUDE-BOOK ...)",
           "ACL2 Warning [Uncertified] in ( INCLUDE-BOOK \"x\" ...)")


class BuildNativeHostRefusalTests(unittest.TestCase):
    def build(self, line, build_text="(value :q)\n", **extra):
        with tempfile.TemporaryDirectory() as temporary:
            base = pathlib.Path(temporary)
            fake = base / "acl2"
            fake.write_text(FAKE)
            fake.chmod(0o755)
            env = {**os.environ, "FN_ACL2": str(fake), "FAKE_LINE": line,
                   "FAKE_TLS": str(TLS),
                   "FN_NATIVE_BUILD": str(base / "build.lisp"),
                   "FN_NATIVE_IMAGE": str(base / "fn-host-test"),
                   "FN_NATIVE_LOG": str(base / "build.log")}
            env.update({k: (v.replace("$BASE", str(base))) for k, v in extra.items()})
            # D64: on Linux the build requires a prefix holding the shipped
            # OpenSSL 3.5.8 pair; a stub pair that carries the version string.
            if "FN_OPENSSL_PREFIX" not in extra:
                prefix = base / "openssl"
                (prefix / "lib").mkdir(parents=True)
                (prefix / "lib" / "libssl.so.3").write_bytes(b"x")
                (prefix / "lib" / "libcrypto.so.3").write_bytes(b"OpenSSL 3.5.8 \n")
                env["FN_OPENSSL_PREFIX"] = str(prefix)
            env.pop("FN_TLS_LIMIT", None)
            (base / "build.lisp").write_text(build_text)
            answer = subprocess.run(["sh", str(SCRIPT)], env=env, cwd=ROOT,
                                    capture_output=True, text=True, timeout=60)
            library = [p for p in (base / "lib").glob("libfn-mldsa65.*")]
            launcher = base / "fn-host-test"
            self.launcher_text = launcher.read_text() if launcher.exists() else ""
            probe = base / "fn-host-test.probe"
            self.probe_text = probe.read_text() if probe.exists() else ""
            record = base / "fn-host-test.catalog"
            self.catalog_text = record.read_text() if record.exists() else None
            record = base / "fn-host-test.source"
            self.source_text = record.read_text() if record.exists() else None
            log = base / "build.log"
            return answer, (log.read_text() if log.exists() else ""), library, base

    def test_each_marker_refuses_the_build_and_prints_the_line(self):
        for line in MARKERS:
            with self.subTest(line=line):
                answer, log, _, _ = self.build(line)
                self.assertIn(line, log)
                self.assertEqual(answer.returncode, 1, answer.stdout + answer.stderr)
                self.assertIn("error or uncertified-book marker", answer.stderr)
                self.assertIn(line, answer.stderr)
                self.assertNotIn("built ", answer.stdout)

    def test_a_build_that_prints_no_tls_figure_is_refused(self):
        global TLS
        saved, TLS = TLS, ""
        try:
            answer, _log, _, _ = self.build("ACL2 !>")
        finally:
            TLS = saved
        self.assertEqual(answer.returncode, 1, answer.stdout + answer.stderr)
        self.assertIn("printed no FN_NATIVE_TLS_LIMIT", answer.stderr)

    def test_a_clean_log_builds(self):
        answer, log, library, base = self.build("ACL2 !>")
        self.assertEqual(answer.returncode, 0, answer.stdout + answer.stderr)
        self.assertIn("built ", answer.stdout)
        # The saved launcher runs at the profile's TLS limit, which the build
        # printed (FN_NATIVE_TLS_LIMIT: :run-tls-limit, MEM-001; the image
        # build's own :tls-limit stays 65536).
        launcher = self.launcher_text
        self.assertIn("--tls-limit {} ".format(TLS), launcher)
        self.assertEqual(TLS, 20480)
        self.assertLess(TLS, profile_limits.get("tls-limit"))
        # MEM-002: the launcher's default heap is the small preset's figure
        # the image's own init probe printed, not ACL2's 32000, and the probe
        # named the preset's fields (books/heap-figure.lisp).
        self.assertIn("--dynamic-space-size 1068 ", launcher)
        self.assertNotIn("--dynamic-space-size 32000", launcher)
        # The launcher decides its heap per command, through the one
        # fn_decide_heap packaging/fn defines (a default-profile store and a
        # BP node decide more than the small preset's figure).
        self.assertIn("fn_decide_heap() {", launcher)
        self.assertIn('fn_decide_command_heap "$@"', launcher)
        self.assertEqual(launcher.splitlines()[0], "#!/bin/sh")
        self.assertEqual(launcher.count("fn_decide_heap() {"),
                         (ROOT / "packaging" / "fn").read_text().count("fn_decide_heap() {"))
        self.assertIn("--max-history-octets 8388608", self.probe_text)
        # HST-016: the ML-DSA-65 library is built into lib/ beside the image
        # and named to the build; the shipped OpenSSL prefix is passed through (D64).
        self.assertEqual(len(library), 1, answer.stderr)
        line = [x for x in log.splitlines() if x.startswith("mldsa=")][0]
        named, openssl = line[len("mldsa="):].split(" openssl=")
        self.assertEqual(os.path.realpath(named), os.path.realpath(library[0]))
        self.assertEqual(openssl, str(base / "openssl"))
        # The catalog is recorded beside the image (tools/image_set.py reads it).
        self.assertEqual(self.catalog_text, "paged\n")
        # So is the source the image was built from (S057): in its own git
        # checkout, that checkout's HEAD, `commit` only when nothing differs
        # from it; in a tree that is not one (hbox_native's `git archive` run
        # tree), the FN_NATIVE_SOURCE its shipper names, else `unknown`.
        top = subprocess.run(["git", "rev-parse", "--show-toplevel"], cwd=ROOT,
                             capture_output=True, text=True)
        if top.returncode == 0 and top.stdout.strip() == str(ROOT.resolve()):
            head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True,
                                  text=True, check=True).stdout.strip()
            clean = not subprocess.run(["git", "status", "--porcelain", "--untracked-files=normal"],
                                       cwd=ROOT, capture_output=True, text=True).stdout.strip()
            expected = f"commit {head}" if clean else f"worktree {head}+dirty"
        else:
            expected = os.environ.get("FN_NATIVE_SOURCE") or "unknown"
        self.assertEqual(self.source_text, expected + "\n")

    def test_the_probe_names_the_small_preset_of_the_heap_book(self):
        """The script's probe flags are books/heap-figure.lisp's
        *fn-heap-small-request*, one preset read twice."""
        book = (ROOT / "books" / "heap-figure.lisp").read_text()
        request = book[book.index("(defconst *fn-heap-small-request*"):]
        request = request[:request.index("(defconst *fn-heap-small-profile*")]
        figures = [int(x) for x in re.findall(r"\*fn-bs-pf-[a-z-]+\* (\d+)", request)]
        script = SCRIPT.read_text()
        flags = [int(x) for x in re.findall(
            r"--max-(?:transactions|history-octets|record-octets|groups-per-article|open-suffix) (\d+)",
            script)]
        self.assertEqual(sorted(figures), sorted(flags))

    @unittest.skipUnless(platform.system() == "Linux", "the shipped-prefix rule is Linux's (D64)")
    def test_a_linux_build_without_the_shipped_openssl_is_refused(self):
        for prefix in ("", "$BASE/no-such-prefix"):
            with self.subTest(prefix=prefix):
                answer, _log, _, _ = self.build("ACL2 !>", FN_OPENSSL_PREFIX=prefix)
                self.assertEqual(answer.returncode, 2, answer.stdout + answer.stderr)
                self.assertIn("OpenSSL 3.5.8", answer.stderr)
                self.assertNotIn("built ", answer.stdout)

    def test_a_failed_acl2_names_its_real_exit_status(self):
        """S142: inside `if ! cmd; then`, $? is the negation's 0, so every
        failed build said 'acl2 exited with status 0'."""
        answer, _log, _, _ = self.build("ACL2 !>", FAKE_EXIT="137")
        self.assertEqual(answer.returncode, 1, answer.stdout + answer.stderr)
        self.assertIn("acl2 exited with status 137", answer.stderr)
        self.assertIsNone(self.source_text)


class LauncherSymlinkTests(unittest.TestCase):
    def linux_uname(self, commands):
        uname = commands / "uname"
        uname.write_text('#!/bin/sh\nprintf "Linux\\n"\n')
        uname.chmod(0o755)

    def render(self, kind, launcher, runtime):
        """Run the real generators' shell blocks, without building an image."""
        source = launcher.parent / "source"
        source.write_text(
            '#!/bin/sh\n'
            + (core_launcher.decision_prelude() if kind == "installed" else "")
            + 'export SBCL_HOME=\'%s\'\n' % launcher.parent
            + 'exec "%s" --dynamic-space-size 1068 --control-stack-size 1024KB '
              '--core "%s.core" ${SBCL_USER_ARGS} "$@"\n' % (runtime, launcher))
        if kind == "core":
            launcher.write_text(core_launcher.launcher(
                str(runtime), str(launcher.parent), str(launcher) + ".core", "1068", "1024KB"))
        else:
            if kind == "native":
                text = SCRIPT.read_text()
                start = text.index("    {\n        echo '#!/bin/sh'", text.index("# The decided heap"))
                end = text.index('} > "$IMAGE.decide"', start)
                block = text[start:end + 1]
                launcher.write_text(source.read_text())
                env = {"IMAGE": str(launcher)}
            elif kind == "frozen":
                text = (ROOT / "packaging/freeze-native-image.sh").read_text()
                start = text.index("  {\n    echo '#!/bin/sh'", text.index("for name in $variants"))
                end = text.index('} > "$out/$name"', start)
                block = text[start:end + 1]
                env = {"src": str(source), "name": launcher.name, "openssl_lib": "", "heap": ""}
            else:
                text = (ROOT / "packaging/install-native.sh").read_text()
                start = text.index("  {\n  echo '#!/bin/sh'", text.index("# Self-locating"))
                end = text.index('} > "$libdir/fn-host"', start)
                block = text[start:end + 1]
                env = {"image": str(source)}
            result = subprocess.run(["sh", "-c", block], cwd=ROOT, env={**os.environ, **env},
                                    capture_output=True, text=True, timeout=10)
            self.assertEqual(result.returncode, 0, result.stderr)
            launcher.write_text(result.stdout)
        launcher.chmod(0o755)

    def exercise_links(self, readlink_mode):
        with tempfile.TemporaryDirectory() as tmp:
            base = pathlib.Path(tmp).resolve()
            commands = base / "commands"
            commands.mkdir()
            # Exercise packaging/fn's installed Linux prefix derivation on every OS.
            self.linux_uname(commands)
            # OpenBSD's plain-readlink interface: reject every option. The
            # failing variant also exercises the ls -l fallback, on this OS.
            readlink = commands / "readlink"
            readlink.write_text('#!/bin/sh\n[ "$#" -eq 1 ] || exit 2\n'
                                'case $1 in -*) exit 2 ;; esac\n'
                                + ('exec /usr/bin/readlink "$1"\n' if readlink_mode == "plain"
                                   else 'exit 1\n'))
            readlink.chmod(0o755)
            links = base / "links"
            links.mkdir()
            for kind in ("native", "core", "installed", "frozen", "operator"):
                with self.subTest(kind=kind, readlink=readlink_mode):
                    product = base / kind
                    product.mkdir()
                    launcher = product / "fn-host"
                    runtime = product / "runtime/sbcl"
                    runtime.parent.mkdir()
                    runtime.write_text(
                        '#!/bin/sh\ncore=\nprobe=\nwant_core=\nwant_heap=\nheap=\n'
                        'echo "openssl-prefix=${FN_OPENSSL_PREFIX-unset}" >&2\n'
                        'for word in "$@"; do\n'
                        '  if [ -n "$want_core" ]; then core=$word; want_core=; fi\n'
                        '  if [ -n "$want_heap" ]; then heap=$word; want_heap=; fi\n'
                        '  [ "$word" != --core ] || want_core=1\n'
                        '  [ "$word" != --dynamic-space-size ] || want_heap=1\n'
                        '  [ "$word" != heap ] || probe=1\n'
                        'done\n[ -s "$core" ] || { echo "missing-core=$core" >&2; exit 9; }\n'
                        'if [ -n "$probe" ]; then\n'
                        '  echo "probe-core=$core" >&2\n'
                        '  echo "probe-heap=$heap" >&2\n'
                        '  echo "heap=777 MB stack=512 KB"\n'
                        'else\n  printf "%s\\n" "core=$core" "$@"\nfi\n')
                    runtime.chmod(0o755)
                    (product / "fn-host.core").write_bytes(b"core")
                    self.render("native" if kind == "operator" else kind, launcher, runtime)
                    entry = launcher
                    if kind == "operator":
                        lib = product / "libexec/fn"
                        lib.mkdir(parents=True)
                        for item in (launcher, product / "fn-host.core"):
                            item.rename(lib / item.name)
                        launcher = lib / "fn-host"
                        # Regenerate to carry the installed core's literal path.
                        self.render("native", launcher, runtime)
                        entry = product / "bin/fn"
                        entry.parent.mkdir()
                        entry.write_text((ROOT / "packaging/fn").read_text())
                        entry.chmod(0o755)
                    absolute = links / (kind + "-absolute")
                    absolute.symlink_to(entry)
                    relative = links / (kind + "-relative")
                    relative.symlink_to(os.path.relpath(entry, links))
                    chain = links / (kind + "-chain")
                    chain.symlink_to(relative.name)
                    spaced = links / (kind + " -> entry with spaces")
                    spaced.symlink_to(chain.name)
                    directory = links / (kind + "-directory")
                    directory.symlink_to(entry.parent, target_is_directory=True)
                    env = {"PATH": str(commands) + ":/usr/bin:/bin"}
                    for link in (absolute, relative, chain, spaced, directory / entry.name,
                                 pathlib.Path(os.path.relpath(chain, base))):
                        for override in ({}, {"SBCL_USER_ARGS": "--dynamic-space-size 888"}):
                            with self.subTest(link=link.name, override=override):
                                args = ["operator", "/cfg with spaces", "run"]
                                result = subprocess.run(
                                    [str(link), *([] if kind == "operator" else ["--fn"]), *args],
                                    cwd=base, env={**env, **override}, capture_output=True,
                                    text=True, timeout=10)
                                self.assertEqual(result.returncode, 0, result.stderr)
                                self.assertIn("core=" + str(launcher) + ".core", result.stdout)
                                self.assertEqual(result.stdout.splitlines()[-3:], args)
                                if kind == "operator":
                                    self.assertIn(f"openssl-prefix={lib}/openssl\n", result.stderr)
                                # Frozen images currently use their fixed runtime
                                # geometry; the other three image paths decide it.
                                if kind != "frozen" and (not override or kind == "operator"):
                                    self.assertIn("probe-core=" + str(launcher) + ".core", result.stderr)
                                    self.assertIn("probe-heap=129\n", result.stderr)
                                    self.assertIn("777", result.stdout.splitlines())

    def test_unresolved_control_reads_the_missing_symlink_core(self):
        """Recreate the old path handling in an isolated launcher, not the fix.

        Its missing core gives the probe only 128 MiB; whether a real image
        can boot at that size is the served-wire evidence run's question.
        """
        with tempfile.TemporaryDirectory() as tmp:
            base = pathlib.Path(tmp).resolve()
            launcher = base / "fn-host"
            runtime = base / "runtime"
            runtime.write_text('#!/bin/sh\ncase "$*" in *"--fn heap"*) '
                               'echo "boot=$SBCL_USER_ARGS" >&2; echo "heap=777 MB stack=512 KB" ;; '
                               '*) echo started ;; esac\n')
            runtime.chmod(0o755)
            (base / "fn-host.core").write_bytes(b"core")
            self.render("native", launcher, runtime)
            launcher.write_text(launcher.read_text().replace(
                'fn_launcher_path=$(fn_resolve_path "$0") || exit 4', 'fn_launcher_path=$0').replace(
                'img=$(fn_resolve_path "$1") || exit 4', 'img=$1'))
            link = base / "alias"
            link.symlink_to(launcher.name)
            result = subprocess.run([str(link), "--fn", "operator", "/cfg", "run"],
                                    env={"PATH": "/usr/bin:/bin"}, capture_output=True,
                                    text=True, timeout=10)
            self.assertIn(str(link) + ".core", result.stderr)
            self.assertIn("boot=--dynamic-space-size 128", result.stderr)

    def test_links_find_the_core_with_plain_readlink(self):
        self.exercise_links("plain")

    def test_links_find_the_core_with_ls_fallback(self):
        self.exercise_links("absent")

    def test_symlinked_installed_launcher_passes_default_and_operator_openssl_prefix(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = pathlib.Path(tmp).resolve()
            release = base / "releases/release1"
            lib = release / "libexec/fn"
            lib.mkdir(parents=True)
            image = lib / "fn-host"
            image.write_text('#!/bin/sh\nif [ "$2" = heap ]; then\n'
                             '  echo "heap=777 MB stack=512 KB"\n  exit 0\nfi\n'
                             'printf "%s\\n" runtime-was-started "openssl-prefix=$FN_OPENSSL_PREFIX"\n')
            image.chmod(0o755)
            (lib / "fn-host.core").write_bytes(b"core")
            launcher = release / "bin/fn"
            launcher.parent.mkdir()
            launcher.write_text((ROOT / "packaging/fn").read_text())
            launcher.chmod(0o755)
            links = base / "links"
            links.mkdir()
            entry = links / "fn"
            entry.symlink_to(os.path.relpath(launcher, links))
            commands = base / "commands"
            commands.mkdir()
            self.linux_uname(commands)
            self.assertFalse((lib / "openssl").exists())
            for prefix in (None, "/operator/../prefix with spaces"):
                with self.subTest(prefix=prefix):
                    env = {"PATH": str(commands) + ":/usr/bin:/bin"}
                    if prefix is not None:
                        env["FN_OPENSSL_PREFIX"] = prefix
                    result = subprocess.run([str(entry), "--version"], env=env,
                                            capture_output=True, text=True, timeout=3)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    self.assertEqual(result.stdout, "runtime-was-started\nopenssl-prefix="
                                     + (prefix if prefix is not None else str(lib / "openssl")) + "\n")
                    self.assertEqual(result.stderr, "")
                    self.assertFalse((lib / "openssl").exists())


class ResolverFailureTests(unittest.TestCase):
    def resolve(self, path, env=None):
        fn = (ROOT / "packaging/fn").read_text()
        resolver = fn[fn.index("# BEGIN fn_resolve_path"):fn.index("# END fn_resolve_path")]
        return subprocess.run(["sh", "-c", resolver + '\nfn_resolve_path "$1"',
                               "resolver-test", str(path)],
                              env={"PATH": "/usr/bin:/bin", **(env or {})},
                              capture_output=True, text=True, timeout=3)

    def cycle(self, self_link):
        with tempfile.TemporaryDirectory() as tmp:
            base = pathlib.Path(tmp).resolve()
            a = base / "a"
            a.symlink_to("a" if self_link else "b")
            if not self_link:
                (base / "b").symlink_to("a")
            result = self.resolve(a)
            self.assertEqual(result.returncode, 4)
            self.assertEqual(result.stdout, "")
            self.assertEqual(result.stderr, f"fn: too many levels of symbolic links: {a}\n")

    def test_a_self_link_ends_with_a_named_error(self):
        self.cycle(True)

    def test_a_two_link_cycle_ends_with_a_named_error(self):
        self.cycle(False)

    def test_forty_hops_succeed_and_forty_one_are_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = pathlib.Path(tmp).resolve()
            target = base / "target"
            target.write_text("target")
            for hops in (40, 41):
                with self.subTest(hops=hops):
                    chain = base / str(hops)
                    chain.mkdir()
                    for hop in range(hops):
                        (chain / str(hop)).symlink_to(str(hop + 1) if hop + 1 < hops else target)
                    entry = chain / "0"
                    result = self.resolve(entry)
                    self.assertEqual(result.returncode, 0 if hops == 40 else 4)
                    self.assertEqual(result.stdout, f"{target}\n" if hops == 40 else "")
                    self.assertEqual(result.stderr, "" if hops == 40 else
                                     f"fn: too many levels of symbolic links: {entry}\n")

    def test_missing_directory_has_one_named_error(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = pathlib.Path(tmp).resolve() / "missing/image"
            result = self.resolve(path)
            self.assertEqual(result.returncode, 4)
            self.assertEqual(result.stdout, "")
            self.assertEqual(result.stderr, f"fn: cannot resolve {path}\n")

    def test_unknown_command_has_one_named_error(self):
        result = self.resolve("fn-m26-no-such-command")
        self.assertEqual(result.returncode, 4)
        self.assertEqual(result.stdout, "")
        self.assertEqual(result.stderr, "fn: cannot resolve fn-m26-no-such-command\n")

    def test_unreadable_link_has_one_named_error(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = pathlib.Path(tmp).resolve()
            path = base / "link"
            path.symlink_to("target")
            commands = base / "commands"
            commands.mkdir()
            for command in ("readlink", "ls"):
                fake = commands / command
                fake.write_text('#!/bin/sh\necho "tool error" >&2\nexit 1\n')
                fake.chmod(0o755)
            result = self.resolve(path, {"PATH": str(commands) + ":/usr/bin:/bin"})
            self.assertEqual(result.returncode, 4)
            self.assertEqual(result.stdout, "")
            self.assertEqual(result.stderr, f"fn: cannot resolve {path}\n")

    def test_developer_missing_image_file_and_directory_name_the_image(self):
        with tempfile.TemporaryDirectory() as tmp:
            base = pathlib.Path(tmp).resolve()
            for missing in ("file", "directory"):
                with self.subTest(missing=missing):
                    checkout = base / missing
                    packaging = checkout / "packaging"
                    packaging.mkdir(parents=True)
                    launcher = packaging / "fn"
                    launcher.write_text((ROOT / "packaging/fn").read_text())
                    image = checkout / "build/fn-host"
                    if missing == "file":
                        image.parent.mkdir()
                    result = subprocess.run(["sh", str(launcher), "--version"],
                                            env={"PATH": "/usr/bin:/bin"},
                                            capture_output=True, text=True, timeout=3)
                    self.assertEqual(result.returncode, 4)
                    self.assertEqual(result.stdout, "")
                    expected = (f"fn: native host image missing: {image} "
                                "(run tools/build_native_host.sh)\n" if missing == "file" else
                                f"fn: cannot resolve {image}\n")
                    self.assertEqual(result.stderr, expected)


if __name__ == "__main__":
    unittest.main()
