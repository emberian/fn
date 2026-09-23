"""The two-host gate binds only recognized frozen/native launcher paths."""
import unittest

from tools.native_two_host_protected_gate import (
    image_argv, launcher_paths, observed_image_paths,
)


IMAGE = "/scratch/frozen-a/fn-host"
EXEC_TAIL = (
    '--tls-limit 16384 --dynamic-space-size 32000 '
    '--control-stack-size 64 --disable-ldb --core "{}" --noinform '
    '${{SBCL_USER_ARGS}} --end-runtime-options --no-userinit '
    "--eval '(acl2::sbcl-restart)' --disable-debugger "
    '--end-toplevel-options "$@"'
)


def frozen(runtime='$here/runtime/sbcl', core='$here/fn-host.core'):
    return ("#!/bin/sh\n# fn frozen image launcher v1\n"
            'here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)\n'
            'export SBCL_HOME="$here/runtime/sbcl-home/"\n'
            'export FN_OPENSSL_PREFIX="$here/openssl"\n'
            'export LD_LIBRARY_PATH="$here/lib:$here/openssl/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"\n'
            + 'exec "{}" '.format(runtime) + EXEC_TAIL.format(core) + "\n")


def legacy(runtime="/opt/sbcl/bin/sbcl", core=IMAGE + ".core"):
    return ("#!/bin/sh\nexport SBCL_HOME='/opt/sbcl/lib/sbcl/'\n"
            + 'exec "{}" '.format(runtime) + EXEC_TAIL.format(core) + "\n")


class LauncherPathsTests(unittest.TestCase):
    def test_current_frozen_layout_resolves_beside_launcher(self):
        self.assertEqual(
            launcher_paths(frozen(), IMAGE),
            ("/scratch/frozen-a/runtime/sbcl", IMAGE + ".core"))

    def test_legacy_literal_layout_still_binds_exact_core(self):
        self.assertEqual(
            launcher_paths(legacy(), IMAGE),
            ("/opt/sbcl/bin/sbcl", IMAGE + ".core"))

    def test_unknown_variables_traversal_wrong_core_and_commands_are_refused(self):
        bad = (
            frozen(runtime="$other/runtime/sbcl"),
            frozen(core="$here/../fn-host.core"),
            frozen(core="$here/fn-host-dtn.core"),
            frozen().replace('exec "$here/runtime/sbcl"',
                             'echo unsafe\nexec "$here/runtime/sbcl"'),
            frozen().replace('export FN_OPENSSL_PREFIX="$here/openssl"',
                             'export FN_OPENSSL_PREFIX="$other/openssl"'),
            frozen().replace('${SBCL_USER_ARGS}', '${OTHER_ARGS}'),
            frozen().replace('"$@"', '"$@"\nexec "/other/runtime"'),
            frozen().replace('"$@"', '"$(touch /tmp/unwanted)" "$@"'),
            legacy(core="/scratch/frozen-a/../other.core"),
            legacy(runtime="/opt/$RUNTIME"),
            legacy().replace('exec "/opt/sbcl/bin/sbcl"',
                             'exec "/opt/sbcl/bin/sbcl" --core "/other.core"'),
        )
        for script in bad:
            with self.subTest(script=script[-130:]), self.assertRaises(ValueError):
                launcher_paths(script, IMAGE)
        for image in ("relative/fn-host", "/scratch/../fn-host", "/scratch//fn-host"):
            with self.subTest(image=image), self.assertRaises(ValueError):
                launcher_paths(frozen(), image)

    def test_known_sbcl_placeholder_is_forced_empty_for_all_invocations(self):
        self.assertEqual(image_argv(IMAGE, "--fn", "operator"),
                         ["env", "SBCL_USER_ARGS=", "LD_LIBRARY_PATH=",
                          IMAGE, "--fn", "operator"])

    def test_proc_runtime_and_core_must_match_declared_paths(self):
        argv = ["/scratch/frozen-a/runtime/sbcl", "--core", IMAGE + ".core"]
        observed_image_paths(argv[0], argv, argv[0], IMAGE + ".core")
        for runtime, arguments in (
            ("/other/sbcl", argv),
            (argv[0], argv + ["--core", IMAGE + ".core"]),
            (argv[0], [argv[0], "--core", "/other/fn-host.core"]),
        ):
            with self.subTest(runtime=runtime, arguments=arguments):
                with self.assertRaises(RuntimeError):
                    observed_image_paths(runtime, arguments, argv[0], IMAGE + ".core")


if __name__ == "__main__":
    unittest.main()
