# Two-host protected NNTP gate (scratch images)

Use this only after root supplies one frozen image directory, its full source
revision, and launcher/core/runtime/source-manifest SHA-256 values. The gate
is `tools/native_two_host_protected_gate.py`; it starts isolated owners and
stores under fresh `/tmp/fn-protected-*` directories on hbox and persvati.
It does not use `/tank/fn/node` or any live node store.

Keep the original image in root's hbox gate under `/tank/fn/gates/`. Copy the
**whole** frozen directory to a new persvati scratch path such as
`/home/ember/fn-gates/two-host-protected-REV/image/`, preserving modes. A
two-step `rsync -a` through a local scratch directory avoids an unchecked
remote-to-remote pipe. Run `sha256sum -c image.sha256` from each image
directory before the gate; the gate repeats this check, verifies the four
supplied digests on each host, and checks the actual `/proc` runtime and core
after each owner starts. Both hosts are Linux x86_64; hbox has glibc 2.40
and persvati 2.42, but copying the image is not evidence that its runtime
and bundled libraries start on persvati.

Supply the full revision as `--source`, the absolute hbox and persvati
`fn-host` paths as `--image-a` and `--image-b`, and the SHA-256 of each
host's `fn-host`, `fn-host.core`, `runtime/sbcl`, and `build-source.sha256`
as the corresponding four `--*-sha-a/b` arguments. Use a new local evidence
directory under `build/` for `--evidence-dir`. The gate clears generated
SBCL runtime arguments and the inherited library path, verifies the frozen
launcher without evaluating it, and uses SSH forwards so only loopback NNTP
listeners are exposed. Its Python observer reads NNTP replies; native owners
perform the actual exchange. Do not run this gate with guessed hashes or a
source revision inferred from a mutable launcher.

If the frozen runtime cannot start on persvati, preserve the failure and
qualify a separately built persvati image at its own core/runtime hashes;
do not call a one-host run a two-host result.
