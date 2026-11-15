# Native artifact binding

Current fn2 CLI TLS startup now sets `FN2_TLS_LIBRARY` to the absolute artifact
path produced by its successful `host/build-tls.sh` invocation. Previously,
`fn init` and `fn serve` built `build/lib/libfn2-tls.{so,dylib}` while passing an
inherited `FN2_TLS_LIBRARY` through to `host/adapter.lisp`, which preferred that
unrelated library. Direct raw/primitive tests retain their explicit override;
the CLI selects its prepared artifact. BLAKE3 startup has no corresponding
environment override and uses the fixed library prepared by its build script.

`python3 tests/test_fn_admin_tls_startup.py` passes seven controls against the
actual `cmd_init`/`cmd_serve` consumers with build/process boundaries mocked.
The two added launch controls fail against `d18bcfbf2`: inherited direct and
symlinked overrides both reach startup. Build failure still prevents launch.
This is a library-path selection repair, not a digest check or protection against
replacement between preparation and `load-shared-object`. No native build or
ACL2 process was needed for these controls.

The legacy composed-image consumer below is separate from current fn2 startup:
`fn_admin` streams `tools/image-node.lsp` to `tools/acl2`, whose configured
launcher selects the ACL2 core/runtime. Its explicit `.lisp` raw loads do not
choose compiled helper sidecars. The recorded native B3 runtime receipts are
historical evidence; the CLI does not consume those receipts as a launch gate.

`tests/native_image_provenance.py` now rehashes every recorded image-set
payload when a composed fixture consumes its source coordinate. Both selected
launcher and core must have manifest digests; recorded nested runtime, shared
library and helper payloads must match too. Receipt paths cannot escape the set,
including through a symlink with identical bytes. The earlier consumer checked
only launcher bytes and core existence, relying on an earlier runner checksum.

`python3 tests/test_native_image_provenance.py` passes eight temporary-fixture
controls. Against frozen `06b1785df`, controls reproduce acceptance of a changed
core, runtime, shared library and helper, an omitted core digest, and an external
library alias. Launcher mutation remains a pre-existing rejection control.

This binds recorded bytes to the manifest's source label at inspection time.
It does not authenticate the manifest, discover unrecorded runtime dependencies,
prove which bytes a process loaded, freeze paths between inspection and execution,
or qualify that source's current ACL2 certificate closure. Source-runner manifests
also still depend on the producer to inventory their loaded shared libraries.

The legacy consumer repair did not connect `image-node.lsp` roots, qualified
certificate selections, raw substitutions or native runtime observations. Later
scoped native receipts remain governed by their own stated closure and source
coordinates. Neither change here relabels those receipts or certificates.
