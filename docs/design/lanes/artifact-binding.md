# Native artifact binding

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

Current served qualification still needs a frozen receipt connecting the actual
`image-node.lsp` roots, current qualified certificate selections, raw substitutions,
native shared objects, ACL2 core/SBCL and runtime observations. No historical image
or certificate was relabeled, and no current B runtime gate was run for this change.
