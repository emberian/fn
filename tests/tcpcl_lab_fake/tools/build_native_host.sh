#!/bin/sh
# tests/twonode_gate_fake: the native image build, for the twonode gate's dry
# run.  It writes a stub image and prints the line the gate looks for, and it
# says nothing whatever about ACL2, SBCL or fn: the dry run exercises the
# gate's sequencing, not its entry points, exactly as the fake run_store and
# run_reader beside it do.
#
# It exists because the gate now records a failed image build as a FAILED step
# rather than a not-exercised one, so a dry run with no image reported a
# failure that was the fake's absence and not the gate's finding.
set -eu
cd "$(dirname "$0")/.."
mkdir -p build
printf '#!/bin/sh\necho fn-host stub\n' > build/fn-host
chmod +x build/fn-host
printf 'stub core\n' > build/fn-host.core
echo "built build/fn-host (1.0K core)"
