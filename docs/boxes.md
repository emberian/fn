# Build boxes: hbox, persvati and rented boxes

fn's certification, image builds and native tests run on build boxes, never on
the laptop.  hbox and persvati are the fixed boxes.  Rented boxes (cloud VMs,
added and removed by the hour) are rows in a config file on the laptop, not
code: nothing in this repository names one.

## Placing work: `tools/boxq.py`

Lanes don't choose boxes.  They queue work:

    python3 tools/boxq.py submit --kind certify-lane|native|overlay|check-lane|image-build|image-set|cmd \
        --priority integrator|lane|fill [--box BOX] [--wait] [kind options] [-- EXTRA]
    python3 tools/boxq.py status          # each box's cores, load, boxq jobs; the queue
    python3 tools/boxq.py results --red   # one json line per finished job

A daemon places each job on the box with the most free capacity: cores minus
boxq's reservations and any load those don't explain, available memory, and,
for native jobs, whether the box holds the image set.  The priorities are
integrator, then lane, then fill.  A native job is split into shards across
the boxes that hold its set.  The tool header has the details.

`tools/batch.py gate HEAD --base SET` is the integrator's batch gate:
- an overlay on SET when it can carry HEAD, otherwise one parallel image
  build and publish followed by a fan-out to every box;
- then the smoke tier plus the natives HEAD's changes reach
  (`tools/scenario_suite.py affected`), sharded.

`tools/batch.py fill SET` queues the full suite on idle capacity.

hbox takes only image-set jobs or work that names `--box hbox`.  It runs one
certify-type job at a time, at `--jobs 8`, and never past load 16, because
another project shares it.

## Adding a box

1. Rent an x86-64 Debian/Ubuntu host with glibc at least what
   `/tank/fn/sbcl/bin/sbcl` needs (2.38 today), and authorize the laptop's key
   for a sudo-capable user.
2. `tools/box_bootstrap.sh NAME user@ADDRESS --seed BOX --until ISO-UTC
   [--identity KEYFILE] [--dry-run]`.  This:
   - checks the host;
   - installs the package list (`FN_BOX_PACKAGES`, the only copy of it);
   - creates user `fn` and the `/tank/fn` layout, and installs `swarm-build`;
   - seeds the toolchain, certificate cache, image sets and evidence archive
     from the seed box, host to host;
   - verifies the result;
   - registers NAME (an ssh alias in `~/.ssh/fn-boxes.conf`, a row in
     `~/.config/fn/boxes.json`, copied to every box);
   - runs `tools/box_qualify.sh`.

   Seed from a rented box rather than hbox, because hbox uploads slowly.  A
   32-core box took 403 s from bare to registered.
3. Authorize each box's `fn` key on every other box, plus hbox's key.  The
   fan-out is pull-based, and hbox pulls certificates back at teardown.

## Qualification: `tools/box_qualify.sh BOX [--quick]`

It checks, one line each:
- the architecture and glibc;
- the toolchain identity of both launchers against hbox's, so certificates
  are interchangeable;
- the package list, python 3.12+, `dilithium-py`, the OpenSSL 3.5.8 test tool,
  and that docker answers *inside a swarm-build scope*;
- that every box-aware tool resolves the box (`tests/test_box_table.py` holds
  the same list, so a box can't be half-registered);
- that every image set has `MANIFEST.json` and `SHA256SUMS`;
- without `--quick`: a cached certify (certify 0), and the environment-sensitive
  native modules passing on the box's newest set.

The verdict is recorded in the box's row (`qualified`).  boxq never places work
on an unqualified box.  Re-run qualification after changing a box's packages or
toolchain.

Environment lessons behind these checks:
- **Docker:** a user added to the `docker` group after its systemd user manager
  started doesn't have the group inside its scopes, so `fn` gets the socket by
  ACL.
- **dilithium-py:** without it the consumer verifier answers "undecided".
- **Image provenance:** tests that check provenance read the published set's
  manifest beside the linked launcher.  Run them against a published set, not
  the build tree that produced it.

## Keeping boxes current

`tools/box_mirror.sh` runs on hbox as a systemd user timer.  Every 5 minutes it
pushes the evidence archive and any newer image sets to each live line of
`~/.config/fn/mirror-targets`.  A batch build's set doesn't wait for it:
`batch.py fanout` copies the set from the builder to every box as soon as it is
published.

## Removing a box: the deadline and the pull-back

Every rented row has an `until` time.  After it passes, every tool ignores the
row, even if the file is never edited.  Before deleting a box:
1. Pull its new certificate-cache entries into hbox's cache, from hbox:
   `rsync -a --ignore-existing --exclude=.entry.lock --exclude='.*'
   fn@BOX:/tank/fn/certcache/ /tank/fn/certcache/`.  This adds new entries
   only and never deletes anything on hbox.
2. Delete the host.
3. Remove its row and its `Host` block.

A burst is run with a laptop timer script that re-reads a `DEADLINE` file every
minute.  Edit that file to move the stop.  The timer does the pull-back,
deletes only hosts carrying the burst's label, and unregisters them.

## Host keys

Providers reuse addresses: a deleted VM's address comes back attached to a new
host key.  So rented hosts' keys live in their own file,
`~/.ssh/known_hosts.fn-boxes`, which the alias names, never in
`~/.ssh/known_hosts`.  `box_bootstrap.sh --forget-host-key` drops a stale key
for an address being reused.

## Quotas

Cloud projects cap cores per type, so check the limits before planning a burst.
On 2026-10-04 the cloud project allowed 8 dedicated and about 18 shared cores,
and the large dedicated types were refused until a limit raise.  The
bare-metal provider allowed two servers per team.  Raising either limit is a
manual request to the provider.
