"""The committed history of a store, as the image reads it.

A store keeps its history in the record log (journal/NNNNNN.log,
books/store-log*.lisp); there are no transaction files to list.  A test that
asked "did a commit happen?" by listing transactions/ asks the image's own
read-only scan instead: `fn log scan-store STORE' (both images;
host/native/io.lisp fnn-command-log-scan-store) reads the log as the open
does -- the segments ACL2's plan over journal/ names (books/store-log-
segments.lisp fn-lgs-open-plan: from the checkpoint's first suffix segment
with the chain the checkpoint records for it, else segment 1 from the
genesis record; a missing segment refused by the open's own name) -- decodes
them with ACL2's fn-lg-decode under the store's own parameters and prints
the history's record count as the open answers it (the checkpoint's S plus
the records scanned) and the last entry's chained trailer.  The trailer
chains every record before it (the FNLG entry names its predecessor's
trailer), so (records, last) identifies the committed history: two
observations are equal exactly when no record was committed in between, a
compaction between them included (it moves records into the checkpoint and
changes neither count nor chain).  Python decodes nothing and types no
parameter here: the image takes the profile from config.json, the chain from
the checkpoint's F row or the genesis record (journal/000000.log,
books/store-genesis.lisp), the write unit and the record bound (the profile's
max-record-octets, against which the entry header's length is read).

Before lane native-reds this helper typed `log scan SEGMENT EXTENT 4096
4294967295 0': the scan started from the log's constant genesis and read the
entry lengths against a bound that is no store's, so every format-10 store
read log-chain-broken (known_abort, topic_local, visibility_join).

The segment is read while an owner may run: the scan reads the durable prefix
a crash would keep, and an entry being written is not yet complete (it
validates only once whole).
"""
import re
import subprocess


class CommittedHistory:
    """(records, last): equal histories compare equal; len() is the count."""

    def __init__(self, records, last):
        self.records, self.last = records, last

    def __len__(self):
        return self.records

    def __eq__(self, other):
        return (isinstance(other, CommittedHistory)
                and (self.records, self.last) == (other.records, other.last))

    def __hash__(self):
        return hash((self.records, self.last))

    def __repr__(self):
        return "CommittedHistory(records={}, last={})".format(self.records, self.last)


def committed_history(image, store, env=None, cwd=None):
    result = subprocess.run(
        [str(image), "--fn", "log", "scan-store", str(store)],
        cwd=cwd, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        timeout=180, check=False)
    text = result.stdout.decode("utf-8", "replace")
    found = re.search(r"SCAN records=(\d+) .*last=(\S+)", text)
    if result.returncode != 0 or not found:
        raise AssertionError("log scan-store of {} failed ({}): {}{}".format(
            store, result.returncode, text, result.stderr.decode("utf-8", "replace")))
    return CommittedHistory(int(found.group(1)), found.group(2))
