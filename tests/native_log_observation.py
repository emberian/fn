"""The committed history of a store, as the image reads it.

A store keeps its history in the record log (journal/NNNNNN.log,
books/store-log*.lisp); there are no transaction files to list.  A test that
asked "did a commit happen?" by listing transactions/ asks the image's own
read-only scan instead: `fn log scan SEGMENT EXTENT UNIT MAX SIZE` (both
images; host/native/io.lisp fnn-command-log) decodes the segment with ACL2's
fn-lg-decode and prints the records it committed and the last entry's chained
trailer.  The trailer chains every record before it (the FNLG entry names
its predecessor's trailer), so (records, last) identifies the committed
history: two observations are equal exactly when no record was committed in
between.  Python decodes nothing here.

UNIT is the log's write unit (books/store-log-route.lisp *fn-olr-unit*, 4096).
MAX is the record bound of the scan: the u32 ceiling, above every profile's
R, so the scan's stop is the log's own (the first entry that does not
validate or chain), never the bound.  SIZE only feeds the rig's `workload=`
flag, which is not read.  The segment is read while an owner may run: the
scan reads the durable prefix a crash would keep, and an entry being written
is not yet complete (it validates only once whole).
"""
from pathlib import Path
import re
import subprocess

UNIT = 4096
MAX = 4294967295
SEGMENT = Path("journal") / "000001.log"


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
    segment = Path(store) / SEGMENT
    extent = segment.stat().st_size
    result = subprocess.run(
        [str(image), "--fn", "log", "scan", str(segment), str(extent), str(UNIT),
         str(MAX), "0"],
        cwd=cwd, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        timeout=180, check=False)
    text = result.stdout.decode("utf-8", "replace")
    found = re.search(r"SCAN records=(\d+) .*last=(\S+)", text)
    if result.returncode != 0 or not found:
        raise AssertionError("log scan of {} failed ({}): {}{}".format(
            segment, result.returncode, text, result.stderr.decode("utf-8", "replace")))
    return CommittedHistory(int(found.group(1)), found.group(2))
