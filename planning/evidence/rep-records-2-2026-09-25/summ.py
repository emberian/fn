#!/usr/bin/env python3
"""Summarize sprof graph files: samples and the Total column for named functions."""
import re, sys, glob
NAMES = ["FN-RECORD-P", "FN-RCON-RECORD-P", "FN-RECORD-STRING-OCTETS", "FN-RECORD-STRING-OCTETS-AUX",
         "FN-OWNER-PENDING-OCTETS", "FN-STORE-EVENT-ENCODE", "FN-RCON-STORE-EVENT-ENCODE",
         "FN-RECORD-ENCODE-IMPL", "FN-OWNER-PENDING-SEQUENCE", "FN-SBUD-PENDING-SEQUENCE",
         "FN-RCON-SBUD-PENDING-SEQUENCE", "FN-OWNER-IO", "FN-SN-IO", "FN-RCON-SN-IO",
         "FN-SF-RECORD-DIR-RESULT", "FN-RCON-SF-RECORD-DIR-RESULT", "FN-STORE-EVENT-SEQUENCE",
         "FN-STORE-EVENT-TXID", "FN-OWNER-FINISH-SUBMISSION", "FN-FRAME-DIGEST", "FN-OWNER-PREPARE"]
for f in sys.argv[1:]:
    t = open(f).read()
    n = int(re.search(r"Number of samples:\s+(\d+)", t).group(1))
    row = {}
    for line in t.splitlines():
        m = re.match(r"^\s+(\d+)\s+[\d.]+\s+(\d+)\s+([\d.]+)\s+(\S.*?) \[\d+\]$", line)
        if m and m.group(4) in NAMES and m.group(4) not in row:
            row[m.group(4)] = (int(m.group(1)), int(m.group(2)))
    print(f.split("/")[-1], "samples", n, "per_post %.1f" % (n / 48))
    for k in NAMES:
        if k in row:
            print("   %-32s self %4d total %4d (%.1f%%)" % (k, row[k][0], row[k][1], 100.0 * row[k][1] / n))
