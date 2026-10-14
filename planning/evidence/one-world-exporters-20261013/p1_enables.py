#!/usr/bin/env python3
"""P1: derive LOCAL pair-rule enables from successful certificate Rules lists.

Run --scan with the default openers, serialization bound and A28 pair rules,
then --apply, then --report after the six static gates.
--provenance reuses recorded dev evidence for exactly the same rune list.
Remote mode only reads the two existing dev-reference certify-log trees.
Consumers equal HEAD with only a single deterministic combined enable line
inserted/replaced. Defining libraries have only selected DEFTHMD token changes
and immediate LOCAL enables when the successful-history census requires them.
"""
import argparse
import glob
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import shlex
import subprocess
import sys
from types import SimpleNamespace

DEV_GLOB = '/Users/ember/dev/fn/build/integrate*/build/acl2/certify-202610*/*.certify.log'
LANE_GLOB = '/Users/ember/dev/fn/build/lanes/*/build/acl2/certify-202610*/*.certify.log'
REMOTE_GLOBS = [
    '/tank/fn/scratch/spans-view-walks/native-c19-vw/tree/build/acl2/certify-202610*/*.certify.log',
    '/tank/fn/gates/vertical-one-world-dev-reference-repl/build/acl2/certify-202610*/*.certify.log',
]
# Prototype guard certificates predate the October publishing runs. Retain
# only function/explicit-guard summaries in this additional historical scope.
DEV_GUARD_GLOB = DEV_GLOB.replace('202610*', '202609*')
LANE_GUARD_GLOB = LANE_GLOB.replace('202610*', '202609*')
REMOTE_GUARD_GLOBS = [p.replace('202610*', '202609*') for p in REMOTE_GLOBS]
GUARD_KINDS = {'DEFUN', 'DEFUND', 'VERIFY-GUARDS', 'VERIFY-GUARDS+'}
LINE = '(local (in-theory (enable adt-nth-1+)))\n'
RUNES = ('ADT-G-COLP-IS-ALL-ELT-P', 'ADT-KCORR-MEM', 'ADT-KGOOD-OF-CORR', 'ADT-LEN-REGION-BELOW-BODY', 'ADT-NTH-0', 'ADT-NTH-1+', 'ADT-REC-P-OF-LIST1', 'ADT-TREE-OKP-IS-SCCB-TREEP', 'DBT-BUF-P-IS-OCTET-LISTP', 'DRI$CP-IS-IX-CP', 'DRT-AB$C-GET-PAYLOAD-OKP-BRIDGE', 'DRT-AB$C-PAYLOAD-LENP-IS', 'DRT-AB$C-PAYLOAD-OFFP-IS', 'DRT-AB$C-POOLP-IS', 'DRT-ABP-IS-SCALAR-SEQ-P', 'DRT-DEC2P-IS-SCALAR-SEQ-P', 'DRT-DEC3$C-GET-OCTET-OKP-BRIDGE', 'DRT-DEC3$C-OCTETP-IS', 'DRT-DEC3$C-POOLP-IS', 'DRT-DEC3P-IS-SCALAR-SEQ-P', 'DRT-DECP-IS-SCALAR-SEQ-P', 'DRT-GEN-COLSP-IS-SCALAR-SEQ-P', 'DRT-HELDP-IS-SEQ-P', 'DRT-MOD$C-GET-PAYLOAD-OKP-BRIDGE', 'DRT-MOD$C-PAYLOAD-LENP-IS', 'DRT-MOD$C-PAYLOAD-OFFP-IS', 'DRT-MOD$C-POOLP-IS', 'DRT-MODP-IS-SCALAR-SEQ-P', 'DRT-NOPGP-IS-SEQ-P', 'DRT-PAYP-IS-SCALAR-SEQ-P', 'DRT-PGBP-IS-SCALAR-SEQ-P', 'DRT-PGMP-IS-SCALAR-SEQ-P', 'DRT-PGP-IS-SEQ-P', 'DRT-T1P-IS-SEQ-P', 'DRT-T2P-IS-SEQ-P', 'DRT-W1P-IS-SEQ-P', 'FN-ACCEPTED-IFF-ID-MEMBER', 'FN-ARENA-BYTES$C-GET-PAYLOAD-OKP-BRIDGE', 'FN-ARENA-BYTES$C-PAYLOAD-LENP-IS', 'FN-ARENA-BYTES$C-PAYLOAD-OFFP-IS', 'FN-ARENA-BYTES$C-POOLP-IS', 'FN-ARENA-BYTESP-IS-SCALAR-SEQ-P', 'FN-ARENA-P-IS-PAYLOAD-LISTP', 'FN-ARENA-PAGEDP-IS-SCALAR-SEQ-P', 'FN-ARN-EXTENTP-OF-LIST', 'FN-ARN-LZ-EXTENTP-OF-LIST', 'FN-ARTICLE-FIELD-CLOSEDP-OF-CLOSE-FIELD', 'FN-ARTICLE-OPEN-FIELD-CLOSEDP-IS-FIELD-CLOSEDP', 'FN-ARTICLES-FRESHP-IS-ONE-PASS', 'FN-ARX-FILESP-IS-TRUE-LISTP', 'FN-ARX-PAGE-BYTESP-IS-OCTETS-BUFP', 'FN-AST-WS-P-IS-OCTET-LISTP', 'FN-CAT$P-LIVEP-IS-LIVE', 'FN-CBOR-OCTET-LISTP-IS-ADT-OCTETSP', 'FN-CPL-FIRST-SKIPS', 'FN-CPL-LAST-SKIPS', 'FN-CPL-LIVE-AT-P-IS-LIVE', 'FN-CPL-OKP-IS-ALL-GOODP', 'FN-CROWP-IS-SEQ-P', 'FN-DLZ$C-GET-OCTET-OKP-BRIDGE', 'FN-DLZ$C-OCTETP-IS', 'FN-DLZ$C-POOLP-IS', 'FN-DLZP-IS-SCALAR-SEQ-P', 'FN-DSS-B-P-IS-OCTET-LISTP', 'FN-DSS-OUT-P-IS-OCTET-LISTP', 'FN-HIST$CP-IS-IX-CP', 'FN-HIST-P-IS-TRUE-LISTP', 'FN-HP-IN-BLOCK-RBLOCK-C-IS-IN-REGION', 'FN-HP-IN-BLOCK-RBLOCK-IS-IN-REGION', 'FN-HP-VHOLD-IS-X', 'FN-HRC-SFXP-IS-TRUE-LISTP', 'FN-KS-ALL-BOUNDP-IS-SUBSET', 'FN-KS-DISTINCTP-IS-NODUPP', 'FN-KS-SUBSETP-IS-SUBSET-LOGIC', 'FN-MPXT2P-IS-FN-MPXTP', 'FN-NO-DUPLICATESP-IS-KS-NODUPP', 'FN-NODE-ARTICLES-HAVE-ARCHIVE-BINDINGSP-IS-INDEXED', 'FN-OCT-OCTETS-P-IS-OCTET-LISTP', 'FN-OCT-PREFIX-EQUALP-IS-LIST-PREFIXP', 'FN-OCTETS-PG-P-IS-OCTET-LISTP', 'FN-OVR-LEASE-P-IS-OCTET-LISTP', 'FN-PCK-ROWP-IS-SEQ-P', 'FN-PGB-P-IS-OCTET-LISTP', 'FN-RETAIN-KNOWN-ID-SCANP-IS-KNOWN-IDP', 'FN-RETAIN-KS-DISJOINTP-KS-IS-LOGIC', 'FN-RETAIN-KS-DISJOINTP-SCAN-AFTER-FILL', 'FN-RETAIN-KS-DISJOINTP-WALK-IS-LOGIC', 'FN-RETAIN-NO-DUPLICATESP-IS-NO-DUPLICATESP', 'FN-SCC-OCTET-LISTP-IS-ADT-OCTETSP', 'FN-SCCB-SCC-OCTETP-IS-CBOR-OCTETP', 'FN-SF-SUCCESS-LISTP-KS-IS-LOGIC', 'FN-SF-SUCCESS-LISTP-SCAN-AFTER-FILL', 'FN-SF-SUCCESS-LISTP-WALK-IS-LOGIC', 'FN-SUBSETP-IS-KS-SUBSET-LOGIC', 'KCT-DISJOINTP-KS-IS-LOGIC', 'KCT-DISJOINTP-SCAN-AFTER-FILL', 'KCT-DISJOINTP-WALK-IS-LOGIC', 'KCT-SUCCESS-LISTP-KS-IS-LOGIC', 'KCT-SUCCESS-LISTP-SCAN-AFTER-FILL', 'KCT-SUCCESS-LISTP-WALK-IS-LOGIC', 'LW-RECP-IS-SEQ-P', 'PT-INSP-IS-SEQ-P')
LIB = 'books/proto/adt-key-lib.lisp'
RUNE_LIBRARIES = {'ADT-TP-NTHCDR-SHORT': 'books/def-representation-pages.lisp', 'ADT-G-COLP-IS-ALL-ELT-P': 'books/proto/adt-lib.lisp', 'ADT-KCORR-MEM': 'books/proto/adt-key-lib.lisp', 'ADT-KGOOD-OF-CORR': 'books/proto/adt-key-lib.lisp', 'ADT-LEN-REGION-BELOW-BODY': 'books/proto/adt-bytes.lisp', 'ADT-NTH-0': 'books/proto/adt-key-lib.lisp', 'ADT-NTH-1+': 'books/proto/adt-key-lib.lisp', 'ADT-REC-P-OF-LIST1': 'books/def-representation-lib.lisp', 'ADT-TREE-OKP-IS-SCCB-TREEP': 'books/def-representation-tree-walk.lisp', 'DBT-BUF-P-IS-OCTET-LISTP': 'tests/acl2/def-buffer-tests.lisp', 'DRI$CP-IS-IX-CP': 'tests/acl2/def-representation-index-tests.lisp', 'DRT-AB$C-GET-PAYLOAD-OKP-BRIDGE': 'tests/acl2/def-representation-tests.lisp', 'DRT-AB$C-PAYLOAD-LENP-IS': 'tests/acl2/def-representation-tests.lisp', 'DRT-AB$C-PAYLOAD-OFFP-IS': 'tests/acl2/def-representation-tests.lisp', 'DRT-AB$C-POOLP-IS': 'tests/acl2/def-representation-tests.lisp', 'DRT-ABP-IS-SCALAR-SEQ-P': 'tests/acl2/def-representation-tests.lisp', 'DRT-DEC2P-IS-SCALAR-SEQ-P': 'tests/acl2/def-representation-tests.lisp', 'DRT-DEC3$C-GET-OCTET-OKP-BRIDGE': 'tests/acl2/def-representation-tests.lisp', 'DRT-DEC3$C-OCTETP-IS': 'tests/acl2/def-representation-tests.lisp', 'DRT-DEC3$C-POOLP-IS': 'tests/acl2/def-representation-tests.lisp', 'DRT-DEC3P-IS-SCALAR-SEQ-P': 'tests/acl2/def-representation-tests.lisp', 'DRT-DECP-IS-SCALAR-SEQ-P': 'tests/acl2/def-representation-tests.lisp', 'DRT-GEN-COLSP-IS-SCALAR-SEQ-P': 'tests/acl2/def-representation-tests.lisp', 'DRT-HELDP-IS-SEQ-P': 'tests/acl2/def-representation-tests.lisp', 'DRT-MOD$C-GET-PAYLOAD-OKP-BRIDGE': 'tests/acl2/def-representation-tests.lisp', 'DRT-MOD$C-PAYLOAD-LENP-IS': 'tests/acl2/def-representation-tests.lisp', 'DRT-MOD$C-PAYLOAD-OFFP-IS': 'tests/acl2/def-representation-tests.lisp', 'DRT-MOD$C-POOLP-IS': 'tests/acl2/def-representation-tests.lisp', 'DRT-MODP-IS-SCALAR-SEQ-P': 'tests/acl2/def-representation-tests.lisp', 'DRT-NOPGP-IS-SEQ-P': 'tests/acl2/def-representation-pages-tests.lisp', 'DRT-PAYP-IS-SCALAR-SEQ-P': 'tests/acl2/def-representation-tests.lisp', 'DRT-PGBP-IS-SCALAR-SEQ-P': 'tests/acl2/def-representation-tests.lisp', 'DRT-PGMP-IS-SCALAR-SEQ-P': 'tests/acl2/def-representation-tests.lisp', 'DRT-PGP-IS-SEQ-P': 'tests/acl2/def-representation-pages-tests.lisp', 'DRT-T1P-IS-SEQ-P': 'tests/acl2/def-representation-tests.lisp', 'DRT-T2P-IS-SEQ-P': 'tests/acl2/def-representation-tests.lisp', 'DRT-W1P-IS-SEQ-P': 'tests/acl2/def-representation-tests.lisp', 'FN-ACCEPTED-IFF-ID-MEMBER': 'books/acceptance-invariants.lisp', 'FN-ARENA-BYTES$C-GET-PAYLOAD-OKP-BRIDGE': 'books/payload-arena-bytes.lisp', 'FN-ARENA-BYTES$C-PAYLOAD-LENP-IS': 'books/payload-arena-bytes.lisp', 'FN-ARENA-BYTES$C-PAYLOAD-OFFP-IS': 'books/payload-arena-bytes.lisp', 'FN-ARENA-BYTES$C-POOLP-IS': 'books/payload-arena-bytes.lisp', 'FN-ARENA-BYTESP-IS-SCALAR-SEQ-P': 'books/payload-arena-bytes.lisp', 'FN-ARENA-P-IS-PAYLOAD-LISTP': 'books/payload-arena.lisp', 'FN-ARENA-PAGEDP-IS-SCALAR-SEQ-P': 'books/payload-arena-paged.lisp', 'FN-ARN-EXTENTP-OF-LIST': 'books/payload-arena-extent-logic.lisp', 'FN-ARN-LZ-EXTENTP-OF-LIST': 'books/payload-arena-extent-logic.lisp', 'FN-ARTICLE-FIELD-CLOSEDP-OF-CLOSE-FIELD': 'books/article.lisp', 'FN-ARTICLE-OPEN-FIELD-CLOSEDP-IS-FIELD-CLOSEDP': 'books/article.lisp', 'FN-ARTICLES-FRESHP-IS-ONE-PASS': 'books/acceptance.lisp', 'FN-ARX-FILESP-IS-TRUE-LISTP': 'books/payload-arena-extent.lisp', 'FN-ARX-PAGE-BYTESP-IS-OCTETS-BUFP': 'books/payload-arena-extent.lisp', 'FN-AST-WS-P-IS-OCTET-LISTP': 'books/article-stream.lisp', 'FN-CAT$P-LIVEP-IS-LIVE': 'books/catalog-paged.lisp', 'FN-CBOR-OCTET-LISTP-IS-ADT-OCTETSP': 'books/catalog-paged.lisp', 'FN-CPL-FIRST-SKIPS': 'books/catalog-live-links.lisp', 'FN-CPL-LAST-SKIPS': 'books/catalog-live-links.lisp', 'FN-CPL-LIVE-AT-P-IS-LIVE': 'books/catalog-live-links.lisp', 'FN-CPL-OKP-IS-ALL-GOODP': 'books/catalog-live-links.lisp', 'FN-CROWP-IS-SEQ-P': 'books/catalog-paged.lisp', 'FN-DLZ$C-GET-OCTET-OKP-BRIDGE': 'books/decoded-payload-buffer.lisp', 'FN-DLZ$C-OCTETP-IS': 'books/decoded-payload-buffer.lisp', 'FN-DLZ$C-POOLP-IS': 'books/decoded-payload-buffer.lisp', 'FN-DLZP-IS-SCALAR-SEQ-P': 'books/decoded-payload-buffer.lisp', 'FN-DSS-B-P-IS-OCTET-LISTP': 'books/def-span-scan.lisp', 'FN-DSS-OUT-P-IS-OCTET-LISTP': 'books/def-span-scan.lisp', 'FN-HIST$CP-IS-IX-CP': 'books/history-columns-foundation.lisp', 'FN-HIST-P-IS-TRUE-LISTP': 'books/history-columns.lisp', 'FN-HP-IN-BLOCK-RBLOCK-C-IS-IN-REGION': 'books/history-pages-grow-cap.lisp', 'FN-HP-IN-BLOCK-RBLOCK-IS-IN-REGION': 'books/history-pages-grow.lisp', 'FN-HP-VHOLD-IS-X': 'books/history-pages-read.lisp', 'FN-HRC-SFXP-IS-TRUE-LISTP': 'books/history-records.lisp', 'FN-KS-ALL-BOUNDP-IS-SUBSET': 'books/acceptance-alloc.lisp', 'FN-KS-DISTINCTP-IS-NODUPP': 'books/acceptance-alloc.lisp', 'FN-KS-SUBSETP-IS-SUBSET-LOGIC': 'books/acceptance-alloc.lisp', 'FN-MPXT2P-IS-FN-MPXTP': 'books/msgid-pages-exec.lisp', 'FN-NO-DUPLICATESP-IS-KS-NODUPP': 'books/acceptance-alloc.lisp', 'FN-NODE-ARTICLES-HAVE-ARCHIVE-BINDINGSP-IS-INDEXED': 'books/node.lisp', 'FN-OCT-OCTETS-P-IS-OCTET-LISTP': 'books/octets-stobj.lisp', 'FN-OCT-PREFIX-EQUALP-IS-LIST-PREFIXP': 'books/octets-stobj.lisp', 'FN-OCTETS-PG-P-IS-OCTET-LISTP': 'books/pagestore-words.lisp', 'FN-OVR-LEASE-P-IS-OCTET-LISTP': 'books/over-render.lisp', 'FN-PCK-ROWP-IS-SEQ-P': 'books/paged-checkpoint.lisp', 'FN-PGB-P-IS-OCTET-LISTP': 'books/assumptions-pgs-host-io.lisp', 'FN-RETAIN-KNOWN-ID-SCANP-IS-KNOWN-IDP': 'books/retention.lisp', 'FN-RETAIN-KS-DISJOINTP-KS-IS-LOGIC': 'books/retention.lisp', 'FN-RETAIN-KS-DISJOINTP-SCAN-AFTER-FILL': 'books/retention.lisp', 'FN-RETAIN-KS-DISJOINTP-WALK-IS-LOGIC': 'books/retention.lisp', 'FN-RETAIN-NO-DUPLICATESP-IS-NO-DUPLICATESP': 'books/retention.lisp', 'FN-SCC-OCTET-LISTP-IS-ADT-OCTETSP': 'books/catalog-paged.lisp', 'FN-SCCB-SCC-OCTETP-IS-CBOR-OCTETP': 'books/store-checkpoint-buffer.lisp', 'FN-SF-SUCCESS-LISTP-KS-IS-LOGIC': 'books/store-files.lisp', 'FN-SF-SUCCESS-LISTP-SCAN-AFTER-FILL': 'books/store-files.lisp', 'FN-SF-SUCCESS-LISTP-WALK-IS-LOGIC': 'books/store-files.lisp', 'FN-SUBSETP-IS-KS-SUBSET-LOGIC': 'books/acceptance-alloc.lisp', 'KCT-DISJOINTP-KS-IS-LOGIC': 'tests/acl2/def-keyset-check-tests.lisp', 'KCT-DISJOINTP-SCAN-AFTER-FILL': 'tests/acl2/def-keyset-check-tests.lisp', 'KCT-DISJOINTP-WALK-IS-LOGIC': 'tests/acl2/def-keyset-check-tests.lisp', 'KCT-SUCCESS-LISTP-KS-IS-LOGIC': 'tests/acl2/def-keyset-check-tests.lisp', 'KCT-SUCCESS-LISTP-SCAN-AFTER-FILL': 'tests/acl2/def-keyset-check-tests.lisp', 'KCT-SUCCESS-LISTP-WALK-IS-LOGIC': 'tests/acl2/def-keyset-check-tests.lisp', 'LW-RECP-IS-SEQ-P': 'tests/acl2/def-representation-late-world-tests.lisp', 'PT-INSP-IS-SEQ-P': 'tests/acl2/def-representation-paged-tests.lisp'}
RUNE_CLASSES = {'ADT-TP-NTHCDR-SHORT': 'REWRITE', 'ADT-G-COLP-IS-ALL-ELT-P': 'REWRITE', 'ADT-KCORR-MEM': 'REWRITE', 'ADT-KGOOD-OF-CORR': 'REWRITE', 'ADT-LEN-REGION-BELOW-BODY': 'LINEAR', 'ADT-NTH-0': 'REWRITE', 'ADT-NTH-1+': 'REWRITE', 'ADT-REC-P-OF-LIST1': 'REWRITE', 'ADT-TREE-OKP-IS-SCCB-TREEP': 'REWRITE', 'DBT-BUF-P-IS-OCTET-LISTP': 'REWRITE', 'DRI$CP-IS-IX-CP': 'REWRITE', 'DRT-AB$C-GET-PAYLOAD-OKP-BRIDGE': 'REWRITE', 'DRT-AB$C-PAYLOAD-LENP-IS': 'REWRITE', 'DRT-AB$C-PAYLOAD-OFFP-IS': 'REWRITE', 'DRT-AB$C-POOLP-IS': 'REWRITE', 'DRT-ABP-IS-SCALAR-SEQ-P': 'REWRITE', 'DRT-DEC2P-IS-SCALAR-SEQ-P': 'REWRITE', 'DRT-DEC3$C-GET-OCTET-OKP-BRIDGE': 'REWRITE', 'DRT-DEC3$C-OCTETP-IS': 'REWRITE', 'DRT-DEC3$C-POOLP-IS': 'REWRITE', 'DRT-DEC3P-IS-SCALAR-SEQ-P': 'REWRITE', 'DRT-DECP-IS-SCALAR-SEQ-P': 'REWRITE', 'DRT-GEN-COLSP-IS-SCALAR-SEQ-P': 'REWRITE', 'DRT-HELDP-IS-SEQ-P': 'REWRITE', 'DRT-MOD$C-GET-PAYLOAD-OKP-BRIDGE': 'REWRITE', 'DRT-MOD$C-PAYLOAD-LENP-IS': 'REWRITE', 'DRT-MOD$C-PAYLOAD-OFFP-IS': 'REWRITE', 'DRT-MOD$C-POOLP-IS': 'REWRITE', 'DRT-MODP-IS-SCALAR-SEQ-P': 'REWRITE', 'DRT-NOPGP-IS-SEQ-P': 'REWRITE', 'DRT-PAYP-IS-SCALAR-SEQ-P': 'REWRITE', 'DRT-PGBP-IS-SCALAR-SEQ-P': 'REWRITE', 'DRT-PGMP-IS-SCALAR-SEQ-P': 'REWRITE', 'DRT-PGP-IS-SEQ-P': 'REWRITE', 'DRT-T1P-IS-SEQ-P': 'REWRITE', 'DRT-T2P-IS-SEQ-P': 'REWRITE', 'DRT-W1P-IS-SEQ-P': 'REWRITE', 'FN-ACCEPTED-IFF-ID-MEMBER': 'REWRITE', 'FN-ARENA-BYTES$C-GET-PAYLOAD-OKP-BRIDGE': 'REWRITE', 'FN-ARENA-BYTES$C-PAYLOAD-LENP-IS': 'REWRITE', 'FN-ARENA-BYTES$C-PAYLOAD-OFFP-IS': 'REWRITE', 'FN-ARENA-BYTES$C-POOLP-IS': 'REWRITE', 'FN-ARENA-BYTESP-IS-SCALAR-SEQ-P': 'REWRITE', 'FN-ARENA-P-IS-PAYLOAD-LISTP': 'REWRITE', 'FN-ARENA-PAGEDP-IS-SCALAR-SEQ-P': 'REWRITE', 'FN-ARN-EXTENTP-OF-LIST': 'REWRITE', 'FN-ARN-LZ-EXTENTP-OF-LIST': 'REWRITE', 'FN-ARTICLE-FIELD-CLOSEDP-OF-CLOSE-FIELD': 'REWRITE', 'FN-ARTICLE-OPEN-FIELD-CLOSEDP-IS-FIELD-CLOSEDP': 'REWRITE', 'FN-ARTICLES-FRESHP-IS-ONE-PASS': 'REWRITE', 'FN-ARX-FILESP-IS-TRUE-LISTP': 'REWRITE', 'FN-ARX-PAGE-BYTESP-IS-OCTETS-BUFP': 'REWRITE', 'FN-AST-WS-P-IS-OCTET-LISTP': 'REWRITE', 'FN-CAT$P-LIVEP-IS-LIVE': 'REWRITE', 'FN-CBOR-OCTET-LISTP-IS-ADT-OCTETSP': 'REWRITE', 'FN-CPL-FIRST-SKIPS': 'REWRITE', 'FN-CPL-LAST-SKIPS': 'REWRITE', 'FN-CPL-LIVE-AT-P-IS-LIVE': 'REWRITE', 'FN-CPL-OKP-IS-ALL-GOODP': 'REWRITE', 'FN-CROWP-IS-SEQ-P': 'REWRITE', 'FN-DLZ$C-GET-OCTET-OKP-BRIDGE': 'REWRITE', 'FN-DLZ$C-OCTETP-IS': 'REWRITE', 'FN-DLZ$C-POOLP-IS': 'REWRITE', 'FN-DLZP-IS-SCALAR-SEQ-P': 'REWRITE', 'FN-DSS-B-P-IS-OCTET-LISTP': 'REWRITE', 'FN-DSS-OUT-P-IS-OCTET-LISTP': 'REWRITE', 'FN-HIST$CP-IS-IX-CP': 'REWRITE', 'FN-HIST-P-IS-TRUE-LISTP': 'REWRITE', 'FN-HP-IN-BLOCK-RBLOCK-C-IS-IN-REGION': 'REWRITE', 'FN-HP-IN-BLOCK-RBLOCK-IS-IN-REGION': 'REWRITE', 'FN-HP-VHOLD-IS-X': 'REWRITE', 'FN-HRC-SFXP-IS-TRUE-LISTP': 'REWRITE', 'FN-KS-ALL-BOUNDP-IS-SUBSET': 'REWRITE', 'FN-KS-DISTINCTP-IS-NODUPP': 'REWRITE', 'FN-KS-SUBSETP-IS-SUBSET-LOGIC': 'REWRITE', 'FN-MPXT2P-IS-FN-MPXTP': 'REWRITE', 'FN-NO-DUPLICATESP-IS-KS-NODUPP': 'REWRITE', 'FN-NODE-ARTICLES-HAVE-ARCHIVE-BINDINGSP-IS-INDEXED': 'REWRITE', 'FN-OCT-OCTETS-P-IS-OCTET-LISTP': 'REWRITE', 'FN-OCT-PREFIX-EQUALP-IS-LIST-PREFIXP': 'REWRITE', 'FN-OCTETS-PG-P-IS-OCTET-LISTP': 'REWRITE', 'FN-OVR-LEASE-P-IS-OCTET-LISTP': 'REWRITE', 'FN-PCK-ROWP-IS-SEQ-P': 'REWRITE', 'FN-PGB-P-IS-OCTET-LISTP': 'REWRITE', 'FN-RETAIN-KNOWN-ID-SCANP-IS-KNOWN-IDP': 'REWRITE', 'FN-RETAIN-KS-DISJOINTP-KS-IS-LOGIC': 'REWRITE', 'FN-RETAIN-KS-DISJOINTP-SCAN-AFTER-FILL': 'REWRITE', 'FN-RETAIN-KS-DISJOINTP-WALK-IS-LOGIC': 'REWRITE', 'FN-RETAIN-NO-DUPLICATESP-IS-NO-DUPLICATESP': 'REWRITE', 'FN-SCC-OCTET-LISTP-IS-ADT-OCTETSP': 'REWRITE', 'FN-SCCB-SCC-OCTETP-IS-CBOR-OCTETP': 'REWRITE', 'FN-SF-SUCCESS-LISTP-KS-IS-LOGIC': 'REWRITE', 'FN-SF-SUCCESS-LISTP-SCAN-AFTER-FILL': 'REWRITE', 'FN-SF-SUCCESS-LISTP-WALK-IS-LOGIC': 'REWRITE', 'FN-SUBSETP-IS-KS-SUBSET-LOGIC': 'REWRITE', 'KCT-DISJOINTP-KS-IS-LOGIC': 'REWRITE', 'KCT-DISJOINTP-SCAN-AFTER-FILL': 'REWRITE', 'KCT-DISJOINTP-WALK-IS-LOGIC': 'REWRITE', 'KCT-SUCCESS-LISTP-KS-IS-LOGIC': 'REWRITE', 'KCT-SUCCESS-LISTP-SCAN-AFTER-FILL': 'REWRITE', 'KCT-SUCCESS-LISTP-WALK-IS-LOGIC': 'REWRITE', 'LW-RECP-IS-SEQ-P': 'REWRITE', 'PT-INSP-IS-SEQ-P': 'REWRITE'}
RUNE_GENERATED = {'DBT-BUF-P-IS-OCTET-LISTP': {'book': 'tests/acl2/def-buffer-tests.lisp', 'macro': 'def-buffer', 'instance': 'DBT-BUF', 'template': 'buffer'}, 'DRI$CP-IS-IX-CP': {'book': 'tests/acl2/def-representation-index-tests.lisp', 'macro': 'def-representation-index', 'instance': 'DRI', 'template': 'index'}, 'DRT-AB$C-GET-PAYLOAD-OKP-BRIDGE': {'book': 'tests/acl2/def-representation-tests.lisp', 'macro': 'def-representation', 'instance': 'DRT-AB', 'template': 'adt-get'}, 'DRT-AB$C-PAYLOAD-LENP-IS': {'book': 'tests/acl2/def-representation-tests.lisp', 'macro': 'def-representation', 'instance': 'DRT-AB', 'template': 'adt-col'}, 'DRT-AB$C-PAYLOAD-OFFP-IS': {'book': 'tests/acl2/def-representation-tests.lisp', 'macro': 'def-representation', 'instance': 'DRT-AB', 'template': 'adt-col'}, 'DRT-AB$C-POOLP-IS': {'book': 'tests/acl2/def-representation-tests.lisp', 'macro': 'def-representation', 'instance': 'DRT-AB', 'template': 'adt-pool'}, 'DRT-ABP-IS-SCALAR-SEQ-P': {'book': 'tests/acl2/def-representation-tests.lisp', 'macro': 'def-representation', 'instance': 'DRT-AB', 'template': 'rep-scalar'}, 'DRT-DEC2P-IS-SCALAR-SEQ-P': {'book': 'tests/acl2/def-representation-tests.lisp', 'macro': 'def-representation', 'instance': 'DRT-DEC', 'template': 'rep-scalar'}, 'DRT-DEC3$C-GET-OCTET-OKP-BRIDGE': {'book': 'tests/acl2/def-representation-tests.lisp', 'macro': 'def-representation', 'instance': 'DRT-DEC', 'template': 'adt-get'}, 'DRT-DEC3$C-OCTETP-IS': {'book': 'tests/acl2/def-representation-tests.lisp', 'macro': 'def-representation', 'instance': 'DRT-DEC', 'template': 'adt-col'}, 'DRT-DEC3$C-POOLP-IS': {'book': 'tests/acl2/def-representation-tests.lisp', 'macro': 'def-representation', 'instance': 'DRT-DEC', 'template': 'adt-pool'}, 'DRT-DEC3P-IS-SCALAR-SEQ-P': {'book': 'tests/acl2/def-representation-tests.lisp', 'macro': 'def-representation', 'instance': 'DRT-DEC', 'template': 'rep-scalar'}, 'DRT-DECP-IS-SCALAR-SEQ-P': {'book': 'tests/acl2/def-representation-tests.lisp', 'macro': 'def-representation', 'instance': 'DRT-DEC', 'template': 'rep-scalar'}, 'DRT-GEN-COLSP-IS-SCALAR-SEQ-P': {'book': 'tests/acl2/def-representation-tests.lisp', 'macro': 'def-representation', 'instance': 'DRT-GEN', 'template': 'rep-scalar'}, 'DRT-HELDP-IS-SEQ-P': {'book': 'tests/acl2/def-representation-tests.lisp', 'macro': 'def-representation', 'instance': 'DRT-HELD', 'template': 'rep-seq'}, 'DRT-MOD$C-GET-PAYLOAD-OKP-BRIDGE': {'book': 'tests/acl2/def-representation-tests.lisp', 'macro': 'def-representation', 'instance': 'DRT-MOD', 'template': 'adt-get'}, 'DRT-MOD$C-PAYLOAD-LENP-IS': {'book': 'tests/acl2/def-representation-tests.lisp', 'macro': 'def-representation', 'instance': 'DRT-MOD', 'template': 'adt-col'}, 'DRT-MOD$C-PAYLOAD-OFFP-IS': {'book': 'tests/acl2/def-representation-tests.lisp', 'macro': 'def-representation', 'instance': 'DRT-MOD', 'template': 'adt-col'}, 'DRT-MOD$C-POOLP-IS': {'book': 'tests/acl2/def-representation-tests.lisp', 'macro': 'def-representation', 'instance': 'DRT-MOD', 'template': 'adt-pool'}, 'DRT-MODP-IS-SCALAR-SEQ-P': {'book': 'tests/acl2/def-representation-tests.lisp', 'macro': 'def-representation', 'instance': 'DRT-MOD', 'template': 'rep-scalar'}, 'DRT-NOPGP-IS-SEQ-P': {'book': 'tests/acl2/def-representation-pages-tests.lisp', 'macro': 'def-representation', 'instance': 'DRT-NOPG', 'template': 'rep-seq'}, 'DRT-PAYP-IS-SCALAR-SEQ-P': {'book': 'tests/acl2/def-representation-tests.lisp', 'macro': 'def-representation', 'instance': 'DRT-PAY', 'template': 'rep-scalar'}, 'DRT-PGBP-IS-SCALAR-SEQ-P': {'book': 'tests/acl2/def-representation-tests.lisp', 'macro': 'def-representation', 'instance': 'DRT-PGB', 'template': 'rep-scalar'}, 'DRT-PGMP-IS-SCALAR-SEQ-P': {'book': 'tests/acl2/def-representation-tests.lisp', 'macro': 'def-representation', 'instance': 'DRT-PGM', 'template': 'rep-scalar'}, 'DRT-PGP-IS-SEQ-P': {'book': 'tests/acl2/def-representation-pages-tests.lisp', 'macro': 'def-representation', 'instance': 'DRT-PG', 'template': 'rep-seq'}, 'DRT-T1P-IS-SEQ-P': {'book': 'tests/acl2/def-representation-tests.lisp', 'macro': 'def-representation', 'instance': 'DRT-T1', 'template': 'rep-seq'}, 'DRT-T2P-IS-SEQ-P': {'book': 'tests/acl2/def-representation-tests.lisp', 'macro': 'def-representation', 'instance': 'DRT-T2', 'template': 'rep-seq'}, 'DRT-W1P-IS-SEQ-P': {'book': 'tests/acl2/def-representation-tests.lisp', 'macro': 'def-representation', 'instance': 'DRT-W1', 'template': 'rep-seq'}, 'FN-ARENA-BYTES$C-GET-PAYLOAD-OKP-BRIDGE': {'book': 'books/payload-arena-bytes.lisp', 'macro': 'def-representation', 'instance': 'FN-ARENA-BYTES', 'template': 'adt-get'}, 'FN-ARENA-BYTES$C-PAYLOAD-LENP-IS': {'book': 'books/payload-arena-bytes.lisp', 'macro': 'def-representation', 'instance': 'FN-ARENA-BYTES', 'template': 'adt-col'}, 'FN-ARENA-BYTES$C-PAYLOAD-OFFP-IS': {'book': 'books/payload-arena-bytes.lisp', 'macro': 'def-representation', 'instance': 'FN-ARENA-BYTES', 'template': 'adt-col'}, 'FN-ARENA-BYTES$C-POOLP-IS': {'book': 'books/payload-arena-bytes.lisp', 'macro': 'def-representation', 'instance': 'FN-ARENA-BYTES', 'template': 'adt-pool'}, 'FN-ARENA-BYTESP-IS-SCALAR-SEQ-P': {'book': 'books/payload-arena-bytes.lisp', 'macro': 'def-representation', 'instance': 'FN-ARENA-BYTES', 'template': 'rep-scalar'}, 'FN-ARENA-PAGEDP-IS-SCALAR-SEQ-P': {'book': 'books/payload-arena-paged.lisp', 'macro': 'def-representation', 'instance': 'FN-ARENA-PAGED', 'template': 'rep-scalar'}, 'FN-AST-WS-P-IS-OCTET-LISTP': {'book': 'books/article-stream.lisp', 'macro': 'def-buffer', 'instance': 'FN-AST-WS', 'template': 'buffer'}, 'FN-CROWP-IS-SEQ-P': {'book': 'books/catalog-paged.lisp', 'macro': 'def-representation', 'instance': 'FN-CROW', 'template': 'rep-seq'}, 'FN-DLZ$C-GET-OCTET-OKP-BRIDGE': {'book': 'books/decoded-payload-buffer.lisp', 'macro': 'def-representation', 'instance': 'FN-DLZ', 'template': 'adt-get'}, 'FN-DLZ$C-OCTETP-IS': {'book': 'books/decoded-payload-buffer.lisp', 'macro': 'def-representation', 'instance': 'FN-DLZ', 'template': 'adt-col'}, 'FN-DLZ$C-POOLP-IS': {'book': 'books/decoded-payload-buffer.lisp', 'macro': 'def-representation', 'instance': 'FN-DLZ', 'template': 'adt-pool'}, 'FN-DLZP-IS-SCALAR-SEQ-P': {'book': 'books/decoded-payload-buffer.lisp', 'macro': 'def-representation', 'instance': 'FN-DLZ', 'template': 'rep-scalar'}, 'FN-DSS-B-P-IS-OCTET-LISTP': {'book': 'books/def-span-scan.lisp', 'macro': 'def-buffer', 'instance': 'FN-DSS-B', 'template': 'buffer'}, 'FN-DSS-OUT-P-IS-OCTET-LISTP': {'book': 'books/def-span-scan.lisp', 'macro': 'def-buffer', 'instance': 'FN-DSS-OUT', 'template': 'buffer'}, 'FN-HIST$CP-IS-IX-CP': {'book': 'books/history-columns-foundation.lisp', 'macro': 'def-representation-index', 'instance': 'FN-HIST', 'template': 'index'}, 'FN-OCTETS-PG-P-IS-OCTET-LISTP': {'book': 'books/pagestore-words.lisp', 'macro': 'def-buffer', 'instance': 'FN-OCTETS-PG', 'template': 'buffer'}, 'FN-OVR-LEASE-P-IS-OCTET-LISTP': {'book': 'books/over-render.lisp', 'macro': 'def-buffer', 'instance': 'FN-OVR-LEASE', 'template': 'buffer'}, 'FN-PCK-ROWP-IS-SEQ-P': {'book': 'books/paged-checkpoint.lisp', 'macro': 'def-representation', 'instance': 'FN-PCK-ROW', 'template': 'rep-seq'}, 'FN-PGB-P-IS-OCTET-LISTP': {'book': 'books/assumptions-pgs-host-io.lisp', 'macro': 'def-buffer', 'instance': 'FN-PGB', 'template': 'buffer'}, 'FN-RETAIN-KS-DISJOINTP-KS-IS-LOGIC': {'book': 'books/retention.lisp', 'macro': 'def-keyset-check', 'instance': 'FN-RETAIN-KS-DISJOINTP', 'template': 'keyset-ks'}, 'FN-RETAIN-KS-DISJOINTP-SCAN-AFTER-FILL': {'book': 'books/retention.lisp', 'macro': 'def-keyset-check', 'instance': 'FN-RETAIN-KS-DISJOINTP', 'template': 'keyset-scan'}, 'FN-RETAIN-KS-DISJOINTP-WALK-IS-LOGIC': {'book': 'books/retention.lisp', 'macro': 'def-keyset-check', 'instance': 'FN-RETAIN-KS-DISJOINTP', 'template': 'keyset-walk'}, 'FN-SF-SUCCESS-LISTP-KS-IS-LOGIC': {'book': 'books/store-files.lisp', 'macro': 'def-keyset-check', 'instance': 'FN-SF-SUCCESS-LISTP', 'template': 'keyset-ks'}, 'FN-SF-SUCCESS-LISTP-SCAN-AFTER-FILL': {'book': 'books/store-files.lisp', 'macro': 'def-keyset-check', 'instance': 'FN-SF-SUCCESS-LISTP', 'template': 'keyset-scan'}, 'FN-SF-SUCCESS-LISTP-WALK-IS-LOGIC': {'book': 'books/store-files.lisp', 'macro': 'def-keyset-check', 'instance': 'FN-SF-SUCCESS-LISTP', 'template': 'keyset-walk'}, 'KCT-DISJOINTP-KS-IS-LOGIC': {'book': 'tests/acl2/def-keyset-check-tests.lisp', 'macro': 'def-keyset-check', 'instance': 'KCT-DISJOINTP', 'template': 'keyset-ks'}, 'KCT-DISJOINTP-SCAN-AFTER-FILL': {'book': 'tests/acl2/def-keyset-check-tests.lisp', 'macro': 'def-keyset-check', 'instance': 'KCT-DISJOINTP', 'template': 'keyset-scan'}, 'KCT-DISJOINTP-WALK-IS-LOGIC': {'book': 'tests/acl2/def-keyset-check-tests.lisp', 'macro': 'def-keyset-check', 'instance': 'KCT-DISJOINTP', 'template': 'keyset-walk'}, 'KCT-SUCCESS-LISTP-KS-IS-LOGIC': {'book': 'tests/acl2/def-keyset-check-tests.lisp', 'macro': 'def-keyset-check', 'instance': 'KCT-SUCCESS-LISTP', 'template': 'keyset-ks'}, 'KCT-SUCCESS-LISTP-SCAN-AFTER-FILL': {'book': 'tests/acl2/def-keyset-check-tests.lisp', 'macro': 'def-keyset-check', 'instance': 'KCT-SUCCESS-LISTP', 'template': 'keyset-scan'}, 'KCT-SUCCESS-LISTP-WALK-IS-LOGIC': {'book': 'tests/acl2/def-keyset-check-tests.lisp', 'macro': 'def-keyset-check', 'instance': 'KCT-SUCCESS-LISTP', 'template': 'keyset-walk'}, 'LW-RECP-IS-SEQ-P': {'book': 'tests/acl2/def-representation-late-world-tests.lisp', 'macro': 'def-representation', 'instance': 'LW-REC', 'template': 'rep-seq'}, 'PT-INSP-IS-SEQ-P': {'book': 'tests/acl2/def-representation-paged-tests.lisp', 'macro': 'def-representation', 'instance': 'PT-INS', 'template': 'rep-seq'}}
EXCLUDED = {
    'books/' + name + '.lisp': 'direct-history-columns book: explicitly excluded from book-level enable'
    for name in ('msgid-pages', 'msgid-pages-exec', 'msgid-linear-exec',
                 'msgid-probe-layout', 'msgid-query-chunk', 'catalog-logic')
}
EXCLUDED['books/catalog-paged.lisp'] = 'catalog-paged: explicitly excluded from book-level enable'
RUNE = re.compile(r'\(:REWRITE\s+ADT-NTH-1\+\)', re.I)
SUMMARY = re.compile(r'^Form:[ \t]*(.*?)\nRules:[ \t]*(.*?)(?=\n\S|\Z)', re.M | re.S)


def rune_pattern(runes):
    # Capture the name in group 1, preserving the census evidence schema.
    classes = '|'.join(RUNE_CLASSES[r] + r'\s+' + re.escape(r) for r in runes)
    suffix = r'(?:\s+\.\s+\d+)?'
    return (r'\(:(?=(?:' + classes + r')' + suffix + r'\))(?:REWRITE|LINEAR)\s+(' + '|'.join(re.escape(r) for r in runes) +
            r')' + suffix + r'\)')


def enable_line(runes):
    return '(local (in-theory (enable ' + ' '.join(r.lower() for r in sorted(runes)) + ')))\n'


def without_enable_lines(text):
    return ''.join(line for line in text.splitlines(keepends=True)
                   if not is_enable_line(line))


def is_enable_line(line):
    match = re.fullmatch(r'\(local \(in-theory \(enable ([^()\s]+(?: [^()\s]+)*)\)\)\)\n', line)
    names = tuple(n.upper() for n in match[1].split()) if match else ()
    return bool(names and set(names) <= set(RUNE_LIBRARIES) and line == enable_line(names))


def library_change(parent, lr, book, needed):
    tree = lr.parse(parent)
    edits, tokens, positions, private = [], [], [], {}
    # Generator templates, never hand-written instance twins.
    template_file = Path(__file__).with_name('fam5_bridges_templates.py')
    if template_file.exists():
        spec = importlib.util.spec_from_file_location('p1_bridge_templates', template_file)
        templates = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(templates)
        if book in {v[0] for v in templates.SPECS.values()}:
            parent, _ = templates.plan(book, parent)
            tree = lr.parse(parent)
    for rune in RUNES:
        if RUNE_LIBRARIES[rune] != book:
            continue
        if rune in RUNE_GENERATED:
            # The generator emits the private LOCAL enable at the definition,
            # before its own guards/proofs, through the derived policy book.
            info = RUNE_GENERATED[rune]
            assert re.search(r'\(' + re.escape(info['macro']) + r'\s+' +
                             re.escape(info['instance']) + r'(?=\s|\))', parent, re.I), (book, rune)
            if rune not in needed or info['template'] not in ('rep-scalar', 'rep-seq', 'adt-col', 'adt-pool', 'adt-get'):
                continue
            def declarations(n):
                if isinstance(n, lr.Pre):
                    return
                if not isinstance(n, lr.Lst):
                    return
                head = getattr(n.items[0], 'low', '') if n.items else ''
                if head.startswith('must-fail') or head in ('defun', 'defmacro'):
                    return
                if head == info['macro'] and len(n.items) > 1 and getattr(n.items[1], 'low', '') == info['instance'].lower():
                    yield n
                else:
                    for child in n.items:
                        yield from declarations(child)
            hits = [n for f in tree.forms for n in declarations(f)]
            assert len(hits) == 1, (book, rune, 'positive declaration', len(hits))
            event = hits[0]
        else:
            hits = [hit for h in ('defthm', 'defthmd')
                    for hit in lr.match(None, tree.forms, deep=True, head=h, name=rune.lower())]
            assert len(hits) == 1, (book, rune, len(hits))
            event = hits[0].node
            token = event.items[0]
            if token.low == 'defthm':
                tokens.append((token.start, token.end, 'defthmd'))
        pos = parent.index('\n', event.end) + 1
        positions.append(pos)
        if rune in needed:
            private.setdefault(pos, set()).add(rune)
    for pos, runes in private.items():
        current_line = parent[pos:].splitlines(keepends=True)[0] if pos < len(parent) else ''
        if is_enable_line(current_line):
            # Existing defining enables keep their historical provenance.
            old = current_line[len('(local (in-theory (enable '):-len(')))\n')].split()
            assert set(old) <= {r.lower() for r in runes}, (book, old, runes)
            line = enable_line(runes)
            if line != current_line:
                edits.append((pos, pos + len(current_line), line))
        else:
            edits.append((pos, pos, enable_line(runes)))
    changed = lr.write(parent, tokens + edits)
    expected = lr.write(parent, tokens)
    assert without_enable_lines(changed) == without_enable_lines(expected)
    return changed, min(positions, default=0)


def census(patterns, remote=False, kinds=None):
    paths = sorted({p for pattern in patterns for p in glob.glob(pattern)})
    # Search in batches before reading full logs; most successful books do not
    # use the opener. Tail checks still account for every named log.
    candidates = set()
    for first in range(0, len(paths), 400):
        found = subprocess.run(['rg', '--pcre2', '-i', '-l', rune_pattern(RUNES), '--',
                                *paths[first:first + 400]], capture_output=True, timeout=60)
        assert found.returncode in (0, 1), found.stderr.decode()
        candidates.update(found.stdout.decode().splitlines())
    records, successful, rejected = {}, 0, 0
    for path in paths:
        with open(path, 'rb') as stream:
            stream.seek(0, 2)
            stream.seek(max(0, stream.tell() - 4096))
            tail = stream.read()
            if not re.search(rb'^FN_CERTIFY_SUCCESS\b', tail, re.M):
                rejected += 1
                continue
            successful += 1
            if path not in candidates:
                continue
            stream.seek(0)
            text = stream.read().decode('utf-8', 'surrogateescape')
        if not RUNE.search(text):
            continue
        summaries = []
        for match in SUMMARY.finditer(text):
            if RUNE.search(match[2]):
                form = ' '.join(match[1].split())
                name = re.match(r'\(\s*([^\s()]+)\s+([^\s()]+)', form)
                assert name, (path, form)
                if kinds is not None and name[1].upper() not in kinds:
                    continue
                # DEFUN includes its implicit guard proof; explicit guard
                # events are retained too. This is not a DEFTHM-only census.
                summaries.append({'event': name[2], 'event_kind': name[1].upper(), 'form': form,
                                  'runes': sorted({m[1].upper() for m in RUNE.finditer(match[2])}),
                                  'rules_line': text.count('\n', 0, match.start(2)) + 1})
        if not summaries:
            continue
        book = Path(path).name.removesuffix('.certify.log').replace('--', '/') + '.lisp'
        assert book.startswith(('books/', 'tests/acl2/', 'host/')), book
        records.setdefault(book, []).append({
            'log': ('hbox:' if remote else '') + path,
            'events': sorted({s['event'] for s in summaries}),
            'summaries': summaries,
            'runes': sorted({r for s in summaries for r in s['runes']}),
        })
    return {'patterns': patterns, 'logs': len(paths), 'successful_logs': successful,
            'non_success_logs': rejected, 'books': records}


def with_guard_history(base, guard):
    """Merge the disjoint October/all-kind and September/guard-only scopes."""
    base['guard_history'] = {k: v for k, v in guard.items() if k != 'books'}
    for key in ('logs', 'successful_logs', 'non_success_logs'):
        base[key] += guard[key]
    for book, entries in guard['books'].items():
        base['books'].setdefault(book, []).extend(entries)
    return base


def fixtures():
    single = re.compile(rune_pattern(('ADT-NTH-1+',)), re.I)
    two = re.compile(rune_pattern(('ADT-NTH-0', 'ADT-NTH-1+')), re.I)
    assert [m[1] for m in two.finditer('(:REWRITE ADT-NTH-0) (:REWRITE ADT-NTH-1+)')] == ['ADT-NTH-0', 'ADT-NTH-1+']
    assert not two.search('(:REWRITE ADT-NTH-01) (:REWRITE ADT-NTH-1+-DECOY)')
    assert enable_line(('ADT-NTH-1+', 'ADT-NTH-0')) == '(local (in-theory (enable adt-nth-0 adt-nth-1+)))\n'
    good = 'Summary\nForm:  ( DEFTHM FOO ...)\nRules: ((:DEFINITION BAR)\n        (:REWRITE ADT-NTH-1+))\nWarnings: None\n'
    assert [m[1].strip() for m in SUMMARY.finditer(good) if single.search(m[2])] == ['( DEFTHM FOO ...)']
    decoy = 'ACL2 !>>>(IN-THEORY (ENABLE ADT-NTH-1+))\nSummary\nForm: (DEFTHM FOO ...)\nRules: NIL\nTime: 1\n(:REWRITE ADT-NTH-1+)\n'
    assert not any(single.search(m[2]) for m in SUMMARY.finditer(decoy))
    for kind in ('DEFUN', 'VERIFY-GUARDS', 'DEFTHM'):
        sample = good.replace('DEFTHM', kind)
        assert len([m for m in SUMMARY.finditer(sample) if single.search(m[2])]) == 1
    # Multiple summaries in a macro-generated declaration must retain the
    # function/guard use even when the surrounding event's Rules list is NIL.
    guard = good.replace('DEFTHM FOO', 'DEFUN CFGROUP$C-POOLW')
    wrapped = guard + 'Summary\nForm: (ENCAPSULATE NIL ...)\nRules: NIL\nTime: 1\n'
    assert len([m for m in SUMMARY.finditer(wrapped) if single.search(m[2])]) == 1
    zero = good.replace('ADT-NTH-1+', 'ADT-NTH-0')
    assert [m[1].upper() for s in SUMMARY.finditer(zero) for m in two.finditer(s[2])] == ['ADT-NTH-0']
    linear = re.compile(rune_pattern(('ADT-LEN-REGION-BELOW-BODY',)), re.I)
    assert linear.search('(:LINEAR ADT-LEN-REGION-BELOW-BODY)')[1] == 'ADT-LEN-REGION-BELOW-BODY'
    assert not linear.search('(:REWRITE ADT-LEN-REGION-BELOW-BODY)')
    assert not linear.search('(:LINEAR ADT-LEN-REGION-BELOW-BODY-DECOY)')
    assert without_enable_lines(enable_line(RUNES) + 'keep\n') == 'keep\n'


def git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args], timeout=30)


def read_head_sources(root, data):
    """Read immutable HEAD sources for insertion/definition checks only."""
    spec = importlib.util.spec_from_file_location('p1_x4_edges', Path(__file__).with_name('x4_partition.py'))
    edges = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(edges)
    # Some ACL2 negative-domain tests contain complex numeric literals. Extend
    # only the shared reader's literal dispatch; x4's edge visitor is unchanged.
    lr = edges.lr

    class LiteralReader(lr._Reader):
        def dispatch(self, start):
            if self.t[start:start + 2].lower() == '#c':
                self.i = start + 2
                node = self.datum()
                assert isinstance(node, lr.Lst) and len(node.items) == 2, 'malformed complex literal'
                return lr.Pre('#c', node, start, node.end)
            return super().dispatch(start)

    def edge_parse(text):
        reader = LiteralReader(text)
        forms = []
        while True:
            reader.skip()
            if reader.i >= reader.n:
                break
            forms.append(reader.datum())
        return lr.Parsed(text, forms, reader.comments)

    edges.lr = SimpleNamespace(parse=edge_parse)
    edges.fixtures()
    assert edges.stream('books/fixture.lisp', '(assert-event (equal #c(1 2) nil))\n(include-book "child")') == [('include', 'books/child.lisp', 2)]
    revision = data['head']
    tracked = set(git(root, 'ls-tree', '-r', '--name-only', revision,
                      'books', 'host', 'tests/acl2').decode().splitlines())
    # Production books, ACL2 test books, and host certificate subjects. Other
    # raw host files are not ACL2 books; any include dependency is added below.
    roots = {p for p in tracked if p.endswith('.lisp') and p.startswith(('books/', 'tests/acl2/'))}
    roots |= set(data['U_dev']) | set(data['U_lane'])
    # Preserve historical evidence for retired D68 subjects; there is no
    # current book in which to insert an enable. Do not recreate old layouts.
    data['retired_certificate_subjects'] = sorted(roots - tracked)
    roots &= tracked
    graph, source_text, todo, missing = {}, {}, sorted(roots), set()
    while todo:
        pending = sorted(set(todo) - set(graph))
        todo = []
        if not pending:
            break
        missing.update(set(pending) - tracked)
        for book in set(pending) - tracked:
            graph[book] = []  # no HEAD source means no further HEAD edges
        pending = [book for book in pending if book in tracked]
        if not pending:
            continue
        # One batched object read, not thousands of git process startups.
        requests = ''.join(revision + ':' + name + '\n' for name in pending).encode()
        result = subprocess.run(['git', '-C', str(root), 'cat-file', '--batch'],
                                input=requests, capture_output=True, check=True, timeout=60).stdout
        pos = 0
        for book in pending:
            end = result.index(b'\n', pos)
            header = result[pos:end].split()
            assert len(header) == 3 and header[1] == b'blob', (book, header)
            size = int(header[2])
            text = result[end + 1:end + 1 + size].decode('utf-8', 'surrogateescape')
            pos = end + size + 2
            source_text[book] = text
            graph[book] = [arg for kind, arg, _ in edges.stream(book, text) if kind == 'include']
            todo.extend(graph[book])
        assert pos == len(result)
    data['source_check_missing_targets'] = sorted(missing)
    return source_text


ONE_WORLD_CHANGE = 'f7760ab8c'


def lane_class(path, head):
    result = subprocess.run(['git', '-C', str(path), 'merge-base', '--is-ancestor',
                             ONE_WORLD_CHANGE, head], capture_output=True, timeout=30)
    assert result.returncode in (0, 1), (path, result.stderr.decode())
    if path.name == 'vertical-one-world':
        return 'own', result.returncode
    return ('ancestry_excluded' if result.returncode == 0 else 'other'), result.returncode


def derive_provenance(root, data):
    paths = sorted({str(Path(p).parents[3]) for pattern in (LANE_GLOB, LANE_GUARD_GLOB)
                    for p in glob.glob(pattern)})
    classes = {name: {'logs': 0, 'successful_logs': 0, 'non_success_logs': 0,
                      'books': {}, 'lanes': []} for name in ('own', 'other', 'ancestry_excluded')}
    lanes = {}
    for path in paths:
        lane_root = Path(path)
        assert lane_root.parent == root.parent, path
        head = git(lane_root, 'rev-parse', 'HEAD').decode().strip()
        kind, code = lane_class(lane_root, head)
        found = with_guard_history(census([str(lane_root / 'build/acl2/certify-202610*/*.certify.log')]),
                    census([str(lane_root / 'build/acl2/certify-202609*/*.certify.log')], kinds=GUARD_KINDS))
        lanes[lane_root.name] = {'head': head, 'class': kind, 'ancestry_exit': code,
                                **{k: v for k, v in found.items() if k != 'books'},
                                'used_books': sorted(found['books'])}
        group = classes[kind]
        group['lanes'].append(lane_root.name)
        for key in ('logs', 'successful_logs', 'non_success_logs'):
            group[key] += found[key]
        for book, entries in found['books'].items():
            group['books'].setdefault(book, []).extend([{**entry, 'lane': lane_root.name,
                                                         'lane_head': head, 'provenance': kind}
                                                        for entry in entries])
    # Validate classification snapshots after the census, without writes to lanes.
    for name, info in lanes.items():
        assert git(root.parent / name, 'rev-parse', 'HEAD').decode().strip() == info['head'], (name, 'HEAD changed during census')
    data['provenance'] = classes
    data['lane_heads'] = lanes
    total = {'patterns': [LANE_GLOB], 'books': {}}
    for key in ('logs', 'successful_logs', 'non_success_logs'):
        total[key] = sum(group[key] for group in classes.values())
    for group in classes.values():
        for book, entries in group['books'].items():
            total['books'].setdefault(book, []).extend(entries)
    data['lane'] = total
    data['U_lane'] = sorted(total['books'])
    data['lane_only'] = sorted(set(data['U_lane']) - set(data['U_dev']))
    data['dev_only'] = sorted(set(data['U_dev']) - set(data['U_lane']))
    data['one_world_change'] = git(root, 'rev-parse', ONE_WORLD_CHANGE).decode().strip()
    dev = set(data['U_dev'])
    other = set(classes['other']['books'])
    own = set(classes['own']['books'])
    excluded = set(classes['ancestry_excluded']['books'])
    data['U_lane_other'] = sorted(other)
    data['U_lane_own'] = sorted(own)
    data['U_lane_ancestry_excluded'] = sorted(excluded)
    data['own_only'] = sorted(own - dev - other - excluded)
    data['own_without_genuine'] = sorted(own - dev - other)
    data['unqualified_only'] = sorted((own | excluded) - dev - other)
    data['U'] = sorted((dev | other) - set(EXCLUDED))
    data['per_rune'] = {}
    for rune in RUNES:
        sets = {'U_dev': sorted(b for b, es in data['dev']['books'].items()
                                if any(rune in e['runes'] for e in es))}
        for kind, group in classes.items():
            sets['U_lane_' + kind] = sorted(b for b, es in group['books'].items()
                                            if any(rune in e['runes'] for e in es))
        sets['U'] = sorted((set(sets['U_dev']) | set(sets['U_lane_other'])) - set(EXCLUDED))
        data['per_rune'][rune] = sets
    # Retired HC classification is not part of the provenance derivation.
    for key in ('HC', 'hc_undecided', 'hc_undecided_paths', 'lane_outside_HC', 'hc_scope'):
        data.pop(key, None)


def main():
    global RUNES, RUNE
    args = argparse.ArgumentParser(description=__doc__)
    args.add_argument('--scan-remote', action='store_true')
    args.add_argument('--scan', action='store_true')
    args.add_argument('--provenance', action='store_true', help='rescan lane logs with HEAD ancestry classes; reuse recorded dev evidence')
    args.add_argument('--apply', action='store_true')
    args.add_argument('--report', action='store_true')
    args.add_argument('--runes', nargs='+', default=list(RUNES), help='pair-rule names (canonical order is sorted)')
    opts = args.parse_args()
    RUNES = tuple(sorted(set(r.upper() for r in opts.runes)))
    assert RUNES and set(RUNES) <= set(RUNE_LIBRARIES), RUNES
    RUNE = re.compile(rune_pattern(RUNES), re.I)
    fixtures()
    if opts.scan_remote:
        print(json.dumps(with_guard_history(census(REMOTE_GLOBS, remote=True),
                         census(REMOTE_GUARD_GLOBS, remote=True, kinds=GUARD_KINDS))))
        return
    out = Path(__file__).resolve().parent
    root = out.parents[2]
    assert str(root) == '/Users/ember/dev/fn/build/lanes/vertical-one-world', root
    if opts.scan:
        dev = with_guard_history(census([DEV_GLOB]), census([DEV_GUARD_GLOB], kinds=GUARD_KINDS))
        command = ['timeout', '180', 'ssh', '-o', 'ControlMaster=no', '-o', 'ControlPath=none',
                   '-o', 'ConnectTimeout=15', 'hbox', 'python3 - --scan-remote --runes ' + shlex.join(RUNES)]
        remote = subprocess.run(command, input=Path(__file__).read_bytes(),
                                capture_output=True, timeout=190, check=True)
        (out / 'p1-remote-census.json').write_bytes(remote.stdout)
        remote = json.loads(remote.stdout)
        assert remote['logs'] > 0, 'No remote reference logs found'
        for book, evidence in remote['books'].items():
            dev['books'].setdefault(book, [])[:0] = evidence
        data = {'head': git(root, 'rev-parse', 'HEAD').decode().strip(), 'gate_prefix': 'fam5',
                'runes': list(RUNES),
                'dev': dev,
                'remote_scope': {k: v for k, v in remote.items() if k != 'books'},
                'U_dev': sorted(dev['books'])}
        derive_provenance(root, data)
        (out / 'p1-census.json').write_text(json.dumps(data, indent=2) + '\n')
        print(json.dumps({k: len(data[k]) for k in ('U_dev', 'U_lane', 'lane_only', 'dev_only')}))
    if opts.provenance:
        data = json.loads((out / 'p1-census.json').read_text())
        assert data['runes'] == list(RUNES), 'rune list changed; run --scan'
        assert git(root, 'rev-parse', 'HEAD').decode().strip() == data['head']
        derive_provenance(root, data)
        (out / 'p1-census.json').write_text(json.dumps(data, indent=2) + '\n')
        print(json.dumps({'U_dev': len(data['U_dev']), 'U_lane_other': len(data['U_lane_other']),
                          'U_lane_own': len(data['U_lane_own']),
                          'U_lane_ancestry_excluded': len(data['U_lane_ancestry_excluded']),
                          'own_only': len(data['own_only']), 'U': len(data['U'])}))
    if opts.apply:
        data = json.loads((out / 'p1-census.json').read_text())
        assert data['runes'] == list(RUNES), 'rune list changed; run --scan'
        assert git(root, 'rev-parse', 'HEAD').decode().strip() == data['head']
        for evidence in data['dev']['books'].values():
            evidence.sort(key=lambda entry: (not entry['log'].startswith('hbox:'), entry['log']))
        sys.path.insert(0, str(root / 'tools'))
        import lisp_rewrite as lr
        assert 'provenance' in data, 'run --provenance or --scan first'
        assert set(data['U']) == (set(data['U_dev']) | set(data['U_lane_other'])) - set(EXCLUDED)
        for name, info in data['lane_heads'].items():
            assert git(root.parent / name, 'rev-parse', 'HEAD').decode().strip() == info['head'], (name, 'HEAD changed since provenance census')
        head_sources = read_head_sources(root, data)

        def head(node):
            return node.items[0].low if isinstance(node, lr.Lst) and node.items and isinstance(node.items[0], lr.Atom) else ''

        def last_include(tree):
            anchors = [form for form in tree.forms if head(form) == 'include-book']
            assert anchors, 'no top-level include-book'
            return anchors[-1]

        fixture = lr.parse('(include-book "a")\n(local (include-book "b"))\n'
                           '(include-book "c") ; keep\n(encapsulate () (include-book "d"))\n')
        anchor_fixture = last_include(fixture)
        assert fixture.text[anchor_fixture.start:anchor_fixture.end] == '(include-book "c")'
        fixture_pos = fixture.text.index('\n', anchor_fixture.end) + 1
        fixture_changed = lr.write(fixture.text, [(fixture_pos, fixture_pos, LINE)])
        assert fixture_changed == fixture.text[:fixture_pos] + LINE + fixture.text[fixture_pos:]
        assert fixture_changed.replace(LINE, '', 1) == fixture.text

        def includes(node, local=False):
            h = head(node)
            if h == 'include-book':
                yield node, local
            elif h in ('local', 'encapsulate', 'progn'):
                for child in node.items[1:]:
                    yield from includes(child, local or h == 'local')

        parsed = {}

        def source(book):
            if book not in parsed:
                parsed[book] = lr.parse(head_sources[book])
            return parsed[book]

        def target(book, node):
            if any(isinstance(x, lr.Atom) and x.low == ':dir' for x in node.items):
                return None  # system books cannot define this project's rune
            assert isinstance(node.items[1], lr.Str), (book, node)
            path = root / Path(book).parent / (node.items[1].text[1:-1] + '.lisp')
            return path.resolve().relative_to(root).as_posix()

        export_cache = {}

        def exports_rune(book, seen, rune):
            key = book, rune
            if key in export_cache:
                return export_cache[key]
            # Visit each book once. Recursive path copying revisited diamonds
            # exponentially when the target library was absent from a branch.
            visited, pending = set(seen), [book]
            while pending:
                current = pending.pop()
                if current == RUNE_LIBRARIES[rune]:
                    export_cache[key] = True
                    return True
                if current in visited:
                    continue
                visited.add(current)
                for form in source(current).forms:
                    for node, local in includes(form):
                        dep = target(current, node)
                        if not local and dep:
                            pending.append(dep)
            export_cache[key] = False
            return False

        plans, judgment, undefined, existing = {}, {}, [], []
        accepted_current = {}
        # A28 explicitly authorizes the four named guard repairs after an
        # off/on proof control. Do not relabel those replay results as dev
        # certificates or relax the historical success/provenance predicate.
        guard_map = {'cfgroup': 'books/proto/adt-config-groups.lisp',
                     'cfpolicy': 'books/proto/adt-config-policy.lisp',
                     'cpent': 'books/proto/adt-consumer-position.lisp',
                     'stxa': 'books/proto/adt-topic-accepted-type.lisp'}
        guard_file = out / 'p1d-guards.json'
        authorized = []
        if guard_file.exists() and 'ADT-NTH-1+' in RUNES:
            controls = json.loads(guard_file.read_text())
            for name, book in guard_map.items():
                assert not controls[name]['off']['admitted'] and controls[name]['on']['admitted'], name
                assert book not in EXCLUDED
                authorized.append(book)
        needed = {book: sorted(r for r in RUNES if book in data['per_rune'][r]['U'])
                  for book in data['U'] if book in head_sources}
        data['retired_qualifying_users'] = sorted(set(data['U']) - set(needed))
        for book in authorized:
            needed[book] = sorted(set(needed.get(book, [])) | {'ADT-NTH-1+'})
        template_spec = importlib.util.spec_from_file_location('p1_templates', out / 'fam5_bridges_templates.py')
        templates = importlib.util.module_from_spec(template_spec)
        template_spec.loader.exec_module(templates)
        template_books = {v[0] for v in templates.SPECS.values()} if RUNE_GENERATED else set()
        selected = sorted(set(needed) | {RUNE_LIBRARIES[r] for r in RUNES} | template_books)
        for book in selected:
            needed.setdefault(book, [])
        # Exclusions still forbid consumer lines at the include anchor. A
        # selected defining event has its established immediate LOCAL-enable
        # exception, derived from the same qualifying history before removing
        # consumer exclusions. Keep those sets and this exception distinct.
        defining_needed = {
            book: sorted(r for r in RUNES if RUNE_LIBRARIES[r] == book and
                         book in set(data['per_rune'][r]['U_dev']) |
                                    set(data['per_rune'][r]['U_lane_other']))
            for book in {RUNE_LIBRARIES[r] for r in RUNES}}
        # read_head_sources already covers all tracked books; all named guards
        # use that same immutable source/insertion check as census selections.
        for book in selected:
            parent = head_sources[book]
            owns = book in {RUNE_LIBRARIES[r] for r in RUNES} | template_books
            changed, pos = library_change(parent, lr, book, defining_needed.get(book, [])) if owns else (parent, 0)
            imported = [r for r in needed[book] if RUNE_LIBRARIES[r] != book]
            if imported:
                tree = lr.parse(changed)
                anchor = last_include(tree)
                wrapped = [tree.text[n.start:n.end] for f in tree.forms if head(f) != 'include-book'
                           for n, _ in includes(f)]
                if wrapped:
                    judgment[book] = {'wrapped_includes': wrapped,
                                      'anchor': tree.text[anchor.start:anchor.end]}
                defined = all(any(dep and exports_rune(dep, set(), rune)
                                 for f in tree.forms if f.end <= anchor.end
                                 for n, _ in includes(f) for dep in [target(book, n)])
                              for rune in imported)
                if not defined:
                    undefined.append(book)
                end = changed.find('\n', anchor.end)
                assert end >= 0, (book, 'anchor has no newline')
                remainder = changed[anchor.end:end].strip()
                assert not remainder or remainder.startswith(';'), (book, remainder)
                pos = end + 1
                line = enable_line(imported)
                old_line = changed[pos:].splitlines(keepends=True)[0] if pos < len(changed) else ''
                before_insert = changed
                if is_enable_line(old_line):
                    old_runes = set(old_line[len('(local (in-theory (enable '):-len(')))\n')].split())
                    assert old_runes <= {r.lower() for r in imported}, (book, 'committed enable lost historical provenance')
                    changed = lr.write(changed, [(pos, pos + len(old_line), line)])
                    existing.append(book)
                else:
                    changed = lr.write(changed, [(pos, pos, line)])
                assert changed[pos:pos + len(line)] == line
                assert without_enable_lines(changed) == without_enable_lines(before_insert), (book, 'consumer byte identity')
            elif owns:
                existing.append(book)
            current = (root / book).read_bytes().decode('utf-8', 'surrogateescape')
            assert current in (parent, changed), (book, 'concurrent/non-P1 change')
            accepted_current[book] = current
            plans[book] = (parent, changed, pos)
        policy_book = 'books/proof-bridge-policy.lisp'
        policy_names = sorted(r for rs in defining_needed.values() for r in rs if r in RUNE_GENERATED)
        policy_parent = head_sources.get(policy_book, '')
        policy_text = templates.policy_source(policy_names)
        policy_path = root / policy_book
        assert (policy_path.read_text() if policy_path.exists() else '') in (policy_parent, policy_text)
        accepted_current[policy_book] = policy_path.read_text() if policy_path.exists() else ''
        plans[policy_book] = (policy_parent, policy_text, 0)
        needed[policy_book] = []
        data['generated_private_policy'] = policy_names
        data['generated_internal_private_events'] = sorted(RUNE_GENERATED)
        assert not undefined, ('rune undefined at insertion point', undefined)
        for book, (parent, changed, pos) in plans.items():
            path = root / book
            current = path.read_bytes().decode('utf-8', 'surrogateescape') if path.exists() else ''
            assert current in (parent, changed, accepted_current[book]), (book, 'concurrent change after planning')
            if current != changed:
                path.write_bytes(changed.encode('utf-8', 'surrogateescape'))
        data['edited'] = sorted(plans)
        data['new_proof_policy_book'] = policy_book
        data['gate_prefix'] = 'fam5-bridges' if 'FN-SCC-OCTET-LISTP-IS-ADT-OCTETSP' in RUNES else ('fam5-a' if 'FN-CPL-LAST-SKIPS' in RUNES else 'fam5')
        data['needed_runes'] = needed
        data['defining_needed_runes'] = defining_needed
        data['changed_from_parent'] = sorted(book for book, (parent, changed, _) in plans.items() if parent != changed)
        data['byte_identity'] = {'consumer_enable_lines_only': True,
                                 'library_exception': 'selected pair-rule DEFTHM -> DEFTHMD, plus derived defining-book LOCAL enables'}
        for rune in RUNES:
            data['per_rune'][rune]['enabled_books'] = sorted(
                {b for b, rs in needed.items() if rune in rs} |
                {b for b, rs in defining_needed.items() if rune in rs})
        data['existing_enables'] = sorted(existing)
        data['new_enables'] = sorted(set(plans) - set(existing))
        data['authorized_guard_repairs'] = sorted(authorized)
        data['guard_repairs_without_historical_logs'] = sorted(set(authorized) - set(data['U']))
        data['judgment'] = judgment
        data['undefined_at_insertion'] = undefined
        data['excluded'] = EXCLUDED
        data['excluded_dev_users'] = sorted(set(EXCLUDED) & set(data['U_dev']))
        data['insertions'] = {book: {'line': parent.count('\n', 0, pos) + 1,
                                     'parent_sha256': hashlib.sha256(parent.encode('utf-8', 'surrogateescape')).hexdigest()}
                              for book, (parent, _, pos) in plans.items()}
        (out / 'p1-census.json').write_text(json.dumps(data, indent=2) + '\n')
        (out / 'p1-enables.txt').write_text(''.join(book + '\t' + ' '.join(needed[book]) + '\n' for book in plans))
        evidence = {book: [{**entry, 'world': 'dev'} for entry in data['dev']['books'].get(book, [])] +
                          [{**entry, 'world': 'lane_other'} for entry in data['provenance']['other']['books'].get(book, [])]
                    for book in plans}
        for name, book in guard_map.items():
            if book in authorized and book not in data['per_rune']['ADT-NTH-1+']['U']:
                evidence[book].append({'world': 'A28-authorized-guard-repair',
                    'runes': ['ADT-NTH-1+'],
                    'event': name.upper() + '$C-POOLW', 'control': controls[name],
                    'not_historical_certificate_evidence': True})
        package = {book: {'runes': sorted(set(needed[book]) | set(defining_needed.get(book, []))),
                           'consumer_runes': needed[book],
                           'defining_runes': defining_needed.get(book, []),
                           'enable_lines': [l.rstrip() for l in plans[book][1].splitlines(keepends=True) if is_enable_line(l)],
                           'generated_defining_enable_events': [enable_line((r,)).rstrip() for r in defining_needed.get(book, []) if r in RUNE_GENERATED],
                           'generated_internal_private_events': [enable_line((r,)).rstrip() for r, info in RUNE_GENERATED.items() if info['book'] == book],
                           'placement': 'after each defining DEFTHMD; prior consumer enables retained' if book in set(RUNE_LIBRARIES.values()) else 'after last top-level include',
                           'evidence': evidence[book]} for book in plans}
        # A disabled rule with no historical users still needs explicit census
        # evidence. Keep the book-keyed package stable; annotate the definition
        # book rather than inventing a consumer or an enable.
        for rune in RUNES:
            package[RUNE_LIBRARIES[rune]].setdefault('defined_runes', {})[rune] = {
                'class': RUNE_CLASSES[rune], 'default': 'disabled',
                'users': data['per_rune'][rune],
                'evidence': [dict(entry, world=world)
                             for world, books in [('dev', data['dev']['books']),
                                                  ('lane_other', data['provenance']['other']['books'])]
                             for entries in books.values() for entry in entries if rune in entry['runes']],
                'zero_historical_users': not data['per_rune'][rune]['U_dev'] and
                                         not data['per_rune'][rune]['U_lane_other']}
        for book in data['retired_qualifying_users']:
            package[book] = {'runes': sorted(r for r in RUNES if book in data['per_rune'][r]['U']),
                             'current_subject': False, 'enable_lines': [],
                             'placement': 'retired D68 subject; evidence retained, no source recreated',
                             'evidence': [dict(e, world=world)
                                          for world, books in [('dev', data['dev']['books']),
                                                               ('lane_other', data['provenance']['other']['books'])]
                                          for e in books.get(book, [])]}
        (out / 'p1-enables.json').write_text(json.dumps(package, indent=2) + '\n')
        print(json.dumps({'edited': len(plans), 'judgment': judgment,
                          'U': len(data['U']), 'own_only': len(data['own_only']),
                          'excluded_dev_users': data['excluded_dev_users'], 'undefined': undefined}, indent=2))
    if opts.report:
        report(out)


def report(out):
    data = json.loads((out / 'p1-census.json').read_text())
    lines = ['# P1 — derived LOCAL enables for recognizer bridges and openers', '',
             f"At parent `{data['head']}`, |U_dev| = {len(data['U_dev'])}, |U_lane_other| = {len(data['U_lane_other'])}, "
             f"|U_lane_own| = {len(data['U_lane_own'])}, |U_lane_ancestry_excluded| = {len(data['U_lane_ancestry_excluded'])}, "
             f"|U| = {len(data['U'])}; own-only books = {len(data['own_only'])}. "
             f"{len(data['edited'])} current subjects are processed. Ordinary consumers get one combined line; "
             'literal defining events and generated proof environments are recorded separately. '
             f"{len(data['changed_from_parent'])} files differ from the parent. No proof or certificate is claimed.", '',
             '`U = (U_dev union U_lane_other) minus the seven exclusions`. '
             'Own-lane logs and logs from other lanes whose current HEAD contains the one-world change are not qualifying evidence. '
             'Include-closure membership is not a selection criterion.', '',
             'Only successful certify logs (`FN_CERTIFY_SUCCESS`) and their Form/Rules summaries count. '
             'Source echoes, hints, warnings and failed/incomplete certify attempts are excluded. '
             'Evidence is the union of the named dev log scopes; hbox reference evidence is preferred in provenance ordering. '
             'Historical logs establish use, not certification of the current closure.', '',
             'The census includes DEFTHM, DEFUN (including implicit guard proofs), and VERIFY-GUARDS summaries. '
             'The original generic Form/Rules parser already accepted DEFUN; the old `certify-2026101*` scope '
             'omitted October 1–9 guard evidence. The current scope is all October, with the same success, '
             'provenance and seven-book exclusion rules.', '',
             'A28 separately authorizes the four named proto guard repairs after off/on proof controls. '
             'These do not alter U or qualify own-lane replay output as a dev certificate. '
             f"Named guard repairs without historical logs in the named corpus: {', '.join(data.get('guard_repairs_without_historical_logs', [])) or 'none'}. "
             'Their recorded provenance in p1-enables.json is A28-authorized-guard-repair.', '',
             '## Log scope', '', f"- Local dev: `{DEV_GLOB}` plus guard-only `{DEV_GUARD_GLOB}` — {data['dev']['logs']} combined logs, {data['dev']['successful_logs']} successful.",
             f"- Local lane: `{LANE_GLOB}` plus guard-only `{LANE_GUARD_GLOB}` — {data['lane']['logs']} combined logs, {data['lane']['successful_logs']} successful."]
    lines += ['', '## Counts per rune', '',
              '| Rune | Dev | Other lane | Own lane (excluded) | Ancestry excluded | Historical U | Enabled books |',
              '| --- | ---: | ---: | ---: | ---: | ---: | ---: |']
    for rune, sets in data['per_rune'].items():
        lines.append('| ' + rune + ' | ' + ' | '.join(str(len(sets[k])) for k in
                     ('U_dev', 'U_lane_other', 'U_lane_own', 'U_lane_ancestry_excluded', 'U', 'enabled_books')) + ' |')
    lines += ['', f"Census-selected enable-book union: **{len(set().union(*(set(v['enabled_books']) for v in data['per_rune'].values())))}**. "
              'The 102-rule list includes generator fan-out; family completeness and controls are in [FAM5.md](FAM5.md).', '',
              'Retired qualifying subjects (evidence retained, no old source recreated): ' + ', '.join(data.get('retired_qualifying_users', [])) + '.', '',
              'Generator-internal LOCAL enables preserve the uniform private proof environment. Consumer and post-ENCAPSULATE enables follow historical U; internal events are listed separately in p1-enables.json.', '',
              '## Remote log scope', '']
    for pattern in REMOTE_GLOBS + REMOTE_GUARD_GLOBS:
        lines.append(f'- Read-only hbox: `{pattern}`.')
    remote = data['remote_scope']
    lines += [f"- Remote total: {remote['logs']} logs, {remote['successful_logs']} successful.", '',
              '## Provenance classes', '',
              f"Other lane HEADs were checked read-only with `git -C /absolute/lane merge-base --is-ancestor {ONE_WORLD_CHANGE} HEAD` "
              f"(resolved change `{data['one_world_change']}`). Exit 0 excludes that lane; exit 1 qualifies it. "
              'Own-lane logs are always excluded. HEADs were checked unchanged after the census.', '',
              '| Class | Lanes | Logs | Successful logs | Other logs | Used books |',
              '| --- | ---: | ---: | ---: | ---: | ---: |']
    lines.append(f"| dev (local + hbox references) | — | {data['dev']['logs'] + remote['logs']} | "
                 f"{data['dev']['successful_logs'] + remote['successful_logs']} | "
                 f"{data['dev']['non_success_logs'] + remote['non_success_logs']} | {len(data['U_dev'])} |")
    for name, group in data['provenance'].items():
        lines.append(f"| {name} | {len(group['lanes'])} | {group['logs']} | {group['successful_logs']} | {group['non_success_logs']} | {len(group['books'])} |")
    lines += ['', 'Book counts overlap between classes; log counts do not. Lane classification covers every lane represented in the named log glob. '
              'Both dev and lane evidence were freshly scanned for the complete rune list.', '',
              '| Lane | HEAD | Class | Ancestry exit | Logs | Successful | Used books |',
              '| --- | --- | --- | ---: | ---: | ---: | ---: |']
    for name, info in data['lane_heads'].items():
        lines.append(f"| {name} | `{info['head']}` | {info['class']} | {info['ancestry_exit']} | {info['logs']} | {info['successful_logs']} | {len(info['used_books'])} |")
    lines += ['', '## Exclusions', '']
    for book, reason in EXCLUDED.items():
        status = ('dev Rules use' if book in data['U_dev'] else
                  'eligible other-lane Rules use' if book in data['U_lane_other'] else
                  'own/ancestry-excluded Rules use' if book in data['U_lane'] else 'no recorded Rules use')
        lines.append(f'- `{book}`: {reason}; {status}; no book-level enable.')
    for book in data['excluded_dev_users']:
        events = sorted({event for e in data['dev']['books'][book] for event in e['events']})
        defining = data.get('defining_needed_runes', {}).get(book, [])
        handling = ('Selected defining-event exception only: immediate LOCAL enable for ' +
                    ', '.join(defining) + '; no consumer enable at the include anchor.'
                    if defining else 'Event-level handling required; no book-level enable authorized.')
        lines.append(f"  Dev events in `{book}`: {', '.join(events)}. {handling}")
    lines += ['', f"## U_lane minus U_dev ({len(data['lane_only'])})", '',
              'Coverage difference only; enable decisions follow log provenance.']
    lines += ['- `' + book + '`' for book in data['lane_only']] or ['None.']
    lines += ['', f"## U_dev minus U_lane ({len(data['dev_only'])})", '']
    lines += ['- `' + book + '`' for book in data['dev_only']] or ['None.']
    lines += ['', f"## Books used only in vertical-one-world logs ({len(data['own_only'])})", '',
              'Each receives no enable; subsequent certify decides.']
    lines += ['- `' + book + '`' for book in data['own_only']] or ['None.']
    lines += ['', f"## Books with no qualifying provenance ({len(data['unqualified_only'])})", '',
              'Union of own and ancestry-excluded users minus dev and qualifying other-lane users. No enable.']
    lines += ['- `' + book + '`' for book in data['unqualified_only']] or ['None.']
    for key in ('U_dev', 'U_lane_other', 'U_lane_own', 'U_lane_ancestry_excluded', 'U'):
        lines += ['', f'## {key} ({len(data[key])})', '']
        lines += ['- `' + book + '`' for book in data[key]]
    lines += ['', '## Insertion checks', '',
              'Each ordinary consumer is asserted byte-for-byte equal to HEAD after removing only the canonical P1 enable lines; '
              'the exact new text is also constructed from HEAD by one insertion or replacement at the same anchor. '
              'Runes are uppercase-sorted, rendered lowercase, and only the runes selected for that book are enabled. '
              'Consumers use their last raw top-level include-book. The defining libraries preserve prior opener enables '
              'and receive selected DEFTHM-to-DEFTHMD tokens and private enables. Generator template heads and private event splices, plus the uniform proof-only event builder, are the explicit generated-source exceptions. '
              'The rune is reachable through non-local exported include closures at every insertion point. '
              'Undefined at insertion: none.', '', 'Wrapped include-book judgment:']
    for book, item in data['judgment'].items():
        lines.append(f"- `{book}`: inserted after `{item['anchor']}`; wrapped includes do not displace this top-level anchor: " + ', '.join('`' + s + '`' for s in item['wrapped_includes']) + '.')
    if not data['judgment']:
        lines.append('None.')
    lines += ['', '## Gates', '']
    for name, command in [('one-world', 'python3 tools/one_world_check.py'),
                          ('book-roots', 'python3 tools/book_roots_check.py'),
                          ('host-attach-order', 'python3 tools/host_check.py --attach-order'),
                          ('host-world', 'python3 tools/host_check.py --world'),
                          ('extract-world', 'python3 tools/extract/world.py --check'),
                          ('interface', 'python3 tools/interface_emit.py --check')]:
        prefix = data.get('gate_prefix', 'p1')
        log = out / (prefix + '-gate-' + name + '.log')
        code = out / (prefix + '-gate-' + name + '.exit')
        result = code.read_text().strip() if code.exists() else 'not run'
        lines.append(f'- `{command}`: exit {result}; [{log.name}]({log.name}).')
    lines += ['', 'The two tools without executable bits were invoked through python3; source permissions were unchanged.', '',
              'The exact sorted edit list is [p1-enables.txt](p1-enables.txt); '
              'book-to-log/event evidence is [p1-enables.json](p1-enables.json); '
              'provenance sets, lane HEADs, excluded evidence and selection are [p1-census.json](p1-census.json). '
              'This derivation does not claim a certificate. Guard replay and diagnosis results are in P1D.md; no commits.', '']
    (out / 'P1.md').write_text('\n'.join(lines))


if __name__ == '__main__':
    main()
