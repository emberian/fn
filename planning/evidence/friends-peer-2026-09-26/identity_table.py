#!/usr/bin/env python3
"""The two-machine identity table (friends-peer, SCN-090).

For each node and group, every article as a reader sees it: local number,
Message-ID, the SHA-256 of the served octets, and the SHA-256 of the authored
source by the spec's drop rule (specs/identity.md "The signed bytes", step 3:
the Path, Xref, Injection-Date, Injection-Info and FN-Authorship field lines
are dropped).  A test client only: it decides nothing for the node, and its
authored-source digest is a comparison aid, not the node's identity function.

  identity_table.py GROUP HOST:PORT:CAFILE [HOST:PORT:CAFILE ...]
  (credentials: --credentials FILE, `user password`)
"""
import argparse, hashlib, json, sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[3] / "tools"))
import fn_client

DROP = ("path", "xref", "injection-date", "injection-info", "fn-authorship")


def authored(lines):
    out, dropping, header = [], False, True
    for line in lines:
        if header and line == "":
            header = False
            out.append(line)
            continue
        if header:
            if line[:1] in (" ", "\t"):
                if not dropping:
                    out.append(line)
                continue
            dropping = line.split(":", 1)[0].strip().lower() in DROP
            if dropping:
                continue
        out.append(line)
    return out


def digest(lines):
    return hashlib.sha256("".join(l + "\r\n" for l in lines).encode("utf-8", "surrogateescape")).hexdigest()


def table(group, host, port, cafile, user, password):
    args = argparse.Namespace(host=host, port=int(port), timeout=30.0, plain=False, cafile=cafile)
    client = fn_client.Client(args, user, password)
    client.open()
    rows = []
    try:
        listed = client.listgroup(group)
        for n in listed.data.get("numbers", []):
            status, body = client.cmd("ARTICLE %d" % n, multiline=True)
            if not status.startswith("220"):
                rows.append({"number": n, "status": status})
                continue
            msgid = status.split()[2] if len(status.split()) > 2 else None
            rows.append({"number": n, "message_id": msgid, "served_sha256": digest(body),
                         "authored_sha256": digest(authored(body))})
    finally:
        client.close()
    return rows


def main():
    p = argparse.ArgumentParser()
    p.add_argument("group")
    p.add_argument("nodes", nargs="+")
    p.add_argument("--credentials", required=True)
    a = p.parse_args()
    user, password = Path(a.credentials).read_text().split()[:2]
    result = {}
    for spec in a.nodes:
        host, port, cafile = spec.split(":", 2)
        result["%s:%s" % (host, port)] = table(a.group, host, port, cafile, user, password)
    by_id = {}
    for node, rows in result.items():
        for r in rows:
            by_id.setdefault(r.get("message_id"), {})[node] = r
    agree = all(len({r["authored_sha256"] for r in per.values()}) == 1 and len(per) == len(result)
                for per in by_id.values())
    print(json.dumps({"group": a.group, "nodes": result, "every_id_on_every_node_same_authored_digest": agree}, indent=1))
    for mid, per in sorted(by_id.items(), key=lambda kv: str(kv[0])):
        print("ID", mid, " ".join("%s#%s:%s" % (n, r["number"], r["authored_sha256"][:16]) for n, r in per.items()), file=sys.stderr)
    return 0 if agree else 1


if __name__ == "__main__":
    sys.exit(main())
