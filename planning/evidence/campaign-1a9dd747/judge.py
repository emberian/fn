"""Judge campaign.json (native_operator_campaign) and nntp-probe.json against the table.

Usage: python3 judge.py campaign.json[.gz] [nntp-probe.json[.gz]]
Prints one Markdown row per cut and column, then the failures with their
observed values.  Every verdict is computed from the record.
"""
import gzip
import json
import sys


def load(path):
    return json.load(gzip.open(path) if path.endswith(".gz") else open(path))


def present(snap):
    return "00000000000000000001.txn" in (snap.get("transactions") or {})


def staging(snap):
    names = sorted((snap.get("staging") or {}).keys())
    return ",".join(n.split("-")[0] + "-" if "-" in n else n for n in names) or "none"


def judge_obs(obs, table, recovery, column):
    problems = []
    seeded = obs["seeded"]["transactions"]
    killed = obs["killed"]["transactions"]
    prior = "00000000000000000000.txn"
    if killed.get(prior) != seeded.get(prior):
        problems.append("prior transaction bytes changed by the death")
    if obs["recover"]["rc"] != 0:
        problems.append("recover rc {}".format(obs["recover"]["rc"]))
    if obs["recovered"]["transactions"] != killed:
        problems.append("recovery changed transactions/")
    if obs["recovered"]["staging"]:
        problems.append("staging not empty after recovery: {}".format(obs["recovered"]["staging"]))
    for reader in ("inspect_prior", "nntp_prior"):
        if not obs.get(reader, {}).get("identical"):
            problems.append("{} not identical: {}".format(reader, obs.get(reader)))
    if obs.get("nntp_prior", {}).get("same_as_inspect") is not True:
        problems.append("prior readers disagree")
    cand = present(obs["recovered"])
    want = {"absent": False, "present": True}.get(table)
    if recovery:
        want = False
    if want is not None and cand != want:
        problems.append("candidate {} but table says {}".format(
            "present" if cand else "absent", table))
    resub = obs.get("resubmit", {})
    if cand:
        if not obs["inspect_candidate"]["identical"] or not obs["nntp_candidate"]["identical"]:
            problems.append("candidate reread not identical")
        if obs["nntp_candidate"]["same_as_inspect"] is not True:
            problems.append("candidate readers disagree")
        if resub.get("rc") != 0 or "duplicate" not in (resub.get("stdout", "") + resub.get("stderr", "")).lower():
            problems.append("resubmit not duplicate: rc {} {!r}".format(resub.get("rc"), resub.get("stdout")))
        if obs["after_resubmit"]["transactions"] != obs["recovered"]["transactions"]:
            problems.append("duplicate resubmit added a transaction")
    else:
        if obs["inspect_candidate"]["rc"] != 1:
            problems.append("absent candidate inspect rc {}".format(obs["inspect_candidate"]["rc"]))
        if not obs["nntp_candidate"]["status"].startswith("430"):
            problems.append("absent candidate NNTP {}".format(obs["nntp_candidate"]["status"]))
        if resub.get("rc") != 0:
            problems.append("resubmit rc {}: {!r}".format(resub.get("rc"), resub.get("stderr")))
        if len(obs["after_resubmit"]["transactions"]) != len(obs["recovered"]["transactions"]) + 1:
            problems.append("resubmit did not add one transaction")
    return cand, problems


def main():
    data = load(sys.argv[1])
    rows, fails = [], []
    for row in data["cuts"]:
        recovery = row["variable"] == "FN_NATIVE_RECOVERY_FAULT"
        coord = row["program"] + (" after " + row["follows"] if row["follows"] else "")
        s, c = row["served"], row["cut_run"]
        sc, sp = judge_obs(s, row["table_candidate"], recovery, "served")
        if recovery:
            if s["owner_ready"] or s["owner"]["rc"] != -9:
                sp.append("served owner ready={} rc={}".format(s["owner_ready"], s["owner"]["rc"]))
            served_exit = "ready {} / - / {}".format(s["owner_ready"], s["owner"]["rc"])
        else:
            if not s["owner_ready"] or s["post"]["rc"] != 3 or s["owner"]["rc"] != -9:
                sp.append("served ready={} client rc={} owner rc={}".format(
                    s["owner_ready"], s.get("post", {}).get("rc"), s["owner"]["rc"]))
            served_exit = "ready {} / {} / {}".format(s["owner_ready"], s["post"]["rc"], s["owner"]["rc"])
        cc, cp = judge_obs(c, row["table_candidate"], recovery, "cut")
        kill = c.get("killed_post") or c.get("killed_recover")
        if kill["rc"] != -9:
            cp.append("cut rc {}".format(kill["rc"]))
        for col, cand, probs, obs, ex in (("served", sc, sp, s, served_exit),
                                          ("store/recover", cc, cp, c, str(kill["rc"]))):
            rc = obs["recover_counts"]
            rows.append("| `{}` | `{}` | {} | {} | {} | {}, {} | {} | {} | {} | {} |".format(
                row["cut"], coord, row["table_candidate"], col, ex,
                len(obs["killed"]["transactions"]), staging(obs["killed"]),
                "{} {} {}".format(rc["transactions"], rc["articles"], rc["staging_orphans"]) if rc else "none",
                "present" if cand else "absent",
                ((obs.get("resubmit", {}).get("stdout", "") + obs.get("resubmit", {}).get("stderr", "")).strip().splitlines() or ["?"])[-1][:40]
                + " rc {}".format(obs.get("resubmit", {}).get("rc")),
                "PASS" if not probs else "FAIL"))
            for p in probs:
                fails.append("{} {}: {}".format(row["cut"], col, p))
    print("| cut | coordinate | table | column | ready / client / owner exit (or cut exit) | at death: txns, staging | recover | candidate | resubmit | verdict |")
    print("|---|---|---|---|---|---|---|---|---|---|")
    print("\n".join(rows))
    print("\ncut observations:", len(rows), "passed:", len(rows) - len({f.split(":")[0] for f in fails}))
    print("failures:")
    for f in fails:
        print("-", f)
    for fault in data.get("faults", []):
        print("fault", fault["name"], json.dumps({k: fault[k].get("rc") if isinstance(fault.get(k), dict) and "rc" in fault[k] else None for k in ("post", "owner", "recover", "first", "second", "open_post", "init", "plain_post")}))
    if len(sys.argv) > 2:
        probe = load(sys.argv[2])
        print("\n| cut | action | table | NNTP reply | owner exit | candidate after | prior reread | candidate reread | repost reply |")
        print("|---|---|---|---|---|---|---|---|---|")
        for r in probe["cuts"] + probe["controls"]:
            cand = present(r["recovered"])
            print("| {} | {} | {} | `{}` | {} | {} | {} | {} | `{}` |".format(
                r.get("cut", r.get("name")), r.get("action", r.get("image")), r.get("table_candidate", "-"),
                r.get("post", {}).get("reply", r.get("post", {}).get("after_kill", "")).strip() or "(closed, no reply)",
                r["owner"]["rc"], "present" if cand else "absent",
                "{}/{}".format(r["inspect_prior"]["identical"], r.get("nntp_prior", {}).get("identical")),
                "{}/{}/{}".format(r["inspect_candidate"]["identical"], r.get("nntp_candidate", {}).get("identical"),
                                  r.get("nntp_candidate", {}).get("same_as_inspect")) if cand else "n/a ({} / {})".format(
                    r["inspect_candidate"]["rc"], r.get("nntp_candidate", {}).get("status", "")[:3]),
                (r.get("repost", {}).get("reply") or "-").strip()))


main()
