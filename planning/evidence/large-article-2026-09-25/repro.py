"""POST sized articles to a developer owner under a 4 MiB profile; print reply,
wall, owner RSS peak and the owner's stderr tail."""
import sys, time, json, shutil, signal
from pathlib import Path
T = Path(sys.argv[1]); work = Path(sys.argv[2]); sizes = [int(x) for x in sys.argv[3].split(",")]
sys.path.insert(0, str(T))
from tests.campaign import native_nntp_post_probe as P
import tests.campaign.native_operator_campaign as C
C.INIT_FLAGS[:] = ["--max-article-octets", "4194304"]
dev = T / "build" / "fn-host-developer"
if work.exists(): shutil.rmtree(work)
work.mkdir(parents=True)
prior = work / "prior.art"; prior.write_bytes(C.article(C.PRIOR_ID, "prior", "prior accepted content"))
def rss_peak(pid):
    try:
        for line in open("/proc/%d/status" % pid):
            if line.startswith("VmHWM"): return line.split()[1] + " kB"
    except OSError: return None
for size in sizes:
    sized = P.sized_article(size)
    node = C.Node(dev, work, "size-%d" % size)
    try:
        row = {}
        C.seed(node, prior, row)
        owner = node.start_owner({"FNX_BACKTRACE": "1"})
        t0 = time.monotonic()
        post = P.nntp_post(node, sized, timeout=600)
        wall = time.monotonic() - t0
        peak = rss_peak(owner["pid"])
        alive = owner["proc"].poll() is None
        stopped = node.stop_owner(owner, signal.SIGTERM)
        insp = node.inspect(C.CANDIDATE_ID)
        stored = insp["_out"]
        print(json.dumps({"size": size, "reply": post.get("reply"), "wall_s": round(wall, 2),
                          "owner_vmhwm": peak, "alive_after": alive,
                          "inspect_rc": insp["rc"], "inspect_len": len(stored)}))
        print("---- owner stderr tail\n" + stopped.get("stderr", "")[-6000:], flush=True)
        print("---- inspect stderr\n" + insp["stderr"][-6000:], flush=True)
        o2 = node.start_owner({"FNX_BACKTRACE": "1"})
        try:
            art = node.nntp_article(C.CANDIDATE_ID)
        except OSError as e:
            art = {"error": repr(e)}
        s2 = node.stop_owner(o2, signal.SIGTERM)
        o = art.get("octets") or b""
        print(json.dumps({"size": size, "article_status": art.get("status"), "article_len": len(o),
                          "reread_identical_to_inspect": o == stored and len(stored) > 0,
                          "source_is_suffix": stored.endswith(sized),
                          "stored_sha256": __import__("hashlib").sha256(stored).hexdigest()}))
        print("---- restarted owner stderr tail\n" + s2.get("stderr", "")[-6000:], flush=True)
    finally:
        node.reap()
