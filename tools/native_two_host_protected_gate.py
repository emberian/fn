#!/usr/bin/env python3
"""Bounded two-host native STARTTLS+AUTHINFO peering gate.

The two native owners bind remote loopback only. Four SSH forwards connect each
remote loopback feed endpoint through the driver; Python configures and observes
but is never an NNTP peer implementation.
"""
import argparse, os, re, secrets, select, shlex, socket, ssl, subprocess, tempfile, time
from pathlib import Path


def run(argv, *, data=None, timeout=120, check=True):
    result = subprocess.run(argv, input=data, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, timeout=timeout)
    if check and result.returncode:
        raise RuntimeError("{} -> {}\n{}".format(argv, result.returncode,
                                                  result.stderr.decode("utf-8", "replace")))
    return result


def ssh(host, words, **kwargs):
    return run(["ssh", "-o", "BatchMode=yes", host,
                " ".join(shlex.quote(str(x)) for x in words)], **kwargs)


def remote_sha(host, path):
    return ssh(host, ["sha256sum", path]).stdout.decode().split()[0]


def free_port():
    with socket.socket() as probe:
        probe.bind(("127.0.0.1", 0)); return probe.getsockname()[1]


def remote_port(host):
    code = "import socket;s=socket.socket();s.bind(('127.0.0.1',0));print(s.getsockname()[1]);s.close()"
    return int(ssh(host, ["python3", "-c", code]).stdout)


def write_remote(host, path, content, mode="600"):
    encoded = __import__("base64").b64encode(content).decode()
    code = "import base64,pathlib;pathlib.Path({!r}).write_bytes(base64.b64decode({!r}))".format(path, encoded)
    ssh(host, ["python3", "-c", code]); ssh(host, ["chmod", mode, path])


def wait_line(process, prefix, timeout=120):
    deadline = time.monotonic() + timeout
    buffered = bytearray()
    while time.monotonic() < deadline:
        ready,_,_=select.select([process.stdout],[],[],min(1,deadline-time.monotonic()))
        if not ready:
            if process.poll() is not None: break
            continue
        chunk=os.read(process.stdout.fileno(),4096)
        if not chunk: break
        buffered.extend(chunk)
        while b"\n" in buffered:
            line,_,rest=buffered.partition(b"\n"); buffered[:]=rest
            line += b"\n"
            if line.startswith(prefix): return line
    raise RuntimeError("owner readiness failed, status={}".format(process.poll()))


def nntp_article(port, ca, login, password, message_id):
    with socket.create_connection(("127.0.0.1", port), timeout=15) as raw:
        def recvline(sock):
            line = bytearray()
            while not line.endswith(b"\n"):
                chunk = sock.recv(1)
                if not chunk: break
                line.extend(chunk)
            return bytes(line)
        if not recvline(raw).startswith((b"200 ", b"201 ")): return None
        raw.sendall(b"STARTTLS\r\n")
        if not recvline(raw).startswith(b"382 "): return None
        context = ssl.create_default_context(cafile=ca)
        with context.wrap_socket(raw, server_hostname="localhost") as tls:
            with tls.makefile("rwb", buffering=0) as stream:
                stream.write(b"AUTHINFO USER " + login.encode() + b"\r\n")
                if not stream.readline().startswith(b"381 "): return None
                stream.write(b"AUTHINFO PASS " + password.encode() + b"\r\n")
                if not stream.readline().startswith(b"281 "): return None
                stream.write(b"ARTICLE " + message_id.encode() + b"\r\n")
                if not stream.readline().startswith(b"220 "): return None
                out = bytearray()
                while True:
                    line = stream.readline()
                    if line == b".\r\n": return bytes(out)
                    if not line: return None
                    out.extend(line[1:] if line.startswith(b"..") else line)


def main():
    ap = argparse.ArgumentParser()
    for side in "ab":
        ap.add_argument("--host-" + side, required=True)
        ap.add_argument("--image-" + side, required=True)
        ap.add_argument("--launcher-sha-" + side, required=True)
        ap.add_argument("--core-sha-" + side, required=True)
        ap.add_argument("--runtime-sha-" + side, required=True)
        ap.add_argument("--source-manifest-sha-" + side, required=True)
    ap.add_argument("--source", required=True)
    ap.add_argument("--evidence-dir", required=True)
    ap.add_argument("--timeout", type=int, default=300)
    args = ap.parse_args()
    nodes = [] ; tunnels = [] ; owners = []
    token = secrets.token_hex(6)
    local = tempfile.TemporaryDirectory(prefix="fn-two-host-protected-")
    try:
        for side in "ab":
            host=getattr(args,"host_"+side); image=getattr(args,"image_"+side)
            core=image+".core"; launcher=remote_sha(host,image); core_sha=remote_sha(host,core)
            script=ssh(host,["cat",image]).stdout.decode("utf-8","replace")
            match=re.search(r'exec "([^"]+)".*--core "([^"]+)"',script)
            if not match or match.group(2) != core: raise RuntimeError("unbound core path on "+host)
            runtime=match.group(1); runtime_sha=remote_sha(host,runtime)
            manifest=str(Path(image).parent/"build-source.sha256")
            if remote_sha(host,manifest) != getattr(args,"source_manifest_sha_"+side):
                raise RuntimeError("source manifest identity mismatch on "+host)
            expected=(getattr(args,"launcher_sha_"+side),getattr(args,"core_sha_"+side),getattr(args,"runtime_sha_"+side))
            if (launcher,core_sha,runtime_sha) != expected: raise RuntimeError("image identity mismatch on "+host)
            root="/tmp/fn-protected-{}-{}".format(args.source[:12],token)
            ssh(host,["mkdir","-m","700",root])
            listen=remote_port(host); tunnel=remote_port(host)
            cert=root+"/cert.pem"; key=root+"/key.pem"; store=root+"/store"; config=root+"/fn.toml"; auth=root+"/auth.toml"
            node=dict(side=side,host=host,image=image,root=root,listen=listen,tunnel=tunnel,cert=cert,key=key,store=store,config=config,auth=auth,runtime=runtime)
            nodes.append(node)
            ssh(host,["openssl","req","-x509","-newkey","rsa:2048","-nodes","-sha256","-days","1","-subj","/CN=localhost","-keyout",key,"-out",cert])
            ssh(host,[image,"--fn","store",store,"init","fn.test"])
        # Fetch each certificate for local validation and install it as the
        # opposite node's explicit outbound trust anchor.
        for n in nodes:
            local_cert=Path(local.name)/(n["side"]+".pem")
            run(["scp",n["host"]+":"+n["cert"],str(local_cert)])
            n["local_cert"]=str(local_cert)
        passwords={"a":"a-"+secrets.token_hex(12),"b":"b-"+secrets.token_hex(12)}
        for n,other in ((nodes[0],nodes[1]),(nodes[1],nodes[0])):
            login=other["side"]+"-peer" # credential this node grants the other
            config=('[store]\npath = "{store}"\n[listener]\nhost = "127.0.0.1"\nport = {listen}\n'
                    'tls_cert = "{cert}"\ntls_key = "{key}"\n[auth]\nrequired = true\n'
                    'protected_only = true\npath = "{auth}"\n[control]\npath = "{root}/control.sock"\n').format(**n)
            write_remote(n["host"],n["config"],config.encode(),"600")
            pw=passwords[other["side"]]
            ssh(n["host"],[n["image"],"--fn","operator",n["config"],"principal","set-password",login,"--posting"],data=(pw+"\n"+pw+"\n").encode(),timeout=180)
            listing=ssh(n["host"],[n["image"],"--fn","operator",n["config"],"principal","list"]).stdout.decode()
            ids=re.findall(r"[0-9a-f]{64}",listing)
            if len(ids)!=1: raise RuntimeError("principal projection on "+n["host"])
            n["principal"]=ids[0]; n["login"]=login; n["password"]=pw
        # Local forwards expose each remote listener only to this driver.
        local_ports={n["side"]:free_port() for n in nodes}
        for n in nodes:
            p=subprocess.Popen(["ssh","-N","-o","BatchMode=yes","-o","ExitOnForwardFailure=yes","-L","127.0.0.1:{}:127.0.0.1:{}".format(local_ports[n["side"]],n["listen"]),n["host"]])
            tunnels.append(p)
        # Reverse forwards expose the driver's opposite local forward to each
        # remote feed dialer, still on remote loopback only.
        for n,other in ((nodes[0],nodes[1]),(nodes[1],nodes[0])):
            p=subprocess.Popen(["ssh","-N","-o","BatchMode=yes","-o","ExitOnForwardFailure=yes","-R","127.0.0.1:{}:127.0.0.1:{}".format(n["tunnel"],local_ports[other["side"]]),n["host"]])
            tunnels.append(p)
        time.sleep(1)
        if any(p.poll() is not None for p in tunnels): raise RuntimeError("SSH tunnel failed")
        for n,other in ((nodes[0],nodes[1]),(nodes[1],nodes[0])):
            anchor=n["root"]+"/peer-ca.pem"; write_remote(n["host"],anchor,Path(other["local_cert"]).read_bytes(),"600")
            profile=n["root"]+"/outbound.fnauth"; write_remote(n["host"],profile,("FNAUTH1\n{}\n{}\n".format(other["login"],other["password"])).encode(),"600")
            n["anchor"], n["profile"] = anchor, profile
            argv=[n["image"],"--fn","operator",n["config"],"peer","add",other["side"],other["side"]+".example.invalid","127.0.0.1",str(n["tunnel"]),"fn.*","fn.*","principal",n["principal"],profile,"false","true","starttls","localhost",anchor]
            ssh(n["host"],argv)

        def start_owner(n):
            pidfile=n["root"]+"/owner.pid"
            remote="echo $$ > {}; exec {}".format(
                shlex.quote(pidfile),
                " ".join(shlex.quote(x) for x in
                         [n["image"],"--fn","operator",n["config"],"run"]))
            cmd=["ssh","-o","BatchMode=yes",n["host"],"sh -c "+shlex.quote(remote)]
            log=Path(local.name)/(n["side"]+"-owner-{}.stderr".format(len(owners)))
            log_handle=log.open("wb")
            p=subprocess.Popen(cmd,stdout=subprocess.PIPE,stderr=log_handle)
            n["log_handle"],n["log_path"] = log_handle,str(log)
            owners.append(p); n["owner"] = p
            wait_line(p,b"LISTENING ")
            pid=ssh(n["host"],["cat",n["root"]+"/owner.pid"]).stdout.decode().strip()
            n["pid"] = pid
            observed_runtime=ssh(n["host"],["readlink","-f","/proc/"+pid+"/exe"]).stdout.decode().strip()
            if remote_sha(n["host"],observed_runtime) != remote_sha(n["host"],n["runtime"]):
                raise RuntimeError("running runtime identity changed on "+n["host"])
            if remote_sha(n["host"],n["image"]+".core") != getattr(args,"core_sha_"+n["side"]):
                raise RuntimeError("running core changed on "+n["host"])

        def stop_owner(n):
            pidfile=n["root"]+"/owner.pid"
            result=ssh(n["host"],["sh","-c","kill -TERM $(cat {})".format(shlex.quote(pidfile))],check=False)
            if result.returncode not in (0,1): raise RuntimeError("cannot stop owner "+n["host"])
            n["owner"].wait(timeout=30)
            n["log_handle"].flush(); n["log_handle"].close()
            n.pop("owner",None)

        def make_article(n, label):
            mid="<protected-{}-{}-{}@example.invalid>".format(label,n["side"],token)
            article=("From: gate@example.invalid\r\nNewsgroups: fn.test\r\nSubject: protected\r\nDate: Mon, 21 Sep 2026 12:00:00 +0000\r\nMessage-ID: {}\r\n\r\n{}\r\n".format(mid,label)).encode()
            payload=n["root"]+"/"+label+".article"
            write_remote(n["host"],payload,article,"600")
            ssh(n["host"],[n["image"],"--fn","operator",n["config"],"post","--message-id",mid,"--payload",payload,"--group","fn.test"])
            return mid,article

        def await_article(n, mid, article, seconds):
            deadline=time.monotonic()+seconds; observed=None
            while time.monotonic()<deadline and observed is None:
                observed=nntp_article(local_ports[n["side"]],n["local_cert"],n["login"],n["password"],mid)
                if observed is None: time.sleep(.2)
            if observed != article: raise RuntimeError("protected transfer mismatch "+mid)

        def assert_absent(n, mid, seconds=4):
            deadline=time.monotonic()+seconds
            while time.monotonic()<deadline:
                if nntp_article(local_ports[n["side"]],n["local_cert"],n["login"],n["password"],mid) is not None:
                    raise RuntimeError("protected refusal delivered "+mid)
                time.sleep(.2)

        for n in nodes: start_owner(n)
        for n,other in ((nodes[0],nodes[1]),(nodes[1],nodes[0])):
            mid,article=make_article(n,"positive")
            await_article(other,mid,article,args.timeout)

        # A wrong outbound password cannot fall back to cleartext.  The
        # accepted article and FNFD journal remain at A; restoring only the
        # profile and restarting A delivers that same queued obligation.
        a,b=nodes
        stop_owner(a)
        write_remote(a["host"],a["profile"],("FNAUTH1\n{}\nwrong-{}\n".format(b["login"],token)).encode(),"600")
        start_owner(a)
        bad_mid,bad_article=make_article(a,"bad-password")
        assert_absent(b,bad_mid)
        if a["owner"].poll() is not None or b["owner"].poll() is not None:
            raise RuntimeError("bad credential stopped an owner")
        ssh(a["host"],["test","-s",a["store"]+"/feed/"+b["side"]+".fnfd"])
        stop_owner(a)
        write_remote(a["host"],a["profile"],("FNAUTH1\n{}\n{}\n".format(b["login"],b["password"])).encode(),"600")
        start_owner(a); await_article(b,bad_mid,bad_article,args.timeout)

        # An unrelated CA likewise stays peer-local and queued.  Restore the
        # exact target certificate, restart A, and require delivery.
        stop_owner(a)
        write_remote(a["host"],a["anchor"],Path(a["local_cert"]).read_bytes(),"600")
        start_owner(a)
        ca_mid,ca_article=make_article(a,"bad-ca")
        assert_absent(b,ca_mid)
        if a["owner"].poll() is not None or b["owner"].poll() is not None:
            raise RuntimeError("untrusted CA stopped an owner")
        ssh(a["host"],["test","-s",a["store"]+"/feed/"+b["side"]+".fnfd"])
        stop_owner(a)
        write_remote(a["host"],a["anchor"],Path(b["local_cert"]).read_bytes(),"600")
        start_owner(a); await_article(b,ca_mid,ca_article,args.timeout)
        print("PASS declared-source={} hosts={},{}".format(args.source,args.host_a,args.host_b))
    finally:
        cleanup_errors=[]
        for n in nodes:
            try:
                cleanup=("if test -f {0}/owner.pid; then p=$(cat {0}/owner.pid); "
                         "kill -TERM $p 2>/dev/null || true; i=0; while kill -0 $p 2>/dev/null && test $i -lt 50; do sleep .1; i=$((i+1)); done; "
                         "if kill -0 $p 2>/dev/null; then kill -KILL $p 2>/dev/null || true; sleep .2; fi; "
                         "if kill -0 $p 2>/dev/null; then exit 70; fi; fi; rm -rf -- {0}").format(shlex.quote(n["root"]))
                ssh(n["host"],["sh","-c",cleanup],timeout=30)
            except Exception as error:
                cleanup_errors.append("{}: {}".format(n.get("host"),error))
        for p in owners+tunnels:
            if p.poll() is None: p.terminate()
        for p in owners+tunnels:
            try: p.wait(timeout=10)
            except subprocess.TimeoutExpired: p.kill(); p.wait(timeout=5)
        for n in nodes:
            handle=n.get("log_handle")
            if handle is not None and not handle.closed:
                handle.flush(); handle.close()
        evidence=Path(args.evidence_dir); evidence.mkdir(parents=True,exist_ok=True)
        for path in Path(local.name).glob("*.stderr"):
            (evidence/path.name).write_bytes(path.read_bytes())
        local.cleanup()
        if cleanup_errors:
            raise RuntimeError("remote cleanup failed: "+"; ".join(cleanup_errors))

if __name__ == "__main__": main()
