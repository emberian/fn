#!/usr/bin/env python3
"""Bounded two-host native STARTTLS+AUTHINFO peering gate.

The two native owners bind remote loopback only. Four SSH forwards connect each
remote loopback feed endpoint through the driver; Python configures and observes
but is never an NNTP peer implementation.
"""
import argparse, hashlib, os, re, secrets, shlex, socket, ssl, subprocess, tempfile, time
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
    while time.monotonic() < deadline:
        line = process.stdout.readline()
        if line.startswith(prefix): return line
        if process.poll() is not None:
            raise RuntimeError("owner exited {}: {}".format(process.returncode,
                               process.stderr.read().decode("utf-8", "replace")))
    raise TimeoutError(prefix)


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
            stream = tls.makefile("rwb", buffering=0)
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
    ap.add_argument("--source", required=True)
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
            expected=(getattr(args,"launcher_sha_"+side),getattr(args,"core_sha_"+side),getattr(args,"runtime_sha_"+side))
            if (launcher,core_sha,runtime_sha) != expected: raise RuntimeError("image identity mismatch on "+host)
            root="/tmp/fn-protected-{}-{}".format(args.source[:12],token)
            ssh(host,["mkdir","-m","700",root])
            listen=remote_port(host); tunnel=remote_port(host)
            cert=root+"/cert.pem"; key=root+"/key.pem"; store=root+"/store"; config=root+"/fn.toml"; auth=root+"/auth.toml"
            ssh(host,["openssl","req","-x509","-newkey","rsa:2048","-nodes","-sha256","-days","1","-subj","/CN=localhost","-keyout",key,"-out",cert])
            ssh(host,[image,"--fn","store",store,"init","fn.test"])
            nodes.append(dict(side=side,host=host,image=image,root=root,listen=listen,tunnel=tunnel,cert=cert,key=key,store=store,config=config,auth=auth))
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
            p=subprocess.Popen(["ssh","-N","-o","ExitOnForwardFailure=yes","-L","{}:127.0.0.1:{}".format(local_ports[n["side"]],n["listen"]),n["host"]])
            tunnels.append(p)
        # Reverse forwards expose the driver's opposite local forward to each
        # remote feed dialer, still on remote loopback only.
        for n,other in ((nodes[0],nodes[1]),(nodes[1],nodes[0])):
            p=subprocess.Popen(["ssh","-N","-o","ExitOnForwardFailure=yes","-R","{}:127.0.0.1:{}".format(n["tunnel"],local_ports[other["side"]]),n["host"]])
            tunnels.append(p)
        time.sleep(1)
        if any(p.poll() is not None for p in tunnels): raise RuntimeError("SSH tunnel failed")
        for n,other in ((nodes[0],nodes[1]),(nodes[1],nodes[0])):
            anchor=n["root"]+"/peer-ca.pem"; write_remote(n["host"],anchor,Path(other["local_cert"]).read_bytes(),"600")
            profile=n["root"]+"/outbound.fnauth"; write_remote(n["host"],profile,("FNAUTH1\n{}\n{}\n".format(other["login"],other["password"])).encode(),"600")
            argv=[n["image"],"--fn","operator",n["config"],"peer","add",other["side"],other["side"]+".example.invalid","127.0.0.1",str(n["tunnel"]),"fn.*","fn.*","principal",n["principal"],profile,"false","true","starttls","localhost",anchor]
            ssh(n["host"],argv)
        for n in nodes:
            pidfile=n["root"]+"/owner.pid"
            remote="echo $$ > {}; exec {}".format(
                shlex.quote(pidfile),
                " ".join(shlex.quote(x) for x in
                         [n["image"],"--fn","operator",n["config"],"run"]))
            cmd=["ssh",n["host"],"sh -c "+shlex.quote(remote)]
            p=subprocess.Popen(cmd,stdout=subprocess.PIPE,stderr=subprocess.PIPE); owners.append(p); wait_line(p,b"LISTENING ")
        for n,other in ((nodes[0],nodes[1]),(nodes[1],nodes[0])):
            mid="<protected-{}-{}@example.invalid>".format(n["side"],token)
            article=("From: gate@example.invalid\r\nNewsgroups: fn.test\r\nSubject: protected\r\nDate: Mon, 21 Sep 2026 12:00:00 +0000\r\nMessage-ID: {}\r\n\r\n{}\r\n".format(mid,n["side"])).encode()
            payload=n["root"]+"/article"; write_remote(n["host"],payload,article,"600")
            ssh(n["host"],[n["image"],"--fn","operator",n["config"],"post","--message-id",mid,"--payload",payload,"--group","fn.test"])
            deadline=time.monotonic()+args.timeout; observed=None
            while time.monotonic()<deadline and observed is None:
                observed=nntp_article(local_ports[other["side"]],other["local_cert"],other["login"],other["password"],mid)
                if observed is None: time.sleep(.2)
            if observed != article: raise RuntimeError("protected transfer mismatch "+n["side"])
        print("PASS source={} hosts={},{}".format(args.source,args.host_a,args.host_b))
    finally:
        for p in owners+tunnels:
            if p.poll() is None: p.terminate()
        for p in owners+tunnels:
            try: p.wait(timeout=10)
            except subprocess.TimeoutExpired: p.kill(); p.wait(timeout=5)
        for n in nodes:
            try:
                cleanup="if test -f {0}/owner.pid; then kill -TERM $(cat {0}/owner.pid) 2>/dev/null || true; fi; rm -rf -- {0}".format(shlex.quote(n["root"]))
                ssh(n["host"],["sh","-c",cleanup],timeout=30)
            except Exception: pass
        local.cleanup()

if __name__ == "__main__": main()
