#!/usr/bin/env python3
"""Bounded two-host native STARTTLS+AUTHINFO peering gate.

The two native owners bind remote loopback only. Four SSH forwards connect each
remote loopback feed endpoint through the driver; Python configures and observes
but is never an NNTP peer implementation.
"""
import argparse, hashlib, json, os, re, secrets, select, shlex, socket, ssl, subprocess, tempfile, time
from pathlib import Path


MAX_LAUNCHER_BYTES = 16 * 1024
SAFE_ABSOLUTE = re.compile(r"/[A-Za-z0-9_./+@%:=-]+")
FROZEN_MARKER = "# fn frozen image launcher v1"
FROZEN_PREAMBLE = [
    'here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)',
    'export SBCL_HOME="$here/runtime/sbcl-home/"',
    'export FN_OPENSSL_PREFIX="$here/openssl"',
    'export LD_LIBRARY_PATH="$here/lib:$here/openssl/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"',
]
RUNTIME_FLAGS = {
    "--disable-ldb", "--noinform", "--end-runtime-options",
    "--no-userinit", "--no-sysinit", "--disable-debugger",
    "--end-toplevel-options", "--lose-on-corruption",
}
RUNTIME_NUMBERS = {"--tls-limit", "--dynamic-space-size", "--control-stack-size"}


def literal_absolute_path(path):
    """Accept only a canonical-looking POSIX path, never a shell expression."""
    return (bool(SAFE_ABSOLUTE.fullmatch(path)) and path.startswith("/")
            and all(part not in ("", ".", "..") for part in path.split("/")[1:]))


def launcher_paths(script, image):
    """Recognize the frozen v1 or literal SBCL launcher; do not execute it.

    The one allowed variable in SBCL's generated exec tail is
    ``${SBCL_USER_ARGS}``.  All gate invocations force it empty.  The frozen
    ``$here`` is resolved only through the exact packaging preamble.
    """
    if not literal_absolute_path(image):
        raise ValueError("image path is not canonical absolute")
    if len(script.encode("utf-8")) > MAX_LAUNCHER_BYTES or "\0" in script or "\r" in script:
        raise ValueError("launcher is not bounded text")
    lines = script.splitlines()
    if not lines or lines[0] != "#!/bin/sh":
        raise ValueError("unknown launcher interpreter")
    frozen = FROZEN_MARKER in lines
    body = [line for line in lines[1:] if line.strip() and not line.lstrip().startswith("#")]
    if frozen:
        if lines.count(FROZEN_MARKER) != 1 or body[:-1] != FROZEN_PREAMBLE:
            raise ValueError("unknown frozen launcher preamble")
    else:
        for line in body[:-1]:
            match = re.fullmatch(r"export (SBCL_HOME|FN_OPENSSL_PREFIX|LD_LIBRARY_PATH)='([^']*)'", line)
            if not match or not literal_absolute_path(match.group(2).rstrip("/")):
                raise ValueError("unknown literal launcher environment")
    if not body:
        raise ValueError("launcher has no exec")
    command = body[-1]
    if any(char in command for char in "`;&|<>\\"):
        raise ValueError("launcher exec has shell syntax")
    if not re.fullmatch(r'exec "[^"\n]+"(?: [^\n]+)+ "\$@"', command):
        raise ValueError("unknown launcher exec shape")
    try:
        words = shlex.split(command, posix=True)
    except ValueError as error:
        raise ValueError("unknown launcher quoting") from error
    if len(words) < 5 or words[0] != "exec" or words[-1] != "$@":
        raise ValueError("unknown launcher arguments")
    runtime = words[1]
    core = None
    seen = set()
    args = words[2:-1]
    index = 0
    while index < len(args):
        option = args[index]
        if option in seen and option != "${SBCL_USER_ARGS}":
            raise ValueError("duplicate launcher option")
        if option in RUNTIME_NUMBERS:
            if index + 1 >= len(args) or not args[index + 1].isdecimal() or int(args[index + 1]) <= 0:
                raise ValueError("unknown numeric runtime option")
            seen.add(option); index += 2
        elif option == "--core":
            if index + 1 >= len(args):
                raise ValueError("launcher has no core path")
            seen.add(option); core = args[index + 1]; index += 2
        elif option == "--eval":
            if index + 1 >= len(args) or args[index + 1] != "(acl2::sbcl-restart)":
                raise ValueError("unknown runtime evaluation")
            seen.add(option); index += 2
        elif option == "${SBCL_USER_ARGS}":
            if (option in seen or index == 0 or args[index - 1] != "--noinform"
                    or index + 1 >= len(args) or args[index + 1] != "--end-runtime-options"):
                raise ValueError("unbound SBCL_USER_ARGS position")
            seen.add(option); index += 1
        elif option in RUNTIME_FLAGS:
            seen.add(option); index += 1
        else:
            raise ValueError("unknown runtime option or variable")
    if core is None:
        raise ValueError("launcher has no core")
    expected_core = image + ".core"
    if frozen:
        expected_runtime = str(Path(image).parent / "runtime" / "sbcl")
        if runtime != "$here/runtime/sbcl" or core != "$here/" + Path(expected_core).name:
            raise ValueError("frozen launcher runtime/core mismatch")
        return expected_runtime, expected_core
    if not literal_absolute_path(runtime) or not literal_absolute_path(core):
        raise ValueError("literal launcher contains expansion or traversal")
    if core != expected_core:
        raise ValueError("literal launcher core mismatch")
    return runtime, core


def image_argv(image, *arguments):
    # Generated SBCL launchers splice this variable into runtime arguments;
    # the frozen wrapper appends an inherited library path after its own libs.
    return ["env", "SBCL_USER_ARGS=", "LD_LIBRARY_PATH=", image, *arguments]


def observed_image_paths(runtime_path, argv, expected_runtime, expected_core):
    if runtime_path != expected_runtime:
        raise RuntimeError("running runtime path changed")
    if argv.count("--core") != 1 or argv.index("--core") + 1 >= len(argv):
        raise RuntimeError("running argv has no unique core")
    if argv[argv.index("--core") + 1] != expected_core:
        raise RuntimeError("running core path changed")


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
        greeting=recvline(raw)
        if not greeting.startswith((b"200 ", b"201 ")):
            raise RuntimeError("protected observer greeting: {!r}".format(greeting))
        raw.sendall(b"STARTTLS\r\n")
        response=recvline(raw)
        if not response.startswith(b"382 "):
            raise RuntimeError("protected observer STARTTLS: {!r}".format(response))
        context = ssl.create_default_context(cafile=ca)
        with context.wrap_socket(raw, server_hostname="localhost") as tls:
            with tls.makefile("rwb", buffering=0) as stream:
                stream.write(b"AUTHINFO USER " + login.encode() + b"\r\n")
                response=stream.readline()
                if not response.startswith(b"381 "):
                    raise RuntimeError("protected observer USER: {!r}".format(response))
                stream.write(b"AUTHINFO PASS " + password.encode() + b"\r\n")
                response=stream.readline()
                if not response.startswith(b"281 "):
                    raise RuntimeError("protected observer PASS: {!r}".format(response))
                stream.write(b"ARTICLE " + message_id.encode() + b"\r\n")
                response=stream.readline()
                if response.startswith(b"430 "): return None
                if not response.startswith(b"220 "):
                    raise RuntimeError("protected observer ARTICLE: {!r}".format(response))
                out = bytearray()
                while True:
                    line = stream.readline()
                    if line == b".\r\n": return bytes(out)
                    if not line: raise RuntimeError("protected observer article EOF")
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
    if not re.fullmatch(r"[0-9a-f]{40}", args.source):
        ap.error("--source must be the full lowercase 40-hex source revision")
    nodes = [] ; tunnels = [] ; owners = [] ; observations = []
    token = secrets.token_hex(6)
    local = tempfile.TemporaryDirectory(prefix="fn-two-host-protected-")
    try:
        for side in "ab":
            host=getattr(args,"host_"+side); image=getattr(args,"image_"+side)
            if not literal_absolute_path(image):
                raise RuntimeError("image path is not canonical absolute on "+host)
            resolved_image=ssh(host,["readlink","-f",image]).stdout.decode().strip()
            if resolved_image != image:
                raise RuntimeError("image path is not canonical on "+host)
            launcher=remote_sha(host,image)
            script_bytes=ssh(host,["head","-c",str(MAX_LAUNCHER_BYTES+1),image]).stdout
            if len(script_bytes) > MAX_LAUNCHER_BYTES:
                raise RuntimeError("launcher exceeds parse bound on "+host)
            if hashlib.sha256(script_bytes).hexdigest() != launcher:
                raise RuntimeError("launcher changed during identity check on "+host)
            script=script_bytes.decode("utf-8","strict")
            runtime,core=launcher_paths(script,image)
            if FROZEN_MARKER in script.splitlines():
                image_dir=shlex.quote(str(Path(image).parent))
                ssh(host,["sh","-c","cd {} && sha256sum -c image.sha256".format(image_dir)],timeout=180)
            core_sha=remote_sha(host,core); runtime_sha=remote_sha(host,runtime)
            resolved_runtime=ssh(host,["readlink","-f",runtime]).stdout.decode().strip()
            manifest=str(Path(image).parent/"build-source.sha256")
            if remote_sha(host,manifest) != getattr(args,"source_manifest_sha_"+side):
                raise RuntimeError("source manifest identity mismatch on "+host)
            expected=(getattr(args,"launcher_sha_"+side),getattr(args,"core_sha_"+side),getattr(args,"runtime_sha_"+side))
            if (launcher,core_sha,runtime_sha) != expected: raise RuntimeError("image identity mismatch on "+host)
            root="/tmp/fn-protected-{}-{}".format(args.source[:12],token)
            ssh(host,["mkdir","-m","700",root])
            node=dict(side=side,host=host,image=image,root=root,
                      runtime=runtime,resolved_runtime=resolved_runtime,core=core)
            nodes.append(node)
            listen=remote_port(host); tunnel=remote_port(host)
            cert=root+"/cert.pem"; key=root+"/key.pem"; store=root+"/store"; config=root+"/fn.toml"; auth=root+"/auth.toml"
            node.update(listen=listen,tunnel=tunnel,cert=cert,key=key,store=store,config=config,auth=auth)
            ssh(host,["openssl","req","-x509","-newkey","rsa:2048","-nodes","-sha256","-days","1","-subj","/CN=localhost","-keyout",key,"-out",cert])
            ssh(host,image_argv(image,"--fn","store",store,"init","fn.test"))
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
            ssh(n["host"],image_argv(n["image"],"--fn","operator",n["config"],"principal","set-password",login,"--posting"),data=(pw+"\n"+pw+"\n").encode(),timeout=180)
            listing=ssh(n["host"],image_argv(n["image"],"--fn","operator",n["config"],"principal","list")).stdout.decode()
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
            argv=image_argv(n["image"],"--fn","operator",n["config"],"peer","add",other["side"],other["side"]+".example.invalid","127.0.0.1",str(n["tunnel"]),"fn.*","fn.*","principal",n["principal"],profile,"false","true","starttls","localhost",anchor)
            ssh(n["host"],argv)

        def start_owner(n):
            pidfile=n["root"]+"/owner.pid"
            remote="echo $$ > {}; exec {}".format(
                shlex.quote(pidfile),
                " ".join(shlex.quote(x) for x in
                         image_argv(n["image"],"--fn","operator",n["config"],"run")))
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
            observed_runtime_sha=remote_sha(n["host"],observed_runtime)
            if observed_runtime_sha != getattr(args,"runtime_sha_"+n["side"]):
                raise RuntimeError("running runtime identity changed on "+n["host"])
            argv=ssh(n["host"],["cat","/proc/"+pid+"/cmdline"]).stdout.split(b"\0")
            argv=[part.decode("utf-8","strict") for part in argv if part]
            observed_image_paths(observed_runtime,argv,n["resolved_runtime"],n["core"])
            observed_core=argv[argv.index("--core")+1]
            observed_core_sha=remote_sha(n["host"],observed_core)
            if observed_core_sha != getattr(args,"core_sha_"+n["side"]):
                raise RuntimeError("running core changed on "+n["host"])
            observations.append(dict(event="owner-start",host=n["host"],pid=int(pid),
                command=cmd,proc_argv=argv,runtime_path=observed_runtime,
                runtime_sha256=observed_runtime_sha,core_path=observed_core,
                core_sha256=observed_core_sha,launcher_path=n["image"],
                launcher_sha256=getattr(args,"launcher_sha_"+n["side"]),
                declared_source=args.source,
                source_manifest_sha256=getattr(args,"source_manifest_sha_"+n["side"])))

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
            ssh(n["host"],image_argv(n["image"],"--fn","operator",n["config"],"post","--message-id",mid,"--payload",payload,"--group","fn.test"))
            return mid,article

        def await_article(n, mid, article, seconds):
            deadline=time.monotonic()+seconds; observed=None
            while time.monotonic()<deadline and observed is None:
                observed=nntp_article(local_ports[n["side"]],n["local_cert"],n["login"],n["password"],mid)
                if observed is None: time.sleep(.2)
            if observed != article:
                label="transfer-mismatch-{}-{}".format(n["side"],len(observations))
                Path(local.name,label+".expected").write_bytes(article)
                if observed is not None:
                    Path(local.name,label+".observed").write_bytes(observed)
                observations.append(dict(event="transfer-mismatch",message_id=mid,
                    expected_sha256=hashlib.sha256(article).hexdigest(),
                    expected_bytes=len(article),
                    observed_sha256=(hashlib.sha256(observed).hexdigest()
                                     if observed is not None else None),
                    observed_bytes=(len(observed) if observed is not None else None)))
                raise RuntimeError("protected transfer mismatch "+mid)

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
        journal=a["store"]+"/feed/"+b["side"]+".fnfd"
        stop_owner(a)
        write_remote(a["host"],a["profile"],("FNAUTH1\n{}\nwrong-{}\n".format(b["login"],token)).encode(),"600")
        start_owner(a)
        before=ssh(a["host"],["cat",journal]).stdout
        bad_mid,bad_article=make_article(a,"bad-password")
        assert_absent(b,bad_mid)
        if a["owner"].poll() is not None or b["owner"].poll() is not None:
            raise RuntimeError("bad credential stopped an owner")
        after=ssh(a["host"],["cat",journal]).stdout
        if after == before: raise RuntimeError("bad credential added no journal evidence")
        Path(local.name,"bad-password.before.fnfd").write_bytes(before)
        Path(local.name,"bad-password.after.fnfd").write_bytes(after)
        observations.append(dict(event="bad-password-observed-absent",message_id=bad_mid,
            journal_before_sha256=hashlib.sha256(before).hexdigest(),
            journal_after_sha256=hashlib.sha256(after).hexdigest(),
            journal_before_bytes=len(before),journal_after_bytes=len(after)))
        stop_owner(a)
        write_remote(a["host"],a["profile"],("FNAUTH1\n{}\n{}\n".format(b["login"],b["password"])).encode(),"600")
        start_owner(a); await_article(b,bad_mid,bad_article,args.timeout)

        # An unrelated CA likewise stays peer-local and queued.  Restore the
        # exact target certificate, restart A, and require delivery.
        stop_owner(a)
        write_remote(a["host"],a["anchor"],Path(a["local_cert"]).read_bytes(),"600")
        start_owner(a)
        before=ssh(a["host"],["cat",journal]).stdout
        ca_mid,ca_article=make_article(a,"bad-ca")
        assert_absent(b,ca_mid)
        if a["owner"].poll() is not None or b["owner"].poll() is not None:
            raise RuntimeError("untrusted CA stopped an owner")
        after=ssh(a["host"],["cat",journal]).stdout
        if after == before: raise RuntimeError("untrusted CA added no journal evidence")
        Path(local.name,"bad-ca.before.fnfd").write_bytes(before)
        Path(local.name,"bad-ca.after.fnfd").write_bytes(after)
        observations.append(dict(event="bad-ca-observed-absent",message_id=ca_mid,
            journal_before_sha256=hashlib.sha256(before).hexdigest(),
            journal_after_sha256=hashlib.sha256(after).hexdigest(),
            journal_before_bytes=len(before),journal_after_bytes=len(after)))
        stop_owner(a)
        write_remote(a["host"],a["anchor"],Path(b["local_cert"]).read_bytes(),"600")
        start_owner(a); await_article(b,ca_mid,ca_article,args.timeout)
        observations.append(dict(event="gate-pass",declared_source=args.source,
                                 hosts=[args.host_a,args.host_b]))
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
        for path in Path(local.name).glob("*"):
            if not path.is_file(): continue
            (evidence/path.name).write_bytes(path.read_bytes())
        (evidence/"observations.json").write_text(
            json.dumps(observations,indent=2,sort_keys=True)+"\n",encoding="utf-8")
        local.cleanup()
        if cleanup_errors:
            raise RuntimeError("remote cleanup failed: "+"; ".join(cleanup_errors))

if __name__ == "__main__": main()
