#!/usr/bin/env python3
"""Stand up one scratch developer-image node for the reader spike (D28).

    python3 tools/spike_reader_node.py --image IMAGE --tree TREE --dir WORK \
        --port 11919 [--protected] [--openssl OPENSSL]

Creates WORK/store (groups fn.agents fn.test), a self-signed certificate,
an operator config with STARTTLS, [auth] required and a control socket,
two AUTHINFO principals (ember, guest) with posting, and one hybrid signing
key per login under WORK/keys/<login>/, enrolled with `hybrid-enroll` on the
control socket.  Then runs the owner in the foreground and prints its
LISTENING line and a JSON description on stdout.

;; SPIKE: defers the login-to-principal binding.  The node has no relation
;; between an AUTHINFO user and a hybrid principal; this script derives the
;; principal as SHA-256("fn-spike-principal:" + login) and the web client
;; reads the key directory it is pointed at.  dev must make the node own it.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

LOGINS = (("ember", "reader-spike-ember"), ("guest", "reader-spike-guest"))


def run(cmd, cwd, env, timeout=600):
    done = subprocess.run(cmd, cwd=cwd, env=env, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, timeout=timeout, check=False)
    if done.returncode != 0:
        sys.exit("failed: %s\n%s%s" % (" ".join(map(str, cmd)),
                                        done.stdout.decode(errors="replace"),
                                        done.stderr.decode(errors="replace")))
    return done.stdout.decode(errors="replace")


def principal_of(login: str) -> bytes:
    return hashlib.sha256(b"fn-spike-principal:" + login.encode()).digest()


def make_key(openssl, directory: Path, login: str, env):
    directory.mkdir(mode=0o700, parents=True, exist_ok=True)
    ed = directory / "ed.pem"
    run([openssl, "genpkey", "-algorithm", "ed25519", "-out", str(ed)], directory, env)
    private_der = run_bytes([openssl, "pkey", "-in", str(ed), "-outform", "DER"], env)
    public_der = run_bytes([openssl, "pkey", "-in", str(ed), "-pubout", "-outform", "DER"], env)
    seed, public = private_der[-32:], public_der[-32:]
    (directory / "principal.bin").write_bytes(principal_of(login))
    (directory / "ed-public.bin").write_bytes(public)
    (directory / "ed-secret.bin").write_bytes(seed + public)
    ed.unlink()
    run([openssl, "genpkey", "-algorithm", "ML-DSA-65", "-out",
         str(directory / "ml-private.pem")], directory, env)
    run([openssl, "pkey", "-in", str(directory / "ml-private.pem"), "-pubout",
         "-out", str(directory / "ml-public.pem")], directory, env)
    for one in directory.iterdir():
        os.chmod(one, 0o600)
    (directory / "login").write_text(login + "\n")


def run_bytes(cmd, env):
    return subprocess.run(cmd, env=env, stdout=subprocess.PIPE, check=True,
                          timeout=60).stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--image", required=True)
    parser.add_argument("--tree", required=True, help="source tree the image was built from")
    parser.add_argument("--dir", required=True, type=Path)
    parser.add_argument("--port", type=int, default=11929)
    parser.add_argument("--protected", action="store_true",
                        help="protected_only = true (AUTHINFO only after STARTTLS)")
    parser.add_argument("--openssl", default="openssl")
    args = parser.parse_args()
    env = dict(os.environ, ACL2_CUSTOMIZATION="NONE")
    work = args.dir.absolute()
    fresh = not (work / "store").exists()
    work.mkdir(parents=True, exist_ok=True)
    store, config = work / "store", work / "fn.toml"
    control, cert, key = work / "control.sock", work / "cert.pem", work / "key.pem"
    if fresh:
        run([args.image, "--fn", "store", str(store), "init", "fn.agents", "fn.test"],
            args.tree, env)
        run([args.openssl, "req", "-x509", "-newkey", "rsa:2048", "-keyout", str(key),
             "-out", str(cert), "-sha256", "-days", "7", "-nodes", "-subj", "/CN=localhost",
             "-addext", "subjectAltName=IP:127.0.0.1,DNS:localhost"], work, env)
    config.write_text(
        '[store]\npath = "{}"\n\n[listener]\nhost = "127.0.0.1"\nport = {}\n'
        'tls_cert = "{}"\ntls_key = "{}"\n\n[auth]\nrequired = true\n'
        'protected_only = {}\npath = "{}"\n\n[control]\npath = "{}"\n\n'
        '[log]\npath = "{}"\n'.format(store, args.port, cert, key,
                                      "true" if args.protected else "false",
                                      work / "credentials.toml", control,
                                      work / "service.log"), encoding="ascii")
    if fresh:
        for login, password in LOGINS:
            run([sys.executable, "bin/fn", "--config", str(config), "principal",
                 "set-password", login, "--password", password, "--posting"],
                args.tree, env)
            make_key(args.openssl, work / "keys" / login, login, env)
    owner = subprocess.Popen([args.image, "--fn", "operator", str(config), "run"],
                             cwd=args.tree, env=env, stdout=subprocess.PIPE,
                             stderr=sys.stderr)
    line = owner.stdout.readline()
    print(line.decode(errors="replace").strip(), flush=True)
    if fresh:
        for generation, (login, _) in enumerate(LOGINS, start=1):
            keys = work / "keys" / login
            for attempt in range(30):
                if control.exists():
                    break
                time.sleep(1)
            print(run([args.image, "--fn", "hybrid-enroll", str(control), str(generation),
                       str(keys / "principal.bin"), str(keys / "ed-public.bin"),
                       str(keys / "ml-public.pem")], args.tree, env).strip(), flush=True)
    print(json.dumps({"pid": owner.pid, "port": args.port, "config": str(config),
                      "store": str(store), "cert": str(cert), "control": str(control),
                      "logins": {login: {"password": password,
                                         "keys": str(work / "keys" / login),
                                         "principal": principal_of(login).hex()}
                                 for login, password in LOGINS}}), flush=True)
    for rest in owner.stdout:
        sys.stdout.write(rest.decode(errors="replace"))
        sys.stdout.flush()
    sys.exit(owner.wait())


if __name__ == "__main__":
    main()
