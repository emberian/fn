"""Pinned, loopback-only BPA processes for the actual fn exchange experiment."""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from tools.bpa_dtn7 import BpaDtn7Client, BpaDtn7Error, PINNED_DTN7_REVISION


class LabBpa:
    def __init__(self, checkout: Path, run: Path, name: str, node: str,
                 endpoint: str, peer_node: str, control: int, cla: int, peer_cla: int):
        self.binary = checkout / 'target' / 'release'
        self.run = run
        self.name = name
        self.control = control
        self.cla = cla
        self.client = BpaDtn7Client(control, max_bundle_bytes=128 * 1024)
        self.process = None
        self.log = None
        self.starts = 0
        spool = run / (name + '-bpa')
        spool.mkdir()
        self.config = run / (name + '.toml')
        # Paths and node names below belong to this local test, never a peer.
        self.config.write_text(
            f'nodeid = {json.dumps(node)}\nipv4 = false\nipv6 = true\n'
            f'webport = {control}\nworkdir = {json.dumps(str(spool))}\ndb = "sled"\n'
            '[routing]\nstrategy = "epidemic"\n[core]\njanitor = "1s"\n'
            f'[convergencylayers]\ncla.0.id = "tcp"\ncla.0.port = "{cla}"\n'
            'cla.0.bind = "::1"\n[statics]\n'
            f'peers = ["tcp://[::1]:{peer_cla}/{peer_node}"]\n'
            f'[endpoints]\nlocal.0 = {json.dumps(endpoint)}\n')

    def start(self):
        if self.process is not None:
            raise RuntimeError('BPA already started')
        self.starts += 1
        self.log = (self.run / f'{self.name}-bpa-{self.starts}.log').open('wb')
        self.process = subprocess.Popen(
            [str(self.binary / 'dtnd'), '-c', str(self.config), '--disable_nd'],
            stdout=self.log, stderr=subprocess.STDOUT,
            env={**os.environ, 'NO_PROXY': '*', 'no_proxy': '*'})
        deadline = time.monotonic() + 15
        while time.monotonic() < deadline:
            if self.process.poll() is not None:
                raise RuntimeError(f'{self.name} BPA exited before ready')
            try:
                self.client.inventory()
                break
            except BpaDtn7Error:
                time.sleep(.1)
        else:
            raise RuntimeError(f'{self.name} BPA readiness timeout')
        listeners = subprocess.check_output(
            ['lsof', '-nP', '-p', str(self.process.pid), '-a', '-iTCP', '-sTCP:LISTEN'],
            text=True, timeout=5)
        (self.run / f'{self.name}-listeners-{self.starts}.txt').write_text(listeners)
        if (f'[::1]:{self.control}' not in listeners or
                f'[::1]:{self.cla}' not in listeners or
                '0.0.0.0' in listeners or '*:' in listeners):
            self.stop()
            raise RuntimeError('BPA listener escaped loopback profile')

    def stop(self):
        if self.process is not None:
            forced = False
            self.process.terminate()
            try:
                self.process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                forced = True
                self.process.kill()
                self.process.wait(timeout=5)
            (self.run / f"{self.name}-stop-{self.starts}.json").write_text(
                json.dumps({"signal": "SIGTERM", "forced_sigkill": forced,
                            "returncode": self.process.returncode}) + "\n")
            self.process = None
        if self.log is not None:
            self.log.close()
            self.log = None

    def submit(self, adu: bytes, destination: str, label: str, lifetime=300) -> str:
        if not isinstance(adu, bytes) or not 0 < len(adu) <= 65538:
            raise ValueError('outbound ADU outside lab profile')
        path = self.run / (label + '.adu')
        path.write_bytes(adu)
        sent = subprocess.run(
            [str(self.binary / 'dtnsend'), '-6', '-p', str(self.control),
             '-r', destination, '-l', str(lifetime), str(path)],
            check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            timeout=10, env={**os.environ, 'NO_PROXY': '*', 'no_proxy': '*'})
        (self.run / (label + '-submit.txt')).write_bytes(sent.stdout + sent.stderr)
        match = re.search(rb'^Bundle-Id: (\S+)$', sent.stdout, re.M)
        if match is None:
            raise RuntimeError('BPA submit reply has no transport ID')
        # This reply precedes asynchronous BPA persistence. The fn attempt
        # intent was already durable before this method could be called.
        return match[1].decode('ascii')

    def wait_for(self, bid: str):
        deadline = time.monotonic() + 15
        while time.monotonic() < deadline:
            if bid in self.client.inventory():
                return
            time.sleep(.1)
        raise RuntimeError(f'BPA did not retain expected bundle {bid}')

    def download(self, bid: str) -> bytes:
        raw = self.client.download_bundle(bid)
        with tempfile.TemporaryDirectory(prefix='extract-', dir=self.run) as tmp:
            source, target = Path(tmp) / 'bundle.cbor', Path(tmp) / 'payload.adu'
            source.write_bytes(raw)
            subprocess.run([str(self.binary / 'fn_bpa_payload_extract'),
                            '--input', str(source), '--output', str(target),
                            '--max-payload', '65538'], check=True,
                           stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, timeout=10)
            if target.stat().st_size > 65538:
                raise RuntimeError('extracted ADU outside lab profile')
            return target.read_bytes()


def verify_build(checkout: Path):
    revision = subprocess.check_output(['git', '-C', str(checkout), 'rev-parse', 'HEAD'],
                                       text=True, timeout=5).strip()
    if revision != PINNED_DTN7_REVISION:
        raise RuntimeError('unexpected BPA revision')
    subprocess.run([str(ROOT / 'tests/bp-dtn7/build_payload_extractor.sh')],
                   env={**os.environ, 'DTN7_REPO': str(checkout)}, check=True, timeout=120)
    return {'revision': revision, 'helper_sha256': hashlib.sha256(
        (checkout / 'target/release/fn_bpa_payload_extract').read_bytes()).hexdigest()}
