#!/usr/bin/env python3
"""Fast VHDL diagnostics via vhdl_ls (rust_hdl), spoken directly over LSP stdio.

No persistent server needed: startup + first diagnostics for an opened file
takes well under a second even against a project with 1000+ VHDL files,
because vhdl_ls resolves lazily per requested document rather than eagerly
analyzing the whole project. So this script just starts vhdl_ls fresh,
opens the given file(s) with their current on-disk content, collects the
diagnostics vhdl_ls publishes for them, and exits.

Usage:
    vhdl_check.py [--root DIR] FILE [FILE ...]

--root must contain vhdl_ls.toml (generate it with `make -C
tests/all_modules`; see SKILL.md in this directory). Defaults to the
repo root, where that make target writes the file.

Exit status: 0 if no errors (warnings are still printed), 1 if vhdl_ls
reported at least one error-severity diagnostic, 2 on a tool/timeout failure.
"""
import argparse
import json
import os
import queue
import subprocess
import sys
import threading
import time

SEVERITY = {1: "error", 2: "warning", 3: "info", 4: "hint"}
TIMEOUT_S = 20


def repo_root():
    here = os.path.dirname(os.path.abspath(__file__))
    return os.path.abspath(os.path.join(here, "..", "..", ".."))


def read_messages(stdout, msgq):
    while True:
        line = stdout.readline()
        if not line:
            break
        if line.startswith(b"Content-Length:"):
            length = int(line.split(b":")[1].strip())
            stdout.readline()  # blank separator line
            body = stdout.read(length)
            msgq.put(json.loads(body))


def send(stdin, msg):
    body = json.dumps(msg).encode()
    stdin.write(f"Content-Length: {len(body)}\r\n\r\n".encode() + body)
    stdin.flush()


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", default=None, help="Directory containing vhdl_ls.toml")
    ap.add_argument("files", nargs="+", help="VHDL file(s) to check")
    args = ap.parse_args()

    root = args.root or repo_root()
    if not os.path.isfile(os.path.join(root, "vhdl_ls.toml")):
        print(f"error: no vhdl_ls.toml in {root} (generate it with 'make -C tests/all_modules' first)", file=sys.stderr)
        return 2

    targets = [os.path.abspath(f) for f in args.files]
    for f in targets:
        if not os.path.isfile(f):
            print(f"error: not a file: {f}", file=sys.stderr)
            return 2

    proc = subprocess.Popen(
        ["vhdl_ls"], cwd=root,
        stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    )
    msgq = queue.Queue()
    threading.Thread(target=read_messages, args=(proc.stdout, msgq), daemon=True).start()

    send(proc.stdin, {
        "jsonrpc": "2.0", "id": 1, "method": "initialize",
        "params": {"processId": None, "rootUri": f"file://{root}", "capabilities": {}},
    })
    deadline = time.time() + TIMEOUT_S
    while time.time() < deadline:
        try:
            m = msgq.get(timeout=1)
        except queue.Empty:
            continue
        if m.get("id") == 1:
            break
    else:
        print("error: vhdl_ls did not respond to initialize", file=sys.stderr)
        proc.kill()
        return 2
    send(proc.stdin, {"jsonrpc": "2.0", "method": "initialized", "params": {}})

    uri_to_file = {}
    for f in targets:
        uri = f"file://{f}"
        uri_to_file[uri] = f
        with open(f) as fh:
            text = fh.read()
        send(proc.stdin, {
            "jsonrpc": "2.0", "method": "textDocument/didOpen",
            "params": {"textDocument": {"uri": uri, "languageId": "vhdl", "version": 1, "text": text}},
        })

    pending = set(uri_to_file)
    results = {}
    deadline = time.time() + TIMEOUT_S
    while pending and time.time() < deadline:
        try:
            m = msgq.get(timeout=1)
        except queue.Empty:
            continue
        if m.get("method") == "textDocument/publishDiagnostics":
            uri = m["params"]["uri"]
            if uri in pending:
                results[uri] = m["params"]["diagnostics"]
                pending.discard(uri)

    proc.terminate()

    had_error = False
    for uri, f in uri_to_file.items():
        diags = results.get(uri)
        if diags is None:
            print(f"{f}: no response from vhdl_ls (timed out)")
            had_error = True
            continue
        if not diags:
            print(f"{f}: OK")
            continue
        for d in sorted(diags, key=lambda d: (d["range"]["start"]["line"], d["range"]["start"]["character"])):
            sev = SEVERITY.get(d.get("severity"), "?")
            line = d["range"]["start"]["line"] + 1
            col = d["range"]["start"]["character"] + 1
            print(f"{f}:{line}:{col}: {sev}: {d['message']}")
            if sev == "error":
                had_error = True

    return 1 if had_error else 0


if __name__ == "__main__":
    sys.exit(main())
