#!/usr/bin/env python3
"""Run an execution command with periodic progress on stdout and in work/."""
import sys
sys.dont_write_bytecode = True
import argparse
import math
from pathlib import Path
import signal
import subprocess

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools.progress import report
from tools.scope import configuration


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--work-dir', type=Path, default=ROOT / 'work')
    parser.add_argument('--interval', type=float, default=configuration()['progress_interval_seconds'])
    parser.add_argument('command', nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ['--'] else args.command
    if not command or not math.isfinite(args.interval) or args.interval <= 0:
        parser.error('supply a command after -- and a finite positive interval')
    work = args.work_dir.resolve()
    report(work)
    try:
        child = subprocess.Popen(command, cwd=ROOT)
    except OSError as error:
        print('Cannot launch execution command:', error, file=sys.stderr)
        return 127
    def forward(signum, frame):
        if child.poll() is None:
            child.send_signal(signum)
    old_term = signal.signal(signal.SIGTERM, forward)
    try:
        while True:
            try:
                code = child.wait(timeout=args.interval)
                break
            except subprocess.TimeoutExpired:
                report(work)
    except KeyboardInterrupt:
        child.send_signal(signal.SIGINT)
        try:
            code = child.wait(timeout=10)
        except subprocess.TimeoutExpired:
            child.terminate()
            try:
                child.wait(timeout=5)
            except subprocess.TimeoutExpired:
                child.kill()
                child.wait()
            code = 130
    finally:
        signal.signal(signal.SIGTERM, old_term)
        report(work)
    return code if code >= 0 else 128 - code


if __name__ == '__main__':
    sys.exit(main())
