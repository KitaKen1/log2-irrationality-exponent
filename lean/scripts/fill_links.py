"""Prepare fixed-commit links locally, after the proof commit is published.

This does not commit, push, submit a PR, or assert that a local commit is public.
Without --write it prints the links and does not change any file.
"""
import argparse
from pathlib import Path
import re
import subprocess
from urllib.parse import quote

ROOT=Path(__file__).resolve().parents[2]
REPOSITORY='https://github.com/KitaKen1/log2-irrationality-exponent'


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('commit',help='Full 40-character SHA of the published proof commit')
    parser.add_argument('--write',action='store_true')
    args=parser.parse_args()
    if not re.fullmatch('[0-9a-f]{40}',args.commit):parser.error('Use a full lowercase commit SHA')
    for path in ['lean/LogTwo/Target.lean','lean4web/LogTwoLean4Web.lean']:
        data=subprocess.check_output(['git','show',args.commit+':'+path],cwd=ROOT)
        if data!=(ROOT/path).read_bytes():raise SystemExit('Commit content differs from the current '+path)
    path='lean/LogTwo/Target.lean'
    line=next(i for i,s in enumerate((ROOT/path).read_text().splitlines(),1)
              if s.startswith('theorem irrationalityExponent_log_two'))
    proof=f'{REPOSITORY}/blob/{args.commit}/{path}#L{line}'
    raw=f'https://raw.githubusercontent.com/KitaKen1/log2-irrationality-exponent/{args.commit}/lean4web/LogTwoLean4Web.lean'
    live='https://live.lean-lang.org/#url='+quote(raw,safe='')
    print('Complete split proof: '+proof)
    print('Single-file attempt (select v4.35.0-rc4; consult its build status): '+live)
    print('The caller must confirm this commit is already public; no upload is performed.')
    if args.write:
        fc=ROOT/'FClikelean/LogTwoIrrationalityExponent.lean'
        text,count=re.subn(r'@\[category research solved, AMS 11(?:,\s*formal_proof using lean4 at "[^"]+")?\]',
            f'@[category research solved, AMS 11,\n    formal_proof using lean4 at "{proof}"]',fc.read_text())
        if count!=1:raise SystemExit('Expected exactly one target attribute')
        fc.write_text(text)
        readme=ROOT/'README.md';text=readme.read_text()
        marker='<!-- FIXED-PUBLICATION-LINKS -->'
        if marker in text:text=text.split(marker)[0].rstrip()+'\n'
        text+=f'\n{marker}\n\nFixed split proof: [Target.lean]({proof}).\n'
        text+=f'Lean4Web single-file attempt: [open source]({live}) (select v4.35.0-rc4; see build status).\n'
        readme.write_text(text)


if __name__=='__main__':main()
