"""Check reported browser compatibility issues on the pinned rc4.

This checks selected complete source modules in isolation, not the whole proof.
The generated harness and bounded compiler result are retained for review.
"""
from datetime import datetime, timezone
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess
import time
from build_audit import graph
from compiler_environment import compiler_environment
from make_lean4web import module_body, rc4_compatibility
from module_headers import imports

ROOT = Path(__file__).resolve().parents[2]
WEB = ROOT/'lean4web'
HILBERT_MODULES = [
    'OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSections',
    'OAI.NumberTheory.PiExponent.LocalAlgebra.QuotientSections',
    'OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDegree',
]
BROWSER_MODULES = HILBERT_MODULES + [
    'OAI.NumberTheory.PiExponent.LocalAlgebra.FiltrationLength',
    'OAI.NumberTheory.PiExponent.LocalAlgebra.LocalComponentDegree',
    'OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDimension',
    'OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFreeResolutionExt',
]
GEOMETRY_TARGETS = [
    'OAI.NumberTheory.PiExponent.Geometry.CartierSequence',
    'OAI.NumberTheory.PiExponent.Geometry.CartierDegreeLength',
    'OAI.NumberTheory.PiExponent.Approximation.TwistSectionClearing',
]
CURVES_TARGETS = [
    'OAI.NumberTheory.PiExponent.Geometry.CurveDegreeAdditivity',
    'OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk',
    'OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree',
    'OAI.NumberTheory.PiExponent.LocalAlgebra.IdealTensorPowers',
    'OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal',
    'OAI.NumberTheory.PiExponent.Cohomology.EulerSupportDimension',
    'OAI.NumberTheory.PiExponent.Geometry.SectionCartierRegular',
    'OAI.NumberTheory.PiExponent.Cohomology.CartierMixedEuler',
    'OAI.NumberTheory.PiExponent.Geometry.GeneralCartierDegreeLength',
]
IDEALS_TARGETS = ['OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal']
TENSOR_FRAME_TARGETS = [
    'OAI.NumberTheory.PiExponent.Geometry.CartierPowerFrames',
    'OAI.NumberTheory.PiExponent.LocalAlgebra.TensorIdealInclusion',
]
DEPENDENCY_CASES = {'geometry': GEOMETRY_TARGETS, 'curves': CURVES_TARGETS,
                    'ideals': IDEALS_TARGETS, 'tensor-frame': TENSOR_FRAME_TARGETS}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case', choices=['hilbert', 'browser', *DEPENDENCY_CASES], default='hilbert')
    parser.add_argument('--timeout-seconds', type=int, default=300)
    args = parser.parse_args()
    if args.timeout_seconds <= 0:
        parser.error('--timeout-seconds must be positive')
    modules = HILBERT_MODULES if args.case == 'hilbert' else BROWSER_MODULES
    _, sources, ordered, _ = graph()
    if args.case in DEPENDENCY_CASES:
        selected = set()
        def visit(name):
            if name in selected:
                return
            selected.add(name)
            for dep in imports((ROOT/'lean'/sources[name]['path']).read_text()):
                if dep in sources:
                    visit(dep)
        for name in DEPENDENCY_CASES[args.case]:
            visit(name)
        modules = [name for name in ordered if name in selected]
    directory = WEB/'evidence'/(datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ-') + args.case)
    directory.mkdir()
    harness = directory/'Compatibility.lean'
    chunks = ['module\npublic import Mathlib\n@[expose] public section\n']
    for i, name in enumerate(modules):
        source = (ROOT/'lean'/sources[name]['path']).read_text()
        body = rc4_compatibility(module_body(source, name), name)
        chunks.append(f'\nsection Source{i:04d}\n{body}\nend Source{i:04d}\n')
    if args.case in {'hilbert', 'browser'}:
        chunks.append('\n#print axioms OAI.PiExponentJets.W27.prime_quotientSection_finrank_pos\n')
    if args.case == 'browser':
        chunks.append('#print axioms OAI.PiExponentSiegelAux.W31.projectiveResolutionOfExact\n')
    if args.case == 'geometry':
        chunks.append('\n#print axioms OAI.PiExponentSeshadri.CartierSequence.exact\n')
        chunks.append('#print axioms OAI.PiExponent.CartierDegreeLength.cartier_euler_difference_eq_sum_local_lengths\n')
        chunks.append('#print axioms OAI.PiExponent.TwistSectionClearing.frame_twistForward_zero_on\n')
    if args.case == 'curves':
        chunks.append('\n#print axioms OAI.PiExponent.CurveDegree.section_tensor_euler_add\n')
        chunks.append('#print axioms OAI.PiExponent.SectionZeroStalk.zero_stalk_kernel\n')
        for name in [
            'PiExponent.CurveSectionDegree.euler_difference_eq_sum_zero_orders',
            'PiExponentSeshadri.Geometry.idealPowerInclusion_ideal',
            'PiExponentSeshadri.InvertibleLocal.local_equation_on_chart',
            'PiExponent.NumericalAmpleness.section_coefficient_regular',
            'PiExponent.NumericalAmpleness.cartierPowerMultiply_mono_of_mono',
            'PiExponent.NumericalAmpleness.cartier_euler_difference',
            'PiExponent.NumericalAmpleness.cartierPower_zeroIdeal_frames',
            'PiExponent.NumericalAmpleness.mixedCartierPower_zeroIdeal_frames',
            'PiExponent.GeneralCartierDegreeLength.cartier_euler_difference_eq_sum_local_lengths',
        ]:
            chunks.append(f'#print axioms OAI.{name}\n')
    if args.case == 'ideals':
        chunks.append('\n#print axioms OAI.PiExponentSeshadri.InvertibleLocal.local_equation_on_chart\n')
    if args.case == 'tensor-frame':
        name = 'OAI.NumberTheory.PiExponent.Cohomology.CartierMixedEuler'
        source = (ROOT/'lean'/sources[name]['path']).read_text()
        body = rc4_compatibility(module_body(source, name), name)
        # Retain both complete lemmas preceding mixedCartierPowerMultiply.
        # Only an unused open of a namespace outside this dependency set is omitted.
        prefix, suffix = body.split('\ndef mixedCartierPowerMultiply ', 1)
        assert suffix and prefix.count('lemma ') == 2
        prefix = prefix.replace('open PiExponent.SectionZeroIdeal PiExponent.CartierPowerFrames',
                                'open PiExponent.CartierPowerFrames')
        chunks.append('\nsection TensorFrameCheck\n' + prefix +
                      '\nend\nend PiExponent.NumericalAmpleness\nend OAI\nend TensorFrameCheck\n')
        chunks.append('#print axioms OAI.PiExponent.NumericalAmpleness.tensorMap_framed\n')
    harness.write_text(''.join(chunks))
    compiler, env = compiler_environment(WEB)
    version = subprocess.check_output([compiler, '--version'], text=True).strip()
    if not version.startswith('Lean (version 4.35.0-rc4,'):
        raise RuntimeError('Expected v4.35.0-rc4')
    revision = subprocess.check_output(['git', '-C', str(WEB/'.lake/packages/mathlib'),
        'rev-parse', 'HEAD'], text=True).strip()
    if revision != '1f414401f69059aa7eead47b53ee40bd38455eeb':
        raise RuntimeError('Unexpected Mathlib revision')
    command = [compiler, '--memory=4096', '--threads=1', '--trust=1', str(harness.relative_to(WEB))]
    started = time.monotonic()
    record = {'scope': f'{len(modules)}-module compatibility check; not a complete proof build',
        'modules': modules, 'compiler_version': version, 'mathlib_commit': revision,
        'source_sha256': hashlib.sha256(harness.read_bytes()).hexdigest(),
        'command': ['lean', *command[1:]], 'timeout_seconds': args.timeout_seconds,
        'browser_execution_performed': False}
    if args.case == 'tensor-frame':
        record['scope'] = (f'{len(modules)} complete dependency modules plus two complete lemmas '
                           'from CartierMixedEuler; not a complete proof build')
        record['declaration_slice'] = {
            'module': 'OAI.NumberTheory.PiExponent.Cohomology.CartierMixedEuler',
            'declarations': ['framed_map', 'tensorMap_framed'],
            'omitted_unused_open': 'PiExponent.SectionZeroIdeal',
        }
    with (directory/'build.log').open('w') as output:
        try:
            run = subprocess.run(command, cwd=WEB, env=env, stdout=output,
                stderr=subprocess.STDOUT, timeout=args.timeout_seconds)
            record.update(status='passed' if run.returncode == 0 else 'failed', exit_code=run.returncode)
        except subprocess.TimeoutExpired:
            record.update(status='failed', stop_reason='time_limit')
    record['elapsed_seconds'] = round(time.monotonic() - started, 3)
    record['completed_at_utc'] = datetime.now(timezone.utc).isoformat()
    log = (directory/'build.log').read_text()
    axioms = {name: [a.strip() for a in names.split(',') if a.strip()]
        for name, names in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log)}
    record['axiom_audit'] = axioms
    if record['status'] == 'passed' and (not axioms or any(
            set(names) - {'propext', 'Classical.choice', 'Quot.sound'} for names in axioms.values())):
        record.update(status='failed', stop_reason='axiom_audit')
    record['log_sha256'] = hashlib.sha256((directory/'build.log').read_bytes()).hexdigest()
    (directory/'result.json').write_text(json.dumps(record, indent=2)+'\n')
    print(json.dumps({k: v for k, v in record.items() if k != 'modules'}, indent=2))
    return 0 if record['status'] == 'passed' else 1


if __name__ == '__main__':
    raise SystemExit(main())
