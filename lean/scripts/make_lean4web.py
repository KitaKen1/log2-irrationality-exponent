"""Flatten the pinned proof closure, preserving source-module local scopes.

Generation is not a Lean build. The generated file targets v4.35.0-rc4;
its actual build result is recorded separately from the v4.34.1 split proof.
"""
from pathlib import Path
import hashlib
import json
import re

LEAN = Path(__file__).resolve().parents[1]
ROOT = LEAN.parent

# These compatibility edits apply only to the generated rc4 edition. The
# original split sources remain byte-identical to the verified v4.34.1 files.
RC4_EDITS = {
    'OAI.NumberTheory.PiExponent.Jets.JetGeometry': [
        ('Finset.mem_antidiagonal.mp', 'Finset.HasAntidiagonal.mem_antidiagonal.mp', 2)],
    'OAI.NumberTheory.PiExponent.Geometry.CurveLocalOrder': [
        ('(IsDiscreteValuationRing.addVal A).map enatToIntegerOrder\n'
         '    enatToIntegerOrder_top enatToIntegerOrder_monotone',
         '(IsDiscreteValuationRing.addVal A).map\n'
         '    { toAddMonoidHom := enatToIntegerOrder\n'
         "      monotone' := enatToIntegerOrder_monotone } enatToIntegerOrder_top", 1)],
    'OAI.NumberTheory.PiExponent.Polynomials.PolynomialPoleBound': [
        ('v.map (Int.castAddHom ℝ).withTopMap rfl\n'
         '    ((show Monotone (fun z : ℤ => (z : ℝ)) from Int.cast_mono).withTop_map)',
         'v.map { toAddMonoidHom := (Int.castAddHom ℝ).withTopMap\n'
         "          monotone' := (show Monotone (fun z : ℤ => (z : ℝ)) from Int.cast_mono).withTop_map } rfl", 1)],
    'OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDegree': [
        ('  apply Module.finrank_pos_iff_exists_ne_zero.mpr',
         '  let : Module.IsTorsionFree k (quotientSection P n) :=\n'
         '    DivisionSemiring.to_moduleIsTorsionFree\n'
         '  apply Module.finrank_pos_iff_exists_ne_zero.mpr', 1)],
    'OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFreeResolutionExt': [
        ("ShortComplex.quasiIso_iff_of_zeros' _ (by simp; rfl)",
         "ShortComplex.quasiIso_iff_of_zeros' _ (by simp)", 1)],
    'OAI.NumberTheory.PiExponent.LocalAlgebra.LocalComponentDegree': [
        ('SetLike.not_le_iff_exists', 'IsConcreteLE.not_le_iff_exists', 1)],
    'OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHilbertDimension': [
        ('SetLike.lt_iff_le_and_exists', 'IsConcreteLE.lt_iff_le_and_exists', 1)],
    'OAI.NumberTheory.PiExponent.Geometry.CartierSequence': [
        ('Ideal.span {U.1.topIso.hom\n          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom))}',
         'Ideal.span {(U.1.topIso.hom\n          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom)))}', 1),
        ('Ideal.span {U.1.topIso.hom\n        (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom))}',
         'Ideal.span {(U.1.topIso.hom\n        (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom)))}', 1)],
    'OAI.NumberTheory.PiExponent.Geometry.CartierDegreeLength': [
        ('Ideal.span {U.1.topIso.hom\n          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom))}',
         'Ideal.span {(U.1.topIso.hom\n          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom)))}', 1)],
    'OAI.NumberTheory.PiExponent.Approximation.TwistSectionClearing': [
        ('(restrictScalar U.toScheme V (c ^ k))',
         '(OAI.PiExponent.GlobalSectionClearing.restrictScalar U.toScheme V (c ^ k))', 1)],
    'OAI.NumberTheory.PiExponent.LocalAlgebra.GlobalInvertibleIdeal': [
        ('mono_iso_inv_comp', 'globalInvertible_mono_iso_inv_comp', 2)],
    'OAI.NumberTheory.PiExponent.Cohomology.EulerSupportDimension': [
        ('mono_iso_inv_comp', 'eulerSupport_mono_iso_inv_comp', 2)],
    'OAI.NumberTheory.PiExponent.Geometry.SectionCartierRegular': [
        ('mono_iso_inv_comp', 'sectionCartier_mono_iso_inv_comp', 2)],
    'OAI.NumberTheory.PiExponent.Geometry.CurveDegreeAdditivity': [
        ('Ideal.span {U.1.topIso.hom\n          (endValue (f.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ e.hom))}',
         'Ideal.span {(U.1.topIso.hom\n          (endValue (f.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ e.hom)))}', 1),
        ('Ideal.span {U.1.topIso.hom\n          (endValue (f.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map s ≫ e.hom))}',
         'Ideal.span {(U.1.topIso.hom\n          (endValue (f.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map s ≫ e.hom)))}', 1),
    ],
    'OAI.NumberTheory.PiExponent.Geometry.SectionZeroStalk': [
        ('Ideal.span {(X.presheaf.germ U.1 _ hy)\n        (U.1.topIso.hom (coefficient e (restrictSection U.1.ι s)))}',
         'Ideal.span {((X.presheaf.germ U.1 _ hy)\n        (U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))))}', 1),
    ],
    'OAI.NumberTheory.PiExponent.Geometry.CurveSectionDegree': [
        ('Ideal.span {U.1.topIso.hom\n          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map s ≫ d.hom))}',
         'Ideal.span {(U.1.topIso.hom\n          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map s ≫ d.hom)))}', 1),
    ],
    'OAI.NumberTheory.PiExponent.LocalAlgebra.IdealTensorPowers': [
        ('Ideal.span {affineMapCoefficient U (idealPowerFrame J U.1 e n)\n      (Scheme.Modules.restrictUnitIso U.1.ι) (idealPowerInclusion J ι n)}',
         'Ideal.span {(affineMapCoefficient U (idealPowerFrame J U.1 e n)\n      (Scheme.Modules.restrictUnitIso U.1.ι) (idealPowerInclusion J ι n))}', 1),
        ('Ideal.span {affineMapCoefficient U (tensorFrame J (J.pow n) U.1 e (idealPowerFrame J U.1 e n))\n      (Scheme.Modules.restrictUnitIso U.1.ι) (tensorInclusion J (J.pow n) ι ≫ idealPowerInclusion J ι n)}',
         'Ideal.span {(affineMapCoefficient U (tensorFrame J (J.pow n) U.1 e (idealPowerFrame J U.1 e n))\n      (Scheme.Modules.restrictUnitIso U.1.ι) (tensorInclusion J (J.pow n) ι ≫ idealPowerInclusion J ι n))}', 1),
        ('Ideal.span {affineMapCoefficient U (tensorFrame J (J.pow n) U.1 e (idealPowerFrame J U.1 e n))\n      (idealPowerFrame J U.1 e n) (tensorInclusion J (J.pow n) ι)}',
         'Ideal.span {(affineMapCoefficient U (tensorFrame J (J.pow n) U.1 e (idealPowerFrame J U.1 e n))\n      (idealPowerFrame J U.1 e n) (tensorInclusion J (J.pow n) ι))}', 1),
    ],
    'LogTwo.Geometry.SectionIdealBridge': [
        ("Ideal.span {affineMapCoefficient V a (f' y)\n      ((lineTensorInverseIso J).inv ≫ tensorInclusion J J.inverse ι)}",
         "Ideal.span {(affineMapCoefficient V a (f' y)\n      ((lineTensorInverseIso J).inv ≫ tensorInclusion J J.inverse ι))}", 1),
    ],
    'OAI.NumberTheory.PiExponent.Cohomology.CartierEulerDifference': [
        ("Ideal.span {U.1.topIso.hom\n          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ e'.hom))}",
         "Ideal.span {(U.1.topIso.hom\n          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ e'.hom)))}", 1),
    ],
    'OAI.NumberTheory.PiExponent.Geometry.SectionCartierPower': [
        ("Ideal.span {U.1.topIso.hom\n          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map\n            (cartierPowerMultiply L s n) ≫ e'.hom))}",
         "Ideal.span {(U.1.topIso.hom\n          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map\n            (cartierPowerMultiply L s n) ≫ e'.hom)))}", 1),
    ],
    'OAI.NumberTheory.PiExponent.Cohomology.CartierMixedEuler': [
        ('simpa only [tensorFrame] using!',
         'simpa only [OAI.PiExponent.CartierPowerFrames.tensorFrame] using!', 1),
        ("Ideal.span {U.1.topIso.hom\n          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map\n            (mixedCartierPowerMultiply L M s n) ≫ e'.hom))}",
         "Ideal.span {(U.1.topIso.hom\n          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map\n            (mixedCartierPowerMultiply L M s n) ≫ e'.hom)))}", 1),
    ],
    'OAI.NumberTheory.PiExponent.Ampleness.AmpleCurveDegreePositive': [
        ('Ideal.span {U.1.topIso.hom\n          (endValue (f.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map s ≫ e.hom))}',
         'Ideal.span {(U.1.topIso.hom\n          (endValue (f.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map s ≫ e.hom)))}', 1),
    ],
    'OAI.NumberTheory.PiExponent.Geometry.GeneralCartierDegreeLength': [
        ('Ideal.span {U.1.topIso.hom\n          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom))}',
         'Ideal.span {(U.1.topIso.hom\n          (endValue (e.inv ≫ (Scheme.Modules.restrictFunctor U.1.ι).map φ ≫ d.hom)))}', 1),
    ],
}


def rc4_compatibility(body, name):
    for old, new, count in RC4_EDITS.get(name, []):
        if body.count(old) != count: raise ValueError('rc4 compatibility pattern drift: ' + name)
        body = body.replace(old, new)
    return body


def mask_comments_strings(text):
    """Keep offsets/newlines so scope commands inside comments are not counted."""
    result = list(text)
    i = depth = 0
    string = False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                result[i:i+2] = '  '; depth += 1; i += 2; continue
            if text.startswith('-/', i):
                result[i:i+2] = '  '; depth -= 1; i += 2; continue
            if text[i] != '\n': result[i] = ' '
        elif string:
            if text[i] == '\\' and i + 1 < len(text):
                result[i:i+2] = '  '; i += 2; continue
            if text[i] == '"': string = False
            if text[i] != '\n': result[i] = ' '
        elif text.startswith('/-', i):
            result[i:i+2] = '  '; depth = 1; i += 2; continue
        elif text.startswith('--', i):
            end = text.find('\n', i)
            end = len(text) if end < 0 else end
            result[i:end] = ' ' * (end-i); i = end; continue
        elif text[i] == '"':
            result[i] = ' '; string = True
        i += 1
    if depth or string: raise ValueError('Unclosed comment or string')
    return ''.join(result)


def module_body(text, name):
    lines = text.splitlines(keepends=True)
    masked = mask_comments_strings(text).splitlines(keepends=True)
    body = []
    stack = []
    for actual, code in zip(lines, masked):
        command = code.strip()
        if re.fullmatch(r'module|(?:public )?import .+|@\[expose\] public section', command):
            continue
        opening = re.fullmatch(r'(namespace|(?:noncomputable )?section)(?:\s+(\S+))?', command)
        closing = re.fullmatch(r'end(?:\s+(\S+))?', command)
        if opening:
            kind, label = opening.group(1), opening.group(2)
            if kind == 'namespace':
                stack.extend((kind, part) for part in label.split('.'))
            else:
                stack.append((kind, label))
        elif closing:
            labels = closing.group(1).split('.') if closing.group(1) else [None]
            for expected in reversed(labels):
                if not stack: raise ValueError(f'{name}: unmatched end')
                kind, label = stack.pop()
                if expected and label != expected:
                    raise ValueError(f'{name}: end {expected} closes {kind} {label}')
        body.append(actual)
    # Lean implicitly closes unnamed sections at EOF. Flattening must do so
    # explicitly, before the next module's local instances/options are opened.
    if any(kind == 'namespace' for kind, _ in stack):
        raise ValueError(f'{name}: unclosed namespace: {stack}')
    result = ''.join(body).strip()
    for _, label in reversed(stack): result += '\nend' + (f' {label}' if label else '')
    return result


def generate():
    manifest = json.loads((LEAN/'evidence/source-manifest.json').read_text())
    sources = {s['module']: s for s in manifest['sources']}
    ordered, seen, active, external = [], set(), set(), set()
    def visit(name):
        if name in seen: return
        if name in active: raise ValueError('Import cycle: ' + name)
        active.add(name)
        record = sources[name]; text = (LEAN/record['path']).read_text()
        if hashlib.sha256(text.encode()).hexdigest() != record['sha256']:
            raise ValueError('Source differs from the manifest: ' + name)
        for line in mask_comments_strings(text).splitlines():
            match = re.fullmatch(r'(?:public )?import (.+)', line.strip())
            if match:
                for dep in match.group(1).split():
                    if dep in sources: visit(dep)
                    else: external.add(dep)
        active.remove(name); seen.add(name); ordered.append(name)
    visit('LogTwo')
    if seen != set(sources): raise ValueError('Manifest contains unreachable modules')
    if any(not n.startswith(('Mathlib', 'Lean', 'Batteries', 'Aesop', 'Qq')) for n in external):
        raise ValueError(f'Unexpected external imports: {external}')
    header = '''/-
Copyright 2026 Kenta Kitamura. Portions: OpenAI, openai/math (Apache-2.0).
Modified for LogTwo: module flattening and Lean v4.35.0-rc4 compatibility edits.
See ../THIRD_PARTY_NOTICES.txt and ../LICENSES/openai-math-Apache-2.0.txt.
-/
module
public import Mathlib
@[expose] public section

/-!
# The irrationality exponent of the natural logarithm of 2

Complete generated proof closure. Target: Lean v4.35.0-rc4.
This file is generated from 883 pinned modules; generation alone is not
verification. See README.md and build-status.json for the actual build result.
The split proof is separately checked on Lean v4.34.1.
No local imports, Formal Conjectures dependency, or proof holes are used.
-/
'''
    header = header.replace('883 pinned modules', f'{len(ordered)} pinned modules')
    chunks, mapping = [header], []
    line = len(header.splitlines()) + 1
    for index, name in enumerate(ordered):
        rec = sources[name]
        # A named section prevents open declarations, local attributes and
        # instances from leaking into the next flattened source module.
        chunk = f'\n-- Source: {rec["path"]}\nsection Source{index:04d}\n'
        body = rc4_compatibility(module_body((LEAN/rec['path']).read_text(), name), name)
        # Each source notice is retained, with its link made relative to this file.
        body = re.sub(r'^See (?:\.\./)+THIRD_PARTY_NOTICES\.txt for provenance and the recorded changes\.$',
                      'See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.', body, flags=re.M)
        chunk += body
        chunk += f'\nend Source{index:04d}\n'
        mapping.append({'module':name, 'path':rec['path'], 'sha256':rec['sha256'],
                        'first_line':line, 'last_line':line+len(chunk.splitlines())-1})
        chunks.append(chunk); line += len(chunk.splitlines())
    chunks.append('''
-- Exact final target, with no unproved argument.
example : LogTwo.irrationalityExponent (Real.log 2) = 2 :=
  LogTwo.irrationalityExponent_log_two
#print axioms LogTwo.irrationalityExponent_log_two
''')
    output = ROOT/'lean4web/LogTwoLean4Web.lean'
    output.parent.mkdir(exist_ok=True)
    content = ''.join(chunks); output.write_text(content)
    info = {'generator':'lean/scripts/make_lean4web.py', 'target_lean':'leanprover/lean4:v4.35.0-rc4',
            'module_count':len(mapping), 'lines':len(content.splitlines()), 'bytes':len(content.encode()),
            'sha256':hashlib.sha256(content.encode()).hexdigest(), 'external_source_imports':sorted(external),
            'transformations':['Remove source module/import/public-section headers',
                               'Wrap each source body in a named section',
                               'Close unnamed sections that originally ended at EOF',
                               'Retain modification notices and normalize their relative provenance links',
                               'Qualify HasAntidiagonal.mem_antidiagonal in JetGeometry',
                               'Bundle the monotonicity proof in two AddValuation.map calls',
                               'Provide the field torsion-free instance explicitly in PrimeHilbertDegree',
                               'Remove redundant rfl after simp in FiniteFreeResolutionExt',
                               'Use IsConcreteLE names for two deprecated SetLike order lemmas',
                               'Parenthesize multiline singleton elements to avoid rc4 set-builder parsing',
                               'Rename three private helpers whose names collide after flattening',
                               'Qualify GlobalSectionClearing.restrictScalar in TwistSectionClearing',
                               'Qualify CartierPowerFrames.tensorFrame in the CartierMixedEuler simplification'],
            'rc4_compatibility_modules':sorted(RC4_EDITS),
            'verification_status':'generation_only_see_build-status.json', 'sources':mapping}
    (output.parent/'source-map.json').write_text(json.dumps(info,indent=2)+'\n')
    status_path = output.parent/'build-status.json'
    if status_path.exists():
        old_status = json.loads(status_path.read_text())
        if old_status.get('source_sha256') != info['sha256']:
            previous = old_status.get('previous_full_attempt')
            if old_status.get('run_id'):
                previous = f"evidence/{old_status['run_id']}/result.json"
            status = {'status':'not_checked', 'source_sha256':info['sha256'],
                      'requested_lean':info['target_lean'], 'browser_execution_performed':False,
                      'scope':'Regenerated current source; previous full attempts apply to earlier hashes.',
                      'previous_full_attempt':previous}
            status_path.write_text(json.dumps(status,indent=2)+'\n')
    print(json.dumps({k:v for k,v in info.items() if k not in {'sources', 'external_source_imports'}},indent=2))


if __name__ == '__main__': generate()
