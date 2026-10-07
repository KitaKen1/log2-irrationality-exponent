"""Canonical interface migration to Lean's public module format.
Hash-pinned allowlists expose legacy private declarations and remove two
redundant rfl tactics already closed by simp. Mathematical statements and type-alias bodies
are unchanged; exported helpers are renamed where necessary; no arbitrary proof-script edits pass.
"""
import hashlib, re

PUBLIC_DECLARATIONS = {
    '34f2e99e81b4d0a6d2fda6d1c83f3b4ffa0cf3c7384068bf77c1e0a0ebccfd20': (('local instance', '<anonymous>'),),
    '8f40dc74e4186c3ebef49e081f91a18ed7550863ec4a72138cc34ee9764498e5': (('abbrev', 'schemeFreeOpen'),),
    '9eb092d5be19a34f05daa8539d69c391d2e9c03c69749446e5c27234f6b89abb': (('abbrev', 'schemeFreeOpen'),),
    'c0f95b8578636b9e04fadd1cb3499b365245b9c33e9610323e032ae418e79129': (('abbrev', 'powerSections'),),
    '10a2d7904ed48890e278a172eb65965f3a0b6720db2167dd4307b26746a66dd2': (('abbrev', 'schemeFreeOpen'),),
    'd4c80f9e314aeade927a027110f1928fd85dac9a9f449a8fb8f9e7c9e5a8bd34': (('abbrev', 'schemeFreeOpen'),),
    '13850c3f96e226c369d41cefd00aa484117a674d7784fb6ee1e15f102e736c5a': (('abbrev', 'coordinateInv'), ('local instance', 'coordinateSpec_isIso')),
    'c43248d4b168d4966902f863f69eae5a95f909259e7cabc6c6f207695ede44bc': (('abbrev', 'chartMap'), ('local instance', 'chartOpenImmersion')),
    'f164fe9763b3c8905996b69adec4f91d18f7e381b261b970c4b1cbe3e967126e': (('abbrev', 'chartMap'), ('local instance', 'chartOpenImmersion')),
    '6ffc93f7912af52140e0debee2de7c796d118db53c9dba8d4e953eb49b32f389': (('abbrev', 'schemeFreeOpen'),),
    'be7bd3a01980abc72283fdff70fa0a10265e403e1a88ab99a763c69b38a5b775': (('abbrev', 'schemeFreeOpen'),),
    '954aa63edfb3f80abe7e9cb2f76d6bb76fb89ea9d882be2a58a9d005fa97f2ca': (('abbrev', 'schemeFreeOpen'), ('abbrev', 'schemeUnit'), ('def', 'freeOpenHomAddCommGroup'), ('def', 'higherCochainAddCommGroup')),
    'dd85183173064be799a727575203428275c0ff001278ed7eda6aa332c4e338da': (('abbrev', 'schemeUnit'), ('abbrev', 'schemeFreeOpen')),
    'e18d292facf931ee43b0f5de47f02444cb19e59548c56cffdb0e7faa10ff143e': (('abbrev', 'chartMap'), ('local instance', 'frozenChartOpenImmersion'), ('abbrev', 'schemeFreeOpen'), ('local instance', 'cochainAddCommGroup')),
    'a29899814b44a6c0fcd1129e86435b36a10018cbdc0facd467fae331d2d7e11e': (('abbrev', 'chartMap'), ('local instance', 'frozenChartOpenImmersion'), ('abbrev', 'schemeFreeOpen')),
    '137d9ca981f8bd2585a9711f9e94f569c720f14710a004355830fb4462a8f67b': (('abbrev', 'schemeFreeOpen'), ('local instance', 'cochainAddCommGroup')),
    'e30dd0adaf16bda7b447ac18f19653917bf557a3bc1e12da84bae1740f4a91a3': (('abbrev', 'schemeFree'), ('abbrev', 'schemeInclusion')),
    '9f676607ee5e6088ac782962929faf302c834cd298423279aa529581bf646e22': (('def', 'presentationOfIso'),),
    '0b2d13cdb5170e924b8815be81c6fc9be1c14bd84d132d6a6993dd86bf137adf': (('abbrev', 'schemeUnit'),),
    '39d907a2c03c9fe0ed16a6ea29be34200761e776d4a88a4165e4cec994bec678': (('abbrev', 'schemeUnit'),),
    'fb48f89356322353fb0967b61e3c85a41c4512d6ff3e4098e1bafdee5b292bda': (('abbrev', 'schemeUnit'),),
    '7b00242f9729298847aff8946004da60f966b278840672aae082dd427b1f6c79': (('abbrev', 'schemeUnit'),),
    '2acc65e3c4d094eb5537af4a81968f9e72c8bd36558d865a60de6308b9eda7d3': (('abbrev', 'schemeFreeOpen'),),
    '317ce8d0d1debf13b20cf0412fbe2107476622e1ef13e30167b189e2812e8925': (('abbrev', 'schemeFreeOpen'),),
    'deebf043f698bbc73b8933b49680ce3ab38577f58abf538c858fb4b4ec11b825': (('abbrev', 'schemeFreeOpen'), ('def', 'freeOpenHomAddCommGroup'), ('def', 'higherCochainAddCommGroup'), ('def', 'freeOpenHomModule')),
    'ff2ae50c8926a1568e345cdf5462c6dacf8c94c66b066063e439435495c91c9d': (('abbrev', 'schemeFreeOpen'),),
    'cf403c0cd6dba39f3ac4c4652bb559c8b475648f4ef4ee2cb859801084146aa4': (('abbrev', 'schemeFreeOpen'),),
    '124957f404f2c9ad0ea2cc03c66a908b07e4c06a839c98a300dd231b32233712': (('abbrev', 'schemeFreeOpen'), ('def', 'freeOpenHomAddCommGroup')),
    '6d6a74534627d54e8fef2c5033afc49ae5c99c4f4ce520280849c9e8095c8d66': (('abbrev', 'schemeFreeOpen'), ('def', 'freeOpenHomAddCommGroup')),
    '8f4dafb6a9e85e6495e253d5e72027e18f517dfd6ceccd4fdf61360edb130927': (('abbrev', 'schemeUnit'),),
    '1c690a7e4242ada63637650ef05b68a7a4285005177ffdcd1ba1e326f410e411': (('abbrev', 'schemeFreeOpen'),),
    '0f9b11f3d1995f10337abbff9e5c6155841d7b75eee7652c126669254e2670b1': (('abbrev', 'schemeFreeOpen'), ('abbrev', 'schemeUnit')),
    '0e80255ad9e72840f6b81bde26febb2f9a35794248235ac90853c1e6afcb33d3': (('abbrev', 'schemeFreeOpen'),),
    '3d7c4250d50fa1ea47de216181e2af685b23dd0c47e2f7eaeb4863e15bc895d6': (('def', 'presentationOfIso'),),
    'cf2034b7db26e90c8b189c578cf63902ffe678327781f7c8c37efb9e656b1242': (('abbrev', 'schemeFreeOpen'),),
    'f9e02e513182655cde7cf34185fa5ab7bc784cb14bf0ab93e9350725cb08ec5c': (('abbrev', 'schemeFreeOpen'),),
    'cf7692fc6911835eee08e67624c9806ca770501ef8905938385034e046f8ada3': (('abbrev', 'schemeFreeOpen'),),
    '955226f1563f50b34f1e2a8895043147f67d44d30a881cb81920237e91d8b278': (('abbrev', 'schemeFreeOpen'),),
    '3aa9360a24987b083676913234df0649a7a1e73b36a68bbe4f07ea3193fd06bd': (('abbrev', 'schemeFreeOpen'),),
    'cdd81d583dfc7fb7440f7fe9dafbccae35bc5fd182a0b79854860eaab59c1372': (('abbrev', 'schemeFreeOpen'),),
    'ac8c295b894736b31bae90eb380463d096a47f316b06579ebd4119ab96b94201': (('abbrev', 'schemeUnit'),),
    '99373d66afcd38fd61bf8d5455ecefb6560ff5898ca6cf2ef60dc79555dd676f': (('def', 'parameterCurveUnit'),),
    '0c0cc2223d18f63b1e3045247a2045811c1811a2929aed39caa97802e9389b48': (('abbrev', 'schemeFreeOpen'), ('abbrev', 'schemeShortComplex'), ('abbrev', 'schemeFreeOpenEquiv')),
    '7e10277f773c017936de3d91a5f59411f1a19cba56b7ad83c354d82e005c4d80': (('abbrev', 'schemeFreeOpen'), ('def', 'freeOpenHomAddCommGroup')),
    # A public theorem type uses this local module instance; retain local scope.
    "544f87d9505294e8d86b740985c5b0b00b7ac9b39cc7fffa8b701029aaafd4a1": (("local instance", "sectionModule"),),
    # Pinned Cohomology/FiniteCoverCohomology.lean, before header migration.
    "c32705bdbd4bcd7b331d025b4edd28d157b83987e6d255326fe5949800fe024a":
        (("abbrev", "schemeUnit"), ("abbrev", "schemeBasicOpen"), ("abbrev", "schemeFreeOpen")),
    "9bf3f3da51a44264ee4767e9b49ceebf1bdce8fc33a85dd2a5c5b80d0dd9bbe1": (("def", "presentationOfIso"),),
}

PROOF_COMPATIBILITY = {
    '2d421a5a027686d46438a51ae38540b4808afa0b08670837657640e541b0ee4b': (('  simp [groupAlgebraToLaurent, fullExponentEquiv]\n  rfl\n', '  simp [groupAlgebraToLaurent, fullExponentEquiv]\n'), ('    simp [groupAlgebraToLaurent, fullExponentEquiv]\n    rfl\n', '    simp [groupAlgebraToLaurent, fullExponentEquiv]\n')),
}

PUBLIC_HELPER_RENAMES = {
    'be7bd3a01980abc72283fdff70fa0a10265e403e1a88ab99a763c69b38a5b775': (('schemeFreeOpen', 'pushforwardComparisonFreeOpen'),),
    '10a2d7904ed48890e278a172eb65965f3a0b6720db2167dd4307b26746a66dd2': (('schemeFreeOpen', 'exceptionalOpaqueFreeOpen'),),
    '1c690a7e4242ada63637650ef05b68a7a4285005177ffdcd1ba1e326f410e411': (('schemeFreeOpen', 'projectiveFramedCechFreeOpen'),),
    'cf2034b7db26e90c8b189c578cf63902ffe678327781f7c8c37efb9e656b1242': (('schemeFreeOpen', 'coordinateScalarFreeOpen'),),
    'f9e02e513182655cde7cf34185fa5ab7bc784cb14bf0ab93e9350725cb08ec5c': (('schemeFreeOpen', 'negativeScalarFreeOpen'),),
    'cdd81d583dfc7fb7440f7fe9dafbccae35bc5fd182a0b79854860eaab59c1372': (('schemeFreeOpen', 'schemeFiniteFreeOpen'),),
    '0c0cc2223d18f63b1e3045247a2045811c1811a2929aed39caa97802e9389b48': (('schemeFreeOpen', 'pencilCechFreeOpen'),),
}

def imports(text):
    return [name for line in text.splitlines()
            if (match := re.match(r'^(?:public )?import (.+)$', line))
            for name in match.group(1).split()]

def to_public_module(text):
    if re.search(r'^module(?:\s|$)',text,re.M):
        return text
    original_hash = hashlib.sha256(text.encode()).hexdigest()
    for old, new in PROOF_COMPATIBILITY.get(original_hash, ()):
        if text.count(old) != 1:
            raise ValueError("Pinned proof compatibility mismatch")
        text = text.replace(old, new, 1)
    for kind, name in PUBLIC_DECLARATIONS.get(original_hash, ()):
        if name == '<anonymous>':
            text, count = re.subn(r'^private ' + re.escape(kind) + r' (?=\()', kind + ' ', text, flags=re.M)
            if count != 1:
                raise ValueError('Pinned anonymous declaration migration mismatch')
            continue
        text, count = re.subn(r'^((?:@\[[^\n]*\] )?)private ' + re.escape(kind) + ' ' + re.escape(name) + r'\b',
                              r'\g<1>' + kind + ' ' + name, text, flags=re.M)
        if count != 1:
            raise ValueError('Pinned declaration migration mismatch: ' + name)
    for old, new in PUBLIC_HELPER_RENAMES.get(original_hash, ()):
        text = re.sub(r"\b" + re.escape(old) + r"\b", new, text)
    lines=text.splitlines(keepends=True)
    last=max(i for i,line in enumerate(lines) if line.startswith('import '))
    return ('module\n\n'+''.join('public '+line if line.startswith('import ') else line
            for line in lines[:last+1])+'\n@[expose] public section\n'+''.join(lines[last+1:]))
