# Mechanical migration of jolt-qed's hand-written proofs from the old Sail
# extraction (Sail eff56f4, lean-sail v3, Lean 4.29) to the new one (Sail
# 2ae2199f, lean-sail v8, Lean 4.35). Run from the repository root on a clean
# checkout of JoltBytecode/ and JoltConstraints/.
#
# Name mapping:
#   old model wrappers  Sail.X                         -> LeanRV64D.X
#                       Sail.ConcurrencyInterfaceV1.X  -> LeanRV64D.ConcurrencyInterfaceV1.X
#                       Sail.assert                    -> LeanRV64D.sail_assert
#   old runtime         PreSail.X                      -> Sail.ConcurrencyInterfaceV1.PreSail.X
#                       PreSail.ConcurrencyInterfaceV1.X -> Sail.ConcurrencyInterfaceV1.PreSail.X
#                       PreSail.assert                 -> Sail.ConcurrencyInterfaceV1.PreSail.sail_assert
#   generated types moved from the root namespace into LeanRV64D: `open LeanRV64D`
#   in every file whose imports reach the model.
import os, re, functools, sys

ROOTS = ('JoltBytecode', 'JoltConstraints')
RT = 'Sail.ConcurrencyInterfaceV1.PreSail'
WRAPPERS = {
    'sailTryCatch', 'sailThrow', 'undefined_unit', 'undefined_bit', 'undefined_bool',
    'undefined_int', 'undefined_range', 'undefined_nat', 'undefined_string',
    'undefined_bitvector', 'undefined_vector', 'internal_pick', 'writeReg', 'readReg',
    'RegisterRef', 'readRegRef', 'writeRegRef', 'reg_deref', 'cycle_count',
    'get_cycle_count', 'print_effect', 'print_int_effect', 'print_bits_effect',
    'print_endline_effect', 'SailME', 'sailTryCatchE', 'unwrapValue',
}
NOT_PRE = r'(?<![\w.])'

def rewrite(s):
    # Runtime names first (they contain `Sail.` as a substring).
    s = re.sub(NOT_PRE + r'PreSail\.ConcurrencyInterfaceV1\.', RT + '.', s)
    s = re.sub(NOT_PRE + r'PreSail\.assert\b', RT + '.sail_assert', s)
    s = re.sub(NOT_PRE + r'PreSail\.(?!sail_assert\b)(?=[A-Za-z_])', RT + '.', s)
    # Model wrappers.
    s = re.sub(NOT_PRE + r'Sail\.assert\b', 'LeanRV64D.sail_assert', s)
    s = re.sub(NOT_PRE + r'Sail\.ConcurrencyInterfaceV1\.(?!PreSail\b)', 'LeanRV64D.ConcurrencyInterfaceV1.', s)
    s = re.sub(NOT_PRE + r'Sail\.(' + '|'.join(sorted(WRAPPERS)) + r')\b', r'LeanRV64D.\1', s)
    # Opens.
    opens = 'Sail Sail.ConcurrencyInterfaceV1 ' + RT + ' LeanRV64D LeanRV64D.Functions'
    s = re.sub(r'\bSail PreSail LeanRV64D\.Functions\b', opens, s)
    s = re.sub(r'^(\s*)open Sail PreSail$', r'\1open Sail Sail.ConcurrencyInterfaceV1 ' + RT + ' LeanRV64D', s, flags=re.M)
    s = re.sub(r'^(\s*)open LeanRV64D\.Functions$', r'\1open LeanRV64D LeanRV64D.Functions', s, flags=re.M)
    return s

FINTYPE_NOTE = ('-- Lean 4.35: Mathlib v4.35.0 derives enum `Fintype` only with this option '
                '(see MathlibTest/DeriveFintype.lean).\n'
                'set_option backward.isDefEq.respectTransparency false in')

def fintype_option(text):
    L = text.split('\n'); ins = []
    for i, l in enumerate(L):
        if re.search(r'deriving.*\bFintype\b', l):
            j = i
            while not L[j].startswith('inductive'): j -= 1
            k = j
            if L[k - 1].rstrip().endswith('-/'):
                k -= 1
                while not L[k].lstrip().startswith('/--'): k -= 1
            if not L[k - 1].startswith('set_option backward.isDefEq.respectTransparency'):
                ins.append(k)
    for k in sorted(set(ins), reverse=True): L.insert(k, FINTYPE_NOTE)
    return '\n'.join(L)

files = {}
for r in ROOTS:
    for d, _, fs in os.walk(r):
        for f in fs:
            if f.endswith('.lean'):
                p = os.path.join(d, f); files[p[:-5].replace('/', '.')] = p
imps = {m: re.findall(r'^import\s+(\S+)', open(p).read(), re.M) for m, p in files.items()}

@functools.lru_cache(None)
def reaches(m):
    for i in imps.get(m, []):
        if i == 'LeanRV64D' or i.startswith('LeanRV64D.'): return True
        if i in files and reaches(i): return True
    return False

changed = 0
for m, p in files.items():
    s = open(p).read(); o = s
    s = rewrite(s)
    s = fintype_option(s)
    if reaches(m) and not re.search(r'^open LeanRV64D$', s, re.M):
        L = s.split('\n')
        idx = [i for i, l in enumerate(L) if l.startswith('import ')]
        L.insert(idx[-1] + 1, '\nopen LeanRV64D'); s = '\n'.join(L)
    if s != o:
        open(p, 'w').write(s); changed += 1
print('files changed', changed, 'of', len(files), file=sys.stderr)
