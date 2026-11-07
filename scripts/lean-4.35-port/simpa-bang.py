# Lean 4.35: `simpa ... using h` checks the simplified hypothesis against the
# goal at reducible transparency; `using!` restores the default-transparency
# check of earlier versions. Rewrites the simpa call at each
# "Type mismatch: After simplification" error in a lake build log.
import re, sys, collections
log = open(sys.argv[1]).read()
sites = collections.defaultdict(set)
for f, l, c in re.findall(r'^error: (\S+\.lean):(\d+):(\d+): Type mismatch: After simplification', log, re.M):
    sites[f].add((int(l), int(c)))
n = 0
for f, ps in sites.items():
    L = open(f).read().split('\n')
    for l, c in sorted(ps):
        i = l - 1
        start = L[i].find('simpa', c)
        if start < 0: print('no simpa at', f, l, c); continue
        for j in range(i, min(i + 8, len(L))):
            s0 = start if j == i else 0
            m = re.compile(r'\busing(?!!)\b').search(L[j], s0)
            if m:
                L[j] = L[j][:m.start()] + 'using!' + L[j][m.end():]; n += 1; break
        else:
            print('no using after', f, l, c)
    open(f, 'w').write('\n'.join(L))
print('rewrote', n, 'sites in', len(sites), 'files')
