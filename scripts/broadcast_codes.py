"""Enumerate linear messages for all three-receiver digraphs."""
from collections import Counter
from itertools import combinations


def span(rows):
    vals={0}
    for r in rows:
        vals |= {r^x for x in vals}
    return frozenset(vals)


def broadcast():
    subspaces=sorted({span(s) for k in range(4) for s in combinations(range(1,8),k)},key=lambda s:(len(s),sorted(s)))
    assert len(subspaces)==16
    counts=Counter()
    e=[1,2,4]
    for graph in range(64):
        edges=[(i,j) for i in range(3) for j in range(3) if i!=j]
        L=[[e[j] for bit,(u,j) in enumerate(edges) if u==i and graph&(1<<bit)] for i in range(3)]
        for B in subspaces:
            if all(e[i] in span((*L[i],*B)) for i in range(3)):
                counts[len(B).bit_length()-1]+=1
                break
    assert counts=={3:25,2:38,1:1}
    return dict(counts)


if __name__ == "__main__":
    print(broadcast())
