#!/bin/python

import math
import os
import random
import re
import sys


#
# Complete the 'solve' function below.
#
# The function is expected to return a STRING_ARRAY.
# The function accepts STRING_ARRAY grid as parameter.
#

# Paste this code above the judge's existing __main__ block.
# Keep the judge's input/output wrapper exactly once.
import os
import sys
import time
from collections import deque

class _TimeUp(Exception):
    pass

class _Masyu(object):
    def __init__(self, grid, limit=9.0):
        self.clock = getattr(time, 'monotonic', time.time)
        self.start = self.clock()
        self.deadline = self.start + limit
        self.hard_deadline = self.deadline
        self.R, self.C = len(grid), len(grid[0])
        self.stride = self.C + 2
        self.n = (self.R + 2) * self.stride
        self.delta = (-self.stride, 1, self.stride, -1)
        self.bits = (1, 2, 4, 8)
        # Edge bits: N=1, E=2, S=4, W=8.
        # Domains are bit sets over these seven cell shapes.
        self.shapes = (0, 5, 10, 3, 9, 6, 12)
        self.edge = (26, 44, 98, 84)
        self.cells = []
        self.kind = ['.'] * self.n
        self.dom = [1] * self.n
        self.adj = [[] for _ in range(self.n)]
        self.watch = [[] for _ in range(self.n)]
        self.pearls = []
        for r, row in enumerate(grid):
            for c, ch in enumerate(row):
                i = (r + 1) * self.stride + c + 1
                self.cells.append(i)
                self.kind[i] = ch
                d = 6 if ch == 'W' else 120 if ch == 'B' else 127
                if r == 0: d &= ~26
                if c == self.C - 1: d &= ~44
                if r == self.R - 1: d &= ~98
                if c == 0: d &= ~84
                self.dom[i] = d
                if ch != '.':
                    self.pearls.append(i)
        self.forced = [0] * 128
        self.possible = [0] * 128
        self.count = [0] * 128
        for d in range(1, 128):
            f, p, cnt = 15, 0, 0
            for s, mask in enumerate(self.shapes):
                if d & (1 << s):
                    f &= mask
                    p |= mask
                    cnt += 1
            self.forced[d], self.possible[d], self.count[d] = f, p, cnt
        tables = {}
        for black_a in (False, True):
            for black_b in (False, True):
                for k in range(4):
                    one = []
                    for a in self.shapes:
                        allowed = 0
                        for t, b in enumerate(self.shapes):
                            ea = bool(a & self.bits[k])
                            eb = bool(b & self.bits[(k + 2) & 3])
                            if ea != eb:
                                continue
                            if ea and ((black_a and b not in (5, 10)) or
                                       (black_b and a not in (5, 10))):
                                continue
                            allowed |= 1 << t
                        one.append(allowed)
                    table = [0] * 128
                    for d in range(1, 128):
                        for s in range(7):
                            if d & (1 << s):
                                table[d] |= one[s]
                    tables[black_a, black_b, k] = table
        for i in self.cells:
            for k, step in enumerate(self.delta):
                j = i + step
                if self.dom[j] != 1:
                    self.adj[i].append((j, tables[self.kind[i] == 'B',
                                                 self.kind[j] == 'B', k]))
                if self.kind[j] == 'W':
                    self.watch[i].append(j)
            if self.kind[i] == 'W':
                self.watch[i].append(i)
        self.parent = list(range(self.n))
        self.size = [1] * self.n
        self.end0 = list(range(self.n))
        self.end1 = list(range(self.n))
        self.fixed = [0] * self.n
        self.trail = []
        self.unions = []
        self.required = sum(not (self.dom[i] & 1) for i in self.cells)
        rr = [i // self.stride for i in self.pearls]
        cc = [i % self.stride for i in self.pearls]
        self.lower = max(4, len(self.pearls),
                         2 * (max(rr) - min(rr) + max(cc) - min(cc)))
        self.lower += self.lower & 1
        self.best = None
        self.best_length = self.R * self.C + 1
        self.ticks = 0
        self.nodes = 0
        self.restarts = 0
        self.weight = [1.0] * self.n
        for i in self.cells:
            self.weight[i] = (1.0 + (2 if self.kind[i] != '.' else 0) +
                              sum(self.kind[i+d] != '.' for d in self.delta))

    def find(self, i):
        while self.parent[i] != i:
            i = self.parent[i]
        return i

    def narrow(self, i, d, queue):
        old = self.dom[i]
        if d == old:
            return True
        if not d:
            self.weight[i] += 2.0
            for j, table in self.adj[i]:
                self.weight[j] += 0.25
            return False
        self.trail.append((i, old))
        if old & 1 and not d & 1:
            self.required += 1
        self.dom[i] = d
        queue.append(i)
        return True

    def undo(self, mark, umark):
        while len(self.unions) > umark:
            i, j, bit, obit, a, b, sz, e0, e1 = self.unions.pop()
            self.fixed[i] ^= bit
            self.fixed[j] ^= obit
            self.parent[b] = b
            self.size[a], self.end0[a], self.end1[a] = sz, e0, e1
        while len(self.trail) > mark:
            i, old = self.trail.pop()
            if old & 1 and not self.dom[i] & 1:
                self.required -= 1
            self.dom[i] = old

    def pearl_ok(self, i, masks):
        m = masks[i]
        if self.kind[i] == 'W':
            if m not in (5, 10):
                return False
            ends = [i + self.delta[k] for k in range(4) if m & self.bits[k]]
            return any(masks[j] in (3, 6, 9, 12) for j in ends)
        if m not in (3, 6, 9, 12):
            return False
        return all(masks[i + self.delta[k]] in (5, 10)
                   for k in range(4) if m & self.bits[k])

    def shorten(self, masks, length):
        stop = min(self.hard_deadline, self.clock() + 0.025)
        changed = True
        while changed and self.clock() < stop:
            changed = False
            for r in range(1, self.R):
                if self.clock() >= stop:
                    return length
                for c in range(1, self.C):
                    a = r * self.stride + c
                    b, d = a + 1, a + self.stride
                    e = d + 1
                    present = (bool(masks[a] & 2) + bool(masks[b] & 4) +
                               bool(masks[e] & 8) + bool(masks[d] & 1))
                    if present != 3:
                        continue
                    vertices = (a, b, e, d)
                    old = [masks[v] for v in vertices]
                    for v, toggle in zip(vertices, (6, 12, 9, 3)):
                        masks[v] ^= toggle
                    affected = set()
                    for v in vertices:
                        if self.kind[v] != '.':
                            affected.add(v)
                        for step in self.delta:
                            if self.kind[v+step] != '.':
                                affected.add(v+step)
                    if all(self.pearl_ok(p, masks) for p in affected):
                        length -= 2
                        changed = True
                    else:
                        for v, m in zip(vertices, old):
                            masks[v] = m
        return length

    def accept_cycle(self, i, j, bit, obit, root):
        if self.size[root] != self.required:
            return False
        masks = self.fixed[:]
        masks[i] |= bit
        masks[j] |= obit
        if not all(self.pearl_ok(p, masks) for p in self.pearls):
            return False
        length = self.size[root]
        if length < self.best_length:
            length = self.shorten(masks, length)
            self.best, self.best_length = masks, length
            now = self.clock()
            # The first second is free in the speed score.
            self.deadline = min(self.deadline,
                                max(self.start + 0.85, now + 0.08))
        return True

    def propagate(self, queue):
        dom, edge, fixed = self.dom, self.edge, self.fixed
        while queue:
            self.ticks += 1
            if self.ticks & 127 == 0 and self.clock() >= self.deadline:
                raise _TimeUp()
            i = queue.pop()
            if not dom[i] or self.required >= self.best_length:
                return False
            for j, table in self.adj[i]:
                if not self.narrow(j, dom[j] & table[dom[i]], queue):
                    return False
            # A white pearl needs a turn at one of its two ends.
            for p in self.watch[i]:
                d = dom[p]
                for shape, k in ((2, 0), (4, 1)):
                    if not d & shape:
                        continue
                    a, b = p + self.delta[k], p - self.delta[k]
                    ta = dom[a] & 120 & edge[(k + 2) & 3]
                    tb = dom[b] & 120 & edge[k]
                    if not (ta or tb):
                        d &= ~shape
                if not self.narrow(p, d, queue):
                    return False
                if d in (2, 4):
                    k = 0 if d == 2 else 1
                    a, b = p + self.delta[k], p - self.delta[k]
                    ta = dom[a] & 120 & edge[(k + 2) & 3]
                    tb = dom[b] & 120 & edge[k]
                    if not ta and not self.narrow(b, tb, queue):
                        return False
                    if not tb and not self.narrow(a, ta, queue):
                        return False
            # Maintain forced paths with a reversible union-find.
            new_edges = self.forced[dom[i]] & ~fixed[i]
            for k in range(4):
                bit = self.bits[k]
                if not new_edges & bit:
                    continue
                j = i + self.delta[k]
                obit = self.bits[(k + 2) & 3]
                if not self.narrow(j, dom[j] & edge[(k + 2) & 3], queue):
                    return False
                a, b = self.find(i), self.find(j)
                if a == b:
                    self.accept_cycle(i, j, bit, obit, a)
                    return False
                e0 = self.end1[a] if self.end0[a] == i else self.end0[a]
                e1 = self.end1[b] if self.end0[b] == j else self.end0[b]
                if self.size[a] < self.size[b]:
                    a, b = b, a
                self.unions.append((i, j, bit, obit, a, b, self.size[a],
                                    self.end0[a], self.end1[a]))
                self.parent[b] = a
                self.size[a] += self.size[b]
                self.end0[a], self.end1[a] = e0, e1
                fixed[i] |= bit
                fixed[j] |= obit
            root = self.find(i)
            if self.size[root] < self.required:
                a, b = self.end0[root], self.end1[root]
                diff = b - a
                if diff in self.delta:
                    k = self.delta.index(diff)
                    if (not fixed[a] & self.bits[k] and
                            not self.narrow(a, dom[a] & ~edge[k], queue)):
                        return False
        return True

    def cut_check(self, queue):
        # A closed loop crosses each full row/column cut an even number of times.
        for k in (1, 2):
            groups = (range(1, self.C) if k == 1 else range(1, self.R))
            for line in groups:
                positions = ([r*self.stride+line for r in range(1, self.R+1)]
                             if k == 1 else
                             [line*self.stride+c for c in range(1, self.C+1)])
                odd, unknown = 0, []
                bit = self.bits[k]
                for i in positions:
                    if self.forced[self.dom[i]] & bit:
                        odd ^= 1
                    elif self.possible[self.dom[i]] & bit:
                        unknown.append(i)
                if not unknown:
                    if odd:
                        return False
                elif len(unknown) == 1:
                    i = unknown[0]
                    allowed = self.edge[k] if odd else ~self.edge[k]
                    if not self.narrow(i, self.dom[i] & allowed, queue):
                        return False
        return True

    def topology(self, queue):
        # Every required cell must belong to one biconnected component.
        # Iterative Tarjan traversal avoids Python 2 recursion limits.
        dom, possible = self.dom, self.possible
        start = self.pearls[0]
        discovery = [-1] * self.n
        low = [0] * self.n
        parent = [-1] * self.n
        discovery[start] = low[start] = 0
        stamp = 1
        frames = [[start, 0]]
        edges = []
        while frames:
            i, k = frames[-1]
            if k < 4:
                frames[-1][1] += 1
                if not possible[dom[i]] & self.bits[k]:
                    continue
                j = i + self.delta[k]
                if not possible[dom[j]] & self.bits[(k + 2) & 3]:
                    continue
                if discovery[j] < 0:
                    parent[j] = i
                    discovery[j] = low[j] = stamp
                    stamp += 1
                    edges.append((i, j))
                    frames.append([j, 0])
                elif j != parent[i] and discovery[j] < discovery[i]:
                    edges.append((i, j))
                    low[i] = min(low[i], discovery[j])
                continue
            frames.pop()
            p = parent[i]
            if p < 0:
                continue
            low[p] = min(low[p], low[i])
            if low[i] >= discovery[p]:
                block = set()
                while edges:
                    a, b = edges.pop()
                    block.add(a)
                    block.add(b)
                    if a == p and b == i:
                        break
                if (len(block) >= self.required and
                        sum(not (dom[v] & 1) for v in block) == self.required):
                    if len(block) < 4:
                        return False
                    for v in self.cells:
                        if v not in block and not self.narrow(v, dom[v] & 1, queue):
                            return False
                    return True
        return False

    def choose(self):
        dom, fixed, count = self.dom, self.fixed, self.count
        chosen, key = -1, (100.0, 8, 8)
        ends = []
        for i in self.cells:
            if dom[i] & 1:
                continue
            if fixed[i] in (0, 1, 2, 4, 8):
                ends.append(i)
            n = count[dom[i]]
            if n > 1:
                rank = ((n - 1.0) / self.weight[i],
                        0 if fixed[i] else 1,
                        (i * (12345 + 2 * self.restarts)) & 65535)
                if rank < key:
                    chosen, key = i, rank
        if chosen < 0:
            return -1, []
        root = self.find(chosen)
        targets = [i for i in ends if self.find(i) != root]
        if not targets:
            targets = [i for i in ends if i != chosen]
        if not targets:
            return -1, []

        # A lower bound on extra cells needed to join the forced path ends.
        if self.best is not None and len(ends) <= 48:
            roots = [self.find(i) for i in ends]
            several = any(r != roots[0] for r in roots)
            total = 0
            for t, i in enumerate(ends):
                ri, ci = divmod(i, self.stride)
                nearest = self.n
                for u, j in enumerate(ends):
                    if i == j or (several and roots[t] == roots[u]):
                        continue
                    rj, cj = divmod(j, self.stride)
                    nearest = min(nearest, abs(ri-rj) + abs(ci-cj) - 1)
                if nearest < self.n:
                    total += nearest * (2 if fixed[i] == 0 else 1)
            if self.required + (total + 1) // 2 >= self.best_length:
                return -1, []

        # Prefer short possible routes to another required path.
        dist = [-1] * self.n
        dist[chosen] = -2
        queue = deque()
        for i in targets:
            dist[i] = 0
            queue.append(i)
        need = set()
        for k in range(4):
            if (self.possible[dom[chosen]] & self.bits[k] and
                    not fixed[chosen] & self.bits[k]):
                need.add(chosen + self.delta[k])
        need.difference_update(targets)
        while queue and need:
            i = queue.popleft()
            allowed = self.possible[dom[i]]
            for k in range(4):
                if not allowed & self.bits[k]:
                    continue
                j = i + self.delta[k]
                if dist[j] != -1 or fixed[j] not in (0, 1, 2, 4, 8):
                    continue
                if not self.possible[dom[j]] & self.bits[(k + 2) & 3]:
                    continue
                dist[j] = dist[i] + 1
                queue.append(j)
                need.discard(j)
        values = []
        for s in range(1, 7):
            value = 1 << s
            if not dom[chosen] & value:
                continue
            mask = self.shapes[s] & ~fixed[chosen]
            score, usable = 0, True
            for k in range(4):
                if mask & self.bits[k]:
                    j = chosen + self.delta[k]
                    if dist[j] < 0:
                        usable = False
                        break
                    score += dist[j] * 4 + bool(dom[j] & 1)
            if usable:
                values.append((score,
                               (s * (12345 + 2 * self.restarts)) & 65535,
                               value))
        values.sort(reverse=True)
        return chosen, [v[2] for v in values]

    def run(self):
        stack = []
        queue = self.cells[:]
        interval, restart_at = 256, 256
        try:
            while True:
                self.nodes += 1
                if self.best is None and self.nodes >= restart_at:
                    self.undo(0, 0)
                    stack = []
                    queue = self.cells[:]
                    self.restarts += 1
                    interval = interval * 3 // 2
                    restart_at += interval
                if self.clock() >= self.deadline or self.best_length <= self.lower:
                    break
                feasible = self.propagate(queue)
                if feasible and self.nodes % 8 == 1:
                    queue = []
                    feasible = self.cut_check(queue)
                    if feasible and queue:
                        feasible = self.propagate(queue)
                    if feasible:
                        feasible = self.topology(queue)
                    if feasible and queue:
                        feasible = self.propagate(queue)
                if feasible:
                    i, values = self.choose()
                    if values:
                        stack.append((len(self.trail), len(self.unions), i, values))
                if self.best_length <= self.lower:
                    break
                while stack:
                    mark, umark, i, values = stack[-1]
                    self.undo(mark, umark)
                    if values:
                        queue = []
                        value = values.pop()
                        self.narrow(i, value, queue)
                        break
                    stack.pop()
                else:
                    break
        except _TimeUp:
            pass
        if self.best is None:
            return None
        chars = {0: '.', 5: '|', 10: '-', 3: 'L', 9: 'J', 6: 'F', 12: '7'}
        return [''.join(chars[self.best[(r+1)*self.stride+c+1]]
                        for c in range(self.C)) for r in range(self.R)]

def solve(grid):
    solver = _Masyu(grid)
    result = solver.run()
    if result is not None:
        return result
    # Search budget exhausted: preserve output dimensions; this case scores zero.
    return ['.' * len(grid[0]) for _ in grid]

if __name__ == '__main__':
    fptr = open(os.environ['OUTPUT_PATH'], 'w')

    grid_count = int(raw_input().strip())

    grid = []

    for _ in xrange(grid_count):
        grid_item = raw_input()
        grid.append(grid_item)

    result = solve(grid)

    fptr.write('\n'.join(result))
    fptr.write('\n')

    fptr.close()
