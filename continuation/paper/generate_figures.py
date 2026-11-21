#!/usr/bin/env python3
"""Reproduce the two Rule 110 figures in the continuation manuscript.

The rule, initial words, coordinate conventions, and displayed domains are
specified in Sections 3 and 5 of the paper. No simulation result is used as a
substitute for the unbounded theorems.
"""
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from matplotlib.colors import ListedColormap
from matplotlib.patches import Rectangle

HERE = Path(__file__).resolve().parent
OUT = HERE / 'figures'
OUT.mkdir(exist_ok=True)
plt.rcParams.update({'font.family': 'DejaVu Sans', 'font.size': 9,
                     'pdf.fonttype': 42, 'ps.fonttype': 42,
                     'axes.spines.top': False, 'axes.spines.right': False,
                     'axes.spines.left': False, 'axes.spines.bottom': False})
CMAP = ListedColormap(['#eef3f5', '#17384b'])
ACCENT = '#b95427'

def rule(l, c, r):
    return (c | r) ^ (l & c & r)

def evolve(initial, times, lo=-80, hi=80):
    coords = np.arange(lo, hi + 1)
    row = np.array([initial(int(x)) for x in coords], dtype=np.uint8)
    rows = [row.copy()]
    for _ in range(times):
        # Boundary values cannot affect any displayed cell within this horizon.
        new = np.zeros_like(row)
        new[1:-1] = rule(row[:-2], row[1:-1], row[2:])
        row = new
        rows.append(row.copy())
    return coords, np.stack(rows)

def setup(ax, xticks, yticks):
    ax.set_xticks(xticks)
    ax.set_yticks(yticks)
    ax.tick_params(length=0, pad=5, labelsize=8, colors='#17384b')
    ax.text(1.02, -0.075, '$x$', transform=ax.transAxes, color='#17384b')
    ax.text(-0.10, 1.025, '$t$', transform=ax.transAxes, color='#17384b')

fig, axes = plt.subplots(1, 2, figsize=(6.8, 2.48), constrained_layout=False)
for ax, phase in zip(axes, (0, 7)):
    def initial(x):
        return ((16072 >> ((x + phase) % 14)) & 1) if x < 4 else (x - 4).bit_count() % 2
    coords, rows = evolve(initial, 20)
    shown = rows[:, (coords >= -16) & (coords <= 15)]
    ax.imshow(shown, interpolation='none', cmap=CMAP, vmin=0, vmax=1,
              extent=(-16.5, 15.5, 20.5, -0.5), aspect='equal')
    # A mark in the boundary cell x=-j; the theorem covers x strictly below it.
    for j in range(11):
        ax.plot([-j - 0.5, -j - 0.5], [2*j - 0.45, 2*j + 0.45],
                color=ACCENT, linewidth=1.5, solid_capstyle='butt')
    ax.set_title(f'$p={phase}$', color='#17384b', pad=8, fontsize=10)
    setup(ax, [-16, -8, 0, 8, 15], [0, 4, 8, 12, 16, 20])
fig.subplots_adjust(left=.065, right=.98, top=.87, bottom=.15, wspace=.24)
fig.savefig(OUT / 'crystal-phases.pdf', bbox_inches='tight', pad_inches=.03)
fig.savefig(OUT / 'crystal-phases.png', dpi=220, bbox_inches='tight', pad_inches=.03)
plt.close(fig)

words = [('00000001100001000000', '00000001100101000000'),
         ('00010111010001000010', '00010111010101000010')]
fig, axes = plt.subplots(1, 2, figsize=(6.8, 1.77), constrained_layout=False)
for k, (ax, pair) in enumerate(zip(axes, words)):
    data = []
    for word in pair:
        coords, rows = evolve(lambda x, w=word: int(w[x+6]) if -6 <= x <= 13 else 0, 4)
        data.append(rows)
    delta = data[0] ^ data[1]
    assert not np.any(delta[-1])
    assert not np.any(delta[:, (coords < 1) | (coords > 9)])
    shown = delta[:, (coords >= 1) & (coords <= 9)]
    ax.imshow(shown, interpolation='none', cmap=CMAP, vmin=0, vmax=1,
              extent=(.5, 9.5, 4.5, -.5), aspect='equal')
    ax.set_xticks(np.arange(.5, 10, 1), minor=True)
    ax.set_yticks(np.arange(-.5, 5, 1), minor=True)
    ax.grid(which='minor', color='white', linewidth=.6)
    ax.tick_params(which='minor', length=0)
    ax.add_patch(Rectangle((2.5, 1.5), 1, 1, fill=False, edgecolor=ACCENT, linewidth=1.7))
    ax.set_title(f'$K={k}$', color='#17384b', pad=7, fontsize=10)
    setup(ax, list(range(1,10)), list(range(5)))
fig.subplots_adjust(left=.065, right=.98, top=.82, bottom=.17, wspace=.46)
fig.savefig(OUT / 'coalescence-witnesses.pdf', bbox_inches='tight', pad_inches=.03)
fig.savefig(OUT / 'coalescence-witnesses.png', dpi=220, bbox_inches='tight', pad_inches=.03)
plt.close(fig)
print('Generated both figures from the stated Rule 110 data.')
