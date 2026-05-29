#!/usr/bin/env python3
"""
Generates and verifies subsetTable and componentTable for the Seahaven solver.

Both tables share the same core predicate:
  output config C is implied by input config P  iff  bits_C is a submask of bits_P
  i.e.  (grlex2bits[C] & grlex2bits[P]) == grlex2bits[C]

Meaning: every suit that C has in extra slots is also in extra in P,
so P "covers" C in terms of king-sequence placement.

subsetTable[childOffset + childSolvable] -> 16-bit parent mask
  Input:  child's solvable bitmask (which k-dedicated-pile configs are solvable).
  Output: full 16-bit grlex mask of parent configs that are provably solvable.
  A parent config P is marked solvable if some solvable child config C covers P.

componentTable[prevOffset + feasibleMask] -> output bitmask (local bits)
  Input:  bitmask of k-1 dedicated-pile configs feasible with one empty pile spare.
  Output: bitmask of k-dedicated-pile configs that form the big reachability component.
  A k-dedicated config C is in the component if some feasible k-1 config P covers C
  (meaning C is a superset of P in dedicated piles, so C is reachable via P).
"""

from math import comb

# grlex2bits[i]: 4-bit mask for grlex index i.
# Bit k SET means suit k's king is in extra slots (not in a dedicated empty pile).
# Grlex ranks by number of SET bits (suits in extra), then lexicographically.
# Index 0 = all 4 kings in dedicated piles; index 15 = all kings in extra.
grlex2bits = [0, 1, 2, 4, 8, 3, 5, 6, 9, 10, 12, 7, 11, 13, 14, 15]

# CLOSURE[k] = (shiftValue, offset):
#   shiftValue: first grlex index for configs with exactly k dedicated piles.
#   offset:     base index in both tables for this freePiles count.
# The number of configs for freePiles = k is C(4, k).
CLOSURE = [
    (15, 98),  # k=0: C(4,0)=1 config,  grlex 15       (all kings in extra)
    (11,  0),  # k=1: C(4,1)=4 configs, grlex 11..14   (1 dedicated pile)
    ( 5, 16),  # k=2: C(4,2)=6 configs, grlex  5..10   (2 dedicated piles)
    ( 1, 80),  # k=3: C(4,3)=4 configs, grlex  1..4    (3 dedicated piles)
    ( 0, 96),  # k=4: C(4,4)=1 config,  grlex  0       (all dedicated)
]


def covers(bits_C, bits_P):
    """True iff config C is covered by config P: bits_C is a submask of bits_P."""
    return (bits_C & bits_P) == bits_C


# ---------------------------------------------------------------------------
# subsetTable
# ---------------------------------------------------------------------------

def compute_subset_table():
    """
    For each child freePiles count k and each solvable bitmask over k-dedicated
    configs, returns a full 16-bit grlex mask of parent configs that are solvable.
    Parent config P is solvable if some solvable child config C covers P.
    """
    table = [0] * 100

    for k in range(5):          # child freePiles = k
        shift_c, offset_c = CLOSURE[k]
        n_bits = comb(4, k)     # C(4,k) valid input bits

        for solvable in range(1 << n_bits):
            parent_mask = 0
            for p_grlex in range(16):
                bits_P = grlex2bits[p_grlex]
                for i in range(n_bits):
                    if solvable & (1 << i):
                        bits_C = grlex2bits[shift_c + i]
                        if covers(bits_C, bits_P):
                            parent_mask |= (1 << p_grlex)
                            break
            table[offset_c + solvable] = parent_mask

    return table


# ---------------------------------------------------------------------------
# componentTable
# ---------------------------------------------------------------------------

def compute_component_table():
    """
    For each freePiles count k (1..4) and each bitmask of feasible k-1 dedicated
    configs (those fitting in 4 extra slots with one pile still empty), returns
    the bitmask of k-dedicated configs that belong to the big reachability component.

    A k-dedicated config C is in the component iff some feasible k-1 config P
    covers C (i.e., bits_C is a submask of bits_P).  The reasoning: all k-1
    feasible configs are mutually reachable via the one empty pile, and from any
    of them you can reach the k-dedicated config C by filling the empty pile with
    the one additional king that C dedicates.

    Unreachable input combinations (e.g. only complementary pairs feasible) are
    not reachable in practice, but the formula still produces a valid result
    (typically 0xf, i.e. all configs reachable) which is safe.
    """
    table = [0] * 100

    for k in range(1, 5):           # freePiles = k (output level)
        shift_in,  offset_in  = CLOSURE[k - 1]   # k-1 dedicated, one empty pile
        shift_out, _          = CLOSURE[k]        # k dedicated
        n_bits_in  = comb(4, k - 1)
        n_bits_out = comb(4, k)

        for feasible_mask in range(1 << n_bits_in):
            out_mask = 0
            for j in range(n_bits_out):
                bits_C = grlex2bits[shift_out + j]
                for i in range(n_bits_in):
                    if feasible_mask & (1 << i):
                        bits_P = grlex2bits[shift_in + i]
                        if covers(bits_C, bits_P):
                            out_mask |= (1 << j)
                            break
            table[offset_in + feasible_mask] = out_mask

    return table


# ---------------------------------------------------------------------------
# Printing
# ---------------------------------------------------------------------------

def print_subset_table(table):
    sections = [
        (1,  0, "level 2 (child freePiles = 1)"),
        (2, 16, "level 3 (child freePiles = 2)"),
        (3, 80, "level 4 (child freePiles = 3)"),
        (4, 96, "level 5 (child freePiles = 4+)"),
        (0, 98, "level 1 (child freePiles = 0)"),
    ]
    print("static const uint16_t subsetTable[100] = {")
    for k, offset, label in sections:
        n = 1 << comb(4, k)
        print(f"    //{label}")
        for start in range(0, n, 8):
            row = [f"0x{table[offset + i]:04x}" for i in range(start, min(start + 8, n))]
            print("    " + ", ".join(row) + ",")
    print("};")


def print_component_table(table):
    sections = [
        (2, 98,  2, "level 1 (freePiles = 1, 2 entries)"),
        (8,  0, 16, "level 2 (freePiles = 2, 16 entries)"),
        (8, 16, 64, "level 3 (freePiles = 3, 64 entries)"),
        (8, 80, 16, "level 4 (freePiles = 4, 16 entries); unused"),
        (2, 96,  2, "level 5 (freePiles = 5+, 2 entries); unused"),
    ]
    print("static const uint8_t componentTable[100] = {")
    for cols, offset, n, label in sections:
        print(f"    // table for {label}")
        for start in range(0, n, cols):
            row = [f"0x{table[offset + i]:02x}" for i in range(start, min(start + cols, n))]
            print("    " + ", ".join(row) + ",")
    print("};")


# ---------------------------------------------------------------------------
# Expected values (from solver.c after subsetTable bug fixes)
# ---------------------------------------------------------------------------

EXPECTED_SUBSET = [
    # offset  0: child freePiles=1
    0x0000, 0x8800, 0x9000, 0x9800, 0xa000, 0xa800, 0xb000, 0xb800,
    0xc000, 0xc800, 0xd000, 0xd800, 0xe000, 0xe800, 0xf000, 0xf800,
    # offset 16: child freePiles=2
    0x0000, 0x9820, 0xa840, 0xb860, 0xc880, 0xd8a0, 0xe8c0, 0xf8e0,
    0xb100, 0xb920, 0xb940, 0xb960, 0xf980, 0xf9a0, 0xf9c0, 0xf9e0,
    0xd200, 0xda20, 0xfa40, 0xfa60, 0xda80, 0xdaa0, 0xfac0, 0xfae0,
    0xf300, 0xfb20, 0xfb40, 0xfb60, 0xfb80, 0xfba0, 0xfbc0, 0xfbe0,
    0xe400, 0xfc20, 0xec40, 0xfc60, 0xec80, 0xfca0, 0xecc0, 0xfce0,
    0xf500, 0xfd20, 0xfd40, 0xfd60, 0xfd80, 0xfda0, 0xfdc0, 0xfde0,
    0xf600, 0xfe20, 0xfe40, 0xfe60, 0xfe80, 0xfea0, 0xfec0, 0xfee0,
    0xf700, 0xff20, 0xff40, 0xff60, 0xff80, 0xffa0, 0xffc0, 0xffe0,
    # offset 80: child freePiles=3 (corrected)
    0x0000, 0xb962, 0xdaa4, 0xfbe6, 0xecc8, 0xfdea, 0xfeec, 0xffee,
    0xf710, 0xff72, 0xffb4, 0xfff6, 0xffd8, 0xfffa, 0xfffc, 0xfffe,
    # offset 96: child freePiles=4+
    0x0000, 0xffff,
    # offset 98: child freePiles=0
    0x0000, 0x8000,
]

EXPECTED_COMPONENT = [
    # offset  0: freePiles=2 (16 entries)
    0x00, 0x07, 0x19, 0x1f, 0x2a, 0x2f, 0x3b, 0x3f,
    0x34, 0x37, 0x3d, 0x3f, 0x3e, 0x3f, 0x3f, 0x3f,
    # offset 16: freePiles=3 (64 entries)
    0x0, 0x3, 0x5, 0x7, 0x6, 0x7, 0x7, 0x7,
    0x9, 0xb, 0xd, 0xf, 0xf, 0xf, 0xf, 0xf,
    0xa, 0xb, 0xf, 0xf, 0xe, 0xf, 0xf, 0xf,
    0xb, 0xb, 0xf, 0xf, 0xf, 0xf, 0xf, 0xf,
    0xc, 0xf, 0xd, 0xf, 0xe, 0xf, 0xf, 0xf,
    0xd, 0xf, 0xd, 0xf, 0xf, 0xf, 0xf, 0xf,
    0xe, 0xf, 0xf, 0xf, 0xe, 0xf, 0xf, 0xf,
    0xf, 0xf, 0xf, 0xf, 0xf, 0xf, 0xf, 0xf,
    # offset 80: freePiles=4 (16 entries, unused)
    0x0, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1,
    0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1,
    # offset 96: freePiles=5+ (2 entries, unused)
    0x0, 0x0,
    # offset 98: freePiles=1 (2 entries)
    0x00, 0x0f,
]


def verify(computed, expected, name):
    if computed == expected:
        print(f"# {name}: verified, matches solver.c exactly.")
    else:
        print(f"# {name}: MISMATCH:")
        for i, (got, exp) in enumerate(zip(computed, expected)):
            if got != exp:
                print(f"#   [{i}]: got 0x{got:x}, expected 0x{exp:x}")


if __name__ == "__main__":
    st = compute_subset_table()
    ct = compute_component_table()

    print("=" * 70)
    print_subset_table(st)
    print()
    print_component_table(ct)
    print()
    verify(st, EXPECTED_SUBSET,    "subsetTable")
    verify(ct, EXPECTED_COMPONENT, "componentTable")
