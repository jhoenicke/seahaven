#!/usr/bin/env python3
"""
Computes the subsetTable for the Seahaven Towers solver.

The subsetTable maps a child state's solvable king-configuration bitmask to
a 16-bit parent mask.  A parent configuration P is marked solvable if there
exists a solvable child configuration C such that the set of suits with
dedicated empty piles in P is a subset of those in C.

In bitmask terms (bit k SET = suit k's king is in extra slots, not in a
dedicated empty pile):

    P is reachable from C  iff  (grlex2bits[C] & grlex2bits[P]) == grlex2bits[C]

i.e., every suit that C has in extra is also in extra in P.

For a given child freePiles count k, the solvable bitmask has C(4,k) valid bits
(one per combination of k suits with dedicated piles), stored at consecutive
grlex positions starting at closureInfos[k].shiftValue.
Note: the numBits field in the C ClosureInfo struct is NOT the number of valid
input bits; it covers configurations for both k and k+1 empty piles.
"""

from math import comb

# grlex2bits[i]: 4-bit mask for grlex index i.
# Bit k SET means suit k's king is in extra slots (not in a dedicated empty pile).
# Ranked by number of SET bits (suits in extra), then lexicographically.
grlex2bits = [0, 1, 2, 4, 8, 3, 5, 6, 9, 10, 12, 7, 11, 13, 14, 15]

# CLOSURE[k] = (shiftValue, offset):
#   shiftValue: first grlex index for configs with exactly k dedicated piles.
#   offset:     base index into subsetTable for child freePiles = k.
# The number of valid input bits for child freePiles = k is C(4, k).
CLOSURE = [
    (15, 98),  # child_piles=0: C(4,0)=1 config,  grlex 15     (all kings in extra)
    (11,  0),  # child_piles=1: C(4,1)=4 configs, grlex 11..14 (1 dedicated pile)
    ( 5, 16),  # child_piles=2: C(4,2)=6 configs, grlex  5..10 (2 dedicated piles)
    ( 1, 80),  # child_piles=3: C(4,3)=4 configs, grlex  1..4  (3 dedicated piles)
    ( 0, 96),  # child_piles=4: C(4,4)=1 config,  grlex  0     (all dedicated)
]


def compute_subset_table():
    table = [0] * 100

    for child_piles in range(5):
        shift_c, offset_c = CLOSURE[child_piles]
        n_bits_c = comb(4, child_piles)  # number of valid input bits

        for child_solvable in range(1 << n_bits_c):
            parent_mask = 0
            for parent_grlex in range(16):
                bits_P = grlex2bits[parent_grlex]
                # P is solvable if some solvable child config C has extraC ⊆ extraP,
                # i.e., (grlex2bits[C] & bits_P) == grlex2bits[C].
                for local_bit in range(n_bits_c):
                    if child_solvable & (1 << local_bit):
                        bits_C = grlex2bits[shift_c + local_bit]
                        if (bits_C & bits_P) == bits_C:
                            parent_mask |= (1 << parent_grlex)
                            break
            table[offset_c + child_solvable] = parent_mask

    return table


def print_c_table(table):
    # Print in the same layout order as solver.c (by ascending offset)
    sections = [
        (1,  0, "level 2 (child freePiles = 1)"),
        (2, 16, "level 3 (child freePiles = 2)"),
        (3, 80, "level 4 (child freePiles = 3)"),
        (4, 96, "level 5 (child freePiles = 4+)"),
        (0, 98, "level 1 (child freePiles = 0)"),
    ]
    print("static const uint16_t subsetTable[100] = {")
    for child_piles, offset_c, label in sections:
        n_entries = 1 << comb(4, child_piles)
        print(f"    //{label}")
        for row_start in range(0, n_entries, 8):
            row = [f"0x{table[offset_c + i]:04x}"
                   for i in range(row_start, min(row_start + 8, n_entries))]
            print("    " + ", ".join(row) + ",")
    print("};")


# Expected values from solver.c (in array index order 0..99)
EXPECTED = [
    # offset  0: child freePiles=1 (16 entries, bits 0..3 of child_solvable)
    0x0000, 0x8800, 0x9000, 0x9800, 0xa000, 0xa800, 0xb000, 0xb800,
    0xc000, 0xc800, 0xd000, 0xd800, 0xe000, 0xe800, 0xf000, 0xf800,
    # offset 16: child freePiles=2 (64 entries, bits 0..5 of child_solvable)
    0x0000, 0x9820, 0xa840, 0xb860, 0xc880, 0xd8a0, 0xe8c0, 0xf8e0,
    0xb100, 0xb920, 0xb940, 0xb960, 0xf980, 0xf9a0, 0xf9c0, 0xf9e0,
    0xd200, 0xda20, 0xfa40, 0xfa60, 0xda80, 0xdaa0, 0xfac0, 0xfae0,
    0xf300, 0xfb20, 0xfb40, 0xfb60, 0xfb80, 0xfba0, 0xfbc0, 0xfbe0,
    0xe400, 0xfc20, 0xec40, 0xfc60, 0xec80, 0xfca0, 0xecc0, 0xfce0,
    0xf500, 0xfd20, 0xfd40, 0xfd60, 0xfd80, 0xfda0, 0xfdc0, 0xfde0,
    0xf600, 0xfe20, 0xfe40, 0xfe60, 0xfe80, 0xfea0, 0xfec0, 0xfee0,
    0xf700, 0xff20, 0xff40, 0xff60, 0xff80, 0xffa0, 0xffc0, 0xffe0,
    # offset 80: child freePiles=3 (16 entries, bits 0..3 of child_solvable)
    0x0000, 0xb962, 0xdaa4, 0xfbe6, 0xecc8, 0xfdea, 0xfeec, 0xffee,
    0xf710, 0xff72, 0xffb4, 0xfff6, 0xffd8, 0xfffa, 0xfffc, 0xfffe,
    # offset 96: child freePiles=4+ (2 entries, bit 0 of child_solvable)
    0x0000, 0xffff,
    # offset 98: child freePiles=0  (2 entries, bit 0 of child_solvable)
    0x0000, 0x8000,
]

if __name__ == "__main__":
    table = compute_subset_table()
    print_c_table(table)

    if table == EXPECTED:
        print("\n# Verified: matches solver.c subsetTable exactly.")
    else:
        print("\n# MISMATCH:")
        for i, (got, exp) in enumerate(zip(table, EXPECTED)):
            if got != exp:
                print(f"#   table[{i}]: got 0x{got:04x}, expected 0x{exp:04x}")
